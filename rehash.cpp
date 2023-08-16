#include <cstdio>
#include <ctime>
#include <cerrno>
#include <cstring>

#include "libxnvme.h"
#include "libxnvme_pp.h"
#include "libxnvme_znd.h"
#include "libxnvme_nvm.h"
#include "libxnvme_spec.h"
#include "libxnvme_lba.h"
#include "libxnvmec.h"
#include "libxnvme_util.h"

#include <iostream>
#include <random>
#include <thread>
#include <chrono>
#include <stack>
#include <queue>
#include <map>
#include <atomic>
#include <vector>
#include "pthread.h"
#include "unistd.h"
#include <mutex>
#include <condition_variable>

using namespace std;

int wp_manager[256][9];         //현재 bucket의 위치
unsigned char cacheInMemData[256][8][4096];
//unsigned char zoneState[40704]; //0 EMPTY, 1 USING(OPENED), 2 FINISH, 3 OPENED & FILLED
atomic<int> zoneState[40704]; 
//unsigned char rehashState[256][9]; //0 not rehashing, 1 rehashing
atomic<int> rehashState[256][9]; 
int currRehashState;
atomic<int> putState[256][9]; 
atomic<int> num_chaining[256][9];
int num_rehash[256][9] = { 0 };
int rehash_ptr[256][9]; //rehash zone 현재 bucket의 위치 
int lastRehashedPt[256]; //zone의 어디까지 rehash되었는지 
stack<unsigned char*> location[256][9];
queue<unsigned char*> storeKeys;
std::map< unsigned char, int> *rehashDicPtr[256][9];
clock_t startPart, endPart, start1, end1;
double totalTime = 0;
double totalTimeJoin = 0; 

void OpenZone(struct xnvme_dev * dev, int zoneNumber){
	//change the zoneState except when openZone function was called from startZoneChaing
        if (zoneState[zoneNumber].load() != 3) {
                zoneState[zoneNumber].store(1);
        }
        //int로 들어온 숫자의 Zone을 open(ZRWA)함
	printf("OPEN ZONE %d \n", zoneNumber);
        int err;
        struct xnvme_cmd_ctx ctx = xnvme_cmd_ctx_from_dev(dev);
       err = xnvme_znd_mgmt_send(&ctx, 0x1, zoneNumber * 24576, false, XNVME_SPEC_ZND_CMD_MGMT_SEND_OPEN,  
		       XNVME_SPEC_ZND_MGMT_OPEN_WITH_ZRWA, NULL); 
        if (err || xnvme_cmd_ctx_cpl_status(&ctx)) {
                printf("xnvme_cmd_zone_mgmt(EOPEN) \n");
                xnvmec_perr("xnvmec_cli_to_opts()", err);
        }
}

void FinishZone(struct xnvme_dev * dev, int zoneNumber){
	zoneState[zoneNumber].store(2);
	printf("FINSH ZONE %d \n", zoneNumber);
        //int로 들어온 숫자의 Zone을 Finish 함
        int err;
        struct xnvme_cmd_ctx ctx = xnvme_cmd_ctx_from_dev(dev);
       err = xnvme_znd_mgmt_send(&ctx, 0x1, zoneNumber * 24576, false, XNVME_SPEC_ZND_CMD_MGMT_SEND_FINISH, XNVME_SPEC_ZND_MGMT_OPEN_WITH_ZRWA, NULL);
        if (err || xnvme_cmd_ctx_cpl_status(&ctx)) {
                printf("xnvme_cmd_zone_mgmt(EOPEN) \n");
                xnvmec_perr("xnvmec_cli_to_opts()", err);
        }
}

void linkInitCacheInMemData(int zoneNum, int inZoneBucketNum, int link){ //cache 데이터 초기화 + linking
	for(int i = 0; i < 4092; i++){
		cacheInMemData[zoneNum][inZoneBucketNum][i] = 0;
	}
	cacheInMemData[zoneNum][inZoneBucketNum][4092] = (wp_manager[zoneNum][8] / 24576) / 256;
	cacheInMemData[zoneNum][inZoneBucketNum][4093] = (wp_manager[zoneNum][8] / 24576) % 256;
	cacheInMemData[zoneNum][inZoneBucketNum][4094] = link / 256;
	cacheInMemData[zoneNum][inZoneBucketNum][4095] = link % 256;
	return;
}

void linkInitCacheInMemDataRehash(int zoneNum, int inZoneBucketNum, int link){ //cache 데이터 초기화 + linking
        for(int i = 0; i < 4092; i++){
                cacheInMemData[zoneNum][inZoneBucketNum][i] = 0;
        }
        cacheInMemData[zoneNum][inZoneBucketNum][4092] = (rehash_ptr[zoneNum][8] / 24576) / 256;
        cacheInMemData[zoneNum][inZoneBucketNum][4093] = (rehash_ptr[zoneNum][8] / 24576) % 256;
        cacheInMemData[zoneNum][inZoneBucketNum][4094] = link / 256;
        cacheInMemData[zoneNum][inZoneBucketNum][4095] = link % 256;
        return;
}

int findSwitchLocation(int zoneNum){
	for(int i = 0; i < 8; i++){
		if(wp_manager[zoneNum][i] / 128 < wp_manager[zoneNum][8] % 24576 + 8){	
			return i;
		}
	}
	return -1;
}

int findSwitchLocationRehash(int zoneNum){
	for(int i = 0; i < 8; i++){
		if(rehash_ptr[zoneNum][i] / 128 < rehash_ptr[zoneNum][8] % 24576 + 8){
			return i;
		}
	}
	return -1;
}


void zoneStateInit(){
	for(int i =0; i < 256; i++){
		for(int j = 0; j < 9; j++){
			(rehashState[i][j]).store(0);
			(putState[i][j]).store(0); 
			(num_chaining[i][j]).store(0); 
		}
	} 
	return;
}


int findAvalableZone(){
	for(int i = 0; i < 40704; i++){
		if(zoneState[i].load() == 0){
			//To prevent other threads to get the same zone
        		zoneState[i].store(3);
			return i;
		}
	}
	return -1;
}

int findNewZone(struct xnvme_dev * dev){
        for(int i = 0; i < 40704; i++){
                if(zoneState[i].load() == 1){
			//To prevent other threads to get the same zone
                        zoneState[i].store(3);
                        return i;
                } 
        }
        return -1;
}

void startZoneChaing(struct xnvme_dev * dev, int zoneBucket, int inZoneBucket){
	int newZone = findAvalableZone();
	if(newZone == -1){
		printf("FULL ZNS\n");
	}
	OpenZone(dev, newZone); 

	for(int i = 0; i < 8; i++){
		//현재 wp 있는 것들 new로 옮기기
		//duf 정보 채우기
		void * dbuf = NULL;
        	dbuf = xnvme_buf_alloc(dev, 4096);
		if (!dbuf) {
			printf("xnvme_buf_alloc\n");
                	return;
		}

		for(int j = 0; j < 4096; j++){
                	*(unsigned char *)(dbuf + j) = cacheInMemData[zoneBucket][i][j];
      		}
	
		{
			int err;
                        struct xnvme_cmd_ctx ctx = xnvme_cmd_ctx_from_dev(dev);
                        ctx = xnvme_cmd_ctx_from_dev(dev);
                        err = xnvme_nvm_write(&ctx, 0x1, newZone * 24576 + i, 0, dbuf, NULL);
                        if (err || xnvme_cmd_ctx_cpl_status(&ctx)) {
                                printf("xnvme_nvm_write ZoneChaining %d -> %d\n",wp_manager[zoneBucket][8] / 24576 , newZone);
                        }
                }

		//현재 wp 를 new wp 로 변경 zone wp 포함
		wp_manager[zoneBucket][i] = i * 128;

		xnvme_buf_free(dev, dbuf);
	}
	//Zone Finish
	FinishZone(dev, wp_manager[zoneBucket][8] / 24576);

	//wp_8 변경
	wp_manager[zoneBucket][8] = newZone * 24576;

	return;
}

void startZoneChaingRehash(struct xnvme_dev * dev, int zoneBucket, int inZoneBucket){
        int newZone = findAvalableZone();
        if(newZone == -1){
                printf("FULL ZNS\n");
        }
        OpenZone(dev, newZone);
        //zoneState[newZone] = 3;

        for(int i = 0; i < 8; i++){
                //현재 wp 있는 것들 new로 옮기기
                //duf 정보 채우기
                void * dbuf = NULL;
                dbuf = xnvme_buf_alloc(dev, 4096);
                if (!dbuf) {
                        printf("xnvme_buf_alloc\n");
                        return;
                }

                for(int j = 0; j < 4096; j++){
                        *(unsigned char *)(dbuf + j) = cacheInMemData[zoneBucket][i][j];
                }

                {
                        int err;
                        struct xnvme_cmd_ctx ctx = xnvme_cmd_ctx_from_dev(dev);
                        ctx = xnvme_cmd_ctx_from_dev(dev);
                        err = xnvme_nvm_write(&ctx, 0x1, newZone * 24576 + i, 0, dbuf, NULL);
                        if (err || xnvme_cmd_ctx_cpl_status(&ctx)) {
                                printf("xnvme_nvm_write ZoneChaining %d -> %d\n",rehash_ptr[zoneBucket][8] / 24576 , newZone);
                        }
                }

                //현재 wp 를 new wp 로 변경 zone wp 포함
                rehash_ptr[zoneBucket][i] = i * 128;

                xnvme_buf_free(dev, dbuf);
        }
        //Zone Finish
        FinishZone(dev, rehash_ptr[zoneBucket][8] / 24576);

        //wp_8 변경
        rehash_ptr[zoneBucket][8] = newZone * 24576;

        return;
}

void rehash(unsigned char * key, struct xnvme_dev *dev, unsigned char newBucket, unsigned char newZone){	
	 //cache값에 key 추가
        for(int i = 0; i < 32; i++){
                cacheInMemData[newZone][newBucket][(rehash_ptr[newZone][newBucket] % 128) * 32 + i] = key[i];
        }

        //duf 정보 채우기

        void * dbuf = NULL;	
        dbuf = xnvme_buf_alloc(dev, 4096);
        if (!dbuf) {
                printf("xnvme_buf_alloc\n");
                exit(-1);
        }	

        for(int i = 0; i < 4096; i++){
                *(unsigned char *)(dbuf + i) = cacheInMemData[newZone][newBucket][i];
        }

	{
	     struct xnvme_cmd_ctx ctx = xnvme_cmd_ctx_from_dev(dev);
                ctx = xnvme_cmd_ctx_from_dev(dev);
                int err; 
		err = xnvme_nvm_write(&ctx, 0x1, (rehash_ptr[newZone][8] / 24576) * 24576 + (rehash_ptr[newZone][newBucket] / 128), 0, dbuf, NULL); //block에 정보 쓰기 
        }
	
	rehash_ptr[newZone][newBucket] = rehash_ptr[newZone][newBucket] + 1;

	
	//꽉찬경우
	if(rehash_ptr[newZone][newBucket] % 128 * 32 == 4096 - 64){ // wp 가 뒤에서 3번째 원소 쓴 이후 trigger
		num_chaining[newZone][newBucket].store(num_chaining[newZone][newBucket].load() + 1);
		//window 1인 경우
		if(rehash_ptr[newZone][newBucket] / 128 < rehash_ptr[newZone][8] % 24576 + 8){
			//다음 cache 초기값
			linkInitCacheInMemDataRehash(newZone, newBucket, rehash_ptr[newZone][newBucket] / 128);
			rehash_ptr[newZone][newBucket] = ((rehash_ptr[newZone][8] + 8) % 24576 + newBucket) * 128 ; // 단순 8 칸올리면 switch 이후 적용 불가
			for(int i = 0; i < 4096; i++){
		                *(unsigned char *)(dbuf + i) = cacheInMemData[newZone][newBucket][i];
        		}
        		{
				int err;
	                	struct xnvme_cmd_ctx ctx = xnvme_cmd_ctx_from_dev(dev);
	                	ctx = xnvme_cmd_ctx_from_dev(dev);
        		        err = xnvme_nvm_write(&ctx, 0x1, (rehash_ptr[newZone][8] / 24576) * 24576 + rehash_ptr[newZone][newBucket] / 128, 0, dbuf, NULL);
        	        	if (err || xnvme_cmd_ctx_cpl_status(&ctx)) {
	                        	printf("xnvme_nvm_write block 1 : %d block loc : %d \n", rehash_ptr[newZone][8]/24576 * 24576 + rehash_ptr[newZone][newBucket] / 128,  rehash_ptr[newZone][newBucket]);
	                	}
        		}
		}
		//window 2인경우 swiching 해줘야함
		else{
			int swapBucketNum = findSwitchLocationRehash(newZone);
			//switch 시켜서 앞에 넣을수 없는경우 + Zone 이 꽉차버린 경우			
			if(swapBucketNum == -1){
				if(rehash_ptr[newZone][8] % 24576 == 24576 - 24){
					startZoneChaingRehash(dev, newZone, newBucket);
				}
				else{
					linkInitCacheInMemDataRehash(newZone, newBucket, rehash_ptr[newZone][newBucket] / 128);
					rehash_ptr[newZone][8] = rehash_ptr[newZone][8] + 8; 	// block 기준 이동
					rehash_ptr[newZone][newBucket] = ((rehash_ptr[newZone][8] + 8) % 24576 + newBucket) * 128; // 단순 8 칸올리면 switch 이후 적용 불가
					for(int i = 0; i < 4096; i++){
	                        	        *(unsigned char *)(dbuf + i) = cacheInMemData[newZone][newBucket][i];
        	        	        }
                		        {
        	                	        int err;
	                                	struct xnvme_cmd_ctx ctx = xnvme_cmd_ctx_from_dev(dev);
	                                	ctx = xnvme_cmd_ctx_from_dev(dev);
        	                	        err = xnvme_nvm_write(&ctx, 0x1, (rehash_ptr[newZone][8] / 24576) * 24576 + rehash_ptr[newZone][newBucket] / 128, 0, dbuf, NULL);
                		                if (err || xnvme_cmd_ctx_cpl_status(&ctx)) {
                	        	                printf("xnvme_nvm_write block 2-1 : %d block loc : %d \n",rehash_ptr[newZone][8]/24576 * 24576 + rehash_ptr[newZone][newBucket] / 128,  rehash_ptr[newZone][newBucket]);
        	                        	}
					}
				}
			}
			//switch 시켜서 앞에 넣을수 있는경우
			else{
				//window 1의 값 2로 옮기기
				for(int i = 0; i < 4096; i++){
                                        *(unsigned char *)(dbuf + i) = cacheInMemData[newZone][swapBucketNum][i];
                                }
				{
                                        int err;
                                        struct xnvme_cmd_ctx ctx = xnvme_cmd_ctx_from_dev(dev);
                                        ctx = xnvme_cmd_ctx_from_dev(dev);
                                        err = xnvme_nvm_write(&ctx, 0x1, rehash_ptr[newZone][8] + 8 + swapBucketNum, 0, dbuf, NULL);
                                        if (err || xnvme_cmd_ctx_cpl_status(&ctx)) {
                                                printf("xnvme_nvm_write block 2-2-1 : %d block loc : %d \n", rehash_ptr[newZone][8]/24576 * 24576 + rehash_ptr[newZone][newBucket] / 128,  rehash_ptr[newZone][newBucket]);
                                        }
                                }
				//window 2의 값 1로 옮기기
				for(int i = 0; i < 4096; i++){
                                        *(unsigned char *)(dbuf + i) = cacheInMemData[newZone][newBucket][i];
                                }
                                {
                                        int err;
                                        struct xnvme_cmd_ctx ctx = xnvme_cmd_ctx_from_dev(dev);
                                        ctx = xnvme_cmd_ctx_from_dev(dev);
                                        err = xnvme_nvm_write(&ctx, 0x1, rehash_ptr[newZone][8] + swapBucketNum, 0, dbuf, NULL);
                                        if (err || xnvme_cmd_ctx_cpl_status(&ctx)) {
                                                printf("xnvme_nvm_write block 2-2-2 : %d block loc : %d \n", rehash_ptr[newZone][8]/24576 * 24576 + rehash_ptr[newZone][newBucket] / 128,  wp_manager[newZone][newBucket]);
                                        }
                                }
				//새로운 window 2 초기값 설정
				//printf("swap : %d WP_swap : %d\n", swapBucketNum, wp_manager[zoneBucket][swapBucketNum]);
				linkInitCacheInMemDataRehash(newZone, newBucket, rehash_ptr[newZone][swapBucketNum] / 128);
				rehash_ptr[newZone][newBucket] = (rehash_ptr[newZone][8] % 24576 + 8 + newBucket) * 128;
				
				for(int i = 0; i < 4096; i++){
                                        *(unsigned char *)(dbuf + i) = cacheInMemData[newZone][newBucket][i];
                                }
                                {
                                        int err;
                                        struct xnvme_cmd_ctx ctx = xnvme_cmd_ctx_from_dev(dev);
                                        ctx = xnvme_cmd_ctx_from_dev(dev);
                                        err = xnvme_nvm_write(&ctx, 0x1, (rehash_ptr[newZone][8] / 24576) * 24576 + rehash_ptr[newZone][newBucket] / 128, 0, dbuf, NULL);
                                        if (err || xnvme_cmd_ctx_cpl_status(&ctx)) {
                                                printf("xnvme_nvm_write block 2-2-3 : %d block loc : %d \n", rehash_ptr[newZone][8]/24576 * 24576 + rehash_ptr[newZone][newBucket] / 128,  rehash_ptr[newZone][newBucket]);
                                        }
                                }
				rehash_ptr[newZone][swapBucketNum] = 8  * 128 + rehash_ptr[newZone][swapBucketNum];				
			}
		}
	}	
	xnvme_buf_free(dev, dbuf);
	return;
       
}

void readDataInChaining(unsigned char * key, struct xnvme_dev * dev){
        //chaining에 있는 key값 모두 다 읽고 stack안에 넣기
       //key값의 inZoneBucket, zoneBucket값 추출
        unsigned char inZoneBucketNum = key[0] % 8;
        unsigned char zoneNum = (key[1] % 8) * 32 + key[0] / 8;	

        while(true){
                int currBit = 0;
                while(currBit < 4096){	
                        void * currKey = NULL;
			currKey = xnvme_buf_alloc(dev, 32);
                	if (!currKey) {
                        	printf("xnvme_buf_alloc\n");
                        	return;
                	}	
                        for(int i=0; i<32; i++){
                                *(unsigned char *)(currKey + i) = cacheInMemData[zoneNum][inZoneBucketNum][i + currBit];
                        }	
                        location[zoneNum][inZoneBucketNum].push((unsigned char *) currKey);
                      
                        currBit += 32;
			xnvme_buf_free(dev, currKey);
                }
                unsigned char zoneNum1 = cacheInMemData[zoneNum][inZoneBucketNum][4092]; //1 byte = 8 bit -> xxxx xxxx
                unsigned char zoneNum2 = cacheInMemData[zoneNum][inZoneBucketNum][4093]; //xxxx xxxx
                unsigned char inZoneNum1 = cacheInMemData[zoneNum][inZoneBucketNum][4094];
                unsigned char inZoneNum2 = cacheInMemData[zoneNum][inZoneBucketNum][4095];

		if((zoneNum1 == 255 && zoneNum2 == 255) || (lastRehashedPt[zoneNum] == (wp_manager[zoneNum][8] / 24576) * 24576 + wp_manager[zoneNum][inZoneBucketNum] / 128)){
                        return;
                }
            
                //new zone and inzone num from the link
                zoneNum = zoneNum1 * 256 + zoneNum2; //Make it to  xxxx xxxx xxxx xxxx?
                inZoneBucketNum = inZoneNum1 * 256 + inZoneNum2;	

        }
        return;
}

void initiateRehash(unsigned char * key, struct xnvme_dev * dev, unsigned char zoneBucket, unsigned char inZoneBucket){      	
        lastRehashedPt[zoneBucket] = (wp_manager[zoneBucket][8] / 24576) * 24576 + wp_manager[zoneBucket][inZoneBucket] / 128;
        map <unsigned char, int> rehashLocPtr;

        readDataInChaining(key, dev); 

        //첫번째 key = lastRehashedPt 니까 빼기- you  don't rehash the first element 
        location[zoneBucket][inZoneBucket].pop();

	// Only rehash the one that has long chaining: if the bucket does not have any chains, just leave it as it is
        // Take the first 3 bits of key[2] xxx0 0000 in least significant order on first rehashing
        unsigned char newBucket = key[2] / 32;
        // starting from key[2] it moves 3 bits to the right xxx0 0000 -> 0000 xxx0
	int newZone = findNewZone(dev);	
        if(newZone == -1){
                printf("FULL ZNS\n");
        }

       	//wp_8 변경
        rehash_ptr[zoneBucket][8] = newZone * 24576;
        while(location[zoneBucket][inZoneBucket].size() != 0){		
        	if(num_rehash[newZone][newBucket] % 2 == 0){
			newBucket = key[2 + (num_rehash[newZone][newBucket] / 2)] / 32;
		} else {
			newBucket = (key[2 + (num_rehash[newZone][newBucket] / 2)] / 2) % 8;
		}	
       
        	unsigned char *newKey = location[zoneBucket][inZoneBucket].top();
		rehash(newKey, dev, newBucket, newZone);       
		location[zoneBucket][inZoneBucket].pop();

                //rehash 끝난 지점 bucket에 rehash위치 저장- in dictionary - store zone and bucket 
                rehashLocPtr.insert({newBucket, newZone});	
		
	}
	num_rehash[newZone][newBucket] += 1;

        // rehash 끝난시점에 현재 bucket 위치- get the most recent bucket - store rehashed location in the bucket
        unsigned char currinZoneBucket = wp_manager[zoneBucket][inZoneBucket] / 128;
        unsigned char currZone = (wp_manager[zoneBucket][inZoneBucket] / 128) / 24576;
 
	int j = 0;
	for (auto i = rehashLocPtr.begin(); i != rehashLocPtr.end(); i++){		
		cacheInMemData[currZone][currinZoneBucket][4033 + j] = (i->first) / 256;
		cacheInMemData[currZone][currinZoneBucket][4034 + j] = (i->first) % 256; 
		cacheInMemData[currZone][currinZoneBucket][4035 + j] = i->second; 
		j++;	
	}
		
        if(num_chaining[newZone][newBucket].load() > 20 && rehashState[newZone][newBucket].load() == 0){
	       
		initiateRehash(key, dev, newZone, newBucket); 
	}       
	rehashState[zoneBucket][inZoneBucket].store(0);
}

void putZNS(unsigned char * key, struct xnvme_dev *dev){	
	//key 값의 hash 값 추출 : 256개의 존에 16개의 hash bucket = 2 ^ 4096 = 2 ^ 12
	//첫 4자리 추출		8	존내에서 block 결정
	unsigned char inZoneBucket = key[0] % 8; 			// xxxx xxxx 에서 0000 xxxx 추출
	//두번째 8 자리 추출	256	존 결정
	unsigned char zoneBucket = (key[1] % 8) * 32  + key[0] / 8;	// 앞수 뒷 4자리 뒷수 앞 4자리 0000 xxxx xxxx 0000
	//printf("key1 : %d, key0 : %d, zone : %d, inzone : %d\n",key[1], key[0], zoneBucket, inZoneBucket);
	
	startPart = clock();
	while(putState[zoneBucket][inZoneBucket].load() != 0){
		if(putState[zoneBucket][inZoneBucket].load() == 0) {	
			break;
		}
	}
	putState[zoneBucket][inZoneBucket].store(1);
	endPart = clock();
        totalTime = totalTime + (double)(endPart - startPart);

	//start1 = clock();
	zoneState[zoneBucket].store(3);

	//cache값에 key 추가
	for(int i = 0; i < 32; i++){	
		cacheInMemData[zoneBucket][inZoneBucket][(wp_manager[zoneBucket][inZoneBucket] % 128) * 32 + i] = key[i];
	}

	
	void * dbuf = NULL;
        dbuf = xnvme_buf_alloc(dev, 4096);
        if (!dbuf) {
                printf("xnvme_buf_alloc\n");
                exit(-1);
        }

	for(int i = 0; i < 4096; i++){
		*(unsigned char *)(dbuf + i) = cacheInMemData[zoneBucket][inZoneBucket][i];
	}


	start1 = clock();	

	//cache를wp에쓰기
	{
		int err;
                struct xnvme_cmd_ctx ctx = xnvme_cmd_ctx_from_dev(dev);
                ctx = xnvme_cmd_ctx_from_dev(dev);
                err = xnvme_nvm_write(&ctx, 0x1, (wp_manager[zoneBucket][8] / 24576) * 24576 + (wp_manager[zoneBucket][inZoneBucket] / 128), 0, dbuf, NULL); //block에 정보 쓰기
                if (err || xnvme_cmd_ctx_cpl_status(&ctx)) {	
                        printf("xnvme_nvm_write on zone %d and bucket %d \n", zoneBucket, inZoneBucket);
			exit(-1);	
                }
        }
	//wp 증가
	wp_manager[zoneBucket][inZoneBucket] = wp_manager[zoneBucket][inZoneBucket] + 1;	

	end1 = clock();
        totalTimeJoin = totalTimeJoin + (double)(end1 - start1);

	//꽉찬경우
	if(wp_manager[zoneBucket][inZoneBucket] % 128 * 32 == 4096 - 64){ // wp 가 뒤에서 3번째 원소 쓴 이후 trigger	
		//increment num_chaining
		int num_chain2;
        	num_chain2 = (num_chaining[zoneBucket][inZoneBucket]).load();
        	num_chaining[zoneBucket][inZoneBucket].compare_exchange_weak(num_chain2,num_chain2 + 1);        
		//window 1인 경우
		if(wp_manager[zoneBucket][inZoneBucket] / 128 < wp_manager[zoneBucket][8] % 24576 + 8){
			//다음 cache 초기값
			linkInitCacheInMemData(zoneBucket, inZoneBucket, wp_manager[zoneBucket][inZoneBucket] / 128);
			wp_manager[zoneBucket][inZoneBucket] = ((wp_manager[zoneBucket][8] + 8) % 24576 + inZoneBucket) * 128 ; // 단순 8 칸올리면 switch 이후 적용 불가
			for(int i = 0; i < 4096; i++){
		                *(unsigned char *)(dbuf + i) = cacheInMemData[zoneBucket][inZoneBucket][i];
        		}
        		{
				int err;
	                	struct xnvme_cmd_ctx ctx = xnvme_cmd_ctx_from_dev(dev);
	                	ctx = xnvme_cmd_ctx_from_dev(dev);
        		        err = xnvme_nvm_write(&ctx, 0x1, (wp_manager[zoneBucket][8] / 24576) * 24576 + wp_manager[zoneBucket][inZoneBucket] / 128, 0, dbuf, NULL);
        	        	if (err || xnvme_cmd_ctx_cpl_status(&ctx)) {
	                        	printf("xnvme_nvm_write block 1 : %d block loc : %d \n", wp_manager[zoneBucket][8]/24576 * 24576 + wp_manager[zoneBucket][inZoneBucket] / 128,  wp_manager[zoneBucket][inZoneBucket]);
	                	}
        		}
		
		}
		
		//window 2인경우 swiching 해줘야함
		else{		
			int swapBucketNum = findSwitchLocation(zoneBucket);
			//switch 시켜서 앞에 넣을수 없는경우 + Zone 이 꽉차버린 경우           
			if(swapBucketNum == -1){
				if(wp_manager[zoneBucket][8] % 24576 == 24576 - 24){
					startZoneChaing(dev, zoneBucket, inZoneBucket);
				}
				else{
					//if(wp_manager[zoneBucket][8] >= 24576 * 256)
					//	printf("\nWINDOW 2-1 OVERFLOW START BUCKET : %d WP_%d : %d \n", wp_manager[zoneBucket][8], inZoneBucket, wp_manager[zoneBucket][inZoneBucket]);
					linkInitCacheInMemData(zoneBucket, inZoneBucket, wp_manager[zoneBucket][inZoneBucket] / 128);
					wp_manager[zoneBucket][8] = wp_manager[zoneBucket][8] + 8; 	// block 기준 이동
					wp_manager[zoneBucket][inZoneBucket] = ((wp_manager[zoneBucket][8] + 8) % 24576 + inZoneBucket) * 128; // 단순 8 칸올리면 switch 이후 적용 불가
					for(int i = 0; i < 4096; i++){
	                        	        *(unsigned char *)(dbuf + i) = cacheInMemData[zoneBucket][inZoneBucket][i];
        	        	        }
                		        {
        	                	        int err;
	                                	struct xnvme_cmd_ctx ctx = xnvme_cmd_ctx_from_dev(dev);
	                                	ctx = xnvme_cmd_ctx_from_dev(dev);
        	                	        err = xnvme_nvm_write(&ctx, 0x1, (wp_manager[zoneBucket][8] / 24576) * 24576 + wp_manager[zoneBucket][inZoneBucket] / 128, 0, dbuf, NULL);
                		                if (err || xnvme_cmd_ctx_cpl_status(&ctx)) {
                	        	                printf("xnvme_nvm_write block 2-1 : %d block loc : %d \n",wp_manager[zoneBucket][8]/24576 * 24576 + wp_manager[zoneBucket][inZoneBucket] / 128,  wp_manager[zoneBucket][inZoneBucket]);
        	                        	}
					}
				}                       
			}
			//switch 시켜서 앞에 넣을수 있는경우
			else{
				//window 1의 값 2로 옮기기
				for(int i = 0; i < 4096; i++){
                                        *(unsigned char *)(dbuf + i) = cacheInMemData[zoneBucket][swapBucketNum][i];
                                }
				{
                                        int err;
                                        struct xnvme_cmd_ctx ctx = xnvme_cmd_ctx_from_dev(dev);
                                        ctx = xnvme_cmd_ctx_from_dev(dev);
                                        err = xnvme_nvm_write(&ctx, 0x1, wp_manager[zoneBucket][8] + 8 + swapBucketNum, 0, dbuf, NULL);
                                        if (err || xnvme_cmd_ctx_cpl_status(&ctx)) {
                                                printf("xnvme_nvm_write block 2-2-1 : %d block loc : %d \n", wp_manager[zoneBucket][8]/24576 * 24576 + wp_manager[zoneBucket][inZoneBucket] / 128,  wp_manager[zoneBucket][inZoneBucket]);
                                        }
                                }
				//window 2의 값 1로 옮기기
				for(int i = 0; i < 4096; i++){
                                        *(unsigned char *)(dbuf + i) = cacheInMemData[zoneBucket][inZoneBucket][i];
                                }
                                {
                                        int err;
                                        struct xnvme_cmd_ctx ctx = xnvme_cmd_ctx_from_dev(dev);
                                        ctx = xnvme_cmd_ctx_from_dev(dev);
                                        err = xnvme_nvm_write(&ctx, 0x1, wp_manager[zoneBucket][8] + swapBucketNum, 0, dbuf, NULL);
                                        if (err || xnvme_cmd_ctx_cpl_status(&ctx)) {
                                                printf("xnvme_nvm_write block 2-2-2 : %d block loc : %d \n", wp_manager[zoneBucket][8]/24576 * 24576 + wp_manager[zoneBucket][inZoneBucket] / 128,  wp_manager[zoneBucket][inZoneBucket]);
                                        }
                                }
				//새로운 window 2 초기값 설정	
				linkInitCacheInMemData(zoneBucket, inZoneBucket, wp_manager[zoneBucket][swapBucketNum] / 128);
				wp_manager[zoneBucket][inZoneBucket] = (wp_manager[zoneBucket][8] % 24576 + 8 + inZoneBucket) * 128;

				for(int i = 0; i < 4096; i++){
                                        *(unsigned char *)(dbuf + i) = cacheInMemData[zoneBucket][inZoneBucket][i];
                                }
                                {
                                        int err;
                                        struct xnvme_cmd_ctx ctx = xnvme_cmd_ctx_from_dev(dev);
                                        ctx = xnvme_cmd_ctx_from_dev(dev);
                                        err = xnvme_nvm_write(&ctx, 0x1, (wp_manager[zoneBucket][8] / 24576) * 24576 + wp_manager[zoneBucket][inZoneBucket] / 128, 0, dbuf, NULL);
                                        if (err || xnvme_cmd_ctx_cpl_status(&ctx)) {
                                                printf("xnvme_nvm_write block 2-2-3 : %d block loc : %d \n", wp_manager[zoneBucket][8]/24576 * 24576 + wp_manager[zoneBucket][inZoneBucket] / 128,  wp_manager[zoneBucket][inZoneBucket]);
                                        }
                                }	
				wp_manager[zoneBucket][swapBucketNum] = 8  * 128 + wp_manager[zoneBucket][swapBucketNum];

			}
		}

		//REHASH
                //If number of chains is greater than some extent
                //먼저 다 읽고 오래된 데이터부터 rehash
                if(num_chaining[zoneBucket][inZoneBucket].load() > 20 && (rehashState[zoneBucket][inZoneBucket]).load() == 0){
			
			rehashState[zoneBucket][inZoneBucket].store(1);
			num_chaining[zoneBucket][inZoneBucket].store(0);	
			initiateRehash(key, dev, zoneBucket, inZoneBucket);
                }
	}
	
	//change the state
        putState[zoneBucket][inZoneBucket].store(0);
	xnvme_buf_free(dev, dbuf);	
}


void getZNS(unsigned char * key, struct xnvme_dev * dev){
        //hash 의 뒤에서 부터 값 읽어서 key에 해당하는 정보가 있으면 get 해온다.

        //key값의 inZoneBucket, zoneBucket값 추출
        unsigned char inZoneBucketNum = key[0] % 8;
        unsigned char zoneNum = (key[1] % 8) * 32 + key[0] / 8;

        //get the most recent bucket 
        unsigned char currinZoneBucket = wp_manager[zoneNum][inZoneBucketNum] / 128;
        unsigned char currZone = (wp_manager[zoneNum][inZoneBucketNum] / 128) / 24576;



        //loop following the chaining from the most recent bucket
        while(true){
                //check if the bucket contains the key
                int ptr = 0;
                while((wp_manager[currZone][currinZoneBucket] % 128) * 32 + ptr < 4096){

                        if(cacheInMemData[currZone][currinZoneBucket][(wp_manager[currZone][currinZoneBucket] % 128) * 32 + ptr] != key[0]){
                                ptr += 32;
                        }else{
                                ptr += 1;
                                if(cacheInMemData[currZone][currinZoneBucket][(wp_manager[currZone][currinZoneBucket] % 128) * 32 + ptr] != key[1]){
                                        ptr += 31;
                                } else {
                                        //if you found out the key, xnvme read
                                        void * dbuf = NULL;
                                        dbuf = xnvme_buf_alloc(dev, 4096);
                                        if (!dbuf) {
                                                printf("xnvme_buf_alloc\n");
                                                return;
                                        }

                                        for(int i = 0; i < 4096; i++){
                                                *(unsigned char *)(dbuf + i) = cacheInMemData[zoneNum][inZoneBucketNum][i];
                                        }
                                        {
                                                int err;
                                                struct xnvme_cmd_ctx ctx = xnvme_cmd_ctx_from_dev(dev);
                                                ctx = xnvme_cmd_ctx_from_dev(dev);
                                                err = xnvme_nvm_read(&ctx, 0x1, (wp_manager[zoneNum][8] / 24576) * 24576 + wp_manager[zoneNum][inZoneBucketNum] / 128, 0, dbuf, NULL);
                                                if (err || xnvme_cmd_ctx_cpl_status(&ctx)) {
                                                        printf("xnvme_nvm_read block \n");
                                                }
                                        }
                                        return;
                                }
                        }
                }
                printf("escaped while loop");

                //if the bucket does not contain the key, follow the link
                unsigned char zoneNum1 = cacheInMemData[currZone][currinZoneBucket][4092]; //1 byte = 8 bit -> xxxx xxxx
                unsigned char zoneNum2 = cacheInMemData[currZone][currinZoneBucket][4093]; //xxxx xxxx
                unsigned char inZoneNum1 = cacheInMemData[currZone][currinZoneBucket][4094];
                unsigned char inZoneNum2 = cacheInMemData[currZone][currinZoneBucket][4095];





                //만약 1로 꽉찬 link발견시 key가 없어서 return;
                if(zoneNum1 == 255 && zoneNum2 == 255){
                        return;
                }

                //new zone and inzone num from the link
                unsigned char currZone = zoneNum1 * 256 + zoneNum2; //Make it to  xxxx xxxx xxxx xxxx?
                unsigned char currinZoneBucketNum = inZoneNum1 * 256 + inZoneNum2;




        }

        return;
}


void makeKeyValueRandom(int key, void * dbuf, size_t dbuf_size){
	//dbuf is filled with 4096 bytes string
	char temp[20];
	sprintf(temp, "%019d", key);
        for(int i = 0; i < 20; i++){
		*((char *)dbuf + i) = temp[i];
	}

	for(int i = 20; i < 128; i++){
		*((char *)dbuf + i) = '!' + (random() % 94);
	}
}

void ZoneSettingInit(struct xnvme_dev * dev){
	//0~255 chd 256개의 초기 zone open 함수
	for(int i = 0; i < 256; i++){
		OpenZone(dev, i);
	}
}

void WpSettingInit(){
        for(int i = 0; i < 256; i++){
                wp_manager[i][8] = i * 24576; //block 기준 zone & block tracking --> 1or2 소속window구분에도 사용
		rehash_ptr[i][8] = i * 24576; 
        }
}

void cacheInMemDataSetting(){
        for(int i = 0; i < 256; i++){
                for(int j = 0; j < 8; j++){
			for(int k = 0; k < 4096; k++){
				cacheInMemData[i][j][k] = 0;
			}
                }
        }
}

// 뒤에 두개(64 char) 전부 1로 만들기 
void cacheInMemDataInit(){
       for(int i = 0; i < 256; i++){
                for(int j = 0; j < 8; j++){
                        for(int k = 4032; k < 4096; k++){
                                cacheInMemData[i][j][k] = 255;
                        }
                }
        }
}

void assignKey(unsigned char* tempKey, unsigned char threadNum, struct xnvme_dev * dev){	
	int num_key;
	int ptr = 2500 * threadNum * 32; 
	while(ptr < (2500 * threadNum * 32) + (2500 * 32)) {
		unsigned char newKey[32];
		for(int i = 0; i < 32; i++){
			newKey[i] = *(unsigned char *)(tempKey + ptr + i);
		}	
	
		putZNS(newKey, dev);
		ptr += 32;
		num_key++;	
		printf("NumKey: %d \n", num_key);
	}	
}

int main(int argc, char **argv){
        struct xnvme_opts opts = xnvme_opts_default(); 	// options default 설정
	struct xnvme_dev *dev;
        uint32_t nsid = 0x1;

	opts.nsid = nsid;

	size_t dbuf_nbytes = 4096;


	//Device Open
	dev = xnvme_dev_open("0000:d8:00.0", &opts);
	if (!dev) { // ERR 출력
                perror("xnvme_dev_open()");
                return 1;
        }
	//최초 존 세팅 (EX. 256개의 hash table open)
	ZoneSettingInit(dev);
	zoneStateInit();
	//최초 wp는 hash bucket이 몇번째 존인지를 알려준다 따라서 0~255의 값을 초기값으로 배정
	WpSettingInit();
	//전부 0 초기화
	cacheInMemDataSetting();
	cacheInMemDataInit();

	clock_t start, end;
  	start = clock();
	
	//여러 KV function 실행 put, get, update, del . . .
	{	

		void* tempKey = xnvme_buf_alloc(dev, 32 * 100000);
		if (!tempKey) {
                        printf("xnvme_buf_alloc\n");
                	exit(-1);
                }
		
		int numKey; 
		for(int REP = 0; REP < 1 * 100000; REP += 40){		//16 * 256 * 24576 * 10	
			for(int i = 0; i < 40; i++){
			 
				for(int keyIndex = 0; keyIndex < 32; keyIndex++){ 
					*(unsigned char *)(tempKey + (32 * numKey) + keyIndex) = random() % 256;	
				}
				numKey++; 	
			} 
		}	

		//spawn 40 threads
                std::thread threads[40];
			
		for(int i = 0; i < 40; i++){
			threads[i] = std::thread(assignKey, (unsigned char*) tempKey, (unsigned char)i, dev);	
		}
		for(int i = 0; i < 40; i++){
			threads[i].join();
		}

		xnvme_buf_free(dev, tempKey);
			
	}
				
	end = clock();
	printf("time : %lf\n", (double)(end-start)/CLOCKS_PER_SEC);
	printf("time part : %lf\n", totalTime/CLOCKS_PER_SEC);
	printf("time part filling : %lf\n", totalTimeJoin/CLOCKS_PER_SEC);

	puts("CLOSE in progress . . .");
	xnvme_dev_close(dev);

	return 0;

}
