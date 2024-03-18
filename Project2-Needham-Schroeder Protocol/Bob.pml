	mtype = {send, acknowledge, userA, userB, keyA, keyB,};
chan communicate = [0] of {mtype, mtype, mtype};
typedef Crypt {mtype key, content1, content2};
mtype partnerB;
active proctype Bob(){
	mtype pkey;
	mtype pnonce;
	Crypt messageBA;
	//Crypt data;

	communicate ? partnerB, pnonce, pkey;
	messageBA.key = pkey;
	messageBA.content1 = send;
	messageBfA.content2 = acknowledge;
}
