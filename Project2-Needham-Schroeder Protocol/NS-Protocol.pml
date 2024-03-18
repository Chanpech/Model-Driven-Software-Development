/* 
Developers: Tony Garnett, Chanpech Hoeng
Latest Update: Oct 31, 2023
Description: 
Develop a Needham-Schroeder Protocol showing its communication between Alice and Bob. 
Then introduce an intruder process that intercepts and extracts the three fields. 
Simulating a man-in-the-middle attack.
*/
#define N 10
#define NULL -1

mtype:msg = {msg1, msg2, msg3};
mtype:user = {alice, bob, intruder};
mtype:msg_cnt = {null, userA, userB, userI, nonceA, nonceB, nonceI};
mtype:msg_key = {keyA, keyB, keyI};
typedef Crypt{mtype:msg_cnt content1, content2; mtype:msg_key key};
chan communicate = [0] of {mtype:msg, mtype:user, Crypt};
mtype:user alicePart;
mtype:user bobPart;
mtype:msg_cnt alliceNonceIn, bobNonceIn;

int term = 0;
int aliceSendMsg, bobReceiveMsg, bobSendAck, aliceReceiveAck, aliceSendConf, bobReceiveConfirmation  = 0;
ltl safety {[]<>(aliceSendMsg == 1 && bobReceiveMsg == 1 && bobSendAck == 1 && aliceReceiveAck == 1 && aliceSendConf == 1 && bobReceiveConfirmation ==1) }
//ltl liveness {<>(term == 2)};

active proctype Alice(){
	mtype:msg_cnt pnonce = nonceA;
	mtype:msg_key pkey = keyA;

	Crypt sender;
	mtype:user receiver;

	atomic{ //choose alice partner
		alicePart = 0;
		if
			:: receiver = bob;
			//:: receiver = intruder;
		fi
	}

	atomic { //set sender crypt parameters
		sender.content1 = userA;
		sender.content2 = pnonce;
		if
		::receiver == bob -> sender.key = keyB;
		//::receiver == intruder -> sender.key = keyI
		fi
	}

	communicate ! msg1(receiver, sender); //breaks and waits for receiver to recieve and send back
	aliceSendMsg++;

	atomic{
		communicate ? msg2(alice, sender);
		aliceReceiveAck++;
		if
		::sender.key == pkey ->
			skip;
		:: else->
			printf("Invalid Key for user Alice\n");
			goto end;
		fi
		if
		::sender.content1 == pnonce ->
			skip;
		:: else->
			printf("Invalid for user Alice\n");
			goto end;
		fi
		//alicePart = receiver; 
	}
	atomic{
		sender.content1 = sender.content2;
		sender.content2 = 0;
	 	if
		:: (receiver == bob) -> sender.key = keyB;
		//:: (receiver == intruder) ->sender.key = keyI;
	 	fi

	}
	communicate ! msg3(receiver, sender);
	aliceSendConf++;
	end: term++;

}

active proctype Bob(){
	mtype:msg_cnt pnonce = nonceB;
	mtype:msg_key pkey = keyB;

	Crypt sender, receiverMessage;
	mtype:user receiver;

	bobPart = 0;

	atomic{
		communicate ? msg1(receiver, receiverMessage);
		if
		:: receiverMessage.key == keyB -> skip;
		:: else->printf("Invalid key for user Bob\n");
		fi
		bobReceiveMsg++;
	}

	atomic{
		if
			::(receiverMessage.content1 == userA) -> receiver = alice; sender.key = keyA;
			//::(receiverMessage.content1 == userI) -> receiver = intruder; sender.key = keyI;
		fi
		sender.content1 = receiverMessage.content2;
		sender.content2 = pnonce;
		communicate ! msg2(receiver, sender);
		bobSendAck++;
	}

	atomic{
		communicate ? msg3(bob, receiverMessage);
		bobReceiveConfirmation++;
		if
		:: receiverMessage.key == pkey -> skip;
		:: else -> printf("Invalid key for user Bob\n");
		goto end;
		fi
		if
		:: receiverMessage.content1 == pnonce -> skip;
		:: else->printf("Invalid Nonce for user Bob\n");
		goto end;
		fi

		bobPart = receiver;
	}
	end:
	term++;
}

// active proctype Intruder(){
// 	mtype:msg_cnt pnonce = nonceI;
// 	mtype:msg_key pkey = keyI;

// 	mtype:msg storedMsg, senderMsg;
// 	mtype:user storedMsgReceiver, senderReceiver, senderSender;
// 	Crypt storySend, sending;
// 	mtype:msg_cnt stored_content1, stored_content2;
// 	mtype:msg_key stored_key;

// 	do
// 		::atomic{
// 			communicate ? storedMsg, storedMsgReceiver, storySend;
// 			if
// 				::(storySend.key == pkey) ->
// 					stored_content1 = storySend.content1;
// 					stored_content2 = storySend.content2;
// 					if
// 						:: storedMsg == msg1 ->
// 							if
// 								::stored_content1 == userA->
// 									alliceNonceIn = stored_content2;
// 								::stored_content1 == userB->
// 									bobNonceIn = stored_content2;
// 							fi
// 					fi
// 			fi
// 		}

// 		::atomic{
// 			storedMsg != 0 && storedMsgReceiver !=0 && storedMsgReceiver != intruder &&storySend.key != 0 ->
// 				communicate ! storedMsg, storedMsgReceiver, storySend;
// 		}
// 		::atomic{
// 			storedMsg !=0 && storedMsgReceiver != 0 && storySend.key == keyI ->
// 				sending.content1 = storySend.content1;
// 				sending.content2 = storySend.content2;
// 				if
// 					:: storedMsg == msg2 ->
// 						senderReceiver = alice;
// 						sending.key = keyA;
// 					:: storedMsg != msg2 ->
// 						senderReceiver = bob;
// 						sending.key = keyB;
// 				fi
// 				communicate ! storedMsg, senderReceiver, sending;
// 		}

// 		::atomic{
// 			if
// 				:: senderReceiver = alice ->
// 					sending.key = keyA;
// 				:: senderReceiver = bob ->
// 					sending.key = keyB;
// 			fi
// 			if
// 				::senderMsg = msg1 ->
// 					if
// 						:: sending.content1 = userI;
// 						:: sending.content1 = userA;
// 						:: sending.content1 = userB;
// 					fi
// 					if
// 						:: sending.content2 = nonceI;
// 						::sending.content2 = alliceNonceIn;
// 						::sending.content2 = bobNonceIn;
// 					fi

// 				::senderMsg = msg2 ->
// 					if
// 						::sending.content2 = nonceI;
// 						::sending.content2 = alliceNonceIn;
// 						::sending.content2 = bobNonceIn;
// 					fi
// 					if
// 						::sending.content2 = nonceI;
// 						::sending.content2 = alliceNonceIn;
// 						::sending.content2 = bobNonceIn;
// 					fi
// 				::senderMsg = msg3->
// 					sending.content2 = 0;
// 					if
// 						:: sending.content2 = nonceI;
// 						::sending.content2 = alliceNonceIn;
// 						::sending.content2 = bobNonceIn;
// 					fi
// 			fi
// 			communicate ! senderMsg, senderReceiver, sending;
// 		}
// 	od
// }
