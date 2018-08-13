chan M_Chan = [0] of {mtype}
chan C_Chan = [0] of {mtype}
chan Trans_Chan = [0] of {mtype}

mtype cache;
mtype C_status;
mtype M_status;
bool M_termination=true;
bool C_termination=false;
byte ter_day=7;
byte time=0;

mtype = {what_price,goods,price,accept_price,e_account,receipt,ask_receipt}
mtype = {Init,Price_Wait,Goods_Wait,Receipt_Wait,Commit_Wait,Success,Ack_Wait,Account_Wait,Busy}

mtype = {C_init,C_Resp_Wait,C_Goods_Wait,C_Receipt_Wait,C_Suc,C_Abort};
mtype = {M_listen,M_Wait_Ack,M_Wait_Ec,M_Ack_Con,M_Suc,M_Busy,M_Abort};

byte contract_account = 0;
byte customer_account = 100;
byte merchant_account = 100;
byte per_price = 10;

//ltl { [](C_status==C_Suc-><>(contract_account==0))}
//ltl { <>(C_status==C_Suc)}
//ltl { [](C_status==C_Goods_Wait-><>(contract_account==per_price))}
//ltl { [](contract_account+customer_account) == customer_account_fin}
//ltl { [](contract_account+merchant_account) == merchant_account_fin}


proctype Customer(){
	//mtype C_status;
	mtype M_tem_status;
	
	C_status=C_init;
	//C_Chan!C_status;
	
	//mtype = {C_init,C_Resp_Wait,C_Goods_Wait,C_Receipt_Wait,C_Suc,C_Abort}	
	
	M_Chan?M_tem_status;
	if
	::(M_tem_status == M_listen && C_status == C_init && time<ter_day )->atomic{
		//Trans_Chan!what_price;
		
		C_status=C_Resp_Wait;
		C_Chan!C_status;
	}
	::else->skip;
	fi;
	
	M_Chan?M_tem_status;
	if
	::(M_tem_status == M_Wait_Ack && C_status == C_Resp_Wait && time<ter_day)->atomic{
		C_status=C_Goods_Wait;
		C_Chan!C_status;
		Trans_Chan!C_status;
		customer_account=customer_account-per_price;
		//contract_account=contract_account+per_price;
	}
	::(M_termination)->atomic{
		C_status=C_init;
		C_Chan!C_status;
	
	}
	::(C_termination)->atomic{
		C_status=C_Abort;
		C_Chan!C_status;
	
	}
	::else->atomic{skip;}
	fi;
	
	M_Chan?M_tem_status;
	Trans_Chan?cache;
	assert(contract_account == per_price);
	if
	::(M_tem_status == M_Wait_Ec && C_status == C_Goods_Wait && cache == Goods_Wait && time<ter_day)->atomic{
		C_status=C_Receipt_Wait;
		C_Chan!C_status;
	}
	::(M_termination)->atomic{
		C_status=C_init;
		C_Chan!C_status;
		
	}
	::(C_termination)->atomic{
		C_status=C_Abort;
		C_Chan!C_status;
89
	}
	::else->atomic{skip;}
	fi;
	
	assert(contract_account == per_price);

	end_C:
	M_Chan?M_tem_status;
	if
	::(M_tem_status == M_Suc && C_status == C_Receipt_Wait && time<ter_day)->atomic{
		printf("transaction finished!/n");
		C_status=C_Suc;
		C_Chan!C_status;
	}
	::else->time=time+1;
	fi;
}

proctype Merchant(){
	//mtype M_status;
	mtype C_tem_status;
	
	M_status=M_listen;
	M_Chan!M_status;
	
	//mtype = {M_listen,M_Wait_Ack,M_Wait_Ec,M_Ack_Con,M_Suc,M_Status_Query,M_Busy,M_Abort}
	
	C_Chan?C_tem_status;
	if
	::(C_tem_status == C_Resp_Wait && M_status == M_listen && time<ter_day)->atomic{
		//Trans_Chan!
		M_status=M_Wait_Ack;
		M_Chan!M_status;
	}
	::else->skip;
	fi;
	
	C_Chan?C_tem_status;
	if
	::(C_tem_status == C_Goods_Wait && M_status == M_Wait_Ack && time<ter_day)->atomic{
		M_status=M_Wait_Ec;
		M_Chan!M_status;
	}
	::(C_termination)->atomic{
		M_status=M_Abort;
		M_Chan!M_status;
	}
	::(M_termination)->atomic{
		M_status=M_listen;
		M_Chan!M_status;
	}
	::else->skip;
	fi;
	
	C_Chan?C_tem_status;
	if
	::(C_tem_status == C_Receipt_Wait && M_status == M_Wait_Ec && time<ter_day)->atomic{
		M_status=M_Ack_Con;
		M_Chan!M_status;
	}
	::(C_termination)->atomic{
		M_status=M_Abort;
		M_Chan!M_status;
	}
	::(M_termination)->atomic{
		M_status=M_listen;
		M_Chan!M_status;
	}
	::else->skip;
	fi;
	
	C_Chan?C_tem_status;
	if
	::(C_tem_status == C_Suc && M_status == M_Suc && cache == Success && time<ter_day)->atomic{
		M_status=M_Suc;
		M_Chan!M_status;
		Trans_Chan!M_status;
		//contract_account=contract_account-per_price;
		merchant_account=merchant_account+per_price;
		printf("transaction finished!\n");
	}
	::else->time=time+1;
	fi;

}

proctype Contract(){
	mtype Con_ststus;
	
	Trans_Chan?Con_ststus;
	if
	::(Con_ststus == C_Goods_Wait)->atomic{
		contract_account=contract_account+per_price;
		Con_ststus=Goods_Wait;
		Trans_Chan!Con_ststus;
	}
	::else->skip;
	fi;
	
	end_Con:
	Trans_Chan?Con_ststus;
	if
	::(Con_ststus == M_Suc)->atomic{
		contract_account=contract_account-per_price;
		Con_ststus=Success;
		Trans_Chan!Con_ststus;
	}
	::else->skip;
	fi;
}

init{

	run Customer();
	run Merchant();
	run Contract();
}
