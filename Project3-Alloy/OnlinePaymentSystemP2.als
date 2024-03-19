// Author: Chanpech Hoeng
// Course: CS4710 R01
// Date: Dec 7, 2023
//Description: Model the Online Payment System thorugh abstractions.
module OnlinePayment


open util/time

//open util/ordering[States] as ord //Similar to a doubly linked-list


//Might introduce ing if we need to scale further 
//However we will likely need a better transaction signature
/////////////////
//SIGNATURES//
////////////////
sig Institution{}

sig Funds{
	timestamp: Time
}

sig ID{}

sig Account{
	id: one ID,
 	balance: set Funds,
	send: lone Account,
	receive: lone Account,
	registered: one FinancialInstitution,
 	spentFunds: set Funds
}

one sig CentralFinancialInstitution extends Institution{
}
//sig User extends Account{}
sig FinancialInstitution extends Institution{
	connections: one CentralFinancialInstitution,
	processSenderID: one ID,
	processReceiverID: one ID,
	processFunds: set Funds
}

sig States {
	senderID, destinationID : set Account,
	send, process, receive, confirm: set Funds,
	timestamp: Time
}
////////////////
//FUNCTIONS//
///////////////
// Function to see the funds that were spent
fun fundsSpentWhen[a: Account, f: Funds, s: States]: set Funds {
    {f: Funds |
        f in a.spentFunds and
        f in s.send and f in s.process}
}


// Function to see all accounts that had their funds processed by the financial institution
fun processedAccounts[fi: FinancialInstitution, s: States]: set Account {
    { a: Account |
        some f: Funds |
            a in s.senderID and f in s.process and f.timestamp = s.process.timestamp and
            a.id in fi.processReceiverID
    }
}


// Function to see all accounts that were able to successfully send funds
fun successfulSenders[fi: FinancialInstitution, s: States]: set Account {
    { a: Account |
        some f: Funds |
            a in s.senderID and f in s.send and f.timestamp = s.send.timestamp and
            a.id in fi.processSenderID
    }
}



// Function to see that a receiver account should have a receive relationship with a sender account
fun receive1EqualSender2[a: Account]: set Account {
    { r: Account |
        r in a.receive and a in r.send
    }
}


//Function to offer a 1 time loan
//fun 

//Function to see that all FinancialInstitution should have one central institution that distribute these funds

///////////
//FACTS//
//////////
//All account will have a Unique ID and unique funds
fact Unique {
  all disj u1, u2: Account| u1.balance != u2.balance and u1.id != u2.id 
}

//An account can't send and receive to itself
fact noReflexiveSendReceive{
 all a: Account| a.send != a and a.receive != a
}

//Since an account won't be sending and receiving to itself, the finacial institution shouldn't process
// a case where processSenderID are the same as processReceiverID.
fact noReflexiveSendReceive{
 all f: FinancialInstitution, a:Account | f.processSenderID = a.id implies f.processReceiverID != a.id
}

//An account can only spent the funds if and only if that fund have a send attribute
//fact spentOnlyWithSend {
//    all a: Account, f: Funds | f in a.spentFunds implies a.send
//}


////////////////
//PREDICATES//
////////////////
//If there are accounts that share the same funds then one of the account must have initate send. 
pred sameFundsImpliesSendReceive[a1, a2: Account] {
    a1.balance = a2.balance implies a1.send = a2 and a2.receive = a1 || 
	a2.send = a1 and a1.receive = a2
}

//An account can send but it does not have an incoming receive from other account
pred sendWithoutReceive[a1, a2: Account] {
    a1 != a2 implies (a1.send = a2 implies a2.receive != a1)
}
// Capture how funds are initially moved from sender to financialInst
pred moveFunds[a: Account, f: Funds, fi: FinancialInstitution] {
    f in a.balance
    f.timestamp = Time
    a.balance = a.balance - f
    fi.processSenderID = fi.processReceiverID + f
}

// Capture how funds are initially placed under processing in financial institution
pred processFunds[a: Account, f: Funds, fi: FinancialInstitution] {
    f in fi.processFunds
    fi.processSenderID = a.id
}

//Four predicates that capture the dynamic changes 

// Capture how funds are initially moved from sender to financial institution
pred moveFunds[a: Account, f: Funds, fi: FinancialInstitution] {
    f in a.balance
    f.timestamp = Time
    a.balance = a.balance - f
    fi.processSenderID = fi.processReceiverID + f
}

// Capture how funds are initially placed under processing in financial institution
pred processFunds[a: Account, f: Funds, fi: FinancialInstitution] {
    f in fi.processFunds
    fi.processSenderID = a.id
}

// Capture how funds are transferred from financial institution to destination
pred transferFunds[fi: FinancialInstitution, s: States] {
    some f: Funds |
        f in s.process and f.timestamp = s.process.timestamp and
        f in s.receive and
        fi.processReceiverID + f = s.destinationID.id
}

// Capture how receiver sends a confirmation message back to the account
pred confirmFunds[a: Account, f: Funds, s: States] {
    some g: Funds |
        g in s.confirm and g.timestamp = s.confirm.timestamp and
        g = f and a in s.destinationID
}



////////////////
//ASSERTIONS//
////////////////

fact noExcessFunds {
    all a: Account, f: Funds, s: States | f in a.balance implies f in s.send or f in s.process or f in s.receive or f in s.confirm
}

assert statesOrdering {
    all s1, s2: States | s1 in s2 implies #s1.timestamp <= #s2.timestamp
}

// Assert that all accounts in processed state are also in successfulSenders
assert processedAccountsInSuccessfulSenders {
    all fi: FinancialInstitution, s: States |
        processedAccounts[fi, s] in successfulSenders[fi, s]
}

// Assert that all accounts that have sent funds are also in successfulSenders
assert sendersInSuccessfulSenders {
    all fi: FinancialInstitution, s: States |
        {a: Account | a in s.senderID and a.id in fi.processSenderID} in successfulSenders[fi, s]
}

// Assert that the send events occur before receive events
assert sendBeforeReceive {
    all s1, s2: States |
        s1.send in s2.send implies #s1.send.timestamp < #s2.receive.timestamp
}

////////////////////////
// Check the assertion//
////////////////////////
//check statesOrdering//
//check sendersInSuccessfulSenders
//check processedAccountsInSuccessfulSenders
//check sendBeforeReceive


////////
//RUN//
///////

//
run fullModelCheckSmallScope {
    // Signatures
    #FinancialInstitution = 2
}
