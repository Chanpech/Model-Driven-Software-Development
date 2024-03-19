module OPS

// Utilize dynamic modeling
// Library for ordering located in the util folder
open util/ordering[Transaction] as ord // Similar to a doubly linked-list

sig ID {}

abstract sig Entity { 
  id: one ID,
  balance: lone Currency //Can have a currency or nothing at all
}

// Generalize
one sig Person1, Person2, FinancialInstitution extends Entity {}

sig Currency {
  amount: Int 
}

sig Transaction {
  sender: set Entity,
  recipient: set Entity
}

// Facts and Predicates

fact UniqueIDs {
  all disj e1, e2: Entity | e1.id != e2.id and e1.balance != e2.balance
}

fact OnlySenderReceiverCanTransact {
  all t: Transaction | {
    some p1: Person1, p2: Person2 | p1 in t.sender && p2 in t.recipient
  }
}

//fact NoSelfTransactions {
//  all t: Transaction | no p: Person1 | p in t.sender && p in t.recipient
//  all t: Transaction | no fi: FinancialInstitution | fi in t.sender && fi in t.recipient
//}

fact CurrencyTransfer {
  all t: Transaction |
    let sender = t.sender,
        recipient = t.recipient |
      sender.balance & recipient.balance = sender.balance
}

fact InitialBalances {
  all e: Entity - FinancialInstitution | lone e.balance
}

fact NoTransactionWithoutCurrency {
  all t: Transaction | some sender: t.sender | lone sender.balance
}

pred TransactionProcessing[t, ut: Transaction] {
  some p1: Person1, p2: Person2 | TransactionProcessingHelper[t, ut, p1, p2]
}

pred TransactionProcessingHelper[t, ut: Transaction, p1: Person1, p2: Person2] {
  (p1 in t.sender && p2 in t.recipient) implies {
    ut.recipient = t.sender && ut.sender = t.recipient + FinancialInstitution
  }
}

pred SystemTransition[t, ut: Transaction] {
  TransactionProcessing[t, ut] or TransactionProcessing[ut, t]
}

run SystemTransition for 5 but exactly 3 Entity, 2 Currency, 3 Transaction
