------------------------------- MODULE Token -------------------------------
EXTENDS Naturals, TLC, FiniteSets, Helper

CONSTANTS CONTRACTS, \* set of contracts in Tezos
          TOKENS, \* set of token contracts
          INIT_TOKEN \* initial token amount
          
VARIABLES tokenMap \* token amount state of contracts
          
----------------------------------------------------------------------------

TOKENTransfer(token, owner, receiver, amount) ==
  IF owner = receiver
  THEN UNCHANGED tokenMap
  ELSE 
  tokenMap' = 
    [t \in TOKENS |-> 
      [x \in CONTRACTS |-> 
        IF t = token
        THEN CASE x = owner -> tokenMap[t][x] - amount
               [] x = receiver -> tokenMap[t][x] + amount
               [] OTHER -> tokenMap[t][x]
        ELSE tokenMap[t][x]]]
           
           
tokenMapChecker ==
  [t \in TOKENS |-> Sum(Range(tokenMap[t]))] = 
    [t \in TOKENS |-> Cardinality(CONTRACTS) * INIT_TOKEN]

TokenInit == 
  /\ tokenMap = [t \in TOKENS |-> [x \in CONTRACTS |-> INIT_TOKEN]]
  \* pick is the variable from Helper
  /\ pick = [
       token |-> RandomElement(TOKENS),
       owner |-> RandomElement(CONTRACTS), 
       receiver |-> RandomElement(CONTRACTS), 
       amount |-> RandomElement(0..INIT_TOKEN * 2)
     ]
  
TokenNext ==
  /\ pick' = [
       token |-> RandomElement(TOKENS),
       owner |-> RandomElement(CONTRACTS), 
       receiver |-> RandomElement(CONTRACTS), 
       amount |-> RandomElement(0..INIT_TOKEN * 2)
     ]
  /\ IF tokenMap[pick.token][pick.owner] >= pick.amount
     THEN TOKENTransfer(pick.token, 
                        pick.owner, 
                        pick.receiver, 
                        pick.amount)
     ELSE UNCHANGED tokenMap
                              
=============================================================================
