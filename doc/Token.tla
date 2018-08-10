------------------------------- MODULE Token -------------------------------
EXTENDS Naturals, TLC, FiniteSets

CONSTANTS CONTRACTS, \* set of contracts in Tezos
          INIT_TOKEN \* initial token amount
          
VARIABLES tokenMap, \* token amount state of contracts
          pick \* current pick for model checking
          
----------------------------------------------------------------------------
\* some common helper operators

Range(T) == {<<T[x], x>> : x \in DOMAIN T}
Pick(S) == CHOOSE s \in S : TRUE

RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_, _), S, value) == 
  IF S = {} THEN value
  ELSE LET s == Pick(S)
       IN IF Op(s[1], value) = Op(value, s[1])
       THEN SetReduce(Op, S \ {s}, Op(s[1], value)) 
       ELSE Assert(FALSE, "error")
       
Sum(S) == LET _op(a, b) == a + b
          IN SetReduce(_op, S, 0)
          
----------------------------------------------------------------------------

TOKENTransfer(owner, receiver, amount) ==
  IF owner = receiver
  THEN UNCHANGED tokenMap
  ELSE 
  tokenMap' = [x \in CONTRACTS |-> 
                CASE x = owner -> tokenMap[x] - amount
                  [] x = receiver -> tokenMap[x] + amount
                  [] OTHER -> tokenMap[x]]

tokenMapChecker ==
  Sum(Range(tokenMap)) = Cardinality(CONTRACTS) * INIT_TOKEN
  

Init == 
  /\ tokenMap = [x \in CONTRACTS |-> INIT_TOKEN]
  /\ pick = [
       owner |-> RandomElement(CONTRACTS), 
       receiver |-> RandomElement(CONTRACTS), 
       amount |-> RandomElement(0..INIT_TOKEN * 2)
     ]
  
Next ==
  /\ pick' = [
       owner |-> RandomElement(CONTRACTS), 
       receiver |-> RandomElement(CONTRACTS), 
       amount |-> RandomElement(0..INIT_TOKEN * 2)
     ]
  /\ IF tokenMap[pick.owner] >= pick.amount
     THEN TOKENTransfer(pick.owner, pick.receiver, pick.amount)
     ELSE UNCHANGED tokenMap
                              
=============================================================================
