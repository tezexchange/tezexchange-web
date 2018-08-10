---------------------------- MODULE TESpec ---------------------------------
EXTENDS Naturals, TLC, FiniteSets, Token

CONSTANTS EXCHANGE, \* exchange contract name
          INIT_XTZ \* initial (mu)xtz amount 

VARIABLES xtzMap, \* XTZ amount state of contracts
          orders \* orders state
          
----------------------------------------------------------------------------
\* some exchange helper operators

Users ==
  {x \in CONTRACTS : x /= EXCHANGE}
  
PickOrder(key) == 
  LET matches == { x \in orders : x.key = key } 
  IN IF matches = {} THEN [ xtz |-> 0, token |-> 0 ] 
     ELSE CHOOSE m \in matches : TRUE

XTZTransfer(owner, receiver, amount) ==
  IF owner = receiver 
  THEN UNCHANGED xtzMap
  ELSE 
  xtzMap' = [x \in CONTRACTS |-> 
              CASE x = owner -> xtzMap[x] - amount
                [] x = receiver -> xtzMap[x] + amount
                [] OTHER -> xtzMap[x]]
  
  
----------------------------------------------------------------------------
\* tez.exchange basic user operators

CreateBuyingOrder(token, buyer, price, xtz_amount) ==
  LET key == <<buyer, token, TRUE, price>>
      order == PickOrder(key)
      prev_xtz_amount == order.xtz
  IN 
  /\ XTZTransfer(buyer, EXCHANGE, xtz_amount)
  /\ orders' = {x \in orders : x.key /= key} \union 
               {[key |-> key, xtz |-> xtz_amount + prev_xtz_amount]}
  /\ UNCHANGED <<tokenMap>>


ExecuteBuyingOrder(order, executer, token_amount) ==
  LET token == order.key[2]
      price == order.key[4]
      owner == order.key[1]
      consumed_xtz == price * token_amount
      remain_xtz == order.xtz - consumed_xtz
  IN 
  /\ remain_xtz >= 0
  /\ XTZTransfer(EXCHANGE, executer, consumed_xtz)
  /\ TOKENTransfer(token, executer, owner, token_amount)
  /\ orders' = IF remain_xtz = 0
               THEN {x \in orders : x.key /= order.key}
               ELSE {x \in orders : x.key /= order.key} \union 
                    {[key |-> order.key, xtz |-> remain_xtz]}
   
        
CreateSellingOrder(token, seller, price, token_amount) ==
  LET key == <<seller, token, FALSE, price>>
      order == PickOrder(key)
      prev_token_amount == order.token
  IN 
  /\ TOKENTransfer(token, seller, EXCHANGE, token_amount)
  /\ orders' = {x \in orders : x.key /= key} \union 
               {[key |-> key, token |-> token_amount + prev_token_amount]}
  /\ UNCHANGED <<xtzMap>>
        
        
ExecuteSellingOrder(order, executer, xtz_amount) ==
  LET token == order.key[2]
      price == order.key[4]
      owner == order.key[1]
  IN 
  /\ price /= 0
  /\ LET consumed_token == xtz_amount \div price
         remain_token == order.token - consumed_token
     IN 
     /\ remain_token >= 0
     /\ XTZTransfer(executer, owner, xtz_amount)
     /\ TOKENTransfer(token, EXCHANGE, executer, consumed_token)
     /\ orders' = IF remain_token = 0
                  THEN {x \in orders : x.key /= order.key}
                  ELSE {x \in orders : x.key /= order.key} \union 
                       {[key |-> order.key, token |-> remain_token]}
  
  
----------------------------------------------------------------------------
\* some invariants for checking

xtzMapChecker == 
  Sum(Range(xtzMap)) = (Cardinality(CONTRACTS) - 1) * INIT_XTZ
  
tokenMapCheckerTE ==
  [t \in TOKENS |-> Sum(Range(tokenMap[t]))] = 
    [t \in TOKENS |-> (Cardinality(CONTRACTS) - 1) * INIT_TOKEN]

ordersChecker ==
  /\ xtzMap[EXCHANGE] = 
       Sum({<<order.xtz, order.key>> : order \in 
             {x \in orders : x.key[3] = TRUE}})
           
  /\ [t \in TOKENS |-> tokenMap[t][EXCHANGE]] = 
       [t \in TOKENS |-> 
         Sum({<<order.token, order.key>> : order \in 
             {x \in orders : x.key[3] = FALSE /\ x.key[2] = t}})]

             
----------------------------------------------------------------------------
\* the init behavior

TEInit == 
  /\ xtzMap = [x \in CONTRACTS |-> IF x = EXCHANGE 
                                   THEN 0
                                   ELSE INIT_XTZ]
  /\ tokenMap = [t \in TOKENS |-> 
                  [x \in CONTRACTS |-> IF x = EXCHANGE
                                       THEN 0
                                       ELSE INIT_TOKEN]]
  /\ orders = {}
  /\ pick = [
       token |-> RandomElement(TOKENS),
       user |-> RandomElement(Users),
       price |-> RandomElement(0..(INIT_XTZ \div INIT_TOKEN))
     ]

----------------------------------------------------------------------------
\* the next behavior
\* this behavior will pick random token and executer to test possible operations

TENext ==
  /\ pick' = [
       token |-> RandomElement(TOKENS),
       user |-> RandomElement(Users),
       price |-> RandomElement(0..(INIT_XTZ \div INIT_TOKEN))
     ]
     
  /\ \/ /\ xtzMap[pick.user] > 0
        /\ \/ CreateBuyingOrder(pick.token, 
                pick.user, 
                pick.price, 
                RandomElement(0..xtzMap[pick.user])
              )
           \/ LET matches == { x \in orders : x.key[3] = FALSE }
              IN /\ matches /= {}
                 /\ ExecuteSellingOrder(RandomElement(matches), 
                      pick.user,
                      RandomElement(0..xtzMap[pick.user])
                    )
                                        
     \/ /\ tokenMap[pick.token][pick.user] > 0
        /\ \/ CreateSellingOrder(pick.token,
                pick.user,
                pick.price,
                RandomElement(0..tokenMap[pick.token][pick.user])
              )
           \/ LET matches == { x \in orders : x.key[3] = TRUE }
              IN /\ matches /= {}
                 /\ ExecuteBuyingOrder(RandomElement(matches), 
                      pick.user,
                      RandomElement(0..tokenMap[pick.token][pick.user])
                    )
     
     \/ UNCHANGED <<xtzMap, tokenMap, orders>>       


=============================================================================
