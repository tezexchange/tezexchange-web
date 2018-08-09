---------------------------- MODULE TESpec ----------------------------
EXTENDS Naturals, TLC, FiniteSets

CONSTANTS CONTRACT, TOKEN, EXCHANGE
VARIABLES XTZ_balance, TOKEN_amount, orders

----------------------------------------------------------------------------
Range(T) == {<<T[x], x>> : x \in DOMAIN T}
Pick(S) == CHOOSE s \in S : TRUE

RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_, _), S, value) == 
  IF S = {} THEN value
  ELSE LET s == Pick(S)
       IN IF Op(s[1], value) = Op(value, s[1])
       THEN SetReduce(Op, S \ {s}, Op(s[1], value)) 
       ELSE Assert(FALSE, "oh no")
       
Sum(S) == LET _op(a, b) == a + b
          IN SetReduce(_op, S, 0)
       
  

----------------------------------------------------------------------------
Buyers ==
  {x \in CONTRACT : XTZ_balance[x] > 0 /\ x /= EXCHANGE}
  
Sellers(token) == 
  {x \in CONTRACT : TOKEN_amount[token][x] > 0 /\ x /= EXCHANGE}

PickOrder(key) == 
  LET matches == { x \in orders : x.key = key } 
  IN IF matches = {} THEN [ xtz |-> 0, token |-> 0 ] 
     ELSE CHOOSE m \in matches : TRUE

XTZTransfer(owner, receiver, amount) ==
  IF owner = receiver 
  THEN XTZ_balance
  ELSE [x \in CONTRACT |-> CASE x = owner -> XTZ_balance[x] - amount
                             [] x = receiver -> XTZ_balance[x] + amount
                             [] OTHER -> XTZ_balance[x]]
  
TOKENTransfer(token, owner, receiver, amount) ==
  IF owner = receiver
  THEN TOKEN_amount
  ELSE [t \in TOKEN |-> 
         [x \in CONTRACT |-> IF t = token
                             THEN CASE x = owner -> TOKEN_amount[t][x] - amount
                                    [] x = receiver -> TOKEN_amount[t][x] + amount
                                    [] OTHER -> TOKEN_amount[t][x]
                             ELSE TOKEN_amount[t][x]]]


----------------------------------------------------------------------------
CreateBuyingOrder(token, buyer, price, xtz_amount) ==
  LET key == <<buyer, token, TRUE, price>>
      order == PickOrder(key)
      prev_xtz_amount == order.xtz
  IN 
\*     /\ PrintT(<<"CreateBuyingOrder", buyer, token, price, xtz_amount>>)
     /\ XTZ_balance' = XTZTransfer(buyer, EXCHANGE, xtz_amount)
     /\ orders' = {x \in orders : x.key /= key} \union 
                  {[key |-> key, xtz |-> xtz_amount + prev_xtz_amount]}
     /\ UNCHANGED <<TOKEN_amount>>


ExecuteBuyingOrder(order, executer, token_amount) ==
  LET token == order.key[2]
      price == order.key[4]
      owner == order.key[1]
      consumed_xtz == price * token_amount
      remain_xtz == order.xtz - consumed_xtz
  IN 
     /\ PrintT(<<"ExecuteBuyingOrder", order.key, executer, token_amount, consumed_xtz>>)
     /\ remain_xtz >= 0
     /\ XTZ_balance' = XTZTransfer(EXCHANGE, executer, consumed_xtz)
     /\ TOKEN_amount' = TOKENTransfer(token, executer, owner, token_amount)
     /\ orders' = IF remain_xtz = 0
                  THEN {x \in orders : x.key /= order.key}
                  ELSE {x \in orders : x.key /= order.key} \union 
                       {[key |-> order.key, xtz |-> remain_xtz]}
   
        
CreateSellingOrder(token, seller, price, token_amount) ==
  LET key == <<seller, token, FALSE, price>>
      order == PickOrder(key)
      prev_token_amount == order.token
  IN 
\*     /\ PrintT(<<"CreateSellingOrder", seller, token, price,price, token_amount>>)
     /\ TOKEN_amount' = TOKENTransfer(token, seller, EXCHANGE, token_amount)
     /\ orders' = {x \in orders : x.key /= key} \union 
                  {[key |-> key, token |-> token_amount + prev_token_amount]}
     /\ UNCHANGED <<XTZ_balance>>
        
        
ExecuteSellingOrder(order, executer, xtz_amount) ==
  LET token == order.key[2]
      price == order.key[4]
      owner == order.key[1]
  IN /\ price /= 0
     /\ LET consumed_token == xtz_amount \div price
            remain_token == order.token - consumed_token
        IN 
\*           /\ PrintT(<<"ExecuteSellingOrder", order.key, executer, xtz_amount>>)
           /\ remain_token >= 0
           /\ XTZ_balance' = XTZTransfer(executer, owner, xtz_amount)
           /\ TOKEN_amount' = TOKENTransfer(token, EXCHANGE, executer, consumed_token)
           /\ orders' = IF remain_token = 0
                        THEN {x \in orders : x.key /= order.key}
                        ELSE {x \in orders : x.key /= order.key} \union 
                             {[key |-> order.key, token |-> remain_token]}
  
  
----------------------------------------------------------------------------
TypeOK == 
  /\ Sum(Range(XTZ_balance)) = (Cardinality(CONTRACT) - 1) * 10000
\*  /\ Sum({{TOKEN_amount[t][x] : x \in CONTRACT} : t \in TOKEN}) = (Cardinality(CONTRACT) - 1) * Cardinality(TOKEN) * 100

Init == 
  /\ XTZ_balance = [x \in CONTRACT |-> IF x = EXCHANGE 
                                       THEN 0
                                       ELSE 10000]
  /\ TOKEN_amount = [t \in TOKEN |-> [x \in CONTRACT |-> IF x = EXCHANGE
                                                         THEN 0
                                                         ELSE 100]]
  /\ orders = {}
  
  
Next ==
  LET token == RandomElement(TOKEN)
      Inside(t) ==
        LET seller == RandomElement(Sellers(t))
            buyer == RandomElement(Buyers)
            price == RandomElement(0..100)
            
            MakeBuy(b, p) ==
              LET xtz_amount == RandomElement(0..XTZ_balance[b])
              IN CreateBuyingOrder(t, b, p, xtz_amount)
            
            ExecuteBuy(s) ==
              LET matches == { x \in orders : x.key[3] = TRUE } 
                  token_amount == RandomElement(0..TOKEN_amount[t][s])
              IN IF matches /= {} 
                 THEN ExecuteBuyingOrder(CHOOSE m \in matches : TRUE, s, token_amount)
                 ELSE FALSE
                 
            MakeSell(s, p) == 
              LET token_amount == RandomElement(0..TOKEN_amount[t][s])
              IN CreateSellingOrder(t, s, p, token_amount)
              
            ExecuteSell(b) ==
              LET matches == { x \in orders : x.key[3] = FALSE } 
                  xtz_amount == RandomElement(0..XTZ_balance[b])
              IN IF matches /= {} 
                 THEN ExecuteSellingOrder(CHOOSE m \in matches : TRUE, b, xtz_amount)
                 ELSE FALSE
              
              
        IN 
        LET BuyerOp == /\ Buyers /= {}
                       /\ \/ MakeBuy(buyer, price)
\*                          \/ ExecuteSell(buyer)
                          
            SellerOp == /\ Sellers(t) /= {}
                        /\ \/ ExecuteBuy(seller)
\*                           \/ MakeSell(seller, price)
        
        IN \/ BuyerOp
           \/ SellerOp
           
                    
                    
  IN Inside(token)

=============================================================================
