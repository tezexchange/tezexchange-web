---------------------------- MODULE TESpec ---------------------------------
EXTENDS Naturals, TLC, FiniteSets

CONSTANTS CONTRACTS, \* set of contracts in Tezos
          TOKENS, \* set of token contracts
          EXCHANGE, \* exchange contract name
          INIT_TOKEN, \* initial token amount
          INIT_XTZ \* initial (mu)xtz amount 

VARIABLES xtzMap, \* XTZ amount state of contracts
          tokenMap, \* token amount state of contracts
          orders \* orders state

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
\* some exchange helper operators

Buyers ==
  {x \in CONTRACTS : xtzMap[x] > 0 /\ x /= EXCHANGE}
  
Sellers(token) == 
  {x \in CONTRACTS : tokenMap[token][x] > 0 /\ x /= EXCHANGE}

PickOrder(key) == 
  LET matches == { x \in orders : x.key = key } 
  IN IF matches = {} THEN [ xtz |-> 0, token |-> 0 ] 
     ELSE CHOOSE m \in matches : TRUE

XTZTransfer(owner, receiver, amount) ==
  IF owner = receiver 
  THEN xtzMap
  ELSE [x \in CONTRACTS |-> 
         CASE x = owner -> xtzMap[x] - amount
           [] x = receiver -> xtzMap[x] + amount
           [] OTHER -> xtzMap[x]]
  
TOKENTransfer(token, owner, receiver, amount) ==
  IF owner = receiver
  THEN tokenMap
  ELSE [t \in TOKENS |-> 
         [x \in CONTRACTS |-> 
           IF t = token
           THEN CASE x = owner -> tokenMap[t][x] - amount
                  [] x = receiver -> tokenMap[t][x] + amount
                  [] OTHER -> tokenMap[t][x]
           ELSE tokenMap[t][x]]]


----------------------------------------------------------------------------
\* tez.exchange basic user operators

CreateBuyingOrder(token, buyer, price, xtz_amount) ==
  LET key == <<buyer, token, TRUE, price>>
      order == PickOrder(key)
      prev_xtz_amount == order.xtz
  IN 
  /\ xtzMap' = XTZTransfer(buyer, EXCHANGE, xtz_amount)
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
  /\ xtzMap' = XTZTransfer(EXCHANGE, executer, consumed_xtz)
  /\ tokenMap' = TOKENTransfer(token, executer, owner, token_amount)
  /\ orders' = IF remain_xtz = 0
               THEN {x \in orders : x.key /= order.key}
               ELSE {x \in orders : x.key /= order.key} \union 
                    {[key |-> order.key, xtz |-> remain_xtz]}
   
        
CreateSellingOrder(token, seller, price, token_amount) ==
  LET key == <<seller, token, FALSE, price>>
      order == PickOrder(key)
      prev_token_amount == order.token
  IN 
  /\ tokenMap' = TOKENTransfer(token, seller, EXCHANGE, token_amount)
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
     /\ xtzMap' = XTZTransfer(executer, owner, xtz_amount)
     /\ tokenMap' = TOKENTransfer(token, EXCHANGE, executer, consumed_token)
     /\ orders' = IF remain_token = 0
                  THEN {x \in orders : x.key /= order.key}
                  ELSE {x \in orders : x.key /= order.key} \union 
                       {[key |-> order.key, token |-> remain_token]}
  
  
----------------------------------------------------------------------------
\* some invariants for checking

xtzMapChecker == 
  Sum(Range(xtzMap)) = (Cardinality(CONTRACTS) - 1) * INIT_XTZ

tokenMapChecker ==
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

Init == 
  /\ xtzMap = [x \in CONTRACTS |-> IF x = EXCHANGE 
                                   THEN 0
                                   ELSE INIT_XTZ]
  /\ tokenMap = [t \in TOKENS |-> 
                  [x \in CONTRACTS |-> IF x = EXCHANGE
                                       THEN 0
                                       ELSE INIT_TOKEN]]
  /\ orders = {}
  

----------------------------------------------------------------------------
\* the next behavior
\* this behavior will pick random token and executer to test possible operations

Next ==
  LET token == RandomElement(TOKENS)
      Inside(t) ==
        LET seller == RandomElement(Sellers(t))
            buyer == RandomElement(Buyers)
            price_range == 0..(INIT_XTZ \div INIT_TOKEN)
            price == RandomElement(price_range)
            
            MakeBuy(b, p) ==
              LET xtz_amount == RandomElement(0..xtzMap[b])
              IN CreateBuyingOrder(t, b, p, xtz_amount)
            
            ExecuteBuy(s) ==
              LET matches == { x \in orders : x.key[3] = TRUE } 
                  token_amount == RandomElement(0..tokenMap[t][s])
              IN 
              IF matches /= {} 
              THEN ExecuteBuyingOrder(Pick(matches), s, token_amount)
              ELSE FALSE
                 
            MakeSell(s, p) == 
              LET token_amount == RandomElement(0..tokenMap[t][s])
              IN CreateSellingOrder(t, s, p, token_amount)
              
            ExecuteSell(b) ==
              LET matches == { x \in orders : x.key[3] = FALSE } 
                  xtz_amount == RandomElement(0..xtzMap[b])
              IN 
              IF matches /= {} 
              THEN ExecuteSellingOrder(Pick(matches), b, xtz_amount)
              ELSE FALSE
              
        IN 
        LET BuyerOp == /\ Buyers /= {}
                       /\ \/ MakeBuy(buyer, price)
                          \/ ExecuteSell(buyer)
                          
            SellerOp == /\ Sellers(t) /= {}
                        /\ \/ ExecuteBuy(seller)
                           \/ MakeSell(seller, price)
        
        IN \/ BuyerOp
           \/ SellerOp
             
  IN Inside(token)


=============================================================================
