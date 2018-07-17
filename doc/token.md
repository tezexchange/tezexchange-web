# Tezos Token Standard

## Sample
As Michelson
[token.tz](token.tz)

As Liquidity
[token.liq](token.liq)

## Parameter

As Michelson
```Michelson
parameter
  (or
    (pair                            <- ENTRY for getting infomation
      address                        <- check amount of address
      (contract                      <- callback contract
        bytes))
    (or
      (pair                          <- ENTRY for transferring
        address                      <- the address of receiver
        (pair
          nat                        <- amount
          (option                    <- decide owner is SENDER or SOURCE
            (pair
              key
              signature))))
      (pair                          <- ENTRY for custom functions
        nat                          <- custom method index
        bytes)))                     <- custom method parameter
```

As Liquidity
```OCaml
type parameter = 
| Info of address * bytes contract
| Transfer of address * nat * (key * signature) option
| Custom of nat * bytes
```

## Storage

As Michelson
```Michelson
storage
  (pair
    (big_map                  <- balance map
      address
      nat)
    (pair
      string                  <- token symbol
      (pair
        string                <- token full name
        (pair
          nat                 <- decimal
          nat))))             <- total amount
```

As Liquidity
```OCaml
type storage = {
  balance_map : (address, nat) big_map;
  symbol : string;
  name : string;
  decimal : nat;
  total : nat;
}
```

## Code

### Info entry
Call the callback contract with the packed bytes from `(amount_of_check_address, storage.symbol, storage.name, storage.decimal, storage.total)`

### Transfer entry
```
if exsit (key, signature) then
  if signature is valid then
    owner = SENDER
  else
    fail
else
  owner = SOURCE

------------ THEN -------------
if balance of owner is enough to pay then
  reduce owner's balance by amount
  add receiver's balance by amount
  update storage
else
  fail
```
### Custom entry
By default it is `fail`, and you can add your own codes in this entry. 


