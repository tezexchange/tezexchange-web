# Tezos Token Standard (draft)

## Sample
As Michelson
[token.liq.tz](token.liq.tz)

As Liquidity
[token.liq](token.liq)

## Parameter

As Michelson
```Michelson
parameter
  (or
    (contract                        <- ENTRY for getting infomation
      bytes)                         <- callback contract
    (or
      (pair                          <- ENTRY for transferring
        address                      <- the address of receiver
        (pair
          nat                        <- amount
          (option                    <- if it needs callback
            (pair
              (contract              <- callback contract
                bytes
              bytes))))              <- passing bytes
      (pair                          <- ENTRY for custom functions
        nat                          <- custom method index
        bytes)))                      <- custom method parameter
```

As Liquidity
```OCaml
type token_parameter = 
| Info of bytes contract
| Transfer of address * nat * (bytes contract * bytes) option
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
type token_storage = {
  balance_map : (address, nat) big_map;
  symbol : string;
  name : string;
  decimal : nat;
  total : nat;
}
```

## Code Logic

### Info entry
Call the callback contract with the packed bytes from `(storage.symbol, storage.name, storage.decimal, storage.total)`

### Transfer entry
```
if balance of owner is enough to pay then
  reduce owner's balance by amount
  add receiver's balance by amount
  update storage
  if callback is needed then
    call the callback contract with the packed bytes from `(passing_bytes, receiver_addr, amount, owner_balance, receiver_balance)`
  else
    do nothing
else
  fail
```

### Custom entry
By default it is `fail`, and you can add your own codes in this entry. 


