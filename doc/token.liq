type token_storage = {
  balance_map : (address, nat) big_map;
  symbol : string;
  name : string;
  decimal : nat;
  total : nat;
}

let%init storage = {
  balance_map = (BigMap [] : (address, nat) big_map);
  symbol = "Symbol";
  name = "Name";
  decimal = 2p;
  total = 999999p;
}

type token_parameter = 
| Info of address * bytes contract
| Transfer of address * nat * (key * signature) option
| Custom of nat * bytes


let%entry main (parameter : token_parameter) (storage : token_storage) =
  match parameter with
  | Info (owner, callback_contract) ->
    let token_amount = match Map.find owner storage.balance_map with
      | None -> 0p
      | Some x -> x
    in
    let op = Contract.call callback_contract 0tz (Bytes.pack (token_amount, storage.symbol, storage.name, storage.decimal, storage.total)) in
    ([op], storage)

  | Transfer (receiver, amount, sig_pair) ->
    let owner = match sig_pair with 
      | None -> Current.source ()
      | Some (pub_key, sig) ->
        if Crypto.check pub_key sig (Bytes.pack (Current.sender (), receiver, amount)) then
          Current.sender ()
        else
          Current.failwith "invalid signature"
    in
    let owner_balance = 
      match Map.find owner storage.balance_map with
      | None -> 0p
      | Some x -> x
    in
    let storage = match%nat owner_balance - amount with
      | Minus _ ->
        Current.failwith "balance insufficient"
      | Plus remain ->
        let balance_map = Map.update owner (Some remain) storage.balance_map in
        let receiver_balance = amount + (match Map.find receiver storage.balance_map with | None -> 0p | Some x -> x) in
        let balance_map = Map.update receiver (Some receiver_balance) balance_map in
        storage.balance_map <- balance_map
    in
    (([] : operation list), storage)

  | Custom _ ->
    Current.failwith ()
