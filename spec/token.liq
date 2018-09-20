type token_storage = {
  balance_map : (address, nat) big_map;
  symbol : string;
  name : string;
  decimal : nat;
  total : nat;
}

let%init storage = {
  balance_map = (BigMap [] : (address, nat) big_map);
  symbol = "Token symbol";
  name = "Token name";
  decimal = 2p;
  total = 100000000p;
}

type token_parameter = 
| Info of bytes contract
| Transfer of address * nat * (bytes contract * bytes) option
| Custom of nat * bytes

let%entry main (parameter : token_parameter) (storage : token_storage) =
  match parameter with
  | Info callback_contract ->
    ([Contract.call callback_contract 0tz (Bytes.pack (storage.symbol, storage.name, storage.decimal, storage.total))], storage)

  | Transfer (receiver_addr, amount, callback_option) ->
    let owner = Current.sender () in
    let owner_balance = 
      match Map.find owner storage.balance_map with
      | None -> 0p
      | Some x -> x
    in
    let (storage, owner_balance, receiver_balance) = match%nat owner_balance - amount with
      | Minus _ ->
        Current.failwith (String.concat ["TOKEN/"; storage.symbol; "/100"])
      | Plus remain ->
        let balance_map = Map.update owner (Some remain) storage.balance_map in
        let receiver_balance = amount + (match Map.find receiver_addr balance_map with | None -> 0p | Some x -> x) in
        let balance_map = Map.update receiver_addr (Some receiver_balance) balance_map in
        ((storage.balance_map <- balance_map), remain, receiver_balance)
    in
    let ops = 
      match callback_option with
      | None -> ([] : operation list)
      | Some (callback_contract, passing_bytes) ->
        [Contract.call callback_contract 0tz (Bytes.pack (passing_bytes, receiver_addr, amount, owner_balance, receiver_balance))]
    in
    (ops, storage)

  | Custom _ ->
    Current.failwith ()
