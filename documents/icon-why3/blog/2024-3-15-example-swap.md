---
slug: example-swap
title: Case study ; Swap fa2 tokens
authors: hsaito
tags: []
---

This example considers the situation where swapping 2 tokens compliant with [FA2](https://gitlab.com/tezos/tzip/-/blob/57c32be0e5d4bc6867cea83a12cf909894c42c41/proposals/tzip-12/tzip-12.md).

The contract compliant with FA2 has 3 entrypoints: `transfer`, `balance_of`, and `update_operators`.
They all receive a list as their operation query. But in this example, they receive one operation for simplicity.
- `transfer from_ to_ token_id amount` sends `amount` tokens indexed by `token_id` from `from_` address to `to_` address
- `update_operators (Left (owner, operator, token_id))` approves permission to transfer `owner`'s tokens indexed by `token_id` to `operator`
- `update_operators (Right (owner, operator, token_id))` removes the permission to transfer `owner`'s tokens indexed by `token_id` from `operator`
- `balance_of owner token_id callback` checks the number of tokens indexed by `token_id` owner holds, and calls `callback` with the argument of the number

```ml

contract Token
{
  map nat (map address nat) balances;
  map nat (map address (set address)) operators;

  entrypoint transfer (from_ : address) (to_ : address) (token_id : nat) (amount : nat)
  {
    assert (sender = from_ || operators[token_id][from_].mem(sender));
    balances[token_id][from_] -= amount;
    balances[token_id][to_] += amount;
    []
  }

  entrypoint update_operators (op : or (address * address * nat) (address * address * nat))
  {
    begin match op with
    | Left (owner, operator, token_id) ->
        assert (owner = sender);
        operators[token_id][owner].add(operator)
    | Right (owner, operator, token_id) ->
        assert (owner = sender);
        operators[token_id][owner].remove(operator)
    end;
    []
  }

  entrypoint balance_of (owner : address) (token_id : nat) (callback : contract (address * nat))
  {
    [TransferTokens ((owner, token_id, balances[token_id][owner]), 0, callback)]
  }
}
```

FA2 has only `transfer` API to send tokens.
It seems that it is difficult to prevent the receiver from taking tokens away at a glance.
But the mechanism to give the right to send tokens to another account enables safe token swapping:
The accounts who want to swap their tokens with each other give permissions to the address of `Swap` contract by calling `update_operators`, and either of them calls `Swap.swap` to invoke each `transfer`.
After calling `Swap.swap`, both can call `update_operators` again to remove `Swap` contract from operators.

```ml
contract Swap
{
  entrypoint swap (a : address * address * nat * nat) (b : address * address * nat * nat)
  {
    let (a_addr, a_owner, a_token_id, a_amount) = a in
    let (b_addr, b_owner, b_token_id, b_amount) = b in
    assert (a_addr <> Swap.addr && b_addr <> Swap.addr);
    let op1 = TransferTokens ((a_owner, b_owner, a_token_id, a_amount), 0, a_addr%transfer) in
    let op2 = TransferTokens ((b_owner, a_owner, b_token_id, b_amount), 0, b_addr%transfer) in
    [op1; op2]
  }
}
```

The code below is the proof.
- If a series of execution called by `swap` terminates successfully,
  `Swap.addr` should be one of their operators. So the postcondition of `Swap` can assume `c.token0_storage.Token0.operators[a_token_id][a_addr][Swap.addr] /\ c.token1_storage.Token1.operators[b_token_id][b_addr][Swap.addr]` condition
  - Because `transfer` can be only called by the owner or one of the operators, and `Swap` is assumed is not the owner
- It provides 2 contracts compliant with FA2 named `Token0` and `Token1` to represent swapping 2 kinds of tokens managed by 2 different FA-compliant contracts.
- It omits the predicate of `balance_of` because it has little to do with the specification
- `Implicit0` emulates one side of exchangers executing a series of operations: adding `Swap` to the operators, executing `Swap.swap`, and removing `Swap` from the operators.
  - It succeeds if `Swap` already has the right of operator to transfer tokens managed by the other side of exchangers.
    The postcondition of `Implicit0` can be a relaxed postcondition of `Swap`.

```ml
scope Preambles
  use string.String
  use list.Length
  use list.Map
  use list.Quant

  function sum_of : (map address nat) -> nat

  axiom SumE : sum_of (const 0) = 0

  axiom SumI : forall m k v.
    v >= 0 ->
    m[k] >= 0 /\ (* Needed to be given by hand *)
    sum_of m[k <- v] = sum_of m + v - m[k]

  meta "algebraic:kept" type (map nat (map address nat), map nat (map address nat))

  function update_balance
    (from_ : address)
    (to_ : address)
    (token_id : nat)
    (amount : nat)
    (balances : map nat (map address nat))
    (balances' : map nat (map address nat))
    : (map nat (map address nat), map nat (map address nat)) =
    let b = balances[token_id] in
    let to_balance = b[to_] + amount in
    let b = b[to_ <- to_balance] in
    let b' = balances'[token_id] in
    let from_balance = b'[from_] + amount in
    let b' = b'[from_ <- from_balance] in
    (balances[token_id <- b], balances'[token_id <- b'])
end

scope Postambles

  predicate balances_invariant (c : ctx) (c' : ctx) =
    true
    (* forall a. sum_of c.token_storage.Token.balances[a] = sum_of c'.token_storage.Token.balances[a]
    (* That's true but can not be proved automatically *) *)
end

scope Unknown
  predicate pre (c : ctx) = Token0.addr <> Token1.addr (* Required!! *)

  predicate post (c : ctx) (c' : ctx) =
    balances_invariant c c'

  scope Entrypoint
    predicate default unit
  end

end

scope Swap

  type storage [@gen_wf] = { }

  predicate pre (st : step) (gp : gparam) (c : ctx) = Token0.addr <> Token1.addr

  predicate post (_st : step) (gp : gparam) (c : ctx) (c' : ctx) =
    balances_invariant c c' /\
    match gp with
    | Gp'Swap'swap a_addr a_token_id a_amount b_addr b_token_id b_amount ->
        c.token0_storage.Token0.operators[a_token_id][a_addr][Swap.addr] /\
        c.token1_storage.Token1.operators[b_token_id][b_addr][Swap.addr] /\
        ( let balances = c.token0_storage.Token0.balances in
          let balances' = c'.token0_storage.Token0.balances in
          let balances, balances' = update_balance a_addr b_addr a_token_id a_amount balances balances' in
          balances = balances'
        ) /\
        ( let balances = c.token1_storage.Token1.balances in
          let balances' = c'.token1_storage.Token1.balances in
          let balances, balances' = update_balance b_addr a_addr b_token_id b_amount balances balances' in
          balances = balances'
        )
    | _ -> false
    end

  let upper_ops = 2

  scope Spec
    predicate swap
      (st : step)
      (a_addr : address)
      (a_token_id : nat)
      (a_amount : nat)
      (b_addr : address)
      (b_token_id : nat)
      (b_amount : nat)
      (s : storage)
      (ops : list operation)
      (s' : storage) =
      a_addr <> self st /\
      b_addr <> self st /\
      let op0 = Xfer (Gp'Token0'transfer a_addr b_addr a_token_id a_amount) 0 Token0.addr in
      let op1 = Xfer (Gp'Token1'transfer b_addr a_addr b_token_id b_amount) 0 Token1.addr in
      ops = Cons op0 (Cons op1 Nil)

  end

end

scope Token0
  type storage [@gen_wf] = {
    balances : map nat (map address nat);
    operators : map nat (map address (map address bool));
  }

  predicate pre (st : step) (gp : gparam) (c : ctx) = Token0.addr <> Token1.addr

  predicate post (st : step) (gp : gparam) (c : ctx) (c' : ctx) =
    balances_invariant c c' /\
    c.token1_storage = c'.token1_storage /\
    match gp with
    | Gp'Token0'transfer from_ to_ token_id amount ->
        ( from_ = sender st \/ c.token0_storage.Token0.operators[token_id][from_][sender st]) /\
          let balances = c.token0_storage.Token0.balances in
          let balances' = c'.token0_storage.Token0.balances in
          let b, b' = update_balance from_ to_ token_id amount balances balances' in
          b = b' /\
          c.token0_storage.Token0.operators = c'.token0_storage.Token0.operators
    | Gp'Token0'update_operators _ ->
        c.token0_storage.Token0.balances = c'.token0_storage.Token0.balances
    | _ -> false
    end

  let upper_ops = 0

  scope Spec

    predicate transfer
      (st : step)
      (from_ : address)
      (to_ : address)
      (token_id : nat)
      (amount : nat)
      (s : storage)
      (ops : list operation)
      (s' : storage) =
        let sender = sender st in
        (from_ = sender \/ s.operators[token_id][from_][sender]) /\
        s.balances[token_id][from_] >= amount /\
        let b, b' = update_balance from_ to_ token_id amount s.balances s'.balances in
        b = b' /\
        s.operators = s'.operators /\
        ops = Nil

  predicate update_operators
    (st : step)
    (e : (or (address, (address, nat)) (address, (address, nat))))
    (s : storage)
    (ops : list operation)
    (s' : storage) =
      let sender = sender st in
      match e with
      | Left (owner, (ope, token_id)) ->
          owner = sender /\
          s'.operators[token_id][owner][ope]
      | Right (owner, (ope, token_id)) ->
          owner = sender /\
          not s'.operators[token_id][owner][ope]
      end /\
      s.balances = s'.balances /\
      ops = Nil

  end
end


scope Token1
  type storage [@gen_wf] = {
    balances : map nat (map address nat);
    operators : map nat (map address (map address bool));
  }

  predicate pre (st : step) (gp : gparam) (c : ctx) = Token0.addr <> Token1.addr

  predicate post (st : step) (gp : gparam) (c : ctx) (c' : ctx) =
    balances_invariant c c' /\
    c.token0_storage = c'.token0_storage /\
    match gp with
    | Gp'Token1'transfer from_ to_ token_id amount ->
        ( from_ = sender st \/ c.token1_storage.Token1.operators[token_id][from_][sender st]) /\
          let balances = c.token1_storage.Token1.balances in
          let balances' = c'.token1_storage.Token1.balances in
          let b, b' = update_balance from_ to_ token_id amount balances balances' in
          b = b' /\
          c.token1_storage.Token1.operators = c'.token1_storage.Token1.operators
    | Gp'Token1'update_operators _ ->
        c.token1_storage.Token1.balances = c'.token1_storage.Token1.balances
    | _ -> false
    end

  let upper_ops = 0

  scope Spec

    predicate transfer
      (st : step)
      (from_ : address)
      (to_ : address)
      (token_id : nat)
      (amount : nat)
      (s : storage)
      (ops : list operation)
      (s' : storage) =
        let sender = sender st in
        (from_ = sender \/ s.operators[token_id][from_][sender]) /\
        s.balances[token_id][from_] >= amount /\
        let b, b' = update_balance from_ to_ token_id amount s.balances s'.balances in
        b = b' /\
        s.operators = s'.operators /\
        ops = Nil

  predicate update_operators
    (st : step)
    (e : (or (address, (address, nat)) (address, (address, nat))))
    (s : storage)
    (ops : list operation)
    (s' : storage) =
      let sender = sender st in
      match e with
      | Left (owner, (ope, token_id)) ->
          owner = sender /\
          s'.operators[token_id][owner][ope]
      | Right (owner, (ope, token_id)) ->
          owner = sender /\
          not s'.operators[token_id][owner][ope]
      end /\
      s.balances = s'.balances /\
      ops = Nil

  end
end

scope Implicit0
  type storage [@gen_wf] = {}

  predicate pre (st : step) (gp : gparam) (c : ctx) = Token0.addr <> Token1.addr

  predicate post (st : step) (gp : gparam) (c : ctx) (c' : ctx) =
    balances_invariant c c' /\
    match gp with
    | Gp'Implicit0'default a_token_id a_amount b_addr b_token_id b_amount ->
        let a_addr = self st in
        c.token1_storage.Token1.operators[b_token_id][b_addr][Swap.addr] /\
        ( let balances = c.token0_storage.Token0.balances in
          let balances' = c'.token0_storage.Token0.balances in
          let balances, balances' = update_balance a_addr b_addr a_token_id a_amount balances balances' in
          balances = balances'
        ) /\
        ( let balances = c.token1_storage.Token1.balances in
          let balances' = c'.token1_storage.Token1.balances in
          let balances, balances' = update_balance b_addr a_addr b_token_id b_amount balances balances' in
          balances = balances'
        )
    | _ -> false
    end

  let upper_ops = 3

  scope Spec
    (* Swap tokens with [b_addr] if [b_addr] set [Swap.addr] as an operator of [b_token_id] token in [Token1] *)
    predicate default
      (st : step)
      (a_token_id : nat)
      (a_amount : nat)
      (b_addr : address)
      (b_token_id : nat)
      (b_amount : nat)
      (s : storage)
      (ops : list operation)
      (s' : storage) =
      let op0 = Xfer (Gp'Token0'update_operators (Left (self st, (Swap.addr, a_token_id)))) 0 Token0.addr in
      let op1 = Xfer (Gp'Swap'swap (self st) a_token_id a_amount b_addr b_token_id b_amount) 0 Swap.addr in
      let op2 = Xfer (Gp'Token0'update_operators (Right (self st, (Swap.addr, a_token_id)))) 0 Token0.addr in
      ops = Cons op0 (Cons op1 (Cons op2 Nil))
  end
end

```
