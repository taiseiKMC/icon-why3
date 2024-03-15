---
slug: example-mixer
title: Case study ; Mixer
authors: hsaito
tags: []
---

This example shows the interaction between `Mixer` contract and `Splitter` contract.

`Mixer` is known as a system that relays transferring tokens for decoupling senders and receivers.
`Mixer` in this example has 2 entrypoints: `deposit` and `withdraw`.
- `deposit key hash` receives balances and records the amount to the storage with `key` and `hash`
  - Assume that the sender knows the `passcode` such that `hash = sha256 (key @ passcode)` holds
    - `@` is a binary operator that means concatenation of 2 byte sequences
- `withdraw key passcode` sends the balances associated with `key` to the caller if the recorded `hash` equals `sha256 (key @ passcode)`

```ml
contract Mixer
{
  map bytes (pair bytes mutez) balances;

  entrypoint deposit (key : bytes) (hash : bytes)
  {
    match balances.find_opt(key) with
    | None -> balances[key] <- (hash, amount)
    | Some (h, b) ->
        if h = hash then
          balances[key] <- (h, b + amount)
        else
          assert false
    []
  }

  entrypoint withdraw (key : bytes) (passcode : bytes)
  {
    match balances.find_opt(key) with
    | None -> assert false
    | Some (h, b) ->
        if h = sha256 (key @ passcode) then
          balances.remove(key);
          [TransferTokens ((), b, sender%default)]
        else
          assert false
  }
}
```

When Mixer contract splits balances and sends them to some accounts,
`withdraw` usually receives an additional hash for getting the rest balances.
But this scenario omits this feature and considers an alternative contract `Splitter` to it.

`Splitter` has 2 entrypoints: `split` and `default`
- `split key passcode dests` memorizes `dests` temporarily and relays `key` and `passcode` to `Mixer.withdraw`
- `default` is expected to be called by `Mixer.withdraw`. It sends the received balances to `dests`, recorded addresses in the storage.


```ml
contract Splitter
{
  option (list address) state;

  entrypoint split (key : bytes) (hash : bytes) (dests : list address)
  {
    state <- dests
    [TransferTokens ((key, hash), 0, Mixer.addr%withdraw)]
  }

  entrypoint default ()
  {
    match state with
    | None -> []
    | Some addrs ->
        state <- None;
        let b = amount / List.length addr in
        List.map (fun addr -> TransferTokens ((), b, addr%default)) addrs
  }
}
```

When calling `Splitter.split`,
- `dests` is stored to `state` as `Some dests`
- It calls `Mixer.withdraw`, and if the given `key` and `passcode` are valid, `Splitter.default` is called back
- `Splitter.default` splits the tokens sent by `Mixer` to the same amounts and sends them to the addresses recorded to `state`.
  - `state` should have `dests`

Overall it behaves to send balances that `Mixer` holds to the given addresses `dests`.

This case holds some properties below at the end of execution.
- `Splitter.state` must hold `None`
- `Mixer.balance : mutez` is greater than the sum of (the second value of) `Mixer.balances : map bytes (pair bytes mutez)`

The tzw code below shows their proof.
- It defines an uninterpreted function like `sum_of` and axioms like `SumE`, `SumI`, and `SumI'`. This is a way to describe a property of a recursive data object like `map`.
- The predicates in `Splitter.Spec` do not need the conditions about the changes in `mixer_balance`.
  The conditions about `amount` and `balance` are automatically extracted.
- The value of `Splitter.state` when `Mixer.withdraw` is called depends on the sender.
  - If the sender is `Splitter` contract, it should be invoked by `Splitter.split` and `state` be `Some`
    (and reset to `None` by the chained call)
  - In the other case, `state` should be `None`
  
  So the precondition of `Mixer` needs conditional branching depending on the caller
- Bad news: This verification tool can not handle a variable number of operations because of this limitation.
  It means this can not handle any number of addresses `dests`.
  Below proof extracts the returning operation list 3 times and can accept up to 3 addresses

```ml
scope Preambles
  use string.String (* for string concat *)
  use list.Length (* for List.length *)

  (* Gives [sha256] as an uninterpreted function *)
  val function sha256 bytes : bytes

  meta "algebraic:kept" type (bytes, nat)
  meta "algebraic:kept" type option (bytes, nat)
  meta "algebraic:kept" type option (list address)

  function sum_of : (map bytes (option (bytes, nat))) -> nat

  axiom SumE : sum_of (const None) = 0

  axiom SumI : forall m k v0 v1.
    let old_value = match m[k] with Some (_, n) -> n | None -> 0 end in
    old_value >= 0 /\ (* Should be given by hands *)
    sum_of m[k <- Some (v0, v1)] = sum_of m + v1 - old_value

  axiom SumI' : forall m k.
    let old_value = match m[k] with Some (_, n) -> n | None -> 0 end in
    sum_of m[k <- None] = sum_of m - old_value
end

scope Postambles
  (* Defines some invariants *)
  predicate addr_inv (c : ctx) =
    c.splitter_storage.Splitter.mixer_addr = Mixer.addr

  predicate storage_inv (c : ctx) =
    c.splitter_balance >= 0 /\
    sum_of c.mixer_storage.Mixer.balances <= c.mixer_balance /\
    addr_inv c

  predicate splitter_storage_inv (c : ctx) =
    c.splitter_storage.Splitter.state = None
end

scope Unknown
  predicate pre (c : ctx) =
    storage_inv c /\
    splitter_storage_inv c

  predicate post (c : ctx) (c' : ctx) =
    storage_inv c' /\
    splitter_storage_inv c'

  scope Entrypoint
    predicate default unit
  end

end

scope Mixer

  type storage [@gen_wf] = {
    balances : big_map bytes (option (bytes, nat));
  }

  predicate pre (st : step) (gp : gparam) (c : ctx) =
    storage_inv c /\
    match gp with
    | Gp'Mixer'withdraw key passcode ->
        (st.sender <> Splitter.addr -> splitter_storage_inv c)
    | _ -> splitter_storage_inv c
    end

  predicate post (st : step) (gp : gparam) (c : ctx) (c' : ctx) =
    storage_inv c' /\
    splitter_storage_inv c'

  let upper_ops = 1

  scope Spec
    predicate deposit (st : step) (key : bytes) (hash : bytes) (s : storage) (ops : list operation) (s' : storage) =
      let b = s.balances[key <- Some (hash, st.amount)] in
      s' = { s with balances = b } /\
      ops = Nil

    predicate withdraw (st : step) (key : bytes) (passcode : bytes) (s : storage) (ops : list operation) (s' : storage) =
      let b = s.balances in
      match b[key] with
      | None -> false
      | Some (hash, token) ->
          if sha256 (concat key passcode) = hash
          then
            s' = { s with balances = b[key <- None] } /\
            ops = Cons (Xfer (Gp'Unknown'default ()) token st.sender) Nil
          else
            s' = s /\
            ops = ops = Cons (Xfer (Gp'Unknown'default ()) 0 st.sender) Nil
      end
  end

end

scope Splitter
  type storage [@gen_wf] = {
    mixer_addr : address;
    state : option (list address)
  }

  predicate pre (st : step) (gp : gparam) (c : ctx) =
    storage_inv c /\
    match gp with
    | Gp'Splitter'split key passcode dests ->
        splitter_storage_inv c
    | Gp'Splitter'default () ->
        st.sender <> Mixer.addr -> splitter_storage_inv c
    | _ -> false
    end

  predicate post (_st : step) (gp : gparam) (c : ctx) (c' : ctx) =
    storage_inv c' /\
    splitter_storage_inv c'

  let upper_ops = 3

  scope Spec
    predicate split (st : step) (key : bytes) (passcode : bytes) (dests : list address) (s : storage) (ops : list operation) (s' : storage) =
      ops = Cons (Xfer (Gp'Mixer'withdraw key passcode) 0 s.mixer_addr) Nil /\
      s'.state = Some dests /\
      s.mixer_addr = s'.mixer_addr
    
    predicate default (st : step) (_p : unit) (s : storage) (ops : list operation) (s' : storage) =
      st.sender = s.mixer_addr /\
      match s.state with
      | None ->
          ops = Nil /\
          s' = s
      | Some dests ->
          let d = div st.amount (length dests) in
          let c_op addr = Xfer (Gp'Unknown'default ()) d addr in
          (* ops = map c_op dests /\ *)
          ops = (* Extract 3 times *)
            match dests with
            | Nil -> Nil
            | Cons addr0 t ->
                Cons (c_op addr0)
                  (match dests with
                  | Nil -> Nil
                  | Cons addr1 t ->
                      Cons (c_op addr1)
                        (match dests with
                        | Nil -> Nil
                        | Cons addr2 _ -> Cons (c_op addr2) Nil
                        end)
                  end)
            end /\
          s' = { s with state = None }
      end
  end
end

```


Originally we don't have to consider the situation if the given `passcode` is wrong,
because the execution fails and the state does not go an invalid state in the case.
To check the recorded balance is sent only if the given `passcode` is correct,
assume the modified `Mixer.withdraw` like below

```ml
entrypoint withdraw (key : bytes) (passcode : bytes)
{
  match balances.find_opt(key) with
  | None -> assert false
  | Some (h, b) ->
      if h = sha256 (key @ passcode) then
        balances.remove(key);
        [TransferTokens ((), b, sender%default)]
      else
        [] (* assert false *)
}
```

and define `Implicit0` that emulates an implicit account that calls `Splitter.split`

```ml
contract Implicit0
{
  entrypoint send (key : bytes) (passcode : bytes)
  {
    [TransferTokens((key, passcode, [self_address], 0, Splitter%split))]
  }

  entrypoint default ()
  {
    []
  }
}
```

When `Splitter.split` sends tokens to `dests`,
The accounts in `dests` could make a chain of calls
and could call `Mixer.withdraw` again.
It means this following postcondition in `Mixer`, in particular `c.mixer_balance = c'.mixer_balance + token`, does not hold
because `Mixer` could send additional tokens in the chained call.

```ml
predicate post (st : step) (gp : gparam) (c : ctx) (c' : ctx) =
  match gp with
  | Gp'Mixer'withdraw key passcode ->
      (match c.mixer_storage.Mixer.balances[key] with
      | None -> false
      | Some hash token ->
          sha256 (concat key passcode) = hash ->
          c.mixer_balance = c'.mixer_balance + token
      end)
  | Gp'Mixer'deposit _ _ _ -> true
  | _ -> false
  end
```

But if it is known that the receiver from `Splitter.split` does not make a chain of calls,
this equation holds.
In this case, it checks this equation holds if the first sender is `Implicit0`,
which does not make a transfer to an unknown account.


```ml
scope Preambles
  use string.String (* for string concat *)
  use list.Length (* for List.length *)

  (* Gives [sha256] as an uninterpreted function *)
  val function sha256 bytes : bytes

  meta "algebraic:kept" type (bytes, nat)
  meta "algebraic:kept" type option (bytes, nat)
  meta "algebraic:kept" type option (list address)

  function sum_of : (map bytes (option (bytes, nat))) -> nat

  axiom SumE : sum_of (const None) = 0

  axiom SumI : forall m k v0 v1.
    let old_value = match m[k] with Some (_, n) -> n | None -> 0 end in
    old_value >= 0 /\ (* Should be given by hands *)
    sum_of m[k <- Some (v0, v1)] = sum_of m + v1 - old_value

  axiom SumI' : forall m k.
    let old_value = match m[k] with Some (_, n) -> n | None -> 0 end in
    sum_of m[k <- None] = sum_of m - old_value
end

scope Postambles
  (* Defines some invariants *)
  predicate addr_inv (c : ctx) =
    c.splitter_storage.Splitter.mixer_addr = Mixer.addr

  predicate storage_inv (c : ctx) =
    c.splitter_balance >= 0 /\
    sum_of c.mixer_storage.Mixer.balances <= c.mixer_balance /\
    addr_inv c

  predicate splitter_storage_inv (c : ctx) =
    c.splitter_storage.Splitter.state = None
end

scope Unknown
  predicate pre (c : ctx) =
    storage_inv c /\
    splitter_storage_inv c

  predicate post (c : ctx) (c' : ctx) =
    storage_inv c' /\
    splitter_storage_inv c'

  scope Entrypoint
    predicate default unit
  end

end

scope Mixer
  type storage [@gen_wf] = {
    balances : big_map bytes (option (bytes, nat));
  }

  predicate pre (st : step) (gp : gparam) (c : ctx) =
    storage_inv c /\
    match gp with
    | Gp'Mixer'withdraw key passcode ->
        (st.sender <> Splitter.addr -> splitter_storage_inv c) /\
        (st.sender = Splitter.addr -> st.amount = 0)
    | Gp'Mixer'deposit _ _ -> splitter_storage_inv c
    | _ -> false
    end

  predicate post (st : step) (gp : gparam) (c : ctx) (c' : ctx) =
    storage_inv c' /\
    splitter_storage_inv c' /\
    match gp with
    | Gp'Mixer'withdraw key passcode ->
        (match c.mixer_storage.Mixer.balances[key] with
        | None -> false
        | Some (hash, token) ->
            sha256 (concat key passcode) = hash ->
            c.splitter_storage.Splitter.state = Some (Cons Implicit0.addr Nil) ->
            c'.mixer_storage.Mixer.balances = c.mixer_storage.Mixer.balances[key <- None] /\
            c.mixer_balance = c'.mixer_balance + token
        end)
    | Gp'Mixer'deposit _ _ -> true
    | _ -> false
    end

  let upper_ops = 1

  scope Spec
    predicate deposit (st : step) (key : bytes) (hash : bytes) (s : storage) (ops : list operation) (s' : storage) =
      match s.balances[key] with
      | None ->
          let b = s.balances[key <- Some (hash, st.amount)] in
          s' = { s with balances = b }
      | Some (h, tokens) ->
          if h = hash then
            let t = st.amount + tokens in
            let b = s.balances[key <- Some (hash, t)] in
            s' = { s with balances = b }
          else
            false
      end /\
      ops = Nil

    predicate withdraw (st : step) (key : bytes) (passcode : bytes) (s : storage) (ops : list operation) (s' : storage) =
      let b = s.balances in
      match b[key] with
      | None -> false
      | Some (hash, token) ->
          if sha256 (concat key passcode) = hash
          then
            s' = { s with balances = b[key <- None] } /\
            ops = Cons (Xfer (Gp'Unknown'default ()) token st.sender) Nil
          else
            s' = s /\
            ops = Cons (Xfer (Gp'Unknown'default ()) 0 st.sender) Nil
      end
    
  end

end

scope Splitter
  type storage [@gen_wf] = {
    mixer_addr : address;
    state : option (list address)
  }

  predicate pre (st : step) (gp : gparam) (c : ctx) =
    storage_inv c /\
    match gp with
    | Gp'Splitter'split key passcode dests ->
        splitter_storage_inv c /\
        (st.sender = Implicit0.addr -> dests = Cons Implicit0.addr Nil)
    | Gp'Splitter'default () ->
        st.sender <> Mixer.addr -> splitter_storage_inv c
    | _ -> false
    end

  predicate post (st : step) (gp : gparam) (c : ctx) (c' : ctx) =
    storage_inv c' /\
    splitter_storage_inv c' /\
    match gp with
    | Gp'Splitter'split key passcode dests ->
        (match c.mixer_storage.Mixer.balances[key] with
        | None -> false
        | Some (hash, token) ->
            sha256 (concat key passcode) = hash ->
            st.sender = Implicit0.addr ->
            c'.mixer_storage.Mixer.balances = c.mixer_storage.Mixer.balances[key <- None] /\
            c.mixer_balance = c'.mixer_balance + token
        end)
    | Gp'Splitter'default () ->
        (c.splitter_storage.Splitter.state = Some (Cons Implicit0.addr Nil) \/
         c.splitter_storage.Splitter.state = None) ->
        (c.mixer_balance = c'.mixer_balance /\
         c.mixer_storage = c'.mixer_storage)
    | _ -> false
    end

  let upper_ops = 3

  scope Spec
    predicate split (st : step) (key : bytes) (passcode : bytes) (dests : list address) (s : storage) (ops : list operation) (s' : storage) =
      ops = Cons (Xfer (Gp'Mixer'withdraw key passcode) 0 s.mixer_addr) Nil /\
      s'.state = Some dests /\
      s.mixer_addr = s'.mixer_addr

    predicate default (st : step) (_p : unit) (s : storage) (ops : list operation) (s' : storage) =
      st.sender = s.mixer_addr /\
      match s.state with
      | None ->
          ops = Nil /\
          s' = s
      | Some dests ->
          let d = div st.amount (length dests) in
          ops = (* Extract 3 times *)
            match dests with
            | Nil -> Nil
            | Cons addr0 t ->
                Cons (Xfer (Gp'Unknown'default ()) d addr0)
                  (match dests with
                  | Nil -> Nil
                  | Cons addr1 t ->
                      Cons (Xfer (Gp'Unknown'default ()) d addr1)
                        (match dests with
                        | Nil -> Nil
                        | Cons addr2 _ -> Cons (Xfer (Gp'Unknown'default ()) d addr2) Nil
                        end)
                  end)
            end /\
          s' = { s with state = None }
      end
  end
end


scope Implicit0
  predicate pre (st : step) (gp : gparam) (c : ctx) =
    storage_inv c /\
    splitter_storage_inv c /\
    match gp with
    | Gp'Implicit0'send _ _
    | Gp'Implicit0'default () -> true
    | _ -> false
    end

  predicate post (st : step) (gp : gparam) (c : ctx) (c' : ctx) =
    storage_inv c' /\
    splitter_storage_inv c' /\
    match gp with
    | Gp'Implicit0'send key passcode ->
        (match c.mixer_storage.Mixer.balances[key] with
        | None -> false
        | Some (hash, token) ->
            sha256 (concat key passcode) = hash ->
            c'.mixer_storage.Mixer.balances[key] = None /\
            c.mixer_balance = c'.mixer_balance + token
        end)
    | Gp'Implicit0'default () ->
        c.mixer_balance = c'.mixer_balance /\
        c.mixer_storage = c'.mixer_storage
    | _ -> false
    end
  
  type storage [@gen_wf] = unit

  let upper_ops = 1

  scope Spec
    predicate send (st : step) (key : bytes) (passcode : bytes) (s : storage) (ops : list operation) (s' : storage) =
      ops = Cons (Xfer (Gp'Splitter'split key passcode (Cons st.self Nil)) 0 Splitter.addr) Nil
    
    predicate default (st : step) (_p : unit) (s : storage) (ops : list operation) (s' : storage) =
      ops = Nil
  end
end

```
