contract DAO
{
  type poll =
    { proposal : lambda unit (list operation),
      author : address,
      votingStartBlock : nat
      votingEndBlock : nat,
      yayVotes : nat,
      nayVotes : nat,
      abstainVotes : nat,
      totalVotes : nat,
      voters : set address }
  poll : option poll
  tokenAddress : address (* FA2 *)
  escrowAddress : address
  escrowAmount : nat (* poll のための deposit *)
  voteLength : nat
  percentageForSuperMajority : nat
  (* quorum : nat (* 最低有効投票数 *) *)
  voteState : option (nat * address)

  DAO()
  {
    escrowAmount = 100
    voteLength = 180
    percentageForSuperMajority = 50
  }

  entrypoint propose (proposal)
  {
    assert(poll == None)
    (* endVote を呼ばせるためのインセンティブ && proposal を出せる資格? *)
    transfer(tokenAddress%transfer, 0, {from = sender, txs = [{to_ = self_address, amount = escrowAmount, token_id=0}]})
    poll = Some
      { proposal, author = sender
        votingStartBlock=level, votingEndBlock = level+voteLength,
        yayVotes=0, nayVotes=0, abstainVotes=0, totalVotes=0,
        voters=empty_set}
  }
  entrypoint endVote ()
  {
    assert(is_some(poll))
    let Some p = poll in
    assert(p.votingEndBlock < level)
    totalOpinionatedVotes = p.yayVotes + p.nayVotes
    (* yayVotesNeededForEscrowReturn = totalOpinionatedVotes * minYayVotesPercentForEscrowReturn / 100 (* 一定の支持を得られなければボッシュート *) *)*)
    yayVotesNeededForSuperMajority = totalOpinionatedVotes * percentageForSuperMajority / 100
    transfer(tokenAddress%transfer, 0, {from = self_address, txs=[{to_=p.sender, amount=escrowAmount, token_id=0}]})
    if(yayVotesNeededForSuperMajority <= yayVotes (* && quorum <= p.totalVotes *))
    {
      p.proposal ()
    }
  }
  entrypoint vote (voteValue) (* voteValue... 0 for yay, 1 for nay, 2 for abstain *)
  {
    assert(voteState == None)
    voteState = Some { voteValue, address=sender }
    transfer((* escrowAddress%getBalance *) tokenAddress%getBalance, 0, { address, callback=voteCallback })
  }
  entrypoint voteCallback(balance)
  {
    assert (is_some (voteState))
    assert (is_some (p))
    let Some vote = voteState in
    let Some p = poll in
    assert (level < p.votingEndBlock)
    if (p.voters.mem(vote.address)) assert false (* 投票済み *)
    p.voters.add(vote.address)
    p.totalVotes += balance
    if (vote.voteValue == 0) p.yayVotes += balance
    else if (vote.voteValue == 1) p.nayVotes += balance
    else if (vote.voteValue == 2) p.abstainVotes += balance
    else assert false
    poll = Some p
    voteState = None
  }

}

(* FA12 の sDAO token? *)
contract Token
{
  balances : map (address) nat
  admin : address
  approvals : map address (map address nat)
  entrypoint transfer(from, to_, value)
  {
    assert(sender == admin || from == sender || approvals[from][sender] >= value)
    assert(balances[from] >= value)
    balances[from] -= value
    balances[to_] += value
    if(sender != from && sender != admin)
    {
      approvals[from][sender] -= value
    }
  }
  entrypoint approve(spender, value)
  {
    assert(value == 0 || approvals[sender][spender] == 0) (* 0 -> x か x -> 0 しか許さない (前なんかで見た) *)
    approvals[sender][spender] = value
  }
  (* violate FA1.2 (it uses view) *)
  entrypoint getBalance(address, callback)
  {
    transfer(callback, 0, balances[address])
  }
  entrypoint mint(address, value)
  {
    assert(sender == admin)
    balances[address] += value
  }
}

(* https://guide.salsadao.xyz/governance-voting
   sDAO locker にtokenを預けると投票券が得られる (flash loan を防ぐためらしい？)
   https://better-call.dev/mainnet/KT1UDqAi1Qt2S6RRkrrq6Ba1tawZsTqTF4aj/operations *)
contract Escrow
{
  balances : map address nat

  view getBalance(address, callback)
  {
    return balance[address]
  }

  entrypoint escrow (value)
  {
    transfer(tokenAdminAddress%transfer, 0, {from=sender, txs=[{amount=value, to_=self_address, token_id=0}]})
    balances[sender] += value
  }
  entrypoint release (value)
  {
    assert(value <= balances[sender])
    transfer(tokenAdminAddress%transfer, 0, {from=self_address, txs=[{amount=value, to_=sender, token_id=0}]})
    balances[sender] -= value
  }
}
