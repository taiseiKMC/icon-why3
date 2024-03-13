- ADTをバイナリに変換する機構の正しさ
- 検証例 https://github.com/kevinelliott/awesome-tezos?tab=readme-ov-file
  - dao
    - tezos だと SalsaDAO?
  - stablecoin
    - 担保付き債務ポジション（CDP = Collateralized Debt Position）
- digital asset の通貨を介しない swap


# 課題？
- Michelson と tzw の連携
  - tzw に書いた条件式を Michelson コードが満たす保証はない
- Michelson のプリミティブとの対応
  - ゼロ知識証明(sapling), ticket, timelock は？
  - block_level は定義されている？
    - step に含めたほうが良い?
  - now, chain_id, voting_power, total_voting_power?
  - hash関数群, sig, implicit_account for key_hash?
- ない型がある
  - lambda 書けなくない？
  - bytes, big_map, set
- DONE: operation を引数の型に使えない？
  - type operation より前に定義されている gparam が operation に依存してしまうのが原因  
  - `type operation` -> `with opration` で解決
- `scope DAO` の balance を参照する際, `dAO_balance` になり奇妙
- view の呼び出し、どうする?
- 引数に`contract`を渡すとき, 引数の仕様が記述できなくないか？
  - `gparam` が `contract` を受け取る場合、例えばどう `contract` が `DAO.vote` であると記述できる？
  - 今 `type contract 'a = int` になっている
- DONE: `use export string.String` と `use export list.Length` をすると `length` が conflict する
  - `export` を消すと `Symbol length is already defined in the current scope` は出なくなるが, 片方使えなくなってそう?
  - 衝突を解決する or shadowing した方を参照する方法はあるんだろうか
  - `Length.length`, `String.length` でいけました
- これ, operation list が本当に list になる場合の証明, 書けなさそう
  - upper_ops の制限もあるし, なぜか証明が死ぬ
- contract.addr が使えたり使えなかったり...?
  - Spec だと使えないかもしれない
- 3 以上の tuple に対して wf が生成されなくなってる？ `unbound function or predicate symbol 'is__tuple3_wf`
- 違うコントラクトを定義しても, (API が同じに近いと? 詳しい条件は分からないが) addr が同じ可能性があると判定される...

# チラシの裏
- 対応していない構文含むtzwのエラーの場所がわからない
  - これは scope 内に storage 以外の型を含むのがエラーの原因の例
  ```
  70    scope DAO
  :
  100     type hoge = unit
  :
  200   end

  Fatal error: exception File "examples/dao.tzw", line 70, characters 0-9:
  anomaly: Failure("unexpected decl")
  ```
  - pair の型を `(a, b)` と書くところを勘違いして `a * b` と書いても同じエラー

- storage 以外の type 書けない?
  - option (nat, nat, nat, ....) みたいな型だと tuple にするのしんどいので,
    storage にレコードを許しているなら他の型のレコード定義も許してほしい
    - 分解するときも大変だし

- `{ s with hoge = hoge }` は書けるけれど `{ s with hoge }` はだめ
- `match` `with` 構文は `end` が要る
- list の `[]` は書けない...
- boolean の True と true は等価なんだろうか
- 割り算あるんかな
- sender を使うために step の tuple を分解するの面倒だなーと思ったら `sender : step -> address` が preamble にあった
- map の default 値, 何?
  - `map 'a 'b = 'a -> 'b` なんか
- `voters[addr <- True]` これきもい
- `inv_pre` と `inv_post`, 何？
- mixer とか zk を使ったコントラクト例として良さそう
  - tezos の mixer, ある？
  - マルチコントラクトの例ではないな...
- list の length とか map とかを使うには preamble に use を書かないといけない
  - API, どこ？ https://www.why3.org/stdlib/string.html
- わかってはいたけれど、debug むずい
- `spec c c' -> post c c'` の条件が直接は生成されていないけれど、大丈夫なんだろうか (反例はまだ無い)
  - いや, callback する場合は post が成り立たないからこれでいいのか
- get counterexamples をしても, 生成されたコードのlocation情報がほぼほぼダミーなので, model の情報に位置情報がろくに乗ってなくて全くわからん
- map の sum の axiom に関して, 値が nat とかのときに自動で `>=0` の条件を導出してほしいなー
  - `old_value >= 0`
- upper_ops の回数だけ list を展開するマクロみたいなのがあると捗る?
- address が smartcontract でないことを条件で記述できると強いことが言えて嬉しいかもしれない
- implicit account を代表して 1 つコントラクトを定義して, 挙動をシミュレート? できないか試しているが,
  source を定義したコントラクトとすることはできないしで条件を記述できなさそうな

# DAO
- TEZOS の DAO 実装 https://github.com/GeniusContracts/murmuration/blob/main/docs/token.md


- DAO
  - propose: Propose a new proposal, escrowing tokens. The DAO must have an approval for the amount of tokens to escrow.
  - endVoting: Evaluate the outcome of a poll, if voting has ended. Adjusts quorum, decides where escrow is sent, and optionally advances the proposal to a timelock.
  - vote: Vote for a proposal from the sender's address.
  - voteCallback: A private callback that returns a voter's token balance.
  - executeTimelock: Executes a proposal in the timelock, if the timelock period has passed. Fails if the sender is not the proposal's author, or if the timelock period is not elapsed.
  - cancelTimelock: Removes an item from the timelock, if the cancellation period has passed. Fails if the cancellation period is not elapsed.
  - setParameters: Sets new values for governance parameters. May only be called by the DAO.

- Token
  - updateContractMetadata: Updates the TZIP-16 contract metadata. May only be called by the administrator.
  - updateTokenMetadata: Updates the TZIP-7 token metadata. May only be called by the administrator.
  - getPriorBalance: Given a block height, an address, and a callback, this entrypoint will determine the given address' balance at the block height and call the callback with the input parameters and the result.
  - disableMinting: Disables minting by setting the mintingDisabled field in storage to True.
  - mint: Mints tokens, unless mintingDisabled is set to True.
  - setAdministrator: Takes an option(address) rather than address as a parameter so that the administrator functions can be locked.
