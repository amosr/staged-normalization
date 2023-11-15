module Stage.Later

new val later (t: Type u#i): Type u#i

val extract (#t: Type) (l: later t):
  Ghost t (requires True) (ensures (fun r -> True))

val return (#t: Type) (value: t):
  Pure (later t) (requires True) (ensures (fun r -> extract r == value))

val combine (#t #u: Type) (fn: later (t -> u)) (value: later t): u: later u { extract u == extract fn (extract value) }

val bind (#t #u: Type) (value: later t) (fn: t -> later u): u: later u { extract u == extract (fn (extract value)) }

// val lemma_expose_later   (t: Type u#i): Lemma (later t == t)
// val lemma_expose_return  (t: Type u#i) (v: t): Lemma (return v == v)
// val lemma_expose_combine (t: Type u#i) (v: t): Lemma (return v == v)


let (<*>) (#t #u: Type) (fn: later (t -> u)) (value: later t): u: later u { extract u == extract fn (extract value) } = fn `combine` value

let (<$>) (#t #u: Type) (fn: (t -> u)) (value: later t): u: later u { extract u == fn (extract value) } =
  return fn <*> value

let (>>=) (#t #u: Type) (value: later t) (fn: t -> later u): u: later u { extract u == extract (fn (extract value)) } = value `bind` fn

// val (<*>) (#t #u: Type) (fn: later (t -> u)) (value: later t): u: later u { extract u == extract fn (extract value) }

// val (<$>) (#t #u: Type) (fn: (t -> u)) (value: later t): u: later u { extract u == fn (extract value) }

let lift1 (#t #u: Type) (fn: (t -> u)) (value: later t): later u =
  fn <$> value

let lift2 (#t #u #v: Type) (fn: (t -> u -> v)) (value1: later t) (value2: later u): later v =
  fn <$> value1 <*> value2

let lift3 (#t #u #v #w: Type) (fn: (t -> u -> v -> w)) (value1: later t) (value2: later u) (value3: later v): later w =
  fn <$> value1 <*> value2 <*> value3
