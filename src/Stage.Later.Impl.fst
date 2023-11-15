module Stage.Later.Impl

// NOTE: type definition should not be exported
type later (t: Type u#i): Type u#i = t

let extract (#t: Type) (l: later t):
  Ghost t (requires True) (ensures (fun r -> True)) =
  l

let return (#t: Type) (value: t):
  (r: later t { extract r == value }) =
  value

let combine (#t #u: Type) (fn: later (t -> u)) (value: later t): u: later u { extract u == extract fn (extract value) } =
  fn value

let bind (#t #u: Type) (value: later t) (fn: t -> later u): u: later u { extract u == extract (fn (extract value)) } =
  fn value

let (<*>) (#t #u: Type) (fn: later (t -> u)) (value: later t): u: later u { extract u == extract fn (extract value) } = fn value

let (<$>) (#t #u: Type) (fn: (t -> u)) (value: later t): u: later u { extract u == fn (extract value) } =
  fn value

let (>>=) (#t #u: Type) (value: later t) (fn: t -> later u): u: later u { extract u == extract (fn (extract value)) } = value `bind` fn

let lift1 (#t #u: Type) (fn: (t -> u)) (value: later t): later u =
  fn <$> value

let lift2 (#t #u #v: Type) (fn: (t -> u -> v)) (value1: later t) (value2: later u): later v =
  fn <$> value1 <*> value2

let lift3 (#t #u #v #w: Type) (fn: (t -> u -> v -> w)) (value1: later t) (value2: later u) (value3: later v): later w =
  fn <$> value1 <*> value2 <*> value3


let pack2 (#a #b: Type) (unp: (later a & later b)): later (a & b) =
  Mktuple2 <$> fst unp <*> snd unp

let unpack2 (#a #b: Type) (pck: later (a & b)): (later a & later b) =
  (fst <$> pck, snd <$> pck)
