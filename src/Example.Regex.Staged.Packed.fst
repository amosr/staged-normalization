(* Toy automaton language *)
module Example.Regex.Staged.Packed

open Example.Regex

// module L = Stage.Later
module L = Stage.Later.Impl

noeq
type dfa' (sym: eqtype) (state: Type) = {
  accept: state -> L.later bool;
  init: state;
  transition: state -> L.later sym -> state;
}

let rec state_of_regex' (#sym: eqtype) (rx: regex sym): Type =
  match rx with
  | Eps   -> L.later bool
  | Const _ -> L.later const_st
  | Seq a b -> (state_of_regex' a & state_of_regex' b)
  | Alt a b -> (state_of_regex' a & state_of_regex' b)
  | Rpt a   -> state_of_regex' a

let rec pack (#sym: eqtype) (rx: regex sym) (unp: state_of_regex' rx): L.later (state_of_regex rx) =
  let open L in
  match rx with
  | Eps -> unp
  | Const _ -> unp
  | Seq a b ->
    let (un1, un2) = unp <: state_of_regex' (Seq a b) in
    Mktuple2 <$> pack a un1 <*> pack b un2
  | Alt a b ->
    let (un1, un2) = unp <: state_of_regex' (Alt a b) in
    Mktuple2 <$> pack a un1 <*> pack b un2
  | Rpt a ->
    let un1: state_of_regex' a = coerce_eq () unp in
    coerce_eq () (pack a un1)

let rec unpack (#sym: eqtype) (rx: regex sym) (pck: L.later (state_of_regex rx)): state_of_regex' rx =
  let open L in
  match rx with
  | Eps -> pck
  | Const _ -> pck
  | Seq a b ->
    let pck: L.later (state_of_regex a & state_of_regex b) = pck in
    (unpack a (fst <$> pck), unpack b (snd <$> pck))
  | Alt a b ->
    let pck: L.later (state_of_regex a & state_of_regex b) = pck in
    (unpack a (fst <$> pck), unpack b (snd <$> pck))
  | Rpt a ->
    let pck: L.later (state_of_regex a) = coerce_eq () pck in
    let unp: state_of_regex' a = unpack a pck in
    coerce_eq () unp

// let rec splat_state (#sym #r: eqtype) (#rx: regex sym) (fn: (state_of_regex rx -> r)) (st: state_of_regex rx):
//   later r

let rec dfa_of_regex (#sym: eqtype) (rx: regex sym): dfa' sym (state_of_regex' rx) =
  match rx with
  | Eps -> {
    accept = (fun st -> st);
    init = L.return true;
    transition = (fun _ _ -> L.return false);
  }
  | Const expect -> {
    accept = L.lift1 (fun st -> st = C'Good);
    init = L.return C'Empty;
    transition = L.lift2 (fun st sy ->
      match st with
      | C'Empty ->
        if sy = expect
        then C'Good
        else C'Bad
      | C'Good -> C'Bad
      | C'Bad -> C'Bad);
  }
  | Seq a b ->
    let a' = dfa_of_regex a in
    let b' = dfa_of_regex b in
    let open L in
    let accept = (fun (sta, stb) -> lift2 (&&) (a'.accept sta) (b'.accept stb)) in
    {
      accept = accept;
      init = (a'.init, b'.init) <: state_of_regex' rx;
      transition = (fun (sta, stb) sy ->
        let accept: later bool      = a'.accept     sta    in
        let sta': state_of_regex' a = a'.transition sta sy in
        let stb': state_of_regex' b = b'.transition stb sy in
        // not correct, very greedy seq
        // a'.accept sta >>= (fun accept -> if accept then (sta, stb') else (sta', b'.init))
        unpack rx (a'.accept sta >>= (fun accept -> if accept then pack rx (sta, stb') else pack rx (sta', b'.init)))
        // admit () <: state_of_regex' rx
      );
    }
  | Alt a b -> admit ()
    // let a' = dfa_of_regex a in
    // let b' = dfa_of_regex b in
    // {
    //   accept = (fun (sta, stb) -> a'.accept sta || b'.accept stb);
    //   init = (a'.init, b'.init);
    //   transition = (fun (sta, stb) sy ->
    //     (a'.transition sta sy, b'.transition stb sy)
    //   );
    // }
  | Rpt a ->
    let a' = dfa_of_regex a in
    let open L in
    {
      accept = (fun sta -> (=) <$> pack a sta <*> pack a a'.init );
      init = a'.init;
      transition = (fun st sy ->
        // very greedy seq
        let st' = a'.transition st sy in
        unpack a ((fun accept st_init st' -> if accept then st_init else st') <$> a'.accept st <*> pack a a'.init <*> pack a st')
      );
    }


let eg1 = Rpt (Const 1 `Seq` Const 2 `Seq` Const 3)

module Tac = FStar.Tactics

[@@Tac.postprocess_with(fun () -> Tac.norm [delta_namespace ["FStar"; "Example"]; nbe; zeta; iota; primops]; Tac.dump "OK"; Tac.trefl ()) ]
inline_for_extraction
let eg1_dfa1 = dfa_of_regex eg1

[@@Tac.postprocess_with(fun () -> Tac.norm [delta_namespace ["Stage.Later"]; delta_qualifier ["inline_for_extraction"]; nbe; zeta; iota; primops]; Tac.dump "OK"; Tac.trefl ()) ]
let eg1_dfa2 = eg1_dfa1
