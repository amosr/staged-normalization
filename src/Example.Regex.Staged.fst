module Example.Regex.Staged

open Example.Regex
module ER = Example.Regex

// module L = Stage.Later
module L = Stage.Later.Impl

noeq
type dfa' (sym: eqtype) (state: eqtype) = {
  accept: L.later state -> L.later bool;
  init: state;
  transition: L.later state -> L.later sym -> L.later state;
}

let rec dfa_of_regex (#sym: eqtype) (rx: regex sym): dfa' sym (state_of_regex rx) =
  let open L in
  match rx with
  | Eps -> {
    accept = (fun st -> st);
    init = true;
    transition = (fun _ _ -> return false);
  }
  | Const expect -> {
    accept = lift1 (fun st -> st = C'Good);
    init = C'Empty;
    transition = lift2 (fun st sy ->
      if st = C'Empty && sy = expect then C'Good else C'Bad);
  }
  | Seq a b ->
    let a' = dfa_of_regex a in
    let b' = dfa_of_regex b in
    let accept = (fun st ->
      let (sta, stb) = unpack2 st in
      lift2 (&&) (a'.accept sta) (b'.accept stb)) in
    {
      accept = accept;
      init = (a'.init, b'.init);
      transition = (fun st sy ->
        let (sta, stb) = unpack2 st in
        let accept: later bool                = a'.accept     sta    in
        let sta' (): later (state_of_regex a) = a'.transition sta sy in
        let stb' (): later (state_of_regex b) = b'.transition stb sy in
        (accept >>= (fun accept -> if accept then pack2 (sta, stb' ()) else pack2 (sta' (), return b'.init)))
      );
    }
  | Alt a b ->
    let a' = dfa_of_regex a in
    let b' = dfa_of_regex b in
    let accept = (fun st ->
      let (sta, stb) = unpack2 st in
      lift2 (fun x y -> x || y) (a'.accept sta) (b'.accept stb)
    ) in
    {
      accept = accept;
      init = (a'.init, b'.init);
      transition = (fun st sy ->
        let (sta, stb) = unpack2 st in
        pack2 (a'.transition sta sy, b'.transition stb sy)
      );
    }
  | Rpt a ->
    let a' = dfa_of_regex a in
    let open L in
    {
      accept = L.lift1 (fun sta -> sta = a'.init );
      init = a'.init;
      transition = (fun st sy ->
        let st'    = a'.transition st sy in
        let accept = a'.accept st' in
        (fun accept st' -> if accept then a'.init else st') <$> accept <*> st'
      );
    }

(* Some relatively simple proofs to show that the laters don't get in the way too much *)
let rec lemma_init_equiv (#sym: eqtype) (rx: regex sym):
  Lemma ((dfa_of_regex rx).init = (ER.dfa_of_regex rx).init) =
  match rx with
  | Eps | Const _ -> ()
  | Seq a b | Alt a b -> lemma_init_equiv a; lemma_init_equiv b
  | Rpt a -> lemma_init_equiv a

let rec lemma_accept_equiv (#sym: eqtype) (rx: regex sym) (st: state_of_regex rx):
  Lemma (L.extract ((dfa_of_regex rx).accept (L.return st)) = (ER.dfa_of_regex rx).accept st) =
  match rx with
  | Eps | Const _ -> ()
  | Seq a b ->
    let (sta, stb): (state_of_regex a & state_of_regex b) = st in
    lemma_accept_equiv a sta;
    lemma_accept_equiv b stb
  | Alt a b ->
    let (sta, stb): (state_of_regex a & state_of_regex b) = st in
    lemma_accept_equiv a sta;
    lemma_accept_equiv b stb
  | Rpt a ->
    let sta: (state_of_regex a) = coerce_eq () st in
    lemma_init_equiv a;
    lemma_accept_equiv a sta

let rec lemma_transition_equiv (#sym: eqtype) (rx: regex sym) (st: state_of_regex rx) (sy: sym):
  Lemma (L.extract ((dfa_of_regex rx).transition (L.return st) (L.return sy)) = (ER.dfa_of_regex rx).transition st sy) =
  match rx with
  | Eps | Const _ -> ()
  | Seq a b ->
    let (sta, stb): (state_of_regex a & state_of_regex b) = st in
    lemma_accept_equiv a sta;
    lemma_init_equiv b;
    lemma_transition_equiv a sta sy;
    lemma_transition_equiv b stb sy
  | Alt a b ->
    let (sta, stb): (state_of_regex a & state_of_regex b) = st in
    lemma_transition_equiv a sta sy;
    lemma_transition_equiv b stb sy
  | Rpt a ->
    let sta: (state_of_regex a) = coerce_eq () st in
    let staged = dfa_of_regex a in
    let sta' = staged.transition sta sy in
    lemma_init_equiv a;
    lemma_transition_equiv a sta sy;
    lemma_accept_equiv a sta'

let eg1 = Rpt (Const 1 `Seq` Const 2)

(* Ideal hand-specialised *)
let eg1_dfa_manual: dfa int (state_of_regex eg1) =
  let st = (const_st & const_st) in
  {
  accept = (fun st -> st = (C'Empty, C'Empty));
  init = (C'Empty, C'Empty);
  transition = (fun st sy ->
    // dfa_of_regex:Rpt:transition:st'
    let rpt_st' =
      // dfa_of_regex:Seq:transition st sy
      let (sta, stb) = st in
      // dfa_of_regex:Seq:transition:accept = dfa_of_regex:Const:accept sta
      let accept = (sta = C'Good) in
      // dfa_of_regex:Seq:transition:sta' () = dfa_of_regex:Const:transition sta sy
      let sta' () = (if sta = C'Empty && sy = 1 then C'Good else C'Bad) in
      // dfa_of_regex:Seq:transition:sta' () = dfa_of_regex:Const:transition sta sy
      let stb' () = (if stb = C'Empty && sy = 2 then C'Good else C'Bad) in
      if accept then (sta, stb' ()) else (sta' (), C'Empty)
    in
    // dfa_of_regex:Rpt:transition:accept
    let rpt_accept =
      // dfa_of_regex:Seq:accept
      let (sta, stb) = rpt_st' in
      // lift2 (&&) (dfa_of_regex:Const:accept sta) (dfa_of_regex:Const:accept stb)
      sta = C'Good && stb = C'Good
    in
    if rpt_accept then (C'Empty, C'Empty) else rpt_st'
  );
}



module Tac = FStar.Tactics

[@@Tac.postprocess_with(fun () -> Tac.norm [delta_namespace ["FStar"; "Example"]; nbe; zeta; iota; primops]; Tac.dump "OK"; Tac.trefl ()) ]
inline_for_extraction
let eg1_dfa1 = dfa_of_regex eg1

[@@Tac.postprocess_with(fun () -> Tac.norm [delta_namespace ["Stage.Later"]; delta_qualifier ["inline_for_extraction"]; nbe; zeta; iota; primops]; Tac.dump "OK"; Tac.trefl ()) ]
let eg1_dfa2 = eg1_dfa1
