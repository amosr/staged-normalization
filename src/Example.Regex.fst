(* Toy regular expression-style language *)
module Example.Regex


type regex (sym: eqtype) =
 | Eps: regex sym
 | Const: sym -> regex sym
 | Seq: regex sym -> regex sym -> regex sym
 | Alt: regex sym -> regex sym -> regex sym
 | Rpt: regex sym -> regex sym

noeq
type dfa (sym: eqtype) (state: eqtype) = {
  accept: state -> bool;
  init: state;
  transition: state -> sym -> state;
}

type const_st = | C'Empty | C'Good | C'Bad

let rec state_of_regex (#sym: eqtype) (rx: regex sym): eqtype =
  match rx with
  | Eps   -> bool
  | Const _ -> const_st
  | Seq a b -> (state_of_regex a & state_of_regex b)
  | Alt a b -> (state_of_regex a & state_of_regex b)
  | Rpt a   -> state_of_regex a

let rec dfa_of_regex (#sym: eqtype) (rx: regex sym): dfa sym (state_of_regex rx) =
  match rx with
  | Eps -> { accept = (fun st -> st); init = true; transition = (fun _ _ -> false); }
  | Const expect -> {
    accept = (fun st -> st = C'Good);
    init = C'Empty;
    transition = (fun st sy ->
      if st = C'Empty && sy = expect then C'Good else C'Bad);
  }
  | Seq a b ->
    let a' = dfa_of_regex a in
    let b' = dfa_of_regex b in
    {
      accept = (fun (sta, stb) -> a'.accept sta && b'.accept stb);
      init = (a'.init, b'.init);
      transition = (fun (sta, stb) sy ->
        // This translation is not totally correct: it is too greedy and stops trying the lhs on the first match.
        // With this translation, `(A|)B` will fail on input AB
        if a'.accept sta
        then (sta, b'.transition stb sy)
        else (a'.transition sta sy, b'.init)
      );
    }
  | Alt a b ->
    let a' = dfa_of_regex a in
    let b' = dfa_of_regex b in
    {
      accept = (fun (sta, stb) -> a'.accept sta || b'.accept stb);
      init = (a'.init, b'.init);
      transition = (fun (sta, stb) sy ->
        (a'.transition sta sy, b'.transition stb sy)
      );
    }
  | Rpt a ->
    let a' = dfa_of_regex a in
    {
      accept = (fun sta -> sta = a'.init );
      init = a'.init;
      transition = (fun st sy ->
        // Again, too greedy
        let st' = a'.transition st sy in
        if a'.accept st'
        then a'.init
        else st'
      );
    }


let eg1 = Rpt (Const 1 `Seq` Const 2)

module Tac = FStar.Tactics

[@@Tac.postprocess_with(fun () -> Tac.norm [delta; nbe; zeta; iota; primops]; Tac.dump "OK"; Tac.trefl ()) ]
let eg1_dfa = dfa_of_regex eg1
