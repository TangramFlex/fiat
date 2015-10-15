Require Fiat.Parsers.BooleanRecognizerOptimized.
Require Fiat.Parsers.ParserInterface Fiat.Parsers.ParserFromParserADT.
Require Import Fiat.Parsers.ContextFreeGrammarNotations.

Global Arguments ilist.ith _ _ _ _ _ !_ / .

Declare Reduction splitter_red0 := cbv beta iota zeta delta [ilist.icons BuildComputationalADT.BuildcADT ilist.inil BuildComputationalADT.cConsBody BuildComputationalADT.cMethBody].

Ltac splitter_red term :=
  let term0 := (eval simpl in term) in
  let term1 := (eval splitter_red0 in term0) in
  let term2 := (eval simpl in term1) in
  let term3 := (eval splitter_red0 in term2) in
  constr:term3.

Declare Reduction parser_red0 := cbv beta iota zeta delta [list_to_grammar item_ascii_cons item_of_char list_to_productions BooleanRecognizerOptimized.str_carrier_default projT1 projT2 proj1_sig proj2_sig].
Declare Reduction parser_red1 := simpl List.hd.
Declare Reduction parser_red2 := simpl List.fold_right.
Declare Reduction parser_red3 := simpl List.map.
Declare Reduction parser_red4 := cbv beta iota zeta delta [ParserInterface.has_parse ParserFromParserADT.parser projT1 projT2 ComputationalADT.pcMethods ComputationalADT.pcConstructors ilist.ith ilist.ith_body VectorFacts.Vector_caseS' Vector.caseS ilist.ilist_hd ilist.ilist_tl ilist.prim_fst ilist.prim_snd BooleanRecognizerOptimized.of_string BooleanRecognizerOptimized.to_string].
Declare Reduction parser_red5 := simpl List.hd.
Declare Reduction parser_red6 := simpl List.map.
Declare Reduction parser_red7 := simpl @fst.
Declare Reduction parser_red8 := simpl @snd.
Declare Reduction parser_red9 := simpl List.length.
Declare Reduction parser_red10 := simpl List.fold_right.

Ltac parser_red term :=
  let term := match term with
                | context[ParserFromParserADT.parser ?splitter] => (eval unfold splitter in term)
                | _ => constr:term
              end in
  let term := (eval parser_red0 in term) in
  let term := (eval parser_red1 in term) in
  let term := (eval parser_red2 in term) in
  let term := (eval parser_red3 in term) in
  let term := (eval parser_red4 in term) in
  let term := (eval parser_red5 in term) in
  let term := (eval parser_red6 in term) in
  let term := (eval parser_red7 in term) in
  let term := (eval parser_red8 in term) in
  let term := (eval parser_red9 in term) in
  let term := (eval parser_red10 in term) in
  constr:term.

Ltac make_parser splitter :=
  idtac;
  let str := match goal with str : String.string |- _ => constr:str end in
  let b := constr:(ParserInterface.has_parse (ParserFromParserADT.parser splitter) str) in
  let b' := parser_red b in
  exact b'.