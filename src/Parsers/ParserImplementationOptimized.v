(** * Implementation of simply-typed interface of the parser *)
Require Export Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.BaseTypes Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.BooleanRecognizerOptimized.
Require Import Fiat.Parsers.BooleanRecognizerEquality.
Require Import Fiat.Parsers.ParserImplementation.
Require Import Fiat.Parsers.ContextFreeGrammar.Notations.
Require Import Fiat.Parsers.ContextFreeGrammar.Transfer.
Require Import Fiat.Parsers.ContextFreeGrammar.TransferProperties.
Require Import Fiat.Parsers.ContextFreeGrammar.Valid.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.

Set Implicit Arguments.

Local Open Scope list_scope.

Definition transfer_parser_keep_string {Char G} {HSLM HSL}
           (old : @Parser Char G HSLM HSL)
           (new : @String Char HSLM -> bool)
           (H : forall s, new s = has_parse old s)
: @Parser Char G HSLM HSL.
Proof.
  refine {| has_parse := new |};
  abstract (
      intros;
      rewrite H in *;
        first [ apply (has_parse_sound old); assumption
              | eapply (has_parse_complete old); eassumption ]
    ).
Defined.

Arguments transfer_parser_keep_string {_ _ _ _} _ _ _.

Definition transfer_parser {Char G} {HSLM1 HSLM2 HSL1 HSL2}
           (old : @Parser Char G HSLM1 HSL1)
           (make_string : @String Char HSLM2 -> @String Char HSLM1)
           (new : @String Char HSLM2 -> bool)
           (H : forall s, new s = has_parse old (make_string s))
           (R : @String Char HSLM1 -> @String Char HSLM2 -> Prop)
           (R_make : forall str, R (make_string str) str)
           (R_respectful : transfer_respectful R)
           (R_flip_respectful : transfer_respectful (Basics.flip R))
: @Parser Char G HSLM2 HSL2.
Proof.
  refine {| has_parse := new |}.
  { abstract (
        intros str H';
        rewrite H in H';
        refine (@transfer_parse_of_item Char _ _ _ _ G R R_respectful (make_string str) str (NonTerminal G) (R_make str) _);
        apply (has_parse_sound old); assumption
      ). }
  { abstract (
        intros str p;
        rewrite H;
        pose (@transfer_parse_of_item Char _ _ _ _ G (Basics.flip R) R_flip_respectful str (make_string str) (NonTerminal G) (R_make str) p) as p';
        apply (has_parse_complete old p'); subst p';
        exact (transfer_forall_parse_of_item _ H')
      ). }
Defined.

Arguments transfer_parser {_ _ _ _ _ _} _ _ _ _ _ _ _ _.

Section implementation.
  Context {ls : list (String.string * productions Ascii.ascii)}.
  Local Notation G := (list_to_grammar nil ls) (only parsing).
  Context (Hvalid : is_true (grammar_rvalid G)).
  Context (splitter : Splitter G).
  Context {string_like_min_lite : StringLikeMin Ascii.ascii}
          {string_like_lite : @StringLike Ascii.ascii string_like_min_lite}
          split_string_for_production_lite
          (HSLPr : @StringLikeProj Ascii.ascii splitter string_like_lite (parser_data splitter) split_string_for_production_lite).
  Context (stringlike_stringlikemin : StringLikeMin Ascii.ascii)
          (stringlike_stringlike : @StringLike Ascii.ascii stringlike_stringlikemin)
          (make_string : @String _ stringlike_stringlike -> @String _ splitter)
          (R : @String _ splitter -> @String _ stringlike_stringlike -> Prop)
          (R_make : forall str, R (make_string str) str)
          (R_respectful : transfer_respectful R)
          (R_flip_respectful : transfer_respectful (Basics.flip R)).

  Local Instance pdata : @boolean_parser_dataT Ascii.ascii string_like_lite
    := @data' _ splitter string_like_lite (parser_data splitter) split_string_for_production_lite.
  Local Instance pdata' : @boolean_parser_dataT Ascii.ascii splitter
    := parser_data splitter.

  Local Arguments Compare_dec.leb !_ !_.

  Definition parser : Parser G stringlike_stringlike.
  Proof.
    apply grammar_rvalid_correct in Hvalid.
    let impl0 := constr:(fun str => (parse_nonterminal_opt (ls := ls) (splitdata := pdata) (proj (make_string str)) (Start_symbol G))) in
    let impl := (eval simpl in (fun str => proj1_sig (impl0 str))) in
    let implH := constr:(fun str => proj2_sig (impl0 str)) in
    let impl' := (eval cbv beta iota zeta delta [RDPList.rdp_list_remove_nonterminal RDPList.rdp_list_initial_nonterminals_data RDPList.rdp_list_nonterminals_listT RDPList.rdp_list_is_valid_nonterminal RDPList.rdp_list_ntl_wf RDPList.rdp_list_nonterminals_listT_R RDPList.rdp_list_of_nonterminal RDPList.rdp_list_to_nonterminal Carriers.default_nonterminal_carrierT Carriers.some_invalid_nonterminal Carriers.default_to_production Carriers.default_to_nonterminal] in impl) in
    let impl := (eval simpl in impl') in
    refine (transfer_parser
              (HSL1 := splitter) (HSL2 := stringlike_stringlike)
              (parser splitter Hvalid) make_string
              impl
              (fun str => eq_trans
                            (implH str)
                            (@parse_nonterminal_proj _ splitter string_like_lite G pdata' _ _ HSLPr _ _))
              R R_make _ _).
  Defined.

End implementation.
