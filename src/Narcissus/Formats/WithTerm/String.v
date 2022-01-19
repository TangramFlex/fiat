Require Import Coq.Strings.String.
Require Import
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.EquivFormat
        Fiat.Narcissus.Formats.Base.FMapFormat
        Fiat.Narcissus.Formats.Base.SequenceFormat
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Formats.Delimiter
        Fiat.Narcissus.Formats.AsciiOpt.

Section String.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid B}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  Definition decode_string_with_term
           (code: string)
           (b : B) (cd : CacheDecode)
    : option (string * B * CacheDecode) := 
    (Fix well_founded_lt_b
           (fun _ => CacheDecode -> option (string * B * CacheDecode))
      (fun b rec cd =>
     `(term_code, b', cd') <- decode_string (String.length code) b cd;
      (* (peekD (T := string) cd) *)
      If String.eqb code term_code Then
        Some (EmptyString, b', cd')
      Else
        (`(a, b1, e1) <- Decode_w_Measure_lt decode_ascii b cd ltac:(exact ascii_decode_lt);
        (`(xs, b2, e2) <- rec _ (proj2_sig b1) e1;
        Some (String a xs, b2, e2)))) b cd).


  Instance Equivalence_ S T : Equivalence (EquivFormat (S := S) (T := T)).
  Proof.
    constructor; 
    red; 
    [ apply EquivFormat_reflexive |
      apply EquivFormat_sym |
      apply EquivFormat_trans
    ].
  Qed.

  Instance Symmetric_ S T : Symmetric (EquivFormat (S := S) (T := T)).
  Proof.
    red; auto.
    intros.
    symmetry.
    auto.
  Qed.

  Add Parametric Morphism S T store M vP vP' decode P
    : (fun format => CorrectDecoder (S := S)
                    (T := T) (store := store) M vP vP' eq format decode P format) with
        signature (@EquivFormat S T store) ==>
                                           iff as cd_morph.
  Proof using Type.
    intros.
    pose proof format_decode_correct_EquivFormatAndView_Proper.
    do 2 red in H0.
    simpl in H0.
    unfold impl in H0.
    split.
    intros.
    unfold flip in H0.
    apply EquivFormat_sym in H.
    eapply H0 in H; eauto.
    intros.
    eapply H0 in H; eauto.
  Qed.

  Theorem string_decode_with_term_correct
          {P : CacheDecode -> Prop}
          (close : string)
    : cache_inv_Property P
    (fun P0 : CacheDecode -> Prop =>
       forall (b : nat) (cd : CacheDecode), P0 cd -> P0 (addD cd b)) -> 
    CorrectDecoder monoid
                   (* This needs to be updated *)                                   
                   (fun s => close <> "")%string
                   (fun s => close <> "")%string
                   eq
                   (format_with_term format_string close)
                   (decode_string_with_term close)
                   P
                   (format_with_term format_string close).
  Proof.
    intros cach_inv.
    split.
    { intros env env' xenv s s' ext ? Eeq Ppred Penc.
      generalize dependent env.
      revert env' xenv s' env_OK.
      induction s.
      { unfold id in *; intros.
        unfold format_with_term in Penc.
        unfold "++" in Penc.
        unfold compose in Penc.
        simpl in Penc.
        unfold Bind2 in Penc.
        apply Bind_inv in Penc.
        destruct_ex.
        split_and.
        apply Return_inv in H0.
        rewrite <- H0 in H1.
        simpl in H1.
        apply Bind_inv in H1.
        destruct H1.
        destruct H.
        rewrite mempty_left in H1.
        apply Return_inv in H1.
        inversion H1; subst.
        clear H1.
        pose proof H as Hsave.
        unfold decode_string_with_term.
        rewrite Init.Wf.Fix_eq.
        destruct H.
        split_and.
        subst.
        pose proof (String_decode_correct (P := P)).
        destruct H with (sz := String.length x); eauto.
        destruct x0.
        eapply H1 in H0; eauto.
        clear H H1 H2.
        destruct_ex; split_and.
        subst.
        simpl.
        rewrite H0.
        simpl.
        replace (x0 =? x0)%string with true by (auto using eqb_refl).
        simpl.
        exists ""%string, x1.
        {
          intuition; auto.
          unfold format_with_term.
          econstructor; eauto.
          split.
          unfold Ensembles.In.
          simpl.
          apply unfold_computes.
          eapply ReturnComputes.
          simpl.
          red.
          unfold Bind2.
          apply unfold_computes.
          eapply BindComputes; eauto.
          rewrite mempty_left.
          auto.
        }
        {
          intros.
          repeat (apply functional_extensionality; intros; f_equal).
          subst; auto.
          unfold DecodeBindOpt2.
          unfold BindOpt.
          unfold If_Opt_Then_Else.
          destruct Decode_w_Measure_lt; auto.
          do 2 destruct p; rewrite H0; auto.
        }
      }
      {
        admit.
      }
    }
    {
      admit.
    }
  Admitted.
End String.
