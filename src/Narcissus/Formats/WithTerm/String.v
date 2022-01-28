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


  Lemma format_string_cons : 
    forall (a : Ascii.ascii) (s : string) (s' : B) (env xenv : CacheFormat)
           (close : string),
      (format_string ++ format_string ◦ constant close) (String a s) env
         ∋ (s', xenv) ->
         exists s'' xenv' env' b,
           (format_string ++ format_string ◦ constant close) s env' ∋ (s'', xenv') /\
           mappend b s'' = s'.
  Proof.
    intros.
    apply Bind_inv in H;
      destruct_ex;
      split_and.
    repeat match goal with
        | H : ComposeOpt.compose _ _ _ _ ∋ _ |- _ =>
          apply Bind_inv in H;
            destruct_ex;
            split_and
        | H : Bind2 _ _ ∋ _ |- _ =>
          apply Bind_inv in H;
            destruct_ex;
            split_and
        end.
        apply Return_inv in H2,H4.
        inversion H4; subst.
        clear H.
        simpl in H2.
        inversion H2.
        subst.
        clear H2.
        exists (mappend (fst x2) (fst x0)).
        exists (snd x0).
        exists (snd x1).
        eexists (fst x1).
        split; eauto.
        econstructor.
        split; red; simpl; eauto.
        exact H3.
        simpl in *.
        apply unfold_computes.
        eapply BindComputes; eauto.
        rewrite mappend_assoc.
        auto.
  Qed.

  Theorem string_decode_with_term_correct
          {P : CacheDecode -> Prop}
          (close : string)
          (cache_inv : cache_inv_Property P
                        (fun P0 : CacheDecode -> Prop =>
                          forall (b : nat) (cd : CacheDecode), P0 cd -> P0 (addD cd b))) :
    CorrectDecoder monoid
                   (fun s => forall s1 s2, s <> s1 ++ close ++ s2)%string
                   (fun s => forall s1 s2, s <> s1 ++ close ++ s2)%string
                   eq
                   (format_with_term format_string close)
                   (decode_string_with_term close)
                   P
                   (format_with_term format_string close).
  Proof.
    split.
    { intros env env' xenv s s' ext ? Eeq Ppred Penc.
      generalize dependent env.
      revert env' xenv s' env_OK.
      induction s.
      { unfold id in *; intros.
        unfold format_with_term in Penc.
        unfold "++" in Penc.
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
        intros.
        unfold format_with_term in Penc;
          unfold decode_string_with_term.
        pose proof Penc as PencInd.
        apply format_string_cons in PencInd.
        destruct PencInd.
        destruct_ex; split_and.
        subst.
        rename H0 into IHPenc.
        simpl in *.
        assert (IHpred : forall s1 s2 : string, s <> (s1 ++ close ++ s2)%string).
        {
          clear -Ppred.
          intros.
          specialize (Ppred (String a s1) s2).
          intros Hnot.
          subst.
          simpl in *.
          auto.
        }
        specialize (IHs IHpred).
        clear IHpred.
        eapply IHs in IHPenc; eauto.
        destruct_ex; split_and.
        (* subst. *)
        {
          unfold "++" in Penc.
          apply Bind_inv in Penc;
            destruct_ex;
            split_and.
          unfold format_with_term in IHs.
          repeat match goal with
                 | H : ComposeOpt.compose _ _ _ _ ∋ _ |- _ =>
                   apply Bind_inv in H;
                     destruct_ex;
                     split_and
                 | H : Bind2 _ _ ∋ _ |- _ =>
                   apply Bind_inv in H;
                     destruct_ex;
                     split_and
                 end.
          apply Return_inv in H7,H9.
          (* inversion H8; subst. *)
          (* clear H. *)
          (* simpl in H7. *)
          simpl in *.
          unfold format_with_term in H1.
          pose proof (String_decode_correct (P := P)) as Hs.
          destruct Hs with (sz := String.length close); eauto.
          clear H10 Hs.
          destruct x6.
          simpl in *.
          inversion H6; subst.
          destruct H10.
          subst.
          simpl in *.
          inversion H7; subst.
          simpl in *.
          (* exists (String a x3). *)
          rewrite Init.Wf.Fix_eq.
          eexists; eauto.
          eexists; eauto.
          {
          
            apply EquivFormat_Projection_Format in H6.
            eapply (@H3 _ _ _ _ _ ext) in H6; eauto.
            clear H3.
            destruct_ex; split_and.
            clear IHs.
            inversion H7; subst.
            unfold decode_string_with_term in H0.
            (* Really close here just need to know that decode_string 
               returns some on bigger args if it did for smaller ones 
               and that the string it results in is not the same 
               and that it is not equal to close using H6
             *)
            (* Then we can hopefully use the decode_ascii in scope and 
               the result of our induction hypothesis to prove the rec bind 
               is some of something 
             *)
            (* Haven't thought about the other conjuncts. *)
  Admitted.
End String.
