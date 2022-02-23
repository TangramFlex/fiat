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

Require Import WordOpt.
Require Import Bedrock.Word.

Section String.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid B}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  Definition decode_string_with_term
             (code: string)
    :  B -> CacheDecode -> option (string * B * CacheDecode) := 
      Fix well_founded_lt_b
           (fun _ => CacheDecode -> option (string * B * CacheDecode))
         (fun b rec cd =>
            match decode_string (String.length code) b cd with
            | None => 
              (`(a, b1, e1) <- Decode_w_Measure_lt decode_ascii b cd ltac:(exact ascii_decode_lt);
              (`(xs, b2, e2) <- rec _ (proj2_sig b1) e1;
              Some (String a xs, b2, e2)))
            | Some((term_code, b', cd')) =>
               If String.eqb code term_code Then
                Some (EmptyString, b', cd')
               Else
                (`(a, b1, e1) <- Decode_w_Measure_lt decode_ascii b cd ltac:(exact ascii_decode_lt);
                (`(xs, b2, e2) <- rec _ (proj2_sig b1) e1;
                Some (String a xs, b2, e2)))
            end).

  Ltac unf H := 
    repeat (
    unfold DecodeBindOpt2 in H;
    unfold BindOpt in H;
    unfold If_Opt_Then_Else in H;
    unfold DecodeBindOpt in H;
    unfold Bind2 in H;
    unfold BindOpt in H).

  Ltac unfg := 
    repeat (unfold DecodeBindOpt2;
    unfold BindOpt;
    unfold If_Opt_Then_Else;
    unfold DecodeBindOpt;
    unfold Bind2;
    unfold BindOpt).

      
  Lemma format_string_env_eq : forall s env env' b,
      (format_string s env) ∋ (b, env') ->
      env' = fold_left (fun acc elt =>
                   (addE acc 8)) (list_ascii_of_string s) env.
  Proof.
    induction s; intros; auto.
    {
      simpl in H.
      computes_to_inv.
      inversion H; subst; auto.
    }
    {
      simpl in H.
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
      computes_to_inv.
      inversion H2.
      subst.
      clear H2.
      unfold format_ascii in H0.
      unfold WordOpt.format_word  in H0.    
      computes_to_inv.
      destruct x.
      inversion H0; subst; auto.
      clear H0.
      simpl in H1.
      destruct x0.
      apply IHs in H1.
      simpl.
      subst; auto.
    }
  Qed.

  Lemma fold_add_eq : forall B A (l : list B) env n (add : A -> nat -> A), 
      (fold_left (fun acc : A => constant add acc n) l (add env n))
      = add (fold_left (fun acc : A => constant add acc n) l env) n.
  Proof.
    induction l; simpl; auto; try auto using IHl.
  Qed.

  Lemma decode_string_env_eq : forall n s env cd env' (b : B),
      decode_string n cd env = Some (s, b, env') ->
      env' = fold_left (fun acc elt =>
                   (addD acc 8)) (repeat 0 n) env.
  Proof.
    induction n; intros; auto.
    {
      simpl in H.
      inversion H; subst; auto.
    }
    {
      simpl in H.
      unf H.
      simpl.
      destruct (decode_ascii cd env) eqn:Ha; try discriminate.
      destruct p,p.
      destruct (decode_string n b0 c) eqn:Hs; try discriminate.
      destruct p,p.
      inversion H; subst.
      apply IHn in Hs.
      assert (c = addD env 8); subst; auto.
      {
        clear -Ha.
        unfold decode_ascii in Ha.
        unfold decode_word in Ha.
        destruct (decode_word' 8 cd); try discriminate.
        simpl in Ha.
        destruct p.
        inversion Ha; auto.
      }
    }
  Qed.

  Lemma decode_word_invar : forall b b' env0 env n (w : word n) env', 
      decode_word b env = Some (w, b', env0) ->
      exists env0', 
        decode_word b env' = Some(w, b', env0').
  Proof.
    intros.
    unfold decode_word in *.
    unf H.
    unfg .
    destruct (decode_word' n b) eqn:Hw.
    inversion H.
    subst; eauto.
    discriminate.
  Qed.

  Lemma decode_ascii_env : forall b b' env0 env a env', 
      decode_ascii b env = Some (a, b', env0) ->
      exists env0', 
        decode_ascii b env' = Some(a, b', env0').
  Proof.
    unfold decode_ascii.
    intros.
    unf H.
    destruct (decode_word b env) eqn:H2; try discriminate.
    destruct p,p.
    eapply decode_word_invar in H2.
    destruct H2 as [env0' H2]; rewrite H2.
    simpl.
    inversion H; subst; eauto.
  Qed.

  Definition head_option (s : string) :=
    match s with
    | EmptyString => None
    | String a s' => Some a
    end.

  Lemma decode_string_ascii : forall n b ext env env0' s b' env', 
      n <> 0 -> 
      decode_string n (mappend b ext) env =
      Some (s, b', env0') ->
      exists b'' env'', 
        decode_ascii (mappend b ext) env' =
        option_map (fun a => (a, b'', env'' )) (head_option s).
  Proof.
    unfold option_map.
    destruct n; 
      intros; [
        contradiction| ].
    destruct n.
    {
      simpl in *.
      unf H0.
      destruct decode_ascii eqn:Ha in H0.
      destruct p,p.
      simpl in *.
      eapply decode_ascii_env in Ha.
      destruct Ha.
      rewrite H1.
      inversion H0; subst.
      simpl.
      eauto.
      discriminate.
    }
    {
      simpl in H0.
      unf H0.
      destruct decode_ascii eqn:Ha in H0; try discriminate.
      destruct p,p.
      eapply decode_ascii_env in Ha; try discriminate.
      destruct_ex.
      rewrite H1.
      destruct decode_ascii eqn:Ha' in H0; try discriminate.
      destruct p,p.
      destruct decode_string eqn:Hs in H0; try discriminate.
      destruct p,p.
      simpl in *.
      inversion H0.
      subst.
      simpl in *.
      eauto.
    }
  Qed.

  Theorem string_decode_with_term_correct
          {P : CacheDecode -> Prop}
          (close : string)
          (cache_inv : cache_inv_Property P
                        (fun P0 : CacheDecode -> Prop =>
                          forall (b : nat) (cd : CacheDecode), P0 cd -> P0 (addD cd b))) :
    CorrectDecoder monoid
                   (fun s => (forall s1 s2, s <> s1 ++ close ++ s2))%string
                   (fun s => (forall s1 s2, s <> s1 ++ close ++ s2))%string
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
      (* destruct Ppred as [Ppred Pclose]. *)
      induction s.
      { unfold id in *; intros; unfold format_with_term in Penc;
        unfold "++" in Penc; simpl in Penc;
        unfold Bind2 in Penc; apply Bind_inv in Penc.
        clear Ppred.
        destruct_ex; split_and.
        apply Return_inv in H0; rewrite <- H0 in H1; simpl in H1.
        apply Bind_inv in H1; destruct H1; destruct H.
        rewrite mempty_left in H1; apply Return_inv in H1.
        inversion H1; subst; clear H1.
        pose proof H as Hsave.
        unfold decode_string_with_term.
        rewrite Init.Wf.Fix_eq.
        destruct H; split_and; subst.
        pose proof (String_decode_correct (P := P)).
        destruct H with (sz := String.length x); eauto.
        destruct x0.
        eapply H1 in H0; eauto.
        clear H H1 H2.
        destruct_ex; split_and; subst; simpl.
        rewrite H0; simpl.
        replace (x0 =? x0)%string with true by (auto using eqb_refl); simpl.
        exists ""%string, x1.
        {
          intuition; auto; unfold format_with_term; econstructor; eauto.
          split.
          unfold Ensembles.In; simpl; apply unfold_computes; eapply ReturnComputes.
          simpl; red; unfold Bind2. apply unfold_computes.
          eapply BindComputes; eauto; rewrite mempty_left; auto.
        }
        {
          intros; 
          repeat (apply functional_extensionality; intros; f_equal); unfg;
          destruct Decode_w_Measure_lt; auto;
          destruct_conjs;
          match goal with| H : context[_ _ _ = _ _ _] |- _ => rewrite H end; auto.
        }
      }
      {
        intros.
        (* pose proof Penc as PencHold. *)
        unfold format_with_term in Penc.
        unfold "++" in Penc.
        unfold ComposeOpt.compose in Penc.
        (* exists (String a s). *)
        unfold decode_string_with_term.
        rewrite Init.Wf.Fix_eq.
        (* assert (Deq : *)
        (*     (`(a0, b1, e1) <- Decode_w_Measure_lt decode_ascii  *)
        (*                       (mappend s' ext) env' ascii_decode_lt; *)
        (*    `(xs, b2, e2) <- Fix well_founded_lt_b *)
        (*                       (constant (CacheDecode -> *)
        (*                                  option (string * B * CacheDecode))) *)
        (*                       (fun (b : B) *)
        (*                          (rec : forall y : B, *)
        (*                                 lt_B y b -> *)
        (*                                 CacheDecode -> *)
        (*                                 option (string * B * CacheDecode)) *)
        (*                          (cd : CacheDecode) => *)
        (*                        `(term_code0, b'0, cd'0) <-  *)
        (*                        decode_string (String.length close) b cd; *)
        (*                        If (close =? term_code0)%string *)
        (*                        Then Some (""%string, b'0, cd'0) *)
        (*                        Else (`(a1, b0, e0) <- Decode_w_Measure_lt decode_ascii *)
        (*                                                 b cd ascii_decode_lt; *)
        (*                              `(xs, b2, e2) <- rec (` b0) (proj2_sig b0) e0; *)
        (*                              Some (String a1 xs, b2, e2))) *)
        (*                       (` b1) e1; *)
        (*                        Some (String a0 xs, b2, e2)) *)
        (*     =  *)
        (*    (`(a0, b1, e1) <- Decode_w_Measure_lt decode_ascii  *)
        (*                                          (mappend s' ext) env' ascii_decode_lt; *)
        (*     `(xs, b2, e2) <- decode_string_with_term close (` b1) e1; *)
        (*    Some (String a0 xs, b2, e2)) *)
        (*   ) by auto. *)
        assert (Deq :
            (`(a0, b1, e1) <- Decode_w_Measure_lt decode_ascii 
                              (mappend s' ext) env' ascii_decode_lt;
           `(xs, b2, e2) <- Fix well_founded_lt_b
                              (constant (CacheDecode ->
                                         option (string * B * CacheDecode)))
                              (fun (b : B)
                                 (rec : forall y : B,
                                        lt_B y b ->
                                        CacheDecode ->
                                        option (string * B * CacheDecode))
                                 (cd : CacheDecode) =>
                               match decode_string (String.length close) b cd with
                            | Some (term_code, b', cd') =>
                                If (close =? term_code)%string
                                Then Some (""%string, b', cd')
                                Else (`(a1, b0, e0) <- Decode_w_Measure_lt decode_ascii
                                                         b cd ascii_decode_lt;
                                      `(xs, b2, e2) <- rec (` b0) (proj2_sig b0) e0;
                                      Some (String a1 xs, b2, e2))
                            | None =>
                                `(a1, b0, e0) <- Decode_w_Measure_lt decode_ascii b cd
                                                   ascii_decode_lt;
                                `(xs, b2, e2) <- rec (` b0) (proj2_sig b0) e0;
                                Some (String a1 xs, b2, e2)
                            end)
                              (` b1) e1;
                               Some (String a0 xs, b2, e2))
            = 
           (`(a0, b1, e1) <- Decode_w_Measure_lt decode_ascii 
                                                 (mappend s' ext) env' ascii_decode_lt;
            `(xs, b2, e2) <- decode_string_with_term close (` b1) e1;
           Some (String a0 xs, b2, e2))
          ) by auto.
        rewrite Deq.
        clear Deq.
        assert (IHpred : (forall s1 s2 : string, s <> s1 ++ close ++ s2)%string).
        {
          clear -Ppred.
          intros.
          specialize (Ppred (String a s1) s2).
          intros Hnot.
          subst; eauto.
        }
        specialize (IHs IHpred).
        clear IHpred.
        unfold Bind2 in Penc.
        computes_to_inv.
        destruct_conjs.
        simpl fst in *.
        simpl snd in *.
        inversion Penc''.
        subst.
        clear Penc''.
        simpl in Penc.
        unf Penc.
        computes_to_inv.
        destruct_conjs.
        simpl in *.
        apply EquivFormat_Projection_Format in Penc'.
        (* eapply String_decode_correct with (sz := String.length close) in Penc'. *)
        (* destruct_ex. *)
        (* split_and. *)
        (* rewrite <- H in *. *)
        (* clear H. *)
        destruct (decode_string (String.length close)
                                (mappend (mappend b0 b) ext) env') eqn:Hs.
        2:{
            simpl.
            (* clear H0. *)
            clear Hs.
            eapply Ascii_decode_correct in Penc; eauto.
            set (forall s1 s2, String a s <> (s1 ++ close ++ s2)%string /\ close <> ""%string) as f in Ppred.
            destruct_ex.
            split_and.
            pose proof H0 as Hhold.
            eapply Decode_w_Measure_lt_eq in H0.
            destruct_ex.
            inversion Penc'0'.
            rewrite <- mappend_assoc.
            rewrite <- mappend_assoc.
            rewrite H0.
            simpl.
            assert (format_with_term format_string close s c1 ∋
                                     (mappend b1 b, xenv)).
            {
              subst.
              unfold format_with_term.
              unfold "++".
              unfold ComposeOpt.compose.
              computes_to_econstructor; eauto.
              computes_to_econstructor; eauto.
              apply EquivFormat_Projection_Format; simpl; eauto.
              simpl.
              eauto.
            }
            {
              eapply IHs in H3; eauto.
              destruct_ex.
              split_and.
              rewrite mappend_assoc.
              rewrite H7; eauto.
              simpl; eauto.
              eexists.
              eexists.
              split; eauto.
              split; subst; eauto.
              split; eauto.
              computes_to_econstructor; eauto.              
              simpl.
              computes_to_econstructor; eauto.
              computes_to_econstructor; eauto.
              simpl.
              computes_to_econstructor; eauto.
              epose proof (EquivFormat_Projection_Format (format_string)).
              red in H.
              red in H.
              specialize (H (constant close) (String x x2) c0).
              destruct H.
              red in H.
              apply H.
              eauto.
              eauto.
            }
        }
        {
          destruct p,p.
          simpl.
          destruct String.eqb eqn:?.
          simpl.
          {
            admit.
          }
          {
            simpl.
            (* clear H0. *)
            clear Hs.
            eapply Ascii_decode_correct in Penc; eauto.
            destruct_ex.
            split_and.
            pose proof H0 as Hhold.
            eapply Decode_w_Measure_lt_eq in H0.
            destruct_ex.
            inversion Penc'0'.
            rewrite <- mappend_assoc.
            rewrite <- mappend_assoc.
            rewrite H0.
            simpl.
            assert (format_with_term format_string close s c1 ∋
                                     (mappend b1 b, xenv)).
            {
              subst.
              unfold format_with_term.
              unfold "++".
              unfold ComposeOpt.compose.
              computes_to_econstructor; eauto.
              computes_to_econstructor; eauto.
              apply EquivFormat_Projection_Format; simpl; eauto.
              simpl.
              eauto.
            }
            {
              eapply IHs in H3; eauto.
              destruct_ex.
              split_and.
              rewrite mappend_assoc.
              rewrite H7; eauto.
              simpl; eauto.
              eexists.
              eexists.
              split; eauto.
              split; subst; eauto.
              split; eauto.
              computes_to_econstructor; eauto.              
              simpl.
              computes_to_econstructor; eauto.
              computes_to_econstructor; eauto.
              simpl.
              computes_to_econstructor; eauto.
              epose proof (EquivFormat_Projection_Format (format_string)).
              red in H.
              red in H.
              specialize (H (constant close) (String x x2) c0).
              destruct H.
              red in H.
              apply H.
              eauto.
              eauto.
            }
          }
        }
        {
          intros; 
          repeat (apply functional_extensionality; intros; f_equal); unfg;
          destruct Decode_w_Measure_lt; auto;
          destruct_conjs;
          match goal with| H : context[_ _ _ = _ _ _] |- _ => rewrite H end; auto.
        }
      }
    }
    { unfold decode_string_with_term, format_with_term;
        intros env env' xenv' data bin;
        revert env env' xenv' data.
      eapply (@well_founded_induction _ _ well_founded_lt_b) with
      (a := bin); intros.
      rewrite Coq.Init.Wf.Fix_eq in H2; auto; simpl.
      destruct (decode_string (String.length close) x env') eqn:Hc.
      {
        destruct p,p.
        destruct (close =? s)%string eqn:Heqc.
        {
          simpl in H2.
          inversion H2; subst.
          split; eauto.
          {
            apply decode_string_env_eq in Hc.
            subst; eauto.
            clear - H1 cache_inv.
            induction (String.length close); auto.
            simpl.
            rewrite fold_add_eq; auto.
          }
          pose proof Hc as Hclose.
          eapply @String_decode_correct in Hc; eauto.
          destruct Hc.
          destruct_ex.
          eexists.
          eexists.
          split; eauto.
          clear H2.
          computes_to_econstructor; eauto.
          {
            computes_to_econstructor; eauto.
          }
          {
            computes_to_econstructor; eauto.
            epose proof (EquivFormat_Projection_Format (format_string)).
            red in H2.
            red in H2.
            specialize (H2 (constant close) ""%string env).
            destruct H2.
            red in H2.
            simpl.
            apply H2.
            clear H2 H3.
            destruct_ex; split_and.
            clear H6 H8.
            apply eqb_eq in Heqc.
            Unshelve.
            2:{
              exact (x0, x1).
            }
            rewrite Heqc.
            exact H2.
          }
          {
            intuition; subst; simpl; auto.
            rewrite mempty_left; auto.
            admit.
          }
        }
        {
          simpl in H2.
          apply DecodeBindOpt2_inv in H2;
            destruct H2 as [? [? [? [? ?] ] ] ]; injections; subst.
          destruct (decode_ascii x env') as [ [ [? ?] ?] | ] eqn: ? .
          - destruct (Decode_w_Measure_lt_eq _ _ _ ascii_decode_lt Heqo).
            rewrite H4 in H2; injections.
            eapply (proj2 (Ascii_decode_correct cache_inv)) in Heqo; eauto;
            destruct Heqo as [? [? ?] ]; destruct_ex.
            symmetry in H3; apply DecodeBindOpt2_inv in H3;
            destruct H3 as [? [? [? [? ?] ] ] ]; injections; subst.
            eapply H in H3; intuition.
            destruct_ex; intuition; subst; eauto.
            unfold "++" in H9.
            unfold ComposeOpt.compose in H9.
            unfold Bind2 in H9.
            computes_to_inv.
            eexists _, _; intuition.
            {
              computes_to_econstructor; eauto.
              -
                simpl.
                computes_to_econstructor; eauto.
                computes_to_econstructor; eauto.
              -
                computes_to_econstructor; eauto.
            }
            {
              destruct_conjs; simpl in *; subst.
              inversion H9''; subst.
              do 2 rewrite mappend_assoc; auto.
            }
            {
              admit.
            }
            {
              destruct_conjs; simpl in *;
              inversion H9''; subst; auto.
            }
            {
              auto.
            }
          - eapply Decode_w_Measure_lt_eq' in Heqo; rewrite Heqo in H2;
              discriminate.
        }
      }
      {
        apply DecodeBindOpt2_inv in H2;
            destruct H2 as [? [? [? [? ?] ] ] ]; injections; subst.
        destruct (decode_ascii x env') as [ [ [? ?] ?] | ] eqn: ? .
        - destruct (Decode_w_Measure_lt_eq _ _ _ ascii_decode_lt Heqo).
            rewrite H4 in H2; injections.
            eapply (proj2 (Ascii_decode_correct cache_inv)) in Heqo; eauto;
            destruct Heqo as [? [? ?] ]; destruct_ex.
            symmetry in H3; apply DecodeBindOpt2_inv in H3;
            destruct H3 as [? [? [? [? ?] ] ] ]; injections; subst.
            eapply H in H3; intuition.
            destruct_ex; intuition; subst; eauto.
            unfold "++" in H9.
            unfold ComposeOpt.compose in H9.
            unfold Bind2 in H9.
            computes_to_inv.
            eexists _, _; intuition.
            {
              computes_to_econstructor; eauto.
              -
                simpl.
                computes_to_econstructor; eauto.
                computes_to_econstructor; eauto.
              -
                computes_to_econstructor; eauto.
            }
            {
              destruct_conjs; simpl in *; subst.
              inversion H9''; subst.
              do 2 rewrite mappend_assoc; auto.
            }
            {
              admit.
            }
            {
              destruct_conjs; simpl in *; subst;
              inversion H9''; subst; auto.
            }
            {
              auto.
            }
        - eapply Decode_w_Measure_lt_eq' in Heqo; rewrite Heqo in H2;
            discriminate.
      }
      intros; 
        repeat (apply functional_extensionality; intros; f_equal); unfg;
        destruct Decode_w_Measure_lt; auto;
        destruct_conjs;
        match goal with| H : context[_ _ _ = _ _ _] |- _ => rewrite H end; auto.
    }
    Admitted.
