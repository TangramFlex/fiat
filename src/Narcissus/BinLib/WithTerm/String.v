Require Import Coq.Strings.String.
Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Formats.Base.FMapFormat
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Formats.Delimiter
        Fiat.Narcissus.Formats.WithTerm.String
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignedEncodeMonad
        Fiat.Narcissus.BinLib.AlignedDecodeMonad
        Fiat.Narcissus.BinLib.AlignedString.
Require Import Recdef.
Require Import Operations.

Section String.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  Variable addD_addD_plus :
    forall (cd : CacheDecode) (n m : nat), addD (addD cd n) m = addD cd (n + m).

  Variable addE_addE_plus :
    forall (ce : CacheFormat) (n m : nat), addE (addE ce n) m = addE ce (n + m).
  Variable addE_0 :
    forall (ce : CacheFormat), addE ce 0 = ce.

  Open Scope AlignedDecodeM_scope.

(* GetByteAt *)
(*   Fixpoint StringTermAlignedDecodeM {m} *)
(*            (term_char : word 8) *)
(*            (n : nat) *)
(*     : AlignedDecodeM string m := *)
(*     match n with *)
(*     | 0 => ThrowAlignedDecodeM *)
(*     | S n' => BindAlignedDecodeM GetCurrentByte *)
(*           (fun c => if (weqb c term_char) *)
(*                      then ReturnAlignedDecodeM EmptyString *)
(*                    else BindAlignedDecodeM (StringTermAlignedDecodeM term_char n') *)
(*                      (fun s => ReturnAlignedDecodeM (String (ascii_of_N (wordToN c)) s))) *)
(*     end%AlignedDecodeM%list. *)

  (* Want to use auto to solve the termination condition *) 
  Local Hint Extern 4 =>
  match goal with
  | H : Nat.leb _ _ = false  |- _ => 
    apply Compare_dec.leb_complete_conv in H; lia
  | H : {res : nat & _ = S _} |- _ =>
    destruct H; simpl; red; auto
  end.
  
  Declare Scope option.
  Notation "res <- c ; k" := (option_bind (fun res => k) c) : option.
  Require Import Bedrock.Word Ascii.

  Open Scope string.
  Open Scope option.

  Fixpoint sequence (l : list (option Core.char)) : option string :=
    match l with
    | nil => Some ""
    | h::t => 
      h' <- h;
      rec <- sequence t;
      Some (String (ascii_of_N (wordToN h')) rec)
  end.
  Definition GetCurrentByte_dep 
             {n : nat}
             (v: ByteBuffer.t n)
             (idx : nat) : CacheDecode -> option (Core.char * {res : nat & res = S idx} * CacheDecode) := 
      (fun c => Ifopt (nth_opt v idx) as b
                Then Some (b, existT _ (S idx) eq_refl, addD c 8) Else None).

  (* This can be made much better but I wanted to make sure I knew how to write this 
     program since it uses fix with a measure *)
  Lemma mr :
    forall n idx,
      Nat.leb n idx = false -> 
      MR lt (fun idx'0 : nat => n - idx'0) (S idx) idx.
  Proof.
    red; auto.
  Qed.

  Definition consume_bytes {m} (num : nat) (buf : ByteBuffer.t m) idx cd :=
    fold_left (fun (acc : option (nat*CacheDecode)) _ =>
                 acc' <- acc;
                 (* next <- GetCurrentByte buf (fst acc') (snd acc'); *)
                  next <- GetByteAt (fst acc') buf (fst acc') (snd acc');
                 let '(_, idx', cd') := next in
                 Some (idx', cd')
              ) (seq idx num) (Some (idx, cd)).

  Definition bytes_to_string_opt {m} (num : nat) (buf : ByteBuffer.t m) idx cd
    : option string :=
    sequence (map (fun elt => option_map (compose fst fst) elt)
                (map (fun i => GetByteAt i buf idx cd) (seq idx num))).

  Definition AlignedDecodeStringWithTerm' {n}
             (close : string)
    : nat -> ByteBuffer.t n -> CacheDecode -> option (string * nat * CacheDecode).
    refine (Fix (measure_wf Wf_nat.lt_wf (fun idx' => n - idx'))
         (fun _ => ByteBuffer.t n -> CacheDecode -> option (string * nat * CacheDecode))
           (fun idx rec buf cd =>
              (if Nat.leb n idx as eqb return (Nat.leb n idx = eqb -> _) then
                fun _ => None
              else
                fun _ => 
                term <- bytes_to_string_opt (String.length close) buf idx cd;
              if term =? close then
                    (* This should be traverse *)
                    res <- consume_bytes (String.length close) buf idx cd;
                Some ("", fst res, snd res)
                (* Some ("", fst res, snd res) *)
              else
                `(b, idx', cd') <- GetCurrentByte buf idx cd;
                `(s, idx'', cd'') <- rec (S idx) _ buf cd';
                 Some(String (ascii_of_N (wordToN b)) s, idx'', cd'')
              ) eq_refl)).
    apply (mr n idx e).
    Defined.

  Definition AlignedDecodeStringWithTerm {n} (close : string)
    : AlignedDecodeM string n :=
    fun buf idx => AlignedDecodeStringWithTerm' close idx buf.
  
  Close Scope option.
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

  Lemma option_bind_eq : forall A B (f : A -> option B) o o'
      (H1 : option_bind f o = option_bind f o')
      (H : forall x y, f x = f y -> x = y)
      (H0 : forall x, f x <> None),
      o = o'.
  Proof.
    clear.
    intros.
    destruct o,o' eqn:Ho; simpl in *; eauto.
    {
      f_equal; eauto.
    }
    {
      exfalso.
      eapply H0; eauto.
    }
    {
      symmetry in H1.
      exfalso.
      eapply H0; eauto.
    }
  Qed.

  Require Import BinNums.
  Require Import BinPos.
  Require Import BinNat.
  Lemma lt_n_p : forall (p : positive) (n : N),
      BinNat.N.lt (BinNums.Npos p) n ->
      BinPos.Pos.lt p (Pos.of_nat (N.to_nat n)).
  Proof.
    clear.
    intros.
    lia.
  Qed.

  Require Import BinNums.
  Require Import BinPos.
  Require Import Coq.Strings.Ascii.
(* Lemma ascii_of_pos_inv : *)
(*   forall p p',  *)
(*     ascii_of_pos p = ascii_of_pos p' ->  *)
(*     (p < 256)%positive -> (p' < 256)%positive ->  *)
(*     p = p'. *)
(* Proof. *)
(*   intros. *)
(*   unfold ascii_of_pos in H1. *)
(*   destruct p. *)
  

  Lemma of_NB : forall n b,
      Some b = Byte.of_N n -> n = (Byte.to_N b).
  Proof.
    clear; simpl; intros.
    destruct n; simpl in *; auto.
    inversion H.
    auto.
    repeat match goal with
             | H: context[match ?p with | _ => _ end] |- _ =>
               destruct p
             end; inversion H; auto.
  Qed.

  Lemma ByteOfN_None : forall p, 
      None = Byte.of_N (N.pos p) ->
      (Pos.lt 255 p)%positive.
  Proof.
    clear.
    intros.
    simpl in *.
    repeat match goal with
           | H: context[match ?p with | _ => _ end] |- _ =>
             destruct p
           end; inversion H; lia.
  Qed.

  Lemma byte_of_N_inv : forall n n',
      BinNat.N.lt n 256 -> 
      BinNat.N.lt n' 256 -> 
      Byte.of_N n = Byte.of_N n' ->
      n = n'.
  Proof.
    clear.
    destruct n.
    {
      intros.
      destruct n'; auto.
      simpl in *.
      repeat match goal with
             | H: context[match ?p with | _ => _ end] |- _ =>
               destruct p
             end; try inversion H1; lia.
    }
    {
      intros.
      destruct n'; auto.
      {
        simpl in *.
        repeat match goal with
             | H: context[match ?p with | _ => _ end] |- _ =>
               destruct p
             end; try inversion H1; lia.
      }        
      {
        simpl Byte.of_N at 1 in H1.
        repeat match goal with
               | H: context[match ?p with | _ => _ end = _] |- _ =>
                 destruct p
               end;
          match goal with
          | H: Some ?b = Byte.of_N _ |- _ =>
            apply of_NB in H1; subst; auto
          | H : None = Byte.of_N _ |- _ =>
            apply ByteOfN_None in H; lia
          end.
      }
    }
  Qed.

  Lemma ascii_of_byte_helper : forall a b,
      a = ascii_of_byte b -> b = (byte_of_ascii a).
  Proof.
    clear.
    intros.
    destruct b; subst; auto.
  Qed.

  Lemma ascii_of_Byte_inv : forall b b',
      ascii_of_byte b = ascii_of_byte b' ->
      b = b'.
  Proof.
    clear.
    intros.
    unfold ascii_of_byte at 1 in H.
    destruct b;
    simpl in *;
    apply ascii_of_byte_helper in H; subst;
    auto.
  Qed.

  Definition pos_of_ascii (a : ascii) : positive :=
    Pos.of_nat (nat_of_ascii a).

  Lemma ascii_of_pos_eq : forall a p, 
      (p < 256)%positive ->
      a = ascii_of_pos p ->
      p = pos_of_ascii a.
  Proof.
    clear; intros.
    unfold ascii_of_pos in H0.
    repeat match goal with
             | H: context[match ?p with | _ => _ end] |- _ =>
               destruct p; try (simpl in *; subst; auto; lia)
             end.
  Qed.

  Lemma ascii_of_N_inv : forall n n',
      BinNat.N.lt n 256 -> 
      BinNat.N.lt n' 256 -> 
      ascii_of_N n = ascii_of_N n' ->
      n = n'.
  Proof.
    clear.
    intros.
    destruct n; intros;
    simpl in *.
    {
      destruct n'; auto.
      unfold ascii_of_N in H1.
      assert (zero = Ascii false false false false false false false false) by auto.
      assert (one = Ascii true false false false false false false false) by auto.
      eauto.
      unfold ascii_of_pos in H1.
      destruct p.
      -
        repeat match goal with
        | H: context[match ?p with | _ => _ end] |- _ =>
          destruct p
        end; inversion H1.
      -
        repeat match goal with
        | H: context[match ?p with | _ => _ end] |- _ =>
          destruct p
        end; inversion H1.
        simpl in *.
        exfalso.
        {
          clear -H0.
          destruct p; 
          inversion H0.
        }
      -
        inversion H1.
    }
    {
      destruct n'; auto.
      unfold ascii_of_N in H1.
      assert (zero = Ascii false false false false false false false false) by auto.
      assert (one = Ascii true false false false false false false false) by auto.
      eauto.
      unfold ascii_of_pos in H1.
      destruct p.
      -
        repeat match goal with
        | H: context[match ?p with | _ => _ end] |- _ =>
          destruct p
        end; inversion H1.
      -
        repeat match goal with
        | H: context[match ?p with | _ => _ end] |- _ =>
          destruct p
        end; inversion H1.
        simpl in *.
        exfalso.
        {
          clear -H.
          destruct p; 
          inversion H.
        }
      -
        inversion H1.
      -
        simpl in *.
        f_equal.
        assert ((p < 256)%positive) by lia.
        assert ((p0 < 256)%positive) by lia.
        clear H H0.
        unfold ascii_of_pos at 1 in H1.
        repeat match goal with
               | H: context[match ?p with | _ => _ end] |- _ =>
                 destruct p
               end;
        apply ascii_of_pos_eq in H1;
        subst; auto; lia.
    }
  Qed.

  Lemma ascii_word_inj : forall (c c0 : word 8),
      ascii_of_N (wordToN c) = ascii_of_N (wordToN c0) ->
      c = c0.
  Proof.
    clear.
    intros.
    apply ascii_of_N_inv in H; eauto.
    apply wordToN_inj; auto.
    apply (InternetChecksum.wordToN_bound c).
    apply (InternetChecksum.wordToN_bound c0).
  Qed.

  Lemma sequence_eq : forall l l',
      (forall e, In e l -> e <> None) -> 
      (forall e, In e l' -> e <> None) -> 
      sequence l = sequence l' ->
      l = l'.
  Proof.
    clear.
    induction l.
    {
      intros l' H1 H2 H.
      simpl in *.
      destruct l'; auto.
      destruct o.
      simpl in H.
      unfold option_bind in H1.
      destruct (sequence l'); simpl in *; try inversion H.
      simpl in H.
      inversion H.
    }
    {
      intros l' H1 H2 H.
      destruct l'.
      {
        destruct a.
        simpl in *.
        destruct (sequence l);
          simpl in *;
          inversion H.
        simpl in *.
        inversion H.
      }
      assert (sequence l = sequence l').
      {
        unfold option_bind in H.
        simpl in H.
        destruct a,o.
        -
          destruct (sequence l), (sequence l'); auto;
            inversion H.
          apply ascii_of_N_inv in H3; auto.
          apply (InternetChecksum.wordToN_bound c).
          apply (InternetChecksum.wordToN_bound c0).
        -
          specialize (H2 None).
          exfalso.
          apply H2; intuition; auto.
        -
          specialize (H1 None).
          exfalso.
          apply H1; intuition; auto.
        -
          specialize (H1 None).
          exfalso.
          apply H1; intuition; auto.
      }
      {
        apply IHl in H0; auto.
        {
          subst.
          clear IHl.
          simpl in H.
          apply option_bind_eq in H; subst; auto.
          intros.
          {
            destruct ((sequence l')) eqn:Hl.
            {
              simpl in *.
              inversion H0; subst; auto using ascii_of_N_inv.
              apply ascii_of_N_inv in H4; auto.
              apply wordToN_inj in H4; auto.
              apply (InternetChecksum.wordToN_bound x).
              apply (InternetChecksum.wordToN_bound y).
            }
            {
              simpl in *.
              exfalso.
              assert (forall e, In e l' -> e <> None).
              {
                intros; intuition.
                subst; auto.
                eapply H2; eauto.
              }
              clear -Hl H3.
              induction l'; inversion Hl.
              destruct a.
              2:{
                simpl in *.
                eapply H3; intuition; subst; eauto.
              }
              {
                simpl in Hl.
                destruct ((sequence l')).
                simpl in *.
                inversion Hl.
                simpl in *.
                apply IHl'; auto.
              }
            }
          }
          {
            intros.
            intuition.
            assert (forall e, In e l' -> e <> None).
            {
              intros; intuition.
              subst; auto.
              eapply H2; eauto.
              simpl in *.
              right; auto.
            }
            clear -H0 H3.
            induction l'.
            simpl in *.
            inversion H0.
            destruct a.
            simpl in *.
            destruct ((sequence l')).
            simpl in *.
            inversion H0.
            simpl in *.
            eauto.
            simpl in *.
            eapply H3; intuition; subst; auto.
          }
        }
        {
          intuition; eauto.
          subst; auto.
          eapply H1; eauto.
          right; auto.
        }
        {
          intuition; eauto.
          subst; auto.
          eapply H2; eauto.
          right; auto.
        }
      }
    }
  Qed.

  Lemma getByteNot_None : forall n (buf : ByteBuffer.t n) idx cd e,
      In e (map (fun i => GetByteAt i buf idx cd) (seq 0 n)) ->
      e <> None.
  Proof.
    clear; intros.
    induction n.
    simpl in *.
    inversion H.
    simpl in *.
    destruct H; subst; intuition; eauto.
    {
      destruct n.
      simpl in *.
      unfold GetByteAt in H.
      destruct (nth_opt buf 0) eqn:He; inversion H.
      simpl in *.
      unfold nth_opt in He.      
      simpl in *.
      clear -He.      
      (* assert (buf <> @Vector.nil Core.char). *)
      (* destruct buf; auto. *)
      (* simpl in *. *)
      admit.
      admit.
    }
  Admitted.

  Lemma asdf : forall A B C O (f : option (A*B*C) -> option O)
                      (l l' : list (option (A*B*C))),
      (forall (a b: option (A*B*C)),
          f a = f b -> option_map (compose fst fst) a = option_map (compose fst  fst) b) ->
      map f l = map f l' ->
      map (option_map (compose fst fst)) l = map (option_map (compose fst fst)) l'.
  Proof.
    clear.
    induction l; simpl; intros.
    {
      symmetry in H0.
      apply map_eq_nil in H0.
      subst; auto.
    }
    {
      destruct l'.      
      simpl in *.
      discriminate.
      simpl in H0.
      inversion H0; auto.
      apply H in H2.
      simpl.
      rewrite H2.
      f_equal.      
      apply IHl; auto.
    }
  Qed.

  (* Require Import CoLoR.Util.Vector.VecUtil. *)
  Lemma nth_opt_cons : forall T (h : T) m (v : Vector.t T m) a,
      Vector_nth_opt (Vector.cons T h m v) (S a) =
      Vector_nth_opt v a.
  Proof.
    clear.
    destruct v; simpl; auto.
  Qed.

  Lemma getByteAt_fst_fst_tl : 
    forall a (m : nat) (v : ByteBuffer.t (S m)) (n : nat) (cd : CacheDecode),
      option_map (fst ∘ fst) (GetByteAt a (Vector.tl v) n cd) =
      option_map (fst ∘ fst) (GetByteAt (S a) v (S n) cd).
  Proof.
    clear.
    intros.
    unfold GetByteAt.
    dependent destruction v.
    simpl.
    unfold nth_opt.
    rewrite nth_opt_cons.
    destruct Vector_nth_opt; simpl; auto.
  Qed.

  Lemma bytes_to_string_eq : forall m num (v : ByteBuffer.t (S m)) n cd, 
        bytes_to_string_opt num (Vector.tl v) n cd =
        bytes_to_string_opt num v (S n) cd.
  Proof.
    clear.
    intros.
    unfold bytes_to_string_opt.
    rewrite <- seq_shift.
    induction (seq n num); simpl; auto.
    simpl.
    rewrite IHl.
    rewrite getByteAt_fst_fst_tl.
    auto.
  Qed.
    
  Lemma foldl_cons : forall A B (f : A -> B -> A) l (elt : B) (acc : A),
      fold_left f l (f acc elt) = f (fold_left f l acc) elt .
  Proof.
    clear.
    induction l; auto.
    intros.
  Admitted.
    
    
  Lemma getByteAt_snd_fst_tl : 
    forall a (m : nat) (v : ByteBuffer.t (S m)) (n : nat) (cd : CacheDecode),
      option_map (compose S (snd ∘ fst)) (GetByteAt a (Vector.tl v) n cd) =
      option_map (snd ∘ fst) (GetByteAt (S a) v (S n) cd).
  Proof.
    clear.
    intros.
    unfold GetByteAt.
    dependent destruction v.
    simpl.
    unfold nth_opt.
    rewrite nth_opt_cons.
    destruct Vector_nth_opt; simpl; auto.
  Qed.

  Lemma getByteAt_snd_tl : 
    forall a (m : nat) (v : ByteBuffer.t (S m)) (n : nat) (cd : CacheDecode),
      option_map snd (GetByteAt a (Vector.tl v) n cd) =
      option_map snd (GetByteAt (S a) v (S n) cd).
  Proof.
    clear.
    intros.
    unfold GetByteAt.
    dependent destruction v.
    simpl.
    unfold nth_opt.
    rewrite nth_opt_cons.
    destruct Vector_nth_opt; simpl; auto.
  Qed.
    
  Lemma comsume_bytes_snd_eq :
    forall (m n num : nat) (v : Vector.t Core.char (S m))
           (cd : CacheDecode),
      option_map snd (consume_bytes num (Vector.tl v) n cd) = 
      option_map snd (consume_bytes num v (S n) cd).
  Proof.
    clear.
    intros.
    unfold consume_bytes.
    rewrite <- seq_shift.
    assert (option_map (compose S fst) (Some (n, cd)) =
            option_map fst (Some (S n, cd))).
    auto.
    assert (option_map snd (Some (n, cd)) =
            option_map snd (Some (S n, cd))).
    auto.
    (* rewrite <- ListFacts.fold_map. *)
    generalize dependent (Some (S n, cd)).
    generalize dependent (Some (n, cd)).
    generalize dependent m.
    generalize dependent cd.
    induction (seq n num); simpl; auto.
    intros.
    assert (option_map snd (option_bind (fun '(_, idx', cd') => Some (idx', cd'))
                          (GetByteAt n (Vector.tl v) n cd)) =
            (option_map snd (option_bind (fun '(_, idx', cd') => Some (idx', cd'))
          (GetByteAt (S n) v (S n) cd)))).
    {
      clear.
      unfold GetByteAt.
      dependent destruction v.
      simpl.
      unfold nth_opt.
      rewrite nth_opt_cons.
      destruct Vector_nth_opt; simpl; auto.
    }
    assert (option_map (compose S fst)
                       (option_bind (fun '(_, idx', cd') => Some (idx', cd'))
                          (GetByteAt n (Vector.tl v) n cd)) =
            (option_map fst (option_bind (fun '(_, idx', cd') => Some (idx', cd'))
          (GetByteAt (S n) v (S n) cd)))).
    {
      clear.
      unfold GetByteAt.
      dependent destruction v.
      simpl.
      unfold nth_opt.
      rewrite nth_opt_cons.
      destruct Vector_nth_opt; simpl; auto.
    }
    rewrite IHl with (o := (option_bind
          (fun acc' : nat * CacheDecode =>
           option_bind (fun '(_, idx', cd') => Some (idx', cd'))
             (GetByteAt (fst acc') (Vector.tl v) (fst acc') (snd acc'))) o))
    (o0 := (option_bind
          (fun acc' : nat * CacheDecode =>
           option_bind (fun '(_, idx', cd') => Some (idx', cd'))
             (GetByteAt (fst acc') v (fst acc') (snd acc'))) o0)); auto.
    {
      unfold option_map.
      unfold option_bind.
      clear -H H2 H0.
      destruct o,o0; auto;
        destruct_conjs;
        simpl in *;
        unfold compose in *;
        simpl in *;
        inversion H;
        subst;
        inversion H0; subst;
        clear H H0.
        destruct (GetByteAt n1 (Vector.tl v) n1 c) eqn:Ht;
          destruct (GetByteAt (S n1) v (S n1) c) eqn:Hv;
          destruct_conjs; simpl in *;
            auto;
            match goal with
            | H1: context[GetByteAt ?n1 (Vector.tl ?v) ?n1 ?c],
              H2: context[GetByteAt (S ?n1) ?v (S ?n1) ?c]
              |- _ =>
              assert (H3: option_map (S ∘ (snd ∘ fst)) (GetByteAt n1 (Vector.tl v) n1 c) =
                      option_map (snd ∘ fst) (GetByteAt (S n1) v (S n1) c)) by
                  apply getByteAt_snd_fst_tl;
              rewrite H1 in H3; rewrite H2 in H3;
              inversion H3; subst; auto
            end.
    }
    {
      unfold option_map.
      unfold option_bind.
      destruct o,o0; auto;
      destruct_conjs;
        simpl in *;
        unfold compose in *;
        simpl in *;
      inversion H; inversion H0; subst;
      clear H H0;
      destruct (GetByteAt n1 (Vector.tl v) n1 c) eqn:Ht;
        destruct (GetByteAt (S n1) v (S n1) c) eqn:Hv;
          destruct_conjs; simpl in *; auto;
      match goal with
      | H1: context[GetByteAt ?n1 (Vector.tl ?v) ?n1 ?c],
            H2: context[GetByteAt (S ?n1) ?v (S ?n1) ?c]
        |- _ =>
        assert (H3: option_map snd (GetByteAt n1 (Vector.tl v) n1 c) =
                    option_map snd (GetByteAt (S n1) v (S n1) c))
          by
            apply getByteAt_snd_tl;
        rewrite H1 in H3; rewrite H2 in H3;
        inversion H3; subst; auto
      end.
    }
  Qed.

  Lemma comsume_bytes_fst_eq :
    forall (m n num : nat) (v : Vector.t Core.char (S m))
           (cd : CacheDecode),
      option_map (compose S fst) (consume_bytes num (Vector.tl v) n cd) = 
      option_map fst (consume_bytes num v (S n) cd).
  Proof.
    clear.
    intros.
    unfold consume_bytes.
    rewrite <- seq_shift.
    assert (option_map (compose S fst) (Some (n, cd)) =
            option_map fst (Some (S n, cd))).
    auto.
    assert (option_map snd (Some (n, cd)) =
            option_map snd (Some (S n, cd))).
    auto.
    generalize dependent (Some (S n, cd)).
    generalize dependent (Some (n, cd)).
    generalize dependent m.
    generalize dependent cd.
    induction (seq n num); simpl; auto.
    intros.
    assert (option_map snd (option_bind (fun '(_, idx', cd') => Some (idx', cd'))
                          (GetByteAt n (Vector.tl v) n cd)) =
            (option_map snd (option_bind (fun '(_, idx', cd') => Some (idx', cd'))
          (GetByteAt (S n) v (S n) cd)))).
    {
      clear.
      unfold GetByteAt.
      dependent destruction v.
      simpl.
      unfold nth_opt.
      rewrite nth_opt_cons.
      destruct Vector_nth_opt; simpl; auto.
    }
    assert (option_map (compose S fst)
                       (option_bind (fun '(_, idx', cd') => Some (idx', cd'))
                          (GetByteAt n (Vector.tl v) n cd)) =
            (option_map fst (option_bind (fun '(_, idx', cd') => Some (idx', cd'))
          (GetByteAt (S n) v (S n) cd)))).
    {
      clear.
      unfold GetByteAt.
      dependent destruction v.
      simpl.
      unfold nth_opt.
      rewrite nth_opt_cons.
      destruct Vector_nth_opt; simpl; auto.
    }
    rewrite IHl with (o := (option_bind
          (fun acc' : nat * CacheDecode =>
           option_bind (fun '(_, idx', cd') => Some (idx', cd'))
             (GetByteAt (fst acc') (Vector.tl v) (fst acc') (snd acc'))) o))
    (o0 := (option_bind
          (fun acc' : nat * CacheDecode =>
           option_bind (fun '(_, idx', cd') => Some (idx', cd'))
             (GetByteAt (fst acc') v (fst acc') (snd acc'))) o0)); auto.
    {
      unfold option_map.
      unfold option_bind.
      clear -H H2 H0.
      destruct o,o0; auto;
        destruct_conjs;
        simpl in *;
        unfold compose in *;
        simpl in *;
        inversion H;
        subst;
        inversion H0; subst;
        clear H H0.
        destruct (GetByteAt n1 (Vector.tl v) n1 c) eqn:Ht;
          destruct (GetByteAt (S n1) v (S n1) c) eqn:Hv;
          destruct_conjs; simpl in *;
            auto;
            match goal with
            | H1: context[GetByteAt ?n1 (Vector.tl ?v) ?n1 ?c],
              H2: context[GetByteAt (S ?n1) ?v (S ?n1) ?c]
              |- _ =>
              assert (H3: option_map (S ∘ (snd ∘ fst)) (GetByteAt n1 (Vector.tl v) n1 c) =
                      option_map (snd ∘ fst) (GetByteAt (S n1) v (S n1) c)) by
                  apply getByteAt_snd_fst_tl;
              rewrite H1 in H3; rewrite H2 in H3;
              inversion H3; subst; auto
            end.
    }
    {
      unfold option_map.
      unfold option_bind.
      destruct o,o0; auto;
      destruct_conjs;
        simpl in *;
        unfold compose in *;
        simpl in *;
      inversion H; inversion H0; subst;
      clear H H0;
      destruct (GetByteAt n1 (Vector.tl v) n1 c) eqn:Ht;
        destruct (GetByteAt (S n1) v (S n1) c) eqn:Hv;
          destruct_conjs; simpl in *; auto;
      match goal with
      | H1: context[GetByteAt ?n1 (Vector.tl ?v) ?n1 ?c],
            H2: context[GetByteAt (S ?n1) ?v (S ?n1) ?c]
        |- _ =>
        assert (H3: option_map snd (GetByteAt n1 (Vector.tl v) n1 c) =
                    option_map snd (GetByteAt (S n1) v (S n1) c))
          by
            apply getByteAt_snd_tl;
        rewrite H1 in H3; rewrite H2 in H3;
        inversion H3; subst; auto
      end.
    }
  Qed.

  Lemma AlignedDecodeStringWithTermM {C : Type}
        (close : string)
    : forall (t : string -> DecodeM (C * _) ByteString)
             (t' : string -> forall {numBytes}, AlignedDecodeM C numBytes),
      (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b))
      -> DecodeMEquivAlignedDecodeM
           (fun v cd => `(s, bs, cd') <- decode_string_with_term close v cd;
                      t s bs cd')
           (fun numBytes => s <- AlignedDecodeStringWithTerm close;
                          t' s).
  Proof.
    split.
    {
      intros.
      unfold AlignedDecodeStringWithTerm.
      unfg.
      unfold BindAlignedDecodeM.
      unfold AlignedDecodeStringWithTerm'.
      rewrite Init.Wf.Fix_eq.
      simpl.
      destruct (Nat.leb numBytes_hd n) eqn:Hn.
      assert (Help: (Fix (measure_wf Wf_nat.lt_wf (fun idx' : nat => numBytes_hd - idx'))
            (constant (ByteBuffer.t numBytes_hd ->
                       CacheDecode -> option (string * nat * CacheDecode)))
            (fun (idx : nat)
               (rec : forall y : nat,
                      MR lt (fun idx' : nat => numBytes_hd - idx') y idx ->
                      ByteBuffer.t numBytes_hd ->
                      CacheDecode -> option (string * nat * CacheDecode))
               (buf : ByteBuffer.t numBytes_hd) (cd0 : CacheDecode) =>
             (if Nat.leb numBytes_hd idx as eqb
               return
                 (Nat.leb numBytes_hd idx = eqb -> option (string * nat * CacheDecode))
              then constant None
              else
               fun H0 : Nat.leb numBytes_hd idx = false =>
               option_bind
                 (fun term : string =>
                  if term =? close
                  then
                   option_bind
                     (fun res : nat * CacheDecode => Some ("", fst res, snd res))
                     (consume_bytes (String.length close) buf idx cd0)
                  else
                   `(b, _, cd') <- GetCurrentByte buf idx cd0;
                   `(s, idx'', cd'') <- rec (S idx) (mr numBytes_hd idx H0) buf cd';
                   Some (String (ascii_of_N (wordToN b)) s, idx'', cd''))
                 (bytes_to_string_opt (String.length close) buf idx cd0)) eq_refl) n
            (Vector.tl v) cd) = (
(if Nat.leb numBytes_hd n as eqb
      return (Nat.leb numBytes_hd n = eqb -> option (string * nat * CacheDecode))
     then constant None
     else
      constant option_bind
                 (fun term : string =>
                  if term =? close
                  then
                   option_bind
                     (fun res : nat * CacheDecode => Some ("", fst res, snd res))
                     (consume_bytes (String.length close) (Vector.tl v) n cd)
                  else
                   `(b0, _, cd') <- GetCurrentByte (Vector.tl v) n cd;
                   `(s, idx'', cd'') <- Fix
                                          (measure_wf Wf_nat.lt_wf
                                             (fun idx' : nat => numBytes_hd - idx'))
                                          (constant (ByteBuffer.t numBytes_hd ->
                                                     CacheDecode ->
                                                     option (string * nat * CacheDecode)))
                                          (fun (idx : nat)
                                             (rec : forall y : nat,
                                                    MR lt
                                                      (fun idx' : nat =>
                                                       numBytes_hd - idx') y idx ->
                                                    ByteBuffer.t numBytes_hd ->
                                                    CacheDecode ->
                                                    option (string * nat * CacheDecode))
                                             (buf : ByteBuffer.t numBytes_hd)
                                             (cd0 : CacheDecode) =>
                                           (if Nat.leb numBytes_hd idx as eqb
                                             return
                                               (Nat.leb numBytes_hd idx = eqb ->
                                                option (string * nat * CacheDecode))
                                            then constant None
                                            else
                                             fun H1 : Nat.leb numBytes_hd idx = false =>
                                             option_bind
                                               (fun term0 : string =>
                                                if term0 =? close
                                                then
                                                 option_bind
                                                   (fun res : nat * CacheDecode =>
                                                    Some ("", fst res, snd res))
                                                   (consume_bytes 
                                                      (String.length close) buf idx cd0)
                                                else
                                                 `(b1, _, cd'0) <- 
                                                 GetCurrentByte buf idx cd0;
                                                 `(s, idx'', cd'') <- 
                                                 rec (S idx) 
                                                   (mr numBytes_hd idx H1) buf cd'0;
                                                 Some
                                                   (String (ascii_of_N (wordToN b1)) s,
                                                   idx'', cd''))
                                               (bytes_to_string_opt
                                                  (String.length close) buf idx cd0))
                                             eq_refl) (S n) 
                                          (Vector.tl v) cd';
                   Some (String (ascii_of_N (wordToN b0)) s, idx'', cd''))
                 (bytes_to_string_opt (String.length close) (Vector.tl v) n cd)) eq_refl
                          )
    ).
        rewrite Init.Wf.Fix_eq.
        auto.
        admit.
        rewrite Help.
      {
        rewrite Hn; auto.
      }
      {
        assert (ahh: Fix (measure_wf Wf_nat.lt_wf (fun idx' : nat => numBytes_hd - idx'))
            (constant (ByteBuffer.t numBytes_hd ->
                       CacheDecode -> option (string * nat * CacheDecode)))
            (fun (idx : nat)
               (rec : forall y : nat,
                      MR lt (fun idx' : nat => numBytes_hd - idx') y idx ->
                      ByteBuffer.t numBytes_hd ->
                      CacheDecode -> option (string * nat * CacheDecode))
               (buf : ByteBuffer.t numBytes_hd) (cd0 : CacheDecode) =>
             (if Nat.leb numBytes_hd idx as eqb
               return
                 (Nat.leb numBytes_hd idx = eqb -> option (string * nat * CacheDecode))
              then constant None
              else
               fun H0 : Nat.leb numBytes_hd idx = false =>
               option_bind
                 (fun term : string =>
                  if term =? close
                  then
                   option_bind
                     (fun res : nat * CacheDecode => Some ("", fst res, snd res))
                     (consume_bytes (String.length close) buf idx cd0)
                  else
                   `(b, _, cd') <- GetCurrentByte buf idx cd0;
                   `(s, idx'', cd'') <- rec (S idx) (mr numBytes_hd idx H0) buf cd';
                   Some (String (ascii_of_N (wordToN b)) s, idx'', cd''))
                 (bytes_to_string_opt (String.length close) buf idx cd0)) eq_refl) n
            (Vector.tl v) cd =
                ((if Nat.leb numBytes_hd n as eqb
      return (Nat.leb numBytes_hd n = eqb -> option (string * nat * CacheDecode))
     then constant None
     else
      constant option_bind
                 (fun term : string =>
                  if term =? close
                  then
                   option_bind
                     (fun res : nat * CacheDecode => Some ("", fst res, snd res))
                     (consume_bytes (String.length close) (Vector.tl v) n cd)
                  else
                   `(b0, _, cd') <- GetCurrentByte (Vector.tl v) n cd;
                   `(s, idx'', cd'') <- Fix
                                          (measure_wf Wf_nat.lt_wf
                                             (fun idx' : nat => numBytes_hd - idx'))
                                          (constant (ByteBuffer.t numBytes_hd ->
                                                     CacheDecode ->
                                                     option (string * nat * CacheDecode)))
                                          (fun (idx : nat)
                                             (rec : forall y : nat,
                                                    MR lt
                                                      (fun idx' : nat =>
                                                       numBytes_hd - idx') y idx ->
                                                    ByteBuffer.t numBytes_hd ->
                                                    CacheDecode ->
                                                    option (string * nat * CacheDecode))
                                             (buf : ByteBuffer.t numBytes_hd)
                                             (cd0 : CacheDecode) =>
                                           (if Nat.leb numBytes_hd idx as eqb
                                             return
                                               (Nat.leb numBytes_hd idx = eqb ->
                                                option (string * nat * CacheDecode))
                                            then constant None
                                            else
                                             fun H1 : Nat.leb numBytes_hd idx = false =>
                                             option_bind
                                               (fun term0 : string =>
                                                if term0 =? close
                                                then
                                                 option_bind
                                                   (fun res : nat * CacheDecode =>
                                                    Some ("", fst res, snd res))
                                                   (consume_bytes 
                                                      (String.length close) buf idx cd0)
                                                else
                                                 `(b1, _, cd'0) <- 
                                                 GetCurrentByte buf idx cd0;
                                                 `(s, idx'', cd'') <- 
                                                 rec (S idx) 
                                                   (mr numBytes_hd idx H1) buf cd'0;
                                                 Some
                                                   (String (ascii_of_N (wordToN b1)) s,
                                                   idx'', cd''))
                                               (bytes_to_string_opt
                                                  (String.length close) buf idx cd0))
                                             eq_refl) (S n) 
                                          (Vector.tl v) cd';
                   Some (String (ascii_of_N (wordToN b0)) s, idx'', cd''))
                 (bytes_to_string_opt (String.length close) (Vector.tl v) n cd))) eq_refl).
        {
          rewrite Init.Wf.Fix_eq.
          admit.
          admit.
        }
        rewrite ahh.
        simpl.
        clear ahh.
        rewrite Hn; auto.
        unfold option_bind.
        rewrite bytes_to_string_eq.
        destruct (bytes_to_string_opt (String.length close) v (S n) cd); simpl; auto.
        destruct (s =? close)%string.
        -
          destruct (consume_bytes (String.length close) v (S n) cd) eqn:Hv.
          {
            destruct (consume_bytes (String.length close) (Vector.tl v) n cd) eqn:Ht.
            {
              simpl.
              assert (option_map (compose S fst) (consume_bytes (String.length close) (Vector.tl v) n cd) = option_map fst (consume_bytes (String.length close) v (S n) cd))
                   by (apply comsume_bytes_fst_eq).
              rewrite Hv in H0.
              rewrite Ht in H0.
              simpl in H0.
              inversion H0.
              unfold compose.
              specialize (H "").
              destruct H.
              rewrite H.
              assert ((option_map snd (consume_bytes (String.length close) (Vector.tl v) n cd) = option_map snd (consume_bytes (String.length close) v (S n) cd)))
                     by apply comsume_bytes_snd_eq.
              rewrite Hv in H3.
              rewrite Ht in H3.
              simpl in H3.
              inversion H3; subst; auto.
            }
            {
              exfalso.
              assert (option_map (compose S fst) (consume_bytes (String.length close) (Vector.tl v) n cd) = option_map fst (consume_bytes (String.length close) v (S n) cd))
                   by (apply comsume_bytes_fst_eq).
              rewrite Ht in H0.
              rewrite Hv in H0.
              simpl in H0.
              inversion H0.
            }
          }
          {
            simpl.
            destruct (consume_bytes (String.length close)
                                    (Vector.tl v) n cd) eqn:Ht; auto.
            exfalso.
            assert (option_map (compose S fst) (consume_bytes (String.length close) (Vector.tl v) n cd) = option_map fst (consume_bytes (String.length close) v (S n) cd))
                   by (apply comsume_bytes_fst_eq).
            rewrite Ht in H0.
            rewrite Hv in H0.
            simpl in H0.
            inversion H0.
          }
        -
          admit.
      }
      {
        intros.
        repeat (apply functional_extensionality; intros; f_equal).
        destruct GetCurrentByte; auto;
          destruct_conjs.
        assert (f_eq_g : forall y, f y = g y).
        intros.
        apply functional_extensionality; intros; f_equal.
        rewrite f_eq_g.
        eauto.
      }
    }
      {
        intros.
        split
        repeat (apply functional_extensionality; intros; f_equal).
        destruct GetCurrentByte; auto;
          destruct_conjs.
        assert (f_eq_g : forall y, f y = g y).
        intros.
        apply functional_extensionality; intros; f_equal.
        rewrite f_eq_g.
        eauto.

      {
        rewrite Init.Wf.Fix_eq.
        rewrite Init.Wf.Fix_eq.
        rewrite Init.Wf.Fix_eq.
        admit.
      }
      {
        intros.
        repeat (apply functional_extensionality; intros; f_equal).
        destruct GetCurrentByte; auto;
          destruct_conjs.
        assert (f_eq_g : forall y, f y = g y).
        intros.
        apply functional_extensionality; intros; f_equal.
        rewrite f_eq_g.
        eauto.
      }
    }
    
  Admitted.

End String.
