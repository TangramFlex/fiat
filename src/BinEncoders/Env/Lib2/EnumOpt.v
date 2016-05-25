Require Import
        Fiat.Common.BoundedLookup.
Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Lib2.WordOpt.
Require Import
        Coq.Vectors.Vector
        Bedrock.Word.

Section Enum.
  Context {len : nat}.
  Context {A : Type}.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.
  Context {transformerUnit : TransformerUnitOpt transformer bool}.

  Context {sz : nat}.
  Context {ta : t A (S len)}.
  Variable (tb : t (word sz) (S len)).

  Inductive NoDupVector {A}
    : forall {n}, Vector.t A n -> Prop :=
    NoDupVector_nil : NoDupVector (Vector.nil _)
  | NoDupVector_cons : forall (x : A) {n} (l : Vector.t A n),
      ~ Vector.In x l -> NoDupVector l -> NoDupVector (Vector.cons _ x _ l).

  Lemma NoDupVector_invert {A'}
    : forall n (l : Vector.t A' n),
      NoDupVector l
      -> match l with
         | Vector.nil => True
         | Vector.cons a _ l' =>
           ~ Vector.In a l' /\ NoDupVector l'
         end.
  Proof.
    clear; induction 1; eauto.
  Qed.

  Definition encode_enum (i : BoundedIndex ta) (ce : CacheEncode) : B * CacheEncode :=
    let fin := i.(indexb).(ibound)
    in  encode_word (nth tb fin) ce.

  Fixpoint word_indexed {n : nat}
           (w : word sz)
           (t : t (word sz) n) : option (Fin.t n)
    := match t in Vector.t _ n return option (Fin.t n) with
       | nil => None
       | cons w' _ t' =>
         if (weqb w w') then Some (Fin.F1) else
           match word_indexed w t' with
           | Some f => Some (Fin.FS f)
           | None => None
           end
       end.

  Definition decode_enum (b : B)
             (cd : CacheDecode)
    : option (BoundedIndex ta * B * CacheDecode) :=
    `(w, b', cd') <- decode_word (sz:=sz) b cd;
      Ifopt word_indexed w tb as i Then 
      Some ({| bindex := _;
          indexb := {| ibound := i;
                       boundi := eq_refl _ |} |}, b', cd')
      Else None
  .

  Lemma word_indexed_correct :
    forall n (i : Fin.t n) (t : t (word sz) n),
      NoDupVector t
      -> match word_indexed (nth t i) t with
      | Some w' => i = w'
      | None => False
      end.
  Proof.
    clear.
    induction i.
    - intro; pattern n, t; apply Vector.caseS; simpl; intros.
      rewrite (proj2 (weqb_true_iff h h)); eauto.
    - intro; generalize i (IHi (Vector.tl t)); clear.
      pattern n, t; apply Vector.caseS; simpl.
      intros h n0 t0 i; case_eq (word_indexed (nth t0 i) t0); intros;
        apply NoDupVector_invert in H1; intuition subst.
      case_eq (weqb (nth t0 t1) h); intros; eauto.
      apply weqb_true_iff in H0; subst.
      destruct H2; generalize t0 H; clear; induction t1.
      + intro; pattern n, t0; apply Vector.caseS; simpl; intros; econstructor.
      + intro; revert t1 IHt1; pattern n, t0; apply Vector.caseS;
          simpl; intros.
        case_eq (weqb (nth t t1) h); intros; eauto.
        * apply weqb_true_iff in H0; subst; econstructor.
        * rewrite H0 in H.
          econstructor 2; apply IHt1.
          destruct (word_indexed (nth t t1) t); try discriminate.
          f_equal; apply Fin.FS_inj; congruence.
  Qed.

  Theorem Enum_decode_correct :
    NoDupVector tb
    -> encode_decode_correct_f cache transformer (fun _ => True) encode_enum decode_enum.
  Proof.
    unfold encode_decode_correct, encode_enum, decode_enum.
    intros ? env env' xenv c c' ext Eeq Ppred Penc.
    destruct (Word_decode_correct _ _ _ _ _ ext Eeq I Penc) as [? [? ?] ].
    rewrite H0; simpl.
    apply (word_indexed_correct _ (ibound (indexb c))) in H.
    subst; simpl in *.
    destruct (word_indexed (nth tb (ibound (indexb c))) tb);
      intros; simpl in *.
    + eexists; intuition eauto.
      repeat f_equal.
      destruct c.
      destruct indexb.
      rewrite <- boundi.
      simpl in H; subst.
      reflexivity.
    + intuition.
  Qed.
End Enum.