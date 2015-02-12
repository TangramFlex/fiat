(** * Common facts about [≤] *)
Require Import Coq.Arith.Le.

Set Implicit Arguments.

Lemma le_pred n m (H : n <= m) : pred n <= pred m.
Proof.
  induction H.
  { constructor. }
  { destruct m; simpl in *; try constructor; assumption. }
Defined.

Lemma le_SS n m (H : n <= m) : S n <= S m.
Proof.
  induction H.
  { constructor. }
  { constructor; assumption. }
Defined.

Lemma le_canonical n m : {n <= m} + {~n <= m}.
Proof.
  revert n; induction m; intro n.
  { destruct n.
    { left; constructor. }
    { right; clear.
      abstract auto with arith. } }
  { destruct (IHm n) as [IHm'|IHm'].
    { left; constructor; assumption. }
    { clear IHm'.
      specialize (IHm (pred n)).
      destruct IHm as [IHm|IHm], n; simpl in *.
      { left; constructor; assumption. }
      { left; apply le_SS; assumption. }
      { exfalso.
        abstract auto with arith. }
      { right; intro H.
        abstract (apply le_pred in H; simpl in *; auto). } } }
Defined.

Lemma le_canonical_nn {n} : le_canonical n n = left (le_n _).
Proof.
  induction n; simpl; try reflexivity.
  rewrite IHn; clear IHn.
  edestruct le_canonical; [ exfalso | reflexivity ].
  { eapply le_Sn_n; eassumption. }
Qed.

Lemma le_canonical_nS {n m pf} (H : le_canonical n m = left pf)
: le_canonical n (S m) = left (le_S _ _ pf).
Proof.
  simpl; rewrite H; reflexivity.
Qed.

Fixpoint le_proof_irrelevance_left {n m} (pf : n <= m)
: left pf = le_canonical n m.
Proof.
  destruct pf.
  { clear. rewrite le_canonical_nn; reflexivity. }
  { erewrite le_canonical_nS; [ reflexivity | ].
    symmetry.
    apply le_proof_irrelevance_left. }
Defined.

Lemma le_proof_irrelevance' {n m} (pf : {n <= m} + {~n <= m})
: le_canonical n m = match pf, le_canonical n m with
                       | left pf', _ => left pf'
                       | _, right pf' => right pf'
                       | right pf', left pf'' => match pf' pf'' with end
                     end.
Proof.
  destruct pf.
  { erewrite <- le_proof_irrelevance_left; reflexivity. }
  { edestruct le_canonical; try reflexivity.
    exfalso; eauto. }
Qed.

Lemma le_proof_irrelevance {n m} (pf pf' : n <= m) : pf = pf'.
Proof.
  transitivity (match le_canonical n m with
                  | left pf' => pf'
                  | right pf' => match pf' pf with end
                end).
  { rewrite (le_proof_irrelevance' (left pf)); reflexivity. }
  { rewrite (le_proof_irrelevance' (left pf')); reflexivity. }
Qed.