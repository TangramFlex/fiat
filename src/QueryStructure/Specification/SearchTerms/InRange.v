Require Import Coq.Arith.Compare_dec
        Coq.ZArith.ZArith
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations.

Section RangeClause.

  Definition le_dec (n : nat) (range : nat)
  : {n <= range} + {~ n <= range} := le_dec n range.

  Global Instance DecideableEnsemble_InRange_le range :
    DecideableEnsemble (fun a => a <= range).
  Proof.
    econstructor 1 with (dec := fun a =>  ?[le_dec a range]).
    intros; destruct (le_dec a range); intuition eauto; discriminate.
  Defined.

  Global Instance DecideableEnsemble_InRange_le_f
         (A : Type)
         (f : A -> nat)
         b :
    DecideableEnsemble (fun a => f a <= b).
  Proof.
    econstructor 1 with (dec := fun a =>  ?[le_dec (f a) b ] ).
    intros; destruct (le_dec (f a) b); intuition eauto; discriminate.
  Defined.

  Global Instance DecideableEnsemble_InRange_ge range :
    DecideableEnsemble (fun a => range <= a).
  Proof.
    econstructor 1 with (dec := fun a => ?[le_dec range a]).
    intros; destruct (le_dec range a); intuition eauto; discriminate.
  Defined.

  Global Instance DecideableEnsemble_InRange_ge_f
         (A : Type)
         (f : A -> nat)
         b :
    DecideableEnsemble (fun a => b <= f a).
  Proof.
    econstructor 1 with (dec := fun a => ?[le_dec b (f a) ]).
    intros; destruct (le_dec b (f a)); intuition eauto; discriminate.
  Defined.

  Definition InRange_dec a minRange maxRange
    : {minRange <= a <= maxRange} + {~ (minRange <= a <= maxRange)}.
  Proof.
    refine (match le_dec minRange a with
            | left _ => match le_dec a maxRange with
                        | left _ => left _
                        | right _ => right _
                        end
            | right _ => right _
            end).
    abstract eauto with arith.
    abstract (intro; destruct H; eapply n; eauto).
    abstract (intro; destruct H; eapply n; eauto).
  Defined.

  Global Instance DecideableEnsemble_InRange minRange maxRange :
    DecideableEnsemble (fun a => minRange <= a <= maxRange).
  Proof.
    econstructor 1 with (dec := fun a => ?[InRange_dec a minRange maxRange]).
    intros; destruct (InRange_dec a minRange maxRange); intuition eauto; discriminate.
  Defined.

  Global Instance DecideableEnsemble_InRange_f
         (A : Type)
         (f : A -> nat)
         minRange maxRange :
    DecideableEnsemble (fun a => minRange <= f a <= maxRange).
   Proof. 
     econstructor 1 with (dec := fun a => ?[InRange_dec (f a) minRange maxRange ]).
    intros; destruct (InRange_dec (f a) minRange maxRange); intuition eauto; discriminate.
  Defined.

End RangeClause.
