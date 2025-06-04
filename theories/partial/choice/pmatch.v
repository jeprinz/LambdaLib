Require Import Classical.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import choiceBase.

Definition Pmatch {T A : Type} (P : T -> Prop)
           (branch1 : T -> A) (branch2 : A) : A.
  refine (choose A (fun a => (exists t, P t /\ branch1 t = a)
                             \/
                               ((~exists t, P t) /\ a = branch2))).
  destruct (classic (exists t, P t)).
  - destruct H.
    exists (branch1 x).
    apply or_introl.
    exists x.
    auto.
  - exists branch2.
    apply or_intror.
    split; auto.
Defined.

Theorem PmatchDef1 {T A : Type} {P : T -> Prop} {t : T} (H : P t)
        (unique : forall t1 t2, P t1 -> P t2 -> t1 = t2)
        (branch1 : T -> A) (branch2 : A)
  : Pmatch P branch1 branch2 = branch1 t.
Proof.
  unfold Pmatch.
  apply choiceInd.
  intros.
  destruct H0.
  - destruct H0, H0.
    specialize (unique _ _ H H0).
    subst.
    reflexivity.
  - destruct H0.
    exfalso.
    apply H0.
    exists t.
    assumption.
Qed.

Theorem PmatchDef2 {T A : Type} (P : T -> Prop)
        (*unique : forall t1 t2, P t1 -> P t2 -> t1 = t2*)
        (branch1 : T -> A) (branch2 : A)
        (ne : forall t, P t -> False)
  : Pmatch P branch1 branch2 = branch2.
Proof.
  unfold Pmatch.
  apply choiceInd.
  intros.
  destruct H.
  - destruct H, H.
    exfalso.
    apply (ne x).
    assumption.
  - destruct H.
    assumption.
Qed.
    
