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
    
Definition Pmatch2 {T1 T2 A : Type} (P : T1 -> T2 -> Prop)
           (branch1 : T1 -> T2 -> A) (branch2 : A) : A.
  refine (choose A (fun a => (exists t1 t2, P t1 t2 /\ branch1 t1 t2 = a)
                             \/
                               ((~exists t1 t2, P t1 t2) /\ a = branch2))).
  destruct (classic (exists t1 t2, P t1 t2)).
  - destruct H, H.
    exists (branch1 x x0).
    apply or_introl.
    exists x.
    exists x0.
    auto.
  - exists branch2.
    apply or_intror.
    split; auto.
Defined.

Theorem Pmatch2Def1 {T1 T2 A : Type} {P : T1 -> T2 -> Prop} {t1 : T1} {t2 : T2} (H : P t1 t2)
        (*(unique : forall t1 t2 t1' t2', P t1 t2 -> P t1' t2' -> t1 = t1' /\ t2 = t2')*)
        (unique1 : forall t1 t2 t1' t2', P t1 t2 -> P t1' t2' -> t1 = t1')
        (unique2 : forall t1 t2 t1' t2', P t1 t2 -> P t1' t2' -> t2 = t2')
        (branch1 : T1 -> T2 -> A) (branch2 : A)
  : Pmatch2 P branch1 branch2 = branch1 t1 t2.
Proof.
  unfold Pmatch2.
  apply choiceInd.
  intros.
  destruct H0.
  - destruct H0, H0, H0.
    specialize (unique1 _ _ _ _ H H0).
    specialize (unique2 _ _ _ _ H H0).
    subst.
    reflexivity.
  - destruct H0.
    exfalso.
    apply H0.
    exists t1.
    exists t2.
    assumption.
Qed.

Theorem Pmatch2Def2 {T1 T2 A : Type} (P : T1 -> T2 -> Prop)
        (*unique : forall t1 t2, P t1 -> P t2 -> t1 = t2*)
        (branch1 : T1 -> T2 -> A) (branch2 : A)
        (ne : forall t1 t2, P t1 t2 -> False)
  : Pmatch2 P branch1 branch2 = branch2.
Proof.
  unfold Pmatch2.
  apply choiceInd.
  intros.
  destruct H.
  - destruct H, H, H.
    exfalso.
    apply (ne x x0).
    assumption.
  - destruct H.
    assumption.
Qed.
    
