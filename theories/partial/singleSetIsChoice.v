(*
The goal of this file is to think about the idea that the original Classical monad
which has exactly one element (and uses LEM axiom)
could allow choice
*)
Require Import Coq.Logic.ProofIrrelevance.
(* Instead of using SProp, for now I'll just use the proof irrelevance axiom.
   I'll see if this causes any issues; probably not. *)
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Definition Classical (A : Type) : Type :=
  {S : A -> Prop | exists! a, S a}.

Definition Preturn {A : Type} (x : A) : Classical A.
  refine (exist _ (fun y => y = x) _).
  intros.
  exists x.
  split.
  - reflexivity.
  - intros.
    congruence.
Defined.

Theorem classicalEq :
  forall A S1 S2 p1 p2,
    S1 = S2 -> @eq (Classical A) (exist _ S1 p1) (exist _ S2 p2).
Proof.
  intros.
  subst S1.
  assert (p1 = p2).
  apply proof_irrelevance.
  subst p1.
  reflexivity.
Qed.

Theorem classicalEq2:
  forall A (x y : Classical A), proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros.
  destruct x.
  destruct y.
  simpl in H.
  apply classicalEq.
  assumption.
Qed.

Theorem itIsReturn :
  forall T (S : T -> Prop) (p : exists! t, S t) (t : T),
    S t -> (exist _ S p) = Preturn t.
Proof.
  intros.
  apply classicalEq.
  apply functional_extensionality.
  intros.
  apply propositional_extensionality.
  split.
  - intros.
    destruct p as [t' [St' unique]].
    assert (e1 := unique _ H).
    assert (e2 := unique _ H0).
    congruence.
  - intros.
    subst.
    assumption.
Qed.

Theorem PreturnInj : forall A (x y : A), Preturn x = Preturn y -> x = y.
Proof.
  intros.
  pose (@f_equal _ _ (@proj1_sig _ _) _ _ H) as fact.
  simpl in fact.
  assert ((fun y => y = x) x).
  reflexivity.
  rewrite fact in H0.
  assumption.
Qed.

Definition Pbind {A B : Type} (pa : Classical A) (f : A -> Classical B) : Classical B.
  refine (exist _ (fun b => exists a, proj1_sig pa a /\ proj1_sig (f a) b) _).
  destruct pa as [Sa [a [Saa Saprop]]].
  simpl.
  remember (f a) as fa.
  destruct fa as [Sfa [fa' [Sfafa Sfaprop]]].
  exists fa'.
  split.
  - exists a.
    split.
    + apply Saa.
    + rewrite <- Heqfa.
      simpl.
      apply Sfafa.
  - intros b [a' [Saa' H]].
    specialize (Saprop _ Saa').
    subst.
    assert (proj1_sig (f a') fa'). {
      rewrite <- Heqfa.
      simpl.
      apply Sfafa.
    }
    
    destruct (proj2_sig (f a')) as [b' [fa'b' b'Unique]].
    rewrite <- (b'Unique _ H0) in *.
    rewrite <- (b'Unique _ H).
    reflexivity.
Defined.

Theorem bindDef : forall A B (a : A) (f : A -> Classical B),
    Pbind (Preturn a) f = f a.
Proof.
  intros.
  apply classicalEq2.
  apply functional_extensionality.
  intros.
  apply propositional_extensionality.
  split.
  - intros.
    simpl in H.
    destruct H.
    destruct H.
    subst x0.
    assumption.
  - intros.
    simpl.
    exists a.
    split.
    reflexivity.
    assumption.
Qed.

Definition propBind {T : Type} (P : T -> Prop) (pa : Classical T) : Prop :=
  Preturn True = (Pbind pa (fun a => Preturn (P a))).

Theorem propBindDef {T : Type} (t : T) (P : T -> Prop) :
  propBind P (Preturn t) = P t.
Proof.
  unfold propBind.
  rewrite bindDef.
  apply propositional_extensionality.
  split.
  - intros.
    apply PreturnInj in H.
    rewrite <- H.
    apply I.
  - intros.
    apply (f_equal Preturn).
    apply propositional_extensionality.
    split; auto.
Qed.

Theorem ind {T : Type} : forall (P : Classical T -> Prop),
    (forall (a : T), P (Preturn a)) -> forall (q : Classical T), (P q).
Proof.
  intros.
  remember q as q'.
  destruct q as [S [a [aInS property]]].
  assert (q' = (Preturn a)). {
    subst.
    apply classicalEq.
    extensionality a'.
    apply propositional_extensionality.
    split.
    - intros.
      symmetry.
      apply property; assumption.
    - intros.
      subst.
      assumption.
  }
  rewrite H0.
  apply H.
Qed.

Definition choose (T : Type) (P : T -> Prop) (H : exists t, P t): Classical T.
  refine (exist _ P _).
  destruct H as [t Pt].
  exists t.
  unfold unique.
  split.
  - assumption.
  - intros.
    (* So no, this doesn't work. choose requires that we don't know what the element is
     constructively. *)

Defined.

Theorem choice_spec' (T : Type) (P : T -> Prop) (H : exists t, P t)
  : Cbind (choose T P H) (fun t => Creturn (P t)) = Creturn True.
Proof.
  apply classicalEq2.
  simpl.
  extensionality X.
  apply propositional_extensionality.
  split.
  - intros.
    destruct H0.
    destruct H0.
    subst.
    apply propositional_extensionality; split; auto.
  - intros.
    subst.
    destruct H.
    exists x.
    split; auto.
    apply propositional_extensionality; split; auto.
Qed.
