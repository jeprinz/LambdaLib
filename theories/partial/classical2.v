Require Import Coq.Logic.ProofIrrelevance.
(* Instead of using SProp, for now I'll just use the proof irrelevance axiom.
   I'll see if this causes any issues; probably not. *)
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Definition Classical (A : Type) : Type :=
  {S : A -> Prop | (forall x y, S x -> S y -> x = y) /\ not (forall x, not (S x))}.

Definition Preturn {A : Type} (x : A) : Classical A.
  refine (exist _ (fun y => y = x) _).
  intros.
  split.
  - intros.
    congruence.
  - intros p.
    specialize (p x).
    contradiction.
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
  destruct pa as [Sa [same nonempty]].
  simpl.
  split.
  - intros.
    destruct H as [a1 [Ssaa1 fa1x]].
    destruct H0 as [a2 [Ssaa2 fa2y]].
    specialize (same _ _ Ssaa1 Ssaa2).
    subst.
    destruct (proj2_sig (f a2)) as [unique _].
    specialize (unique x y fa1x fa2y).
    assumption.
  - intros p.
    apply nonempty.
    intros a Sax.
    remember (f a) as fa.
    destruct fa as [SB [unique nonemptyB]].
    apply nonemptyB.
    intros b SBb.
    specialize (p b).
    apply p.
    exists a.
    split.
    + apply Sax.
    + rewrite <- Heqfa.
      simpl.
      apply SBb.
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

Theorem doesClassicalImplyNormal (P : Prop) : Classical P -> P.
Proof.
  intros [S [unique nonempty]].
  (*I don't think so*)
Abort.

Theorem thing (P : Prop) : ~ (~ (P \/ ~P)).
Proof.
  intros n.
  apply n.
  apply or_intror.
  intros p.
  apply n.
  apply or_introl.
  apply p.
Qed.

Theorem lem (P : Prop) : Classical (P \/ not P).
Proof.
  refine (exist _ (fun pornotp => True) _).
  split.
  - intros.
    exact (proof_irrelevance _ x y).
  - intros nn.
    assert ((~True) = False). {
      apply propositional_extensionality.
      split; auto.
    }
    rewrite H in nn.
    apply nn.
    + apply or_intror.
      intros p.
      apply nn.
      apply or_introl.
      apply p.
Defined.

Theorem ind {T : Type} : forall (P : Classical T -> Prop),
    (forall (a : T), P (Preturn a)) -> forall (q : Classical T), (P q).
Proof.
  intros.
  (*remember q as q'.*)
  (* Maybe this might be possible? *)
  destruct q as [S [unique nonempty]].

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

Definition choice {A B : Type} (R : A -> B -> Prop)
      (Rfunction : forall a, exists! b, R a b)
  : A -> Classical B.
Proof.
  intros a.
  refine (exist _ (fun b => R a b) _).
  specialize (Rfunction a) as [b property].
  exists b.
  assumption.
Defined.

Theorem choiceSpec (A B : Type) (R : A -> B -> Prop)
        (Rfunction : forall a, exists! b, R a b)
  : forall a, propBind (fun b => R a b) (choice R Rfunction a).
Proof.
  intros.
  
  
Lemma lemmaThing (A : Type) (P : A -> Prop) (H : exists a, P a)
  : exists (P' : A -> Prop), exists! a, P' a.
Proof.
  destruct H.
  exists (fun a => a = x).
  exists x.
  split.
  - reflexivity.
  - intros.
    congruence.
Qed.

Lemma doesThisWorkProbablyNot (A : Type) (thing : exists (P : A -> Prop), True) : A -> Prop.
Proof.
  intros.
  

Theorem indefiniteDescription (A : Type) (P : A -> Prop) (H : exists a, P a)
  : Classical { a : A | P a }.
Proof.
  refine (exist _ (fun aPa => (proj1_sig aPa)) _).

Definition Pif {A : Type} (P : Prop) (a1 a2 : Classical A) : Classical A.
  refine (exist _ (fun a => (P /\ proj1_sig a1 a) \/ ((not P) /\ proj1_sig a2 a)) _).
  (* This doesn't seem to be possible.
   But maybe it somehow can work by using Diaconescu's theorem? *)

(*
Theorem PifDef1 : forall (A : Type) P (a1 a2 : A), P -> Pif P a1 a2 = Preturn a1.
Proof.
  intros.
  apply classicalEq.
  apply functional_extensionality.
  intros.
  apply propositional_extensionality.
  split.
  - intros.
    destruct H0.
    destruct H0.
    assumption.
    destruct H0.
    contradiction.
  - intros.
    subst.
    apply or_introl.
    split.
    assumption.
    reflexivity.
Qed.

Theorem PifDef2 : forall (A : Type) P (a1 a2 : A), not P -> Pif P a1 a2 = Preturn a2.
Proof.
  intros.
  apply classicalEq.
  apply functional_extensionality.
  intros.
  apply propositional_extensionality.
  split.
  - intros.
    destruct H0.
    + destruct H0.
      contradiction.
    + destruct H0.
      assumption.
  - intros.
    subst.
    apply or_intror.
    split.
    assumption.
    reflexivity.
Qed.
*)
 
