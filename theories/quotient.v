(*
https://lean-lang.org/theorem_proving_in_lean4/axioms_and_computation.html
 *)

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import PropExtensionality.
Require Import FunctionalExtensionality.
Require Import Coq.Program.Basics.

Module Type EqRel.
  Parameter A : Type.
  Parameter R : relation A.
  Parameter eqRel : Equivalence R.
End EqRel.

Module Quotient (EqRel : EqRel).
  Import EqRel.

  Axiom t : Type.
  
  Axiom mk : A -> t.

  Axiom ind : forall (P : t -> Prop), (forall (a : A), P (mk a)) -> forall (q : t), (P q).

  Axiom lift : forall {T : Type} (f : A -> T),
      (forall a b, R a b -> f a = f b) -> t -> T.

  Axiom lift_eq : forall {T : Type} (f : A -> T) (respects : forall a b, R a b -> f a = f b)
                         (a : A), lift f respects (mk a) = f a.

  Axiom sound : forall {a b : A}, R a b -> mk a = mk b.

  (* Thats all the axioms. Below are definitions in terms of those axioms. *)
  
  Theorem complete : forall {a b : A}, mk a = mk b -> R a b.
  Proof.
    Set Nested Proofs Allowed.
    Definition f (a : A) : t -> Prop.
    Proof.
      refine (lift (fun x => R a x) _).
      intros.
      apply propositional_extensionality.
      split.
      - intros.
        eapply (@Equivalence_Transitive _ _ eqRel).
        apply H0.
        apply H.
      - intros.
        Print Equivalence.
        eapply (@Equivalence_Transitive _ _ eqRel).
        apply H0.
        apply (@Equivalence_Symmetric _ _ eqRel) in H.
        apply H.
    Defined.
    Unset Nested Proofs Allowed.
    intros.
    assert (f a (mk a)).
    unfold f.
    rewrite lift_eq.
    apply (@Equivalence_Reflexive _ _ eqRel).
    rewrite H in H0.
    unfold f in H0.
    rewrite lift_eq in H0.
    assumption.
  Qed.


  Definition map (f : A -> A) (respects : forall a b, R a b -> R (f a) (f b)) (x : t) : t.
    refine (lift (compose mk f) _ x).
    intros.
    unfold compose.
    apply sound.
    apply respects.
    apply H.
  Defined.

  Theorem map_eq (f : A -> A) (respects : forall a b, R a b -> R (f a) (f b)) (a : A)
    : map f respects (mk a) = mk (f a).
  Proof.
    unfold map.
    rewrite lift_eq.
    reflexivity.
  Qed.

  Definition lift2 {T : Type} (f : A -> A -> T)
             (respects: forall a b c d, R a b -> R c d -> f a c = f b d) (x : t) (y : t) : T.
    Check lift.
    refine (lift (fun a => lift (fun b => f a b) _ y) _ x).
    shelve.
    all: revgoals.
    Unshelve.
    - intros.
      apply respects.
      apply (@Equivalence_Reflexive _ _ eqRel).
      apply H.
    - intros.
      Check ind.
      refine (ind (fun y => lift (fun b0 : A => f a b0) _ y =
                              lift (fun b0 : A => f b b0) _ y) _ y).
      intros.
      rewrite lift_eq.
      rewrite lift_eq.
      apply respects.
      apply H.
      apply (@Equivalence_Reflexive _ _ eqRel).
  Defined.

  Theorem lift2_eq {T : Type} (f : A -> A -> T)
             (respects : forall a b c d, R a b -> R c d -> f a c = f b d)
             (a b : A) : lift2 f respects (mk a) (mk b) = f a b.
  Proof.
    unfold lift2.
    rewrite lift_eq.
    rewrite lift_eq.
    reflexivity.
  Qed.

  Definition map2 (f : A -> A -> A)
             (respects : forall a b c d, R a b -> R c d -> R (f a c) (f b d)) (t1 t2 : t) : t.
    refine (lift2 (fun a b => mk (f a b)) _ t1 t2).
    intros.
    apply sound.
    apply respects.
    apply H. apply H0.
  Defined.

  Theorem map2_eq (f : A -> A -> A)
          (respects : forall a b c d, R a b -> R c d -> R (f a c) (f b d))
          (a b : A) : map2 f respects (mk a) (mk b) = mk (f a b).
  Proof.
    unfold map2.
    rewrite lift2_eq.
    reflexivity.
  Qed.
    
End Quotient.
 
