(*
https://lean-lang.org/theorem_proving_in_lean4/axioms_and_computation.html
 *)

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import PropExtensionality.

Module Type EqRel.
  Parameter A : Type.
  Parameter R : relation A.
  (*Parameter eqRel : Equivalence R.*)
  Parameter Rsym : symmetric A R.
  Parameter Rtrans : transitive A R.
  Parameter Rrefl : reflexive A R.
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


  (* Can I prove that if (not (R x y)), then mk x != mk y? *)

  
  
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
        Check Rtrans.
        Print transitive.
        eapply Rtrans.
        apply H0.
        apply H.
      - intros.
        eapply Rtrans.
        apply H0.
        apply Rsym in H.
        apply H.
    Defined.
    Unset Nested Proofs Allowed.
    intros.
    assert (f a (mk a)).
    unfold f.
    rewrite lift_eq.
    apply Rrefl.
    rewrite H in H0.
    unfold f in H0.
    rewrite lift_eq in H0.
    assumption.
  Qed.
  
End Quotient.
 
