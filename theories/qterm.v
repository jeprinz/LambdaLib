(*
In this file, I will define terms quotiented by conversion,
using a quotient
*)
Require Import String.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
From stdpp Require Import relations (rtsc, rtsc_congruence, rtsc_equivalence).

Require Import IdentParsing.IdentParsing.

Require Import quotient.
Require Import terms1.


Check rtsc.

Print Equivalence.

(*https://stackoverflow.com/questions/77921199/coq-using-a-parametrized-type-from-within-a-module*)
Module TermConversion <: EqRel.
  Definition A := Term.
  (* conversion is the reflexive transitive symmetric closure of single steps *)
  Definition R := rtsc step.
  Definition eqRel := @rtsc_equivalence Term step.
End TermConversion.
Import TermConversion.

Module QTerm := Quotient TermConversion.

Definition QTerm := QTerm.t.

Definition app (t1 t2 : QTerm) : QTerm.
Proof.
  Check QTerm.map2.
  Check terms1.app.
  refine (QTerm.map2 terms1.app _ t1 t2).
  intros.
  assert (R (terms1.app a c) (terms1.app a d)).
  unfold R.
  apply (@rtsc_congruence _ step _ _ step c d).
  intros.
  apply app_cong2.
  apply H1.
  apply H0.
  apply (@Equivalence_Transitive _ _ eqRel _ _ _ H1).
  apply (@rtsc_congruence _ step _ (fun x => terms1.app x d) step a b).
  intros.
  apply app_cong1. apply H2.
  apply H.
Qed.

Definition lam (name : string) (t : QTerm) : QTerm.
Proof.
  refine (QTerm.map (lam name) _ t).
  intros.
  apply (@rtsc_congruence _ step _ _ step a b).
  intros.
  apply lam_cong. apply H0.
  apply H.
Qed.

(* There is an issue where I need var to not unfold by default so that notations can work well.
Qed is just a temporary solution. *)
Definition var (name : string) (index : nat) : QTerm.
  exact (QTerm.mk (var name index)).
Qed.

Definition lift (name : string) (t : QTerm) : QTerm.
Proof.
  refine (QTerm.map (fun t => lift t name) _ t).
  intros.
Admitted.  

Definition subst (t : QTerm) (name : string) (index : nat) (toSub : QTerm) : QTerm.
Admitted.

(* To define these correctly will require a substantial amount of work to implement all of the
usual facts about lifting and substitution and how they commute with reduction.
Before I put in the hours to do that, I'll test out that the whole plan will work by axiomatizing
what the result would be:*)

(*Lift and subst defining equations*)
Check lift.
Axiom lift_app : forall (s : string) (t1 t2 : QTerm),
    lift s (app t1 t2) = app (lift s t1) (lift s t2).
Axiom lift_lam : forall (s1 s2 : string) (t : QTerm),
    lift s1 (lam s2 t) = lam s2 (lift s1 t).
Axiom lift_var : forall (s1 s2 : string) (i : nat),
    lift s1 (var s2 i) =
      if String.eqb s1 s2
      then var s2 (S i)
      else var s2 i.
Axiom subst_app : forall (s : string) (i : nat) (t1 t2 t3 : QTerm),
    subst (app t1 t2) s i t3 = app (subst t1 s i t3) (subst t2 s i t3).
Axiom subst_lam : forall (s1 s2 : string) (i : nat) (t1 t2 : QTerm),
    subst (lam s1 t1) s2 i t2 =
      if String.eqb s1 s2
      then lam s1 (subst t1 s2 (S i) (lift s2 t2))
      else lam s1 (subst t1 s2 i t2).
Axiom subst_var : forall x y n i toSub,
    subst (var y n) x i toSub =
    if andb (String.eqb y x) (Nat.eqb n i) then toSub else var y n.


(*Copying from https://softwarefoundations.cis.upenn.edu/plf-current/Stlc.html#tm:3, not sure what
all this does*)
Declare Scope term_scope.
Delimit Scope term_scope with term.
Open Scope term_scope.

Declare Custom Entry term_term.

Notation "x" := (ident_to_string x) (in custom term_term at level 0, x ident) : term_scope.

Notation "< x >" := x (x custom term_term).

Notation "( t )" := t (in custom term_term at level 0, t custom term_term) : term_scope.
Notation "x y" := (app x y) (in custom term_term at level 10, left associativity).
Notation "'fun' x => y" := (lam (ident_to_string x) y)
                             (in custom term_term at level 200, x ident,
                                 y custom term_term at level 200,
                                 left associativity).
(*
Notation "'fun2' x1 x2 => y" := (lam (ident_to_string x1) (lam (ident_to_string x2) y))
                                  (in custom term_term at level 200,
                                      x1 ident, x2 ident,
                                      y custom term_term at level 200,
                                      left associativity).

 *)
(* subst and lift notations *)
Notation "t1 [ s @ i / t2 ]" := (subst t1 s i t2) (in custom term_term at level 40,
                                                      t1 custom term_term,
                                                      i custom term_term,
                                                      t2 custom term_term,
                                                      s custom term_term) : term_scope.
Notation "t1 [ s / t2 ]" := (subst t1 s 0 t2) (in custom term_term at level 40,
                                                  t1 custom term_term,
                                                  t2 custom term_term,
                                                  s custom term_term) : term_scope.
Notation "t1 [ s ]" := (lift s t1) (in custom term_term at level 40,
                                       t1 custom term_term,
                                       s custom term_term) : term_scope.

(* Unquote expression so you can refer to other QTerms in scope *)
Notation "` x" := x (in custom term_term at level 0, x global) : term_scope.

Definition var_coerce (s : string) := var s 0.
Coercion var_coerce : string >-> QTerm.
Arguments var_coerce _%_string.

Compute <fun y => fun z => y (fun x => x y)>.

(* It wont use those notations for printing. But maybe I should specify separate notations,
only for printing? *)

Notation "a b" := (app a b) (at level 10, left associativity, only printing).
Notation "s" := (var s 0) (at level 5, only printing).
Notation "'fun' x => t" := (lam x t) (at level 200, right associativity,  only printing).

Compute <fun y => fun z => y (fun x => x y)>.
Definition metavar_example: QTerm. exact <fun x => x>. Qed.
Compute <fun x => x `metavar_example x>.


(* Notations for subst and lift *)
(*
Notation "t1 [ s @ i / t2 ]" := (subst t1 s i t2) (at level 40).
Notation "t1 [ s / t2 ]" := (subst t1 s 0 t2) (at level 40, s at level 10).
Notation "t1 [ s ]" := (lift s t1) (at level 40).
*)

(*Reduction rules*)
Axiom beta : forall (t1 t2 : QTerm) (s : string),
    <(fun `s => `t1) `t2> = <`t1 [ `s  / `t2 ]>.
Axiom eta : forall (t : QTerm),
    t = <fun x => t[x] x>.

Check beta.
Check eta.
(*
TODO: The substitution notations should go in 
*)
