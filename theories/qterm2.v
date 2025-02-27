
(*
A second take at quotiented terms, hopefully simpler now that the underlying syntactic
terms have been defined more regularly
*)
Require Import String.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Require Import IdentParsing.IdentParsing.

Require Import quotient.
Require Import term.


Print Equivalence.
Check Build_Equivalence.
Print Reflexive.

Module Type LambdaSpec.
  Parameter QTerm : Type.
  Parameter app : QTerm -> QTerm -> QTerm.
  Parameter lam : string -> QTerm -> QTerm.
  Parameter var : string -> nat -> QTerm.
  Parameter lift : string -> QTerm -> QTerm.
  Parameter subst : string -> nat -> QTerm -> QTerm -> QTerm.
  Parameter pair : QTerm -> QTerm -> QTerm.
  Parameter pi1 : QTerm -> QTerm.
  Parameter pi2 : QTerm -> QTerm.

  Axiom lift_lam : forall (s1 s2 : string) (t : QTerm), lift s1 (lam s2 t) = lam s2 (lift s1 t).
  Axiom lift_app : forall (s : string) (t1 t2 : QTerm), lift s (app t1 t2) = app (lift s t1) (lift s t2).
  Axiom lift_var : forall (s1 s2 : string) (i : nat),
      lift s1 (var s2 i) = (if (s1 =? s2)%string then var s2 (S i) else var s2 i).
  Axiom subst_lam : forall (s1 s2 : string) (i : nat) (t1 t2 : QTerm),
      subst s2 i t2 (lam s1 t1) =
        (if (s1 =? s2)%string
         then lam s1 (subst s2 (S i) (lift s2 t2) t1)
         else lam s1 (subst s2 i t2 t1)).
  Axiom subst_app : forall (s : string) (i : nat) (t1 t2 t3 : QTerm),
      subst s i t3 (app t1 t2) = app (subst s i t3 t1) (subst s i t3 t2).
  Axiom subst_var : forall (x y : string) (n i : nat) (toSub : QTerm),
      subst x i toSub (var y n) = (if ((y =? x)%string && Nat.eqb n i)%bool then toSub else var y n).
  Axiom beta : forall s t1 t2, app (lam s t1) t2 = subst s 0 t2 t1.
  Axiom eta : forall (s : string) (t : QTerm), t = lam s (app (lift s t) (var s 0)).
  Axiom alpha : forall (s1 s2 : string) (t : QTerm),
    lam s1 t = lam s2 (subst s1 0 (var s2 0) t).
End LambdaSpec.

Module Lambda : LambdaSpec.
(*https://stackoverflow.com/questions/77921199/coq-using-a-parametrized-type-from-within-a-module*)
Module TermConversion <: EqRel.
  Definition A := Term.
  Definition R := convertible.
  Definition eqRel := Build_Equivalence convertible conv_refl conv_sym conv_trans.
End TermConversion.
Import TermConversion.

Module QTerm := Quotient TermConversion.

Definition QTerm := QTerm.t.

(* TODO: its possible that I need these definitions to not unfold in order to be performant? *)
Definition app := QTerm.map2 app app_cong.
Definition lam s := QTerm.map (lam s) (lam_cong s).
Definition var s i := QTerm.mk (var s i).
Definition lift s := QTerm.map (lift s) (lift_cong s).
Definition subst s i := QTerm.map2 (subst s i) (subst_cong s i).
Definition pair := QTerm.map2 pair pair_cong.
Definition pi1 := QTerm.map pi1 pi1_cong.
Definition pi2 := QTerm.map pi2 pi2_cong.

Check QTerm.sound.
Check lift_lam.


(* If we have a Quot.t in context, we can apply the quotient induction principle to
assume that it is of the form (Quot.mk a). *)
Ltac generalize_ind_QTerm :=
  match goal with
  | [ x : QTerm  |- _] => (generalize x; clear x; refine (QTerm.ind _ _); intro)
  | [ x : QTerm.t  |- _] => (generalize x; clear x; refine (QTerm.ind _ _); intro)
  end
.

Ltac quotient_map_eq_simpl :=
  repeat generalize_ind_QTerm;
  repeat (rewrite ?QTerm.map2_eq, ?QTerm.map_eq);
  apply QTerm.sound.


Theorem lift_lam : forall (s1 s2 : string) (t : QTerm),
    lift s1 (lam s2 t) = lam s2 (lift s1 t).
Proof.
  (*
  intros.
  generalize t.
  Check QTerm.ind.
  apply QTerm.ind.
  intros.
  unfold lift, lam.
  repeat rewrite QTerm.map_eq.
  apply QTerm.sound.
  apply lift_lam.
   *)
  intros.
  unfold lift, lam.
  quotient_map_eq_simpl.
  apply lift_lam.
Qed.

Theorem lift_app : forall (s : string) (t1 t2 : QTerm),
    lift s (app t1 t2) = app (lift s t1) (lift s t2).
Proof.
  intros.
  unfold lift, app.
  quotient_map_eq_simpl.
  apply lift_app.
Qed.

Lemma if_commute {A B : Type} (f : A -> B) (b : bool) (x y : A)
  : (if b then f x else f y) = f (if b then x else y).
Proof.
  destruct b; reflexivity.
Qed.
    
Theorem lift_var : forall (s1 s2 : string) (i : nat),
    lift s1 (var s2 i) =
      if String.eqb s1 s2
      then var s2 (S i)
      else var s2 i.
Proof.
  intros.
  unfold lift, var.
  rewrite if_commute.
  quotient_map_eq_simpl.
  apply lift_var.
Qed.

Theorem subst_app : forall (s : string) (i : nat) (t1 t2 t3 : QTerm),
    subst s i t3 (app t1 t2) = app (subst s i t3 t1) (subst s i t3 t2).
Proof.
  intros.
  unfold subst, app.
  quotient_map_eq_simpl.
  apply subst_app.
Qed.

Theorem subst_lam : forall (s1 s2 : string) (i : nat) (t1 t2 : QTerm),
    subst s2 i t2 (lam s1 t1) =
      if String.eqb s1 s2
      then lam s1 (subst s2 (S i) (lift s2 t2) t1)
      else lam s1 (subst s2 i t2 t1).
Proof.
  intros.
  unfold subst, lam, lift.
  rewrite if_commute.
  repeat generalize_ind_QTerm.
  repeat (rewrite ?QTerm.map2_eq, ?QTerm.map_eq).
  rewrite if_commute.
  rewrite QTerm.map_eq.
  apply QTerm.sound.
  rewrite <- if_commute.
  apply subst_lam.
Qed.

Theorem subst_var : forall x y n i toSub,
    subst x i toSub (var y n) =
    if andb (String.eqb y x) (Nat.eqb n i) then toSub else var y n.
Proof.
  intros.
  unfold subst, var.
  generalize_ind_QTerm.
  repeat (rewrite ?QTerm.map2_eq, ?QTerm.map_eq).
  rewrite if_commute.
  apply QTerm.sound.
  apply subst_var.
Qed.

Theorem alpha : forall (s1 s2 : string) (t : QTerm),
    lam s1 t = lam s2 (subst s1 0 (var s2 0) t).
Proof.
  intros.
  unfold lam, subst, var.
  quotient_map_eq_simpl.
  apply alpha.
Qed.

Theorem beta : forall s t1 t2, (app (lam s t1) t2) = (subst s 0 t2 t1).
Proof.
  intros.
  unfold app, lam, subst.
  quotient_map_eq_simpl.
  apply beta.
Qed.

Theorem eta : forall s t, t = (lam s (app (lift s t) (var s 0))).
Proof.
  intros.
  unfold lam, app, lift, var.
  quotient_map_eq_simpl.
  apply eta.
Qed.

End Lambda.

Include Lambda.

(*Copying from https://softwarefoundations.cis.upenn.edu/plf-current/Stlc.html#tm:3, not sure what
all this does*)
Declare Scope term_scope.
Delimit Scope term_scope with term.
Open Scope term_scope.

Declare Custom Entry term_term.
Declare Custom Entry term_name.

Notation "x" := (var (ident_to_string x) 0) (in custom term_term at level 0, x ident) : term_scope.

Notation "< x >" := x (x custom term_term).

Notation "( t )" := t (in custom term_term at level 0, t custom term_term) : term_scope.
Notation "x y" := (app x y) (in custom term_term at level 10, left associativity).
Notation "'fun' x => y" := (lam x y)
                             (in custom term_term at level 200,
                                 x custom term_name,
                                 y custom term_term at level 200,
                                 left associativity).
Notation "x" := (ident_to_string x) (in custom term_name at level 0, x ident) : term_scope.
(*
Notation "'fun2' x1 x2 => y" := (lam (ident_to_string x1) (lam (ident_to_string x2) y))
                                  (in custom term_term at level 200,
                                      x1 ident, x2 ident,
                                      y custom term_term at level 200,
                                      left associativity).

 *)
(* subst and lift notations *)
Notation "t1 [ s @ i / t2 ]" := (subst s i t2 t1) (in custom term_term at level 40,
                                                      t1 custom term_term,
                                                      i custom term_term,
                                                      t2 custom term_term,
                                                      s custom term_name) : term_scope.
Notation "t1 [ s / t2 ]" := (subst s 0 t2 t1) (in custom term_term at level 40,
                                                  t1 custom term_term,
                                                  t2 custom term_term,
                                                  s custom term_name) : term_scope.
Notation "t1 [ s ]" := (lift s t1) (in custom term_term at level 40,
                                       t1 custom term_term,
                                       s custom term_name) : term_scope.

(* Unquote expression so you can refer to other QTerms in scope *)
Notation "` x" := x (in custom term_term at level 0, x global) : term_scope.
Notation "` x" := x (in custom term_name at level 0, x global) : term_scope.

Compute <fun y => fun z => y (fun x => x y)>.

(* It wont use those notations for printing. But maybe I should specify separate notations,
only for printing? *)

Notation "a b" := (app a b) (at level 10, left associativity, only printing).
Notation "s" := (var s 0) (at level 5, only printing).
Notation "'fun' x => t" := (lam x t) (at level 200, right associativity,  only printing).
(* For some mystery reason, the subtitution notation defined above already works for printing.
Even though none of the other notations (all defined above in the same way) work for printing.*)
Notation "t [ s ]" := (lift s t) (at level 300, only printing).

Compute <fun y => fun z => y (fun x => x y)>.
Definition metavar_example: QTerm. exact <fun x => x>. Qed.
Compute <fun x => x `metavar_example x>.


(* Notations for subst and lift *)
(*
Notation "t1 [ s @ i / t2 ]" := (subst s i t2 t1) (at level 40).
Notation "t1 [ s / t2 ]" := (subst s 0 t2 t1) (at level 40, s at level 10).
Notation "t1 [ s ]" := (lift s t1) (at level 40).
*)

Definition var_coerce (s : string) := var s 0.
Coercion var_coerce : string >-> QTerm.
Arguments var_coerce _%_string.


Check beta.
Check eta.
Check alpha.
Check lift_app.

(* So there is an issue where I need to hide the definitions.
Maybe make a module? *)
Compute <fun x => fun y => x y y>.
