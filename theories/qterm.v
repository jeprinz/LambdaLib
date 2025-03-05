
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
  Parameter lift : string -> nat -> QTerm -> QTerm.
  Parameter subst : string -> nat -> QTerm -> QTerm -> QTerm.
  Parameter pair : QTerm -> QTerm -> QTerm.
  Parameter pi1 : QTerm -> QTerm.
  Parameter pi2 : QTerm -> QTerm.
  Parameter const : string -> QTerm.

  Parameter lift_lam : forall (s1 s2 : string) (i : nat) (t : QTerm),
      lift s1 i (lam s2 t) = lam s2 (lift s1 (if eqb s1 s2 then S i else i) t).
  Parameter lift_app : forall s i t1 t2, lift s i (app t1 t2) = app (lift s i t1) (lift s i t2).
  Parameter lift_var : forall (s1 s2 : string) (i k : nat),
      lift s1 k (var s2 i) = (if andb (s1 =? s2)%string (negb (Nat.ltb i k)) then var s2 (S i) else var s2 i).
  Parameter lift_const : forall s1 s2 i , lift s1 i (const s2) = const s2.
  Parameter lift_pair : forall s i t1 t2, lift s i (pair t1 t2) = pair (lift s i t1) (lift s i t2).

  Parameter subst_lam : forall (s1 s2 : string) (i : nat) (t1 t2 : QTerm),
      subst s2 i t2 (lam s1 t1) =
        (if (s1 =? s2)%string
         then lam s1 (subst s2 (S i) (lift s1 0 t2) t1)
         else lam s1 (subst s2 i (lift s1 0 t2) t1)).
  Parameter subst_app : forall (s : string) (i : nat) (t1 t2 t3 : QTerm),
      subst s i t3 (app t1 t2) = app (subst s i t3 t1) (subst s i t3 t2).
  Parameter subst_var : forall (x y : string) (n i : nat) (toSub : QTerm),
      subst x i toSub (var y n) = (if ((y =? x)%string && Nat.eqb n i)%bool then toSub else var y n).
  Parameter subst_const : forall s1 s2 i t, subst s1 i t (const s2) = const s2.
  Parameter subst_pair : forall s i t t1 t2,
      subst s i t (pair t1 t2) = pair (subst s i t t1) (subst s i t t2).
  Parameter beta : forall s t1 t2, app (lam s t1) t2 = subst s 0 t2 t1.
  Parameter betapi1 : forall t1 t2, pi1 (pair t1 t2) = t1.
  Parameter betapi2 : forall t1 t2, pi2 (pair t1 t2) = t2.
  Parameter eta : forall (s : string) (t : QTerm), t = lam s (app (lift s 0 t) (var s 0)).
  Parameter alpha : forall (s1 s2 : string) (t : QTerm),
      lam s1 t = lam s2 (subst s1 0 (var s2 0) t).

  Parameter subst_id : forall s i t, subst s i (var s i) t = t.
  Parameter subst_lift : forall s i t1 t2, subst s i t1 (lift s i t2) = t2.
  Parameter consistency : exists (t1 t2 : QTerm), not (t1 = t2).
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
Definition lift s i := QTerm.map (lift s i) (lift_cong s i).
Definition subst s i := QTerm.map2 (subst s i) (subst_cong s i).
Definition pair := QTerm.map2 pair pair_cong.
Definition pi1 := QTerm.map pi1 pi1_cong.
Definition pi2 := QTerm.map pi2 pi2_cong.
Definition const s := QTerm.mk (constant s).

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

Theorem lift_lam : forall (s1 s2 : string) (i : nat) (t : QTerm),
      lift s1 i (lam s2 t) = lam s2 (lift s1 (if eqb s1 s2 then S i else i) t).
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

Theorem lift_app : forall s i t1 t2, lift s i (app t1 t2) = app (lift s i t1) (lift s i t2).
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

Theorem lift_var : forall (s1 s2 : string) (i k : nat),
    lift s1 k (var s2 i) = (if andb (s1 =? s2)%string (negb (Nat.ltb i k)) then var s2 (S i) else var s2 i).
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
        (if (s1 =? s2)%string
         then lam s1 (subst s2 (S i) (lift s1 0 t2) t1)
         else lam s1 (subst s2 i (lift s1 0 t2) t1)).
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

Theorem betapi1 : forall t1 t2, pi1 (pair t1 t2) = t1.
Proof.
  intros.
  unfold pi1, pair.
  quotient_map_eq_simpl.
  apply betapi1.
Qed.

Theorem betapi2 : forall t1 t2, pi2 (pair t1 t2) = t2.
Proof.
  intros.
  unfold pi2, pair.
  quotient_map_eq_simpl.
  apply betapi2.
Qed.

Theorem eta : forall s t, t = (lam s (app (lift s 0 t) (var s 0))).
Proof.
  intros.
  unfold lam, app, lift, var.
  quotient_map_eq_simpl.
  apply eta.
Qed.

Theorem lift_internal_const : forall s i c, lift s i (QTerm.mk (term.const c)) = QTerm.mk (term.const c).
Proof.
  intros.
  unfold lift, const.
  quotient_map_eq_simpl.
  apply lift_const.
Qed.

Theorem lift_const : forall s1 s2 i, lift s1 i (const s2) = const s2.
Proof.
  intros.
  apply lift_internal_const.
Qed.

Lemma subst_internal_const : forall s1 i c t, subst s1 i t (QTerm.mk (term.const c))
                                               = QTerm.mk (term.const c).
Proof.
  intros.
  unfold subst, const.
  quotient_map_eq_simpl.
  apply subst_const.
Qed.

Theorem subst_const : forall s1 s2 i t, subst s1 i t (const s2) = const s2.
Proof.
  unfold const.
  intros.
  apply subst_internal_const.
Qed.

Lemma pair_def : forall t1 t2,
    pair t1 t2 = app (app (QTerm.mk (term.const pairc)) t1) t2.
Proof.
  intros.
  unfold pair, app, term.pair.
  quotient_map_eq_simpl.
  apply conv_refl.
Qed.

Theorem subst_pair : forall s i t t1 t2,
    subst s i t (pair t1 t2) = pair (subst s i t t1) (subst s i t t2).
Proof.
  intros.
  repeat rewrite pair_def.
  repeat rewrite subst_app.
  rewrite subst_internal_const.
  reflexivity.
Qed.

Theorem lift_pair : forall s i t1 t2,
    lift s i (pair t1 t2) = pair (lift s i t1) (lift s i t2).
Proof.
  intros.
  repeat rewrite pair_def.
  repeat rewrite lift_app.
  rewrite lift_internal_const.
  reflexivity.
Qed.
  
Theorem subst_id : forall s i t, subst s i (var s i) t = t.
Proof.
  intros.
  unfold subst, var.
  quotient_map_eq_simpl.
  apply subst_id.
Qed.

Theorem subst_lift : forall s i t1 t2, subst s i t1 (lift s i t2) = t2.
Proof.
  intros.
  unfold subst, lift.
  quotient_map_eq_simpl.
  apply subst_lift.
Qed.

Theorem consistency : exists (t1 t2 : QTerm), not (t1 = t2).
Proof.
  pose consistency as consistent.
  destruct consistent as [t1 H].
  destruct H as [t2 p].
  exists (QTerm.mk t1).
  exists (QTerm.mk t2).
  intro eq.
  apply p.
  apply QTerm.complete.
  apply eq.
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
Notation "t1 [ s ]" := (lift s 0 t1) (in custom term_term at level 40,
                                       t1 custom term_term,
                                       s custom term_name) : term_scope.
Notation "t1 , t2" := (pair t1 t2) (in custom term_term at level 30,
                                       t1 custom term_term,
                                       t2 custom term_term) : term_scope.
Notation "'pi1' t" := (pi1 t) (in custom term_term at level 35,
                                  t custom term_term, only parsing) : term_scope.
Notation "'pi2' t" := (pi2 t) (in custom term_term at level 35,
                                  t custom term_term, only parsing) : term_scope.

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
Even though none of the other notations (all defined above in the same way) work for printing.
But in other files, it doesn't work, so I need these.*)
Notation "t [ s ]" := (lift s 0 t) (at level 300, only printing).
Notation "t1 [ s / t2 ]" := (subst s 0 t2 t1) (at level 300, only printing).
Notation "( t1 , t2 )" := (pair t1 t2) (at level 30, only printing).

Notation "'pi1' t" := (Lambda.pi1 t) (at level 35, only printing).
Notation "'pi2' t" := (Lambda.pi2 t) (at level 35, only printing).

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
 
Compute <pi2 (a , b)>.

