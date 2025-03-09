Require Import String.
Require Import qterm.
Require Import lambdaFacts.

(*
The goal of these tactics is to reduce terms to a normal form.
In order for them to work, we need to assume that the input terms have a particular form:
All QTerms should consist of lam, app, var, pair, pi1, pi2, const, and coq variables.
Any lifts should be around a coq variable.

There should not be any lifts anywhere else or subst forms anywhere at all
except during intermediate states.
*)

Ltac compute_subst := repeat (try rewrite subst_app ;
                          try (rewrite subst_lam ; simpl) ;
                          try (rewrite subst_var ; simpl;
                               repeat (rewrite lift_lam, lift_app, lift_var))).
(* Is there a way to not have this be repetetive with the above? *)
Ltac compute_subst_in H := repeat (try rewrite subst_app ;
                          try (rewrite subst_lam in H ; simpl in H) ;
                          try (rewrite subst_var in H; simpl in H;
                                  repeat (rewrite lift_lam, lift_app, lift_var in H))).
Ltac normalize := repeat (rewrite ?beta, ?betapi1, ?betapi2; compute_subst).

(*
[x] - add pairs and stuff to qterm
[ ] - find old file that had most advanced unification tactic
[ ] - port to this version
*)

Check alpha.
Ltac proveNeutral := constructor ; repeat constructor.

Ltac lambda_solve :=
  (*repeat ( *)
      match goal with
      | H : lam ?s ?t1 = lam ?s ?t2 |- _ => apply lamInj in H
      | |- lam ?s ?t1 = lam ?s ?t2 => apply (f_equal (lam s))
      | H : lam ?s1 ?t1 = lam ?s2 ?t2 |- _ => rewrite (@alpha s1 s2 t1) in H; compute_subst_in H
      | |- lam ?s1 ?t1 = lam ?s2 ?t2 => rewrite (@alpha s1 s2 t1); compute_subst
      | H : var ?s1 0 = var ?s2 0 |- _ => apply varInj in H
      | H : @eq string ?s ?s |- _ => clear H
      | H : @eq string ?s1 ?s2 |- _ => inversion H
      | H : @eq QTerm (pair ?t1 ?t2) (pair ?t1' ?t2') |- _ => apply pairInj in H; destruct H
      | H : @eq QTerm ?t1 ?t2 |- _ => subst t1
      end
    (*)*)
.

Theorem test_lambda_solve_0
        (t : QTerm)
  : <fun x => `t> = <fun y => `t>.
Proof.
  repeat lambda_solve.
Abort. (* This shouldn't be true, because t could have x or y in it. *)

(* We need to hide Mark in a module *)
Module Type HowToHideMark.
  Parameter Mark : forall {X : Type}, X -> X. (* He hides in here where no one can see him *)
  Parameter MarkIsJustId : forall {X : Type} {x : X}, Mark x = x.
End HowToHideMark.
Module HiddenMark : HowToHideMark.
  Definition Mark {X : Type} (x : X) := x.
  Theorem MarkIsJustId {X : Type} {x : X} : Mark x = x.
  Proof.
    intros.
    reflexivity.
  Qed.
End HiddenMark.

Import HiddenMark.

Theorem mark_stuck : forall t s1 i1 s2 i2 t',
    subst s1 i1 t' (lift s2 i2 t) = subst s1 i1 t' ((Mark lift) s2 i2 t).
Proof.
  rewrite MarkIsJustId.
  reflexivity.
Qed.

Theorem swap_marked_lift : forall (s1 s2 : string) (i1 i2 : nat) (t : QTerm),
    (Mark lift) s1 i1 (lift s2 i2 t) =
      lift s2 (if (s1 =? s2)%string then S i2 else i2) ((Mark lift) s1 i1 t).
Proof.
  rewrite MarkIsJustId.
  apply lift_lift.
Qed.

Ltac fix_subst_lifts :=
  repeat (
      (* First, cancel any substs and lifts that already match*)
      repeat rewrite subst_lift;
      (* Next, mark any lifts under a subst as being the wrong one *)
      repeat rewrite mark_stuck;
      (* Next, push the marked lift down *)
      repeat (rewrite swap_marked_lift ; simpl)
    );
  (* When we are done, remove Mark *)
  repeat rewrite MarkIsJustId.


Theorem test_lambda_solve_1
        (t : QTerm)
  : <fun x => `t [x]> = <fun y => `t [y]>.
Proof.
  repeat lambda_solve.
  (* In order to be able to cancel out lifts and substitutions in general, I will need
   simultaneous lifts and substitutions. There is not a solution where we commute the subs
   and lifts past each other, because that isn't always possible.
   If I make the assumption that we only have lifts around metavariables, and that metavariables
   are always in the empty context, then I think I can get away with only having simultaneous
   lifts but not substitutions. *)
  (*
    One possible solution: write a tactic which repeatedly raised lift x through other lifts,
    and a tactic which searches for a subst around a lift and returns the x from the subst
    so that it can know which thing to looks for.
    A problem is how this would work with multiple lifts of the same name but different
    debruin indices.
    Note that you can just match on expressions however you want in LTac:
    https://softwarefoundations.cis.upenn.edu/plf-current/LibTactics.html
   *)
  fix_subst_lifts.
  Check subst_lift.
  Check alpha.
  rewrite lift_lift. simpl.
  rewrite subst_lift.
  reflexivity.
Qed.
  

Theorem test_lambda_solve
        (t1 t2 : QTerm)
        (H1 : <fun x => `t1 [x]> = <fun x => `t2 [x]>)
  : <fun x => `t1[x]> = <fun y => `t2[x]>.
Proof.
  repeat lambda_solve.
  rewrite H0.
  Check subst_lift.
  rewrite subst_lift.
  (* Some axiom is wrong. *)
  

  
  

