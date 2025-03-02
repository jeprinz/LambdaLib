Require Import String.
Require Import qterm.
Require Import lambdaFacts.



Ltac compute_subst := repeat (try rewrite subst_app ;
                          try (rewrite subst_lam ; simpl) ;
                          try (rewrite subst_var ; simpl;
                               repeat (rewrite lift_lam, lift_app, lift_var))).
(* Is there a way to not have this be repetetive with the above? *)
Ltac compute_subst_in H := repeat (try rewrite subst_app ;
                          try (rewrite subst_lam in H ; simpl) ;
                          try (rewrite subst_var in H; simpl;
                                  repeat (rewrite lift_lam, lift_app, lift_var in H))).
Ltac normalize := repeat (rewrite beta; compute_subst).

(*
[x] - add pairs and stuff to qterm
[ ] - find old file that had most advanced unification tactic
[ ] - port to this version
*)

Ltac proveNeutral := constructor ; repeat constructor.

Ltac lambda_solve :=
  repeat (
      match goal with
      | H : 

