Require Import String.
Require Import qterm.

Ltac normalize := repeat (rewrite ?beta; repeat (rewrite ?subst_app) ;
                          repeat (rewrite ?subst_lam ; simpl) ;
                          repeat (rewrite ?subst_var ; simpl) ;
                          repeat (rewrite ?lift_lam, ?lift_app, lift_var)).

(*
[ ] - add pairs and stuff to qterm
[ ] - find old file that had most advanced unification tactic
[ ] - port to this version
*)
