Require Import String.
Require Import qterm.
Require Import lambdaFacts.



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

Theorem test_lambda_solve
        (t1 t2 : QTerm)
        (H1 : <Pi , A , fun x => `t1 [x]> = <Pi , A , fun x => `t2 [x]>)
  : <fun x => `t1[x]> = <fun y => `t2[x]>.
Proof.
  repeat lambda_solve.
  rewrite H0.
  rewrite subst_lift.
  (* Some axiom is wrong. *)
  

  
  

