Require Import String.
Require Import qterm.
Require Import lambdaFacts.
Require Import lambdaSolve.


(* Can I recover first order unification on STLC types? *)

Ltac solve_all := repeat (lambda_solve ; repeat neutral_inj_case ;lambda_solve
                  ; repeat fast_neutral_unequal_case). 

Theorem test1
        (A B C : QTerm)
        :
        <Arrow `A `B> = <Arrow `B `C>
        -> A = C.
Proof.
  intros.
  solve_all.
Qed.

(* I guess obviously yes. *)
