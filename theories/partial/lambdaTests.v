(*
So Partial works successfully, but I need to make some kind of a match or case function.
I can already do a Pif with the proposition
(exists A B, t = Pi A B).
But this doesn't let me extract the A and B.
In order to extract it, I will need to prove them unique, or else its not a function.
So I will need to be able to prove:

exists A, t = Const A /\ forall A', t = Const A' -> A = A'.

Let me see how this can be done automatically with lambda_solve.
The idea is that there will be a tactic for automatically computing with this case expression
form that takes a tactic as a parameter, and that parameter will need to be able to solve
this proof.
*)

Require Import String.
Require Import qterm.
Require Import lambdaFacts.
Require Import lambdaSolve.

Ltac solve_all := repeat (lambda_solve ; repeat neutral_inj_case ;lambda_solve
                  ; repeat fast_neutral_unequal_case). 

Theorem test1 :
  let t := <Const A> in
  exists A,
    t = <Const `A> /\ forall A', t = <Const `A'> -> A = A'.
Proof.
  eexists.
  split.
  solve_all.
  intros.
  solve_all.
Qed.

Theorem test2 :
  not (exists X, <Const1 A> = <Const2 `X>).
Proof.
  intros x.
  destruct x.
  solve_all.
Qed. 
