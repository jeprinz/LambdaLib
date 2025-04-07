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

Require Import partial.

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

(* I will test writing a partial function with match on Qterms
   that sends (A x) => x  and otherwise B *)

Check Pmatch.
Definition test_function_1 (t : QTerm) : Partial QTerm.
  refine (Pmatch (fun x => t = <A `x>) _ (fun x => Preturn x) (Preturn <B>)).
  intros.
  solve_all.
Defined.

Theorem run_test_function_1_1 : test_function_1 <A C> = Preturn <C>.
Proof.
  unfold test_function_1.
  evaluate_function solve_all.
  reflexivity.
Qed.

Theorem run_test_function_1_2 : test_function_1 <C> = Preturn <B>.
Proof.
  unfold test_function_1.
  evaluate_function solve_all.
  reflexivity.
Qed.

(*
Ok, now a function which uses both match and general recursion
f (A x) = B (f x)
f C = D
 *)

Definition test_function_2 : QTerm -> Partial QTerm.
  refine ().
