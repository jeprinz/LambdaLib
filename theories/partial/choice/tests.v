Require Import choiceBase.
Require Import prog2.
Require Import pmatch.
Require Import automation.


Require Import String.
Require Import qterm.
Require Import lambdaFacts.
Require Import lambdaSolve.

(* I will test writing a partial function with match on Qterms
   that sends (A x) => x  and otherwise B

  f (A x) = x
  f _ = B
 *)

Ltac solve_all := repeat (lambda_solve ; repeat neutral_inj_case ;lambda_solve
                  ; repeat fast_neutral_unequal_case). 

Check Pmatch.
Definition test_function_1 (t : QTerm) : QTerm :=
  Pmatch (fun x => t = <A `x>) (fun x => x) <B>.

Theorem run_test_function_1_1 : test_function_1 <A C> = <C>.
Proof.
  unfold test_function_1.
  evaluate_function solve_all.
  reflexivity.
Qed.

Theorem run_test_function_1_2 : test_function_1 <C> = <B>.
Proof.
  unfold test_function_1.
  evaluate_function solve_all.
  reflexivity.
Qed.


(*
Ok, now a function which uses both match and general recursion
f (A x) = B (f x)
f _ = D
 *)

Definition ret {A B} := fun x => Ret A B (Some x).
Definition rec {A B} x := fun rest => Rec A B unit (fun _ => x) (fun r => rest (r tt)).


(*
Definition test_function_2 : QTerm -> option QTerm.
  Check runProg.
  Check Pmatch.
  refine (runProg (fun t =>
                     Pmatch
                       (fun x => t = <A `x>)
                       (fun x => Rec _ _ unit (fun _ => x) (fun res => Ret _ _ (Some <B {res tt}>)))
                       (Ret _ _ (Some <D>)))).
Defined.
 *)

Definition test_function_2 : QTerm -> option QTerm :=
  runProg (fun t =>
             Pmatch
               (fun x => t = <A `x>)
               (fun x => rec x (fun res => ret <B `res>))
               (ret <D>)).

(*Notation "'pmatch' t 'with' | x 'in' pattern => case1 | case2" :=
  (Pmatch (fun x => t = pattern) (fun x => case1) case2) (at level 50).

Definition test_function_2' : QTerm -> option QTerm :=
  runProg (fun t =>
             pmatch t with
             | x in <A `x> => rec x (fun res => ret <B `res>)
             | ret <D>).

Theorem run_test_function_2_1 : test_function_2' <A (A C)> = Some <B (B D)>.
Proof.
  unfold test_function_2', rec, ret.
  evaluate_function solve_all.
  reflexivity.
Qed.*)

Theorem something_bad : test_function_1 <C> = <B>.
Proof.
  unfold test_function_1, runProg.
  evaluate_function solve_all.
  easy.
Qed.  

(* now, test Pmatch2 *)

(*
f (A x y) = (x, y)
f _ _ = (D, E)
 *)
Check Pmatch.
Check Pmatch2.

Definition test_function_3 (t : QTerm) : QTerm * QTerm :=
  Pmatch2 (fun x y => t = <A `x `y>) (fun x y => (x, y)) (<D>, <E>).

Theorem run_test_function_3_1 : test_function_3 <A B C> = (<B>, <C>).
Proof.
  unfold test_function_3.
  evaluate_function solve_all.
  reflexivity.
Qed.

Theorem run_test_function_3_2 : test_function_3 <C> = (<D>, <E>).
Proof.
  unfold test_function_3.
  evaluate_function solve_all.
  reflexivity.
Qed.

(*
Ok, now a function which uses both Pmatch2 and general recursion
f (A x y) = B (f x) (f y)
f _ = D
 *)

Check Rec.
Definition test_function_4 : QTerm -> option QTerm.
  refine (
      runProg (fun t =>
             Pmatch2
               (fun x y => t = <A `x `y>)
               (fun x y => Rec _ _ bool
                               (fun b => if b then x else y)
                               (fun rec => ret <B {rec true} {rec false}>)
               )
               (ret <D>))

    ).
Defined.

Theorem run_test_function_4_1 : test_function_4 <A E F> = Some <B D D>.
Proof.
  unfold test_function_4.
  evaluate_function solve_all.
  (* SO, this demonstrates the problem! *)
  Fail Qed.
Abort.


(* a simpler demonstration of the problem: 

again,
f (A x) = B (f x)
f _ = D


but this time write the definition so it can't beta-normalize away the index family when
applied to a free variable

*)


Definition test_function_5 : QTerm -> option QTerm :=
  runProg (fun t =>
             Pmatch
               (fun x => t = <A `x>)
               (fun x => Rec _ _ unit
                             (fun u => match u with tt => x end)
                             (fun res => ret <B {res tt}>))
               (ret <D>)).

Theorem run_test_function_5_1 : test_function_5 <A (A C)> = Some <B (B D)>.
Proof.
  unfold test_function_5.
  evaluate_function solve_all.
  Check runProgDefinitionRec.
  Check PmatchDef1.
  Check @Pmatch.
  Locate "with".
  Set Printing All.
  Check Pmatch.
  Fail reflexivity.
Abort.

(*
one idea is that if i have a default case for the function, then
i don't need the option.
then i also wouldn't need collectOption.
i'll try this in prog3
*)
