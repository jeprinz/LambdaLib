From Ltac2 Require Import Ltac2 Printf.

Require Import String.
Require Import -(coercions) qterm. (* TODO: Do I ever need the coeercion? This is very strange*)
Require Import lambdaFacts.
Require Import Lia.
Require Import lambdaSolve.

(* Using ltac2 to implement the pair case 
The goal is to be able to take an expression like
(t [x] a [y] b c)
and find t' such that
t [x] a [y] b c (l, r) = t' [x] a [y] b c l r
t can then be globally substituted for t'

specifically, we need
t' = fun a b c l r => t [a][b][c][l][r] [x] a [y] b c (l, r)
t = fun a b c p => t' [a][b][c][p] [x] a [y] b c (fst p) (snd p)
*)



Ltac2 rec test_fun (t : constr) : constr :=
  match! t with
  | (qterm.app ?t1 ?_t2) => t1
  end.

Ltac2 Type ArgLift := [Arg(constr) | Lift(constr, constr)].

Ltac2 rec pair_case_data (t : constr) : ArgLift list :=
  match! t with
  | (qterm.app ?t1 ?t2) =>
      Arg(t2) :: pair_case_data t2
  | (lift ?s ?i ?t) =>
      Lift s i :: pair_case_data t
  | ?t => []
  end
.

Ltac2 rec lift_for_each_arg (t : constr) (l : ArgLift list) : constr :=
  match l with
  | Arg(_) :: rest => lift_for_each_arg '<t [x]> rest
  | Lift _ _ :: rest => lift_for_each_arg t rest
  | [] => t
  end.

(*Ltac2 apply_lifts_and_apps (t : constr) (l : ArgLift list)*)

Print pair_case_data.
Compute ltac2:(pair_case_data '<a b c>).
    (*
  [('1, '2)].
*)

Print pair_case_data.
Ltac2 test1 := [1; 2; 3].
Print test1.
