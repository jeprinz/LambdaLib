Require Import String.
Require Import qterm.
Require Import lambdaSolve.


(*
Here I will use the library to define dependent type theory.
For now, I'll just do type : type.
*)

(*
Notation "t1 [ s / t2 ]" := (subst s 0 t2 t1) (in custom term_term at level 40,
                                                  t1 custom term_term,
                                                  t2 custom term_term,
                                                  s custom term_name) : term_scope.

Notation "'fun' x => y" := (lam x y)
                             (in custom term_term at level 200,
                                 x custom term_name,
                                 y custom term_term at level 200,
                                 left associativity).
*)
Definition t1 : QTerm := <x>.
Compute <fun env => (`t1 env) (`t1 env)>.
Notation "( x : y ) => z" := (*(app (var "Pi" 0) <`y (fun `x => `z)>)*)
  (pair (pair (var "Pi" 0) y) (lam x z))
    (in custom term_term at level 100,
        x custom term_name).

Notation "( x : y ) => z" := (*(app (var "Pi" 0) <`y (fun `x => `z)>)*)
  (pair (pair (var "Pi" 0) y) (lam x z))
    (at level 100).


Locate "+++".
Compute < (x : y) => z>.

Theorem test1
        (t1 t2 : QTerm)
        (H : <(x : A) => `t1 [x]> = <(x : B) => `t2 [x]>)
  : t1 = t2.
Proof.
  lambda_solve.
Qed.
(* This doesn't work anymore *)

Compute <fun env => (`t1 env) (`t1 env)>.


Notation "'sapp' t1 t2" := <fun env => (`t1 env) (`t2 env)>.
