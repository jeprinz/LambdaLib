Require Import String.
Require Import qterm.
Require Import lambdaFacts.
Require Import lambdaSolve.


(*
Can I define partial functions over lambda calculus terms with equations
if I can prove that the inputs don't overlap?
Or does it only work with elements of an inductive type?
*)

From Coq Require Import Arith Program.
From Equations Require Import Equations.


Equations neg (b : bool) : bool :=
neg true := false ;
neg false := true.

Fail Equations test (t : QTerm) : nat :=
  test (var "a"%string 0) := 0.



(* No, it doesn't work. It wants a constructor. *)

(*
Maybe I can define my own way of defining partial functions?
 *)

Inductive Inhabited {T : Type} (set : T -> Prop) : Prop :=
| squash : forall (t : T), set t -> Inhabited set
.

Record Partial (T : Type) : Type := {
    elem : T -> Prop;
    inhabited : Inhabited elem;
    unique : forall t1 t2, elem t1 -> elem t2 -> t1 = t2
  }.

Theorem bind (A B : Type) (f : A -> Partial B) (a : Partial A) : Partial B.
Proof.
  refine {|
      elem := fun b => forall x, elem _ a x -> elem _ (f x) b
    ;
      inhabited := _
    ;
      unique := _
    |}.
  (* inhabited *)
  destruct (inhabited _ a).
  destruct (inhabited _ (f t)).
  eapply squash.
  intros.
  destruct (inhabited _ (f x)).
  apply H2.
  apply t0.
  (* unique *)
  intros.
  destruct (inhabited _ a).
  destruct (inhabited _ (f t)).
  specialize (H t).
  apply (unique (f x)).

Theorem bind (A B : Type) (f : A -> Partial B) (a : Partial A) : Partial B.
Proof. 
  refine {|elem := _; unique := _|}.
  Unshelve.
  2: {
    intro b.
    Check (elem (f a)).
    apply (elem f).
    

Record FunSpec (A B: Type) : Type := {
    X : Type;
    lhs : X -> A;
    rhs : (A -> Partial B) -> X -> Partial B;
    unique_lhs : forall a1 a2, lhs a1 = lhs a2 -> a1 = a2
  }.

(*
Actually, there is no need for all that. It should be possible to just define:
partialIf : Prop -> A -> A -> Partial A
that just does "if" except with a proposition.
Also, define
fixpoint : (A -> Partial A) -> Partial A
or maybe instead,
fixpoint : ((A -> Partial B) -> A -> Partial B) -> A -> Partial B
 *)

Theorem propIf : forall A, Prop -> A -> A -> Partial A.
Proof.

Inductive Graph (A B : Type) (spec : FunSpec A B) : Prop :=
| call : forall ,
    
.
