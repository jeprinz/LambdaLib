From Equations Require Import Equations.

Inductive ty : Type :=
| arrow : ty -> ty -> ty
| base : ty.

Derive NoConfusion for ty.

Definition ctx := list ty.

Inductive Deriv : ctx -> ty -> Type :=
| var : forall ctx ty, List.In ty ctx -> Deriv ctx ty
| lambda : forall {ctx A B}, Deriv (cons A ctx) B -> Deriv ctx (arrow A B)
| application : forall {ctx A B}, Deriv ctx (arrow A B) -> Deriv ctx A -> Deriv ctx B
| tt : forall ctx, Deriv ctx base.

Axiom substitute : forall {ctx A B}, Deriv ctx A -> Deriv (cons A ctx) B -> Deriv ctx B.

Equations betaReduce : forall {ctx ty}, Deriv ctx ty -> Deriv ctx ty :=
betaReduce (application (lambda t1) t2) := substitute t2 t1;
betaReduce t := t.

Search (_ -> list _ -> Prop).

Theorem test (H :  2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 = 2 + 2 + 2
             + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2
             + 2 + 2 + 2 + 2 + 2 ) : 1 = 1.
Proof.
