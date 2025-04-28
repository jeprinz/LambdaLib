(* The syntax from autosubst *)
Require Import qterm.

(* There is a notation conflict. For now, I commented the notations in the
   autosubst output.*)
Require Import Syntax.
Require Import String.

Require Import lambdaFacts.
Require Import lambdaSolve.

Locate "[".
(*Global Open Scope subst_scope.*)

Require Import unscoped.

Check subst_tm.
Check scons.
Locate "[".

Inductive Typed : ctx -> nat -> tm -> tm -> Prop :=
| ty_lam : forall ctx lvl A B t,
    Typed (cons ctx lvl A) lvl B t
    -> Typed ctx lvl (pi A B) (lambda t)
| ty_app : forall ctx lvl A B t1 t2,
    Typed ctx lvl (pi A B) t1
    -> Typed ctx lvl A t2
    (*-> Typed ctx lvl (B [t1..]) (app t1 t2)*)
    -> Typed ctx lvl (subst_tm (scons t1 ids) B) (app t1 t2)
             
.






Definition qnil := <Nil>.
Definition qcons := <fun ctx => fun lvl => fun ty => Cons ctx lvl ty>.

Definition qzero := <fun env => proj2 env>.
Definition qsucc := <fun x => fun env => x (proj1 env)>.

Definition qpi := <fun x => fun y => fun env => Pi (x env) (fun a => y (env , a))>.
Definition qU : QTerm := <(*fun lvl => *)fun env => U (*lvl*)>.
Definition qEmpty := <fun env => Empty>.
Definition qBool := <fun env => Bool>.
Definition qLift := <fun T => fun env => Lift (T env)>.

Definition qvar_to_term := <fun x => x>.
Definition qlambda := <fun t => fun env => fun a => t (env , a)>.
Definition qapp := <fun t1 => fun t2 => fun env => (t1 env) (t2 env)>.
Definition qtrue := <fun env => fun p => proj1 p>.
Definition qfalse := <fun env => fun p => proj2 p>.
Definition qifexpr := <fun cond => fun t1 => fun t2 => fun env => (cond env) (t1 env, t2 env)>.

Definition qweaken := <fun t => fun env => t (proj1 env)>.
Definition qsubLast := <fun t => fun toSub => fun env => t (env , toSub env)>.

Fixpoint code (t : tm) : QTerm :=
  match t with
  | app t1 t2 => <fun env => ({code t1} env) ({code t2} env)>
  | lambda t => <`qlambda {code t}>
  | pi a b => <`qpi {code a} {code b}>
  | other => <TODO>
  end.

Fixpoint ctxcode (c : ctx) : QTerm :=
  match c with
  | nil => qnil
  | cons c' lvl tm => <`qcons {ctxcode c'} {const lvl} {code tm}>
  end.

Ltac unfold_all := unfold qnil, qcons, qzero, qsucc, qpi, qU, qBool, qEmpty, qvar_to_term, qlambda,
    qapp, qweaken, qsubLast, qtrue, qfalse, qifexpr, qLift in *.

(* The deeper shallow embedding *)

Inductive VarQTyped : QTerm -> nat -> QTerm -> QTerm -> Prop :=
| ty_zero : forall ctx T lvl, VarQTyped <`qcons `ctx {const lvl} `T> lvl <`qweaken `T> qzero
| ty_succ : forall ctx A T s lvl1 lvl2, VarQTyped ctx lvl1 A s
                              -> VarQTyped <`qcons `ctx `lvl2 `T> lvl1 <`qweaken `A> <`qsucc `s>.


Inductive QTyped : (*context*) QTerm -> (*level*) nat -> (*Type*) QTerm -> (*Term*) QTerm -> Prop :=
| qty_lambda : forall ctx A B s lvl,
    QTyped ctx (S lvl) <`qU(*{const lvl}*)> <`qpi `A `B> ->
    QTyped <`qcons `ctx {const lvl} `A> lvl B s -> QTyped ctx lvl <`qpi `A `B> <`qlambda `s>
| qty_app : forall ctx A B s1 s2 lvl, QTyped ctx lvl <`qpi `A `B> s1 -> QTyped ctx lvl A s2
                                 -> QTyped ctx lvl <`qsubLast `B `s2> <`qapp `s1 `s2>
| qty_var : forall ctx T t lvl, VarQTyped ctx lvl T t -> QTyped ctx lvl T t
| qty_true : forall ctx, QTyped ctx 0 qBool qtrue
| qty_false : forall ctx, QTyped ctx 0 qBool qfalse
| qty_if : forall ctx T cond t1 t2 lvl,
    QTyped ctx lvl qBool cond ->
    QTyped ctx lvl <`qsubLast `T `qtrue> t1 ->
    QTyped ctx lvl <`qsubLast `T `qfalse> t2 ->
    QTyped ctx lvl <`qsubLast `T `cond> <`qifexpr `cond `t1 `t2>
| qty_Empty : forall ctx, QTyped ctx 1 <`qU(*{const 0}*)> qEmpty
| qty_Bool : forall ctx, QTyped ctx 1 <`qU(*{const 0}*)> qBool
| qty_pi : forall ctx A B lvl,
    QTyped ctx (S lvl) <`qU(*{const lvl}*)> A
    (* TODO: is S lvl correct below? *)
    -> QTyped <`qcons `ctx {const lvl} `A> (S lvl) <`qU(*{const lvl}*)> B -> QTyped ctx (S lvl) <`qU(*{const lvl}*)> <`qpi `A `B>
| qty_U : forall ctx lvl, QTyped ctx (S (S lvl)) <`qU(*{const (S lvl)}*)> <`qU(*{const lvl}*)>
| qty_Lift : forall ctx lvl T, QTyped ctx (S lvl) <`qU> T -> QTyped ctx (S (S lvl)) <`qU> <`qLift `T>
| qty_lift : forall ctx lvl T t, QTyped ctx lvl T t -> QTyped ctx (S lvl) <`qLift `T> t
| qty_lower : forall ctx lvl T t, QTyped ctx (S lvl) <`qLift `T> t -> QTyped ctx lvl T t
.

Ltac solve_no_unfold := repeat (lambda_solve ; repeat neutral_inj_case ;lambda_solve
                  ; repeat fast_neutral_unequal_case). 

Ltac solve_all := repeat (unfold_all ; lambda_solve ; repeat neutral_inj_case ;lambda_solve
                          ; repeat fast_neutral_unequal_case).

Theorem canIDoThis : forall ctx lvl ty tm,
    Typed ctx lvl ty tm
    -> QTyped (ctxcode ctx) lvl (code ty) (code tm).
Proof.
  intros.
  induction H.
  - simpl.
    normalize.
    apply qty_lambda.

