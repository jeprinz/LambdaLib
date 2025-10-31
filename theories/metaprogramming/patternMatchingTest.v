Require Import String.
Require Import qterm.
Require Import lambdaFacts.
Require Import lambdaSolve.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

(*
the goal of this file is to test if pattern matching works.
i know already that there will be a transport hell issue.
instead, i'm going to try to prove something by pattern matching that shouldn't
get stuck on that

TODO: what thing, maybe pulling a body from a lambda? is that already in substitution.v?

*)

Definition pair := <fun t1 => fun t2 => fun p => p t1 t2>.
Notation "t1 , t2" := <`pair `t1 `t2> (in custom term_term at level 30,
                                       t1 custom term_term,
                                             t2 custom term_term) : term_scope.

Notation "'proj1' t" := <`t (fun x => fun y => x)> (in custom term_term at level 35,
                                  t custom term_term, only parsing) : term_scope.
Notation "'proj2' t" := <`t (fun x => fun y => y)> (in custom term_term at level 35,
                                  t custom term_term, only parsing) : term_scope.

(* Contexts *)
Definition nil := <Nil>.
Definition cons := <fun ctx => fun lvl => fun ty => Cons ctx lvl ty>.

(* Variables *) 
Definition zero := <fun env => proj2 env>.
Definition succ := <fun x => fun env => x (proj1 env)>.

Definition pi := <fun x => fun y => fun env => Pi (x env) (fun a => y (env , a))>.
Definition U : QTerm := <fun env => U>.
Definition Empty := <fun env => Empty>.
Definition Bool := <fun env => Bool>.
Definition Lift := <fun T => fun env => Lift (T env)>.

Definition var_to_term := <fun x => x>.
Definition lambda := <fun t => fun env => fun a => t (env , a)>.
Definition app := <fun t1 => fun t2 => fun env => (t1 env) (t2 env)>.
Definition true := <fun env => fun p => proj1 p>.
Definition false := <fun env => fun p => proj2 p>.
Definition ifexpr := <fun cond => fun t1 => fun t2 => fun env => (cond env) (t1 env , t2 env)>.

Definition weaken := <fun t => fun env => t (proj1 env)>.
Definition subLast := <fun t => fun toSub => fun env => t (env , (toSub env))>.

Ltac unfold_all := unfold nil, cons, zero, succ, pi, U, Bool, Empty, var_to_term, lambda,
    app, weaken, subLast, true, false, ifexpr, Lift, pair in *.

(* The deeper shallow embedding *)

Inductive VarTyped : QTerm -> nat -> QTerm -> QTerm -> Prop :=
| ty_zero : forall ctx T lvl, VarTyped <`cons `ctx {const (term.nconst lvl)} `T> lvl <`weaken `T> zero
| ty_succ : forall ctx A T s lvl1 lvl2, VarTyped ctx lvl1 A s
                              -> VarTyped <`cons `ctx `lvl2 `T> lvl1 <`weaken `A> <`succ `s>.

Inductive Typed : (*context*) QTerm -> (*level*) nat -> (*Type*) QTerm -> (*Term*) QTerm -> Prop :=
| ty_lambda : forall ctx A B s lvl,
    Typed ctx (S lvl) <`U> <`pi `A `B> ->
    Typed <`cons `ctx {const (term.nconst lvl)} `A> lvl B s -> Typed ctx lvl <`pi `A `B> <`lambda `s>
| ty_app : forall ctx A B s1 s2 lvl, Typed ctx lvl <`pi `A `B> s1 -> Typed ctx lvl A s2
                                 -> Typed ctx lvl <`subLast `B `s2> <`app `s1 `s2>
| ty_var : forall ctx T t lvl, VarTyped ctx lvl T t -> Typed ctx lvl T t
| ty_true : forall ctx, Typed ctx 0 Bool true
| ty_false : forall ctx, Typed ctx 0 Bool false
| ty_if : forall ctx T cond t1 t2 lvl,
    Typed ctx lvl Bool cond ->
    Typed ctx lvl <`subLast `T `true> t1 ->
    Typed ctx lvl <`subLast `T `false> t2 ->
    Typed ctx lvl <`subLast `T `cond> <`ifexpr `cond `t1 `t2>
| ty_Empty : forall ctx, Typed ctx 1 <`U> Empty
| ty_Bool : forall ctx, Typed ctx 1 <`U> Bool
| ty_pi : forall ctx A B lvl,
    Typed ctx (S lvl) <`U> A
    -> Typed <`cons `ctx {const (term.nconst lvl)} `A> (S lvl) <`U> B -> Typed ctx (S lvl) <`U> <`pi `A `B>
| ty_U : forall ctx lvl, Typed ctx (S (S lvl)) <`U> <`U>
| ty_Lift : forall ctx lvl T, Typed ctx (S lvl) <`U> T -> Typed ctx (S (S lvl)) <`U> <`Lift `T>
| ty_lift : forall ctx lvl T t, Typed ctx lvl T t -> Typed ctx (S lvl) <`Lift `T> t
| ty_lower : forall ctx lvl T t, Typed ctx (S lvl) <`Lift `T> t -> Typed ctx lvl T t
.
