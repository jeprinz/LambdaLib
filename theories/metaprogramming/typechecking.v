Require Import String.
Require Import qterm.
Require Import lambdaFacts.
Require Import lambdaSolve.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

(*
in this file, i'm making sure that typechecking will work.
the idea is that i can build up a term out of the constructors of the deep embedding,
and put casts in between when they don't directly line up.
then solve_all at the end.
the question is does this work out.

also, i need to find out what term to test this on, but for now just the simplest one.
 *)

Definition pair := <fun t1 => fun t2 => fun p => p t1 t2>.
Notation "t1 , t2" := <`pair `t1 `t2> (in custom term_term at level 30,
                                       t1 custom term_term,
                                             t2 custom term_term) : term_scope.

Notation "'proj1' t" := <`t (fun x => fun y => x)> (in custom term_term at level 35,
                                  t custom term_term, only parsing) : term_scope.
Notation "'proj2' t" := <`t (fun x => fun y => y)> (in custom term_term at level 35,
                                  t custom term_term, only parsing) : term_scope.

Module S.
  Definition nil := <Nil>.
  Definition cons := <fun ctx => fun lvl => fun ty => Cons ctx lvl ty>.

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
  Definition ifexpr := <fun cond => fun t1 => fun t2 => fun env => (cond env) (t1 env, t2 env)>.

  Definition weaken := <fun t => fun env => t (proj1 env)>.
  Definition subLast := <fun t => fun toSub => fun env => t (env , toSub env)>.

  (* Shallow substitutions *)
  Definition idSub := <fun env => env>. (* : Sub ctx ctx *)
  Definition weaken1Ren := <fun env => proj1 env>. (* : Sub ctx (ctx, T) *)
  (* liftSub : Sub ctx1 ctx2 -> Sub (cons ctx1 lvl T) (cons ctx2 lvl (subTerm sub T)) *)
  Definition liftSub := <fun sub => fun env => (sub (proj1 env), proj2 env)>.
  (* subTerm : (sub : Sub ctx1 ctx2) -> Term ctx1 T -> Term ctx2 (subTerm sub T) *)
  (* extendSub : Sub ctx1 ctx2 -> Term ctx1 T -> Sub (ctx1, T) ctx2 *)
  Definition extendSub := <fun sub => fun t => fun env => (sub env, t (sub env))>.
  Definition subTerm := <fun sub => fun t => fun env => t (sub env)>.

  Ltac unfold_all := unfold nil, cons, zero, succ, pi, U, Bool, Empty, var_to_term, lambda,
      app, weaken, subLast, true, false, ifexpr, Lift,
      idSub, weaken1Ren, liftSub, subTerm, pair in *.
End S.

(* The deeper shallow embedding *)

Inductive Var : QTerm -> nat -> QTerm -> QTerm -> Type :=
| zero : forall {ctx T lvl}, Var <`S.cons `ctx {const (term.nconst lvl)} `T> lvl <`S.weaken `T> S.zero
| succ : forall {ctx A T s lvl1 lvl2}, Var ctx lvl1 A s
                              -> Var <`S.cons `ctx `lvl2 `T> lvl1 <`S.weaken `A> <`S.succ `s>.

Inductive Typed : (*context*) QTerm -> (*level*) nat -> (*Type*) QTerm -> (*Term*) QTerm -> Type :=
| lambda : forall {ctx A B s lvl},
    (*Typed ctx (S lvl) <`U(*{const lvl}*)> <`pi `A `B> ->*)
    Typed <`S.cons `ctx {const (term.nconst lvl)} `A> lvl B s -> Typed ctx lvl <`S.pi `A `B> <`S.lambda `s>
| app : forall {ctx A B s1 s2 lvl}, Typed ctx lvl <`S.pi `A `B> s1 -> Typed ctx lvl A s2
                                  -> Typed ctx lvl <`S.subLast `B `s2> <`S.app `s1 `s2>
| ann_app : forall ctx A B s1 s2 lvl,
    Typed ctx (S lvl) S.U A
    -> Typed ctx lvl <`S.pi `A `B> s1 -> Typed ctx lvl A s2
    -> Typed ctx lvl <`S.subLast `B `s2> <`S.app `s1 `s2>
| var : forall {ctx T t lvl}, Var ctx lvl T t -> Typed ctx lvl T t
| true : forall {ctx}, Typed ctx 0 S.Bool S.true
| false : forall {ctx}, Typed ctx 0 S.Bool S.false
(*
| if : forall ctx T cond t1 t2 lvl,
    Typed ctx lvl Bool cond ->
    Typed ctx lvl <`subLast `T `true> t1 ->
    Typed ctx lvl <`subLast `T `false> t2 ->
    Typed ctx lvl <`subLast `T `cond> <`ifexpr `cond `t1 `t2>
| Empty : forall ctx, Typed ctx 1 <`U(*{const 0}*)> Empty
| Bool : forall ctx, Typed ctx 1 <`U(*{const 0}*)> Bool
| pi : forall ctx A B lvl,
    Typed ctx (S lvl) <`U(*{const lvl}*)> A
    (* TODO: is S lvl correct below? *)
    -> Typed <`cons `ctx {const lvl} `A> (S lvl) <`U(*{const lvl}*)> B -> Typed ctx (S lvl) <`U(*{const lvl}*)> <`pi `A `B>
| U : forall ctx lvl, Typed ctx (S (S lvl)) <`U(*{const (S lvl)}*)> <`U(*{const lvl}*)>
| Lift : forall ctx lvl T, Typed ctx (S lvl) <`U> T -> Typed ctx (S (S lvl)) <`U> <`Lift `T>
| lift : forall ctx lvl T t, Typed ctx lvl T t -> Typed ctx (S lvl) <`Lift `T> t
| lower : forall ctx lvl T t, Typed ctx (S lvl) <`Lift `T> t -> Typed ctx lvl T t
*)
.

Ltac solve_no_unfold := repeat (lambda_solve ; repeat neutral_inj_case ;lambda_solve
                  ; repeat fast_neutral_unequal_case). 

Ltac solve_all := repeat (S.unfold_all ; lambda_solve ; (repeat neutral_inj_case ;lambda_solve)
                          ; (repeat fast_neutral_unequal_case); (repeat simple_pattern_case);
                          hide_evars;
                          rewrite <- ?eta;
                          sort_lifts;
                          unhide_evars).


Definition cast {ctx1 ctx2 lvl1 lvl2 ty1 ty2 tm1 tm2}
           {_ : ctx1 = ctx2}
           {_ : lvl1 = lvl2}
           {_ : ty1 = ty2}
           {_ : tm1 = tm2}
           (prog : Typed ctx1 lvl1 ty1 tm1) : Typed ctx2 lvl2 ty2 tm2.
  subst.
  apply prog.
Defined.

Definition castVar {ctx1 ctx2 lvl1 lvl2 ty1 ty2 tm1 tm2}
           {_ : ctx1 = ctx2}
           {_ : lvl1 = lvl2}
           {_ : ty1 = ty2}
           {_ : tm1 = tm2}
           (prog : Var ctx1 lvl1 ty1 tm1) : Var ctx2 lvl2 ty2 tm2.
  subst.
  apply prog.
Defined.



(*
the term should be
((fun x : Bool => x) true) : Bool
*)
Definition test_typecheck_1 : Typed S.nil 0 S.Bool S.true.
  refine (cast (app (lambda (var zero)) true)); solve_all.
Defined.
