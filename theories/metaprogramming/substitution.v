Require Import String.
Require Import qterm.
Require Import lambdaFacts.
Require Import lambdaSolve.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Module S.
  Definition nil := <Nil>.
  Definition cons := <fun ctx => fun lvl => fun ty => Cons ctx lvl ty>.

  Definition zero := <fun env => proj2 env>.
  Definition succ := <fun x => fun env => x (proj1 env)>.

  Definition level (n : nat) : QTerm := const n.

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
  Definition subTerm := <fun sub => fun t => fun env => t (sub env)>.

  Ltac unfold_all := unfold nil, cons, zero, succ, pi, U, Bool, Empty, var_to_term, lambda,
      app, weaken, subLast, level, true, false, ifexpr, Lift,
      idSub, weaken1Ren, liftSub, subTerm in *.
End S.

(* The deeper shallow embedding *)

Inductive Var : QTerm -> nat -> QTerm -> QTerm -> Type :=
| zero : forall {ctx T lvl}, Var <`S.cons `ctx {const lvl} `T> lvl <`S.weaken `T> S.zero
| succ : forall {ctx A T s lvl1 lvl2}, Var ctx lvl1 A s
                              -> Var <`S.cons `ctx `lvl2 `T> lvl1 <`S.weaken `A> <`S.succ `s>.

Inductive Typed : (*context*) QTerm -> (*level*) nat -> (*Type*) QTerm -> (*Term*) QTerm -> Type :=
| lambda : forall {ctx A B s lvl},
    (*Typed ctx (S lvl) <`U(*{const lvl}*)> <`pi `A `B> ->*)
    Typed <`S.cons `ctx {const lvl} `A> lvl B s -> Typed ctx lvl <`S.pi `A `B> <`S.lambda `s>
(*
| app : forall ctx A B s1 s2 lvl, Typed ctx lvl <`pi `A `B> s1 -> Typed ctx lvl A s2
                                 -> Typed ctx lvl <`subLast `B `s2> <`app `s1 `s2>*)
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
                          (repeat pair_pattern_case; subst);
                          hide_evars;
                          rewrite <- ?eta, <- ?SP;
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

Axiom uip : forall T (t1 t2 : T) (p1 p2 : t1 = t2), p1 = p2.
Theorem remove_cast
        (ctx ty tm : QTerm)
        (lvl : nat)
        (pctx : ctx = ctx)
        (plvl : lvl = lvl)
        (pty : ty = ty)
        (ptm : tm = tm)
        (input : Typed ctx lvl ty tm)
        : @cast _ _ _ _ _ _ _ _ pctx plvl pty ptm input = input.
Proof.
  rewrite (uip _ _ _ pctx eq_refl).
  rewrite (uip _ _ _ plvl eq_refl).
  rewrite (uip _ _ _ pty eq_refl).
  rewrite (uip _ _ _ ptm eq_refl).
  reflexivity.
Qed.

Definition Ren (sub ctx1 ctx2 : QTerm) : Type :=
  forall {lvl T t}, Var ctx1 lvl T t -> Var ctx2 lvl <`S.subTerm `sub `T> <`S.subTerm `sub `t>.

Definition idRen {ctx} : Ren S.idSub ctx ctx.
  refine (fun lvl T t x => castVar x); solve_all.
Defined.

Definition liftRen {ctx1 ctx2 lvl T sub} (ren : Ren sub ctx1 ctx2)
  : Ren <`S.liftSub `sub> <`S.cons `ctx1 `lvl `T> <`S.cons `ctx2 `lvl (`S.subTerm `sub `T)>.
intros lvl2 T2 t2 x.
remember <`S.cons `ctx1 `lvl `T> as ctx in x.
generalize dependent Heqctx.
refine (match x with
        | zero  => fun _ => castVar zero
        | succ x' => fun _ => castVar (succ (ren _ _ _ (castVar x')))
        end); solve_all.
Defined.
(*
So the above works. However, somewhere deep in a solve_all, it uses reflexivity to solve a goal
like
?x [x] (`t1 [x] x) = `t2 [x] (`t1 [x] x)
where `t1 and `t2 are rocq "metavariables", and ?x is an evar.
I'm not sure if this is correct, since the evar wasn't exactly "forced" to have the value `t2.
*)

(*
TODO:
[ ] - implement renTerm
[ ] - see if I can get that to actually compute despite transports getting stuck
*)

Fixpoint renTerm {ctx1 ctx2 sub lvl T t} (ren : Ren sub ctx1 ctx2)
           (prog : Typed ctx1 lvl T t) : Typed ctx2 lvl <`S.subTerm `sub `T> <`S.subTerm `sub `t>.
(*dep match generalize*)
generalize dependent ren.
refine (match prog with
        | lambda t => fun ren => cast (lambda (renTerm _ _ _ _ _ _ (liftRen ren) t))
        | var x => fun ren => var (ren _ _ _ (castVar x))
        | true => fun _ => cast true
        | false => fun _ => cast false
        end ); solve_all.
Defined.
