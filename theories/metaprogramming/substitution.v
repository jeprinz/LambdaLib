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
| var : forall ctx T t lvl, Var ctx lvl T t -> Typed ctx lvl T t
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
                          ; (repeat fast_neutral_unequal_case); (repeat simple_pattern_case();
                          (repeat pair_pattern_case; subst); rewrite <- ?eta, <- ?SP)).


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

Compute (1 + ltac:(exact 2)).

Axiom hole : forall {T}, T.
(*Definition idRen {ctx} : Ren S.idSub ctx ctx := fun lvl T t x => x.*)
Definition liftRen {ctx1 ctx2 lvl T sub} (ren : Ren sub ctx1 ctx2)
  : Ren <`S.liftSub `sub> <`S.cons `ctx1 `lvl `T> <`S.cons `ctx1 `lvl (`S.subTerm `sub `T)>.
intros lvl2 T2 t2 x.
remember <`S.cons `ctx1 `lvl `T> as ctx in x.
generalize dependent Heqctx.
refine (match x with
        | @zero _ _ n => fun _ => castVar zero (*(@zero ctx1 <`S.subTerm `sub `T> n)*)
        | succ x' => hole (*castVar (succ (ren _ _ _ _))*)
        end); intros(*; solve_all*).
S.unfold_all.

(try match goal with
     | |- context [app (lam ?s ?t1) ?t2] => rewrite (@beta s t1 t2)
     | |- context [pi1 (pair ?t1 ?t2)] => rewrite (@betapi1 t1 t2)
     | |- context [pi2 (pair ?t1 ?t2)] => rewrite (@betapi2 t1 t2)
     end;
 compute_subst).
(try match goal with
     | |- context [app (lam ?s ?t1) ?t2] => rewrite (@beta s t1 t2)
     | |- context [pi1 (pair ?t1 ?t2)] => rewrite (@betapi1 t1 t2)
     | |- context [pi2 (pair ?t1 ?t2)] => rewrite (@betapi2 t1 t2)
     end).
repeat (
    try match goal with
        | |- context [subst ?s ?i ?t3 (app ?t1 ?t2)] => rewrite (@subst_app s i t1 t2 t3)
        | |- context [subst ?s ?i ?t (pair ?t1 ?t2)] => rewrite (@subst_pair s i t t1 t2)
        | |- context [subst ?s ?i ?t1 (pi1 ?t2)] => rewrite (@subst_pi1 s i t1 t2)
        | |- context [subst ?s ?i ?t1 (pi2 ?t2)] => rewrite (@subst_pi2 s i t1 t2)
        | |- context [subst ?s2 ?i ?t2 (lam ?s1 ?t1)] =>
            rewrite (@subst_lam s1 s2 i t1 t2); simpl; compute_lifts
        | |- context [subst ?s1 ?k ?toSub (var ?s2 ?i)] =>
            rewrite (@subst_var s1 s2 k i toSub); simpl
        end;
    compute_lifts).
fix_subst_lifts.

normalize.


refine (castVar zero).
S.unfold_all.
Print normalize.

Print hide_evars_in_goal.
Fail match goal with
| |- context [ ?v : QTerm ] => idtac v; is_evar v; (let H := fresh v in
                                                    pose (H := v); fold H)
end.

pose (H := ?Goal3).
repeat (rewrite ?beta, ?betapi1, ?betapi2; compute_subst).
unhide_evars_in_goal.

Check ren.
Compute (Ren sub ctx1 ctx2).
Check (succ (ren _ _ _ x')).
rewrite <- SP.

(*
I can potentially fix solve_all to work around metavariables in the goal.
But, also I can prevent there from being metavariables in the first place by giving arguments
to "zero".
*)


(* normalize nonterminates here. Why? *)

Print solve_all.
S.unfold_all.
Set Printing Goal Names.
Unshelve.

(*
It appears that in practice, the evars only show up in the goal, not the context.
*)

repeat rewrite beta.
rewrite subst_lam.
simpl.
(* TODO: right here is the point where I need to figure out what is going on
with existential variables. Try running the next two tactics. *)


rewrite lift_lam.
simpl.

repeat
   (try (rewrite lift_lam; simpl); try rewrite lift_app; try rewrite lift_pair; try rewrite lift_pi1;
     try rewrite lift_pi2; try (rewrite lift_var; simpl)).


(*
1) when you run solve when there are term metavariables, it nonterminates because it just keeps
   refining the metavaraibles with every rewrite.
2) But why even are there term metavariables? The idea of cast is that it should be specifically
   the equality proofs that are left for later. Everything else should be defined in the refine.
   So what is causing these terms to be left unspecified?
*)
