
Require Import String.
Require Import qterm.
Require Import lambdaFacts.
Require Import lambdaSolve.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Definition nil := <Nil>.
Definition cons := <fun ctx => fun lvl => fun ty => Cons ctx lvl ty>.

Definition zero := <fun env => proj2 env>.
Definition succ := <fun x => fun env => x (proj1 env)>.

Definition level (n : nat) : QTerm := const n.
(* Should I have an explicit type level on the pis? *)
Definition pi := <fun x => fun y => fun env => Pi (x env) (fun a => y (env , a))>.
Definition U : QTerm := <(*fun lvl => *)fun env => U (*lvl*)>.
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

Ltac unfold_all := unfold nil, cons, zero, succ, pi, U, Bool, Empty, var_to_term, lambda,
    app, weaken, subLast, level, true, false, ifexpr, Lift in *.

(* The deeper shallow embedding *)

Inductive VarTyped : QTerm -> nat -> QTerm -> QTerm -> Prop :=
| ty_zero : forall ctx T lvl, VarTyped <`cons `ctx {const lvl} `T> lvl <`weaken `T> zero
| ty_succ : forall ctx A T s lvl1 lvl2, VarTyped ctx lvl1 A s
                              -> VarTyped <`cons `ctx `lvl2 `T> lvl1 <`weaken `A> <`succ `s>.

Inductive Typed : (*context*) QTerm -> (*level*) nat -> (*Type*) QTerm -> (*Term*) QTerm -> Type :=
| ty_lambda : forall {ctx A B s lvl},
    (*Typed ctx (S lvl) <`U(*{const lvl}*)> <`pi `A `B> ->*)
    Typed <`cons `ctx {const lvl} `A> lvl B s -> Typed ctx lvl <`pi `A `B> <`lambda `s>
(*
| ty_app : forall ctx A B s1 s2 lvl, Typed ctx lvl <`pi `A `B> s1 -> Typed ctx lvl A s2
                                 -> Typed ctx lvl <`subLast `B `s2> <`app `s1 `s2>
| ty_var : forall ctx T t lvl, VarTyped ctx lvl T t -> Typed ctx lvl T t
*)
| ty_true : forall {ctx}, Typed ctx 0 Bool true
| ty_false : forall {ctx}, Typed ctx 0 Bool false
(*
| ty_if : forall ctx T cond t1 t2 lvl,
    Typed ctx lvl Bool cond ->
    Typed ctx lvl <`subLast `T `true> t1 ->
    Typed ctx lvl <`subLast `T `false> t2 ->
    Typed ctx lvl <`subLast `T `cond> <`ifexpr `cond `t1 `t2>
| ty_Empty : forall ctx, Typed ctx 1 <`U(*{const 0}*)> Empty
| ty_Bool : forall ctx, Typed ctx 1 <`U(*{const 0}*)> Bool
| ty_pi : forall ctx A B lvl,
    Typed ctx (S lvl) <`U(*{const lvl}*)> A
    (* TODO: is S lvl correct below? *)
    -> Typed <`cons `ctx {const lvl} `A> (S lvl) <`U(*{const lvl}*)> B -> Typed ctx (S lvl) <`U(*{const lvl}*)> <`pi `A `B>
| ty_U : forall ctx lvl, Typed ctx (S (S lvl)) <`U(*{const (S lvl)}*)> <`U(*{const lvl}*)>
| ty_Lift : forall ctx lvl T, Typed ctx (S lvl) <`U> T -> Typed ctx (S (S lvl)) <`U> <`Lift `T>
| ty_lift : forall ctx lvl T t, Typed ctx lvl T t -> Typed ctx (S lvl) <`Lift `T> t
| ty_lower : forall ctx lvl T t, Typed ctx (S lvl) <`Lift `T> t -> Typed ctx lvl T t
*)
.

Ltac solve_no_unfold := repeat (lambda_solve ; repeat neutral_inj_case ;lambda_solve
                  ; repeat fast_neutral_unequal_case). 

Ltac solve_all := repeat (unfold_all ; lambda_solve ; repeat neutral_inj_case ;lambda_solve
                          ; repeat fast_neutral_unequal_case; repeat simple_pattern_case;
                          repeat pair_pattern_case; subst).


Definition cast {ctx1 ctx2 lvl1 lvl2 ty1 ty2 tm1 tm2}
           {_ : ctx1 = ctx2}
           {_ : lvl1 = lvl2}
           {_ : ty1 = ty2}
           {_ : tm1 = tm2}
           (prog : Typed ctx1 lvl1 ty1 tm1) : Typed ctx2 lvl2 ty2 tm2.
  subst.
  apply prog.
Defined.

Definition match_on_id {ctx T t: QTerm} {lvl} (prog : Typed ctx lvl T t)
  :
  ctx = nil
  -> lvl = 0
  -> T = <`pi `Bool `Bool>
  -> {t' & Typed <`cons `nil {const 0} `Bool> 0 Bool t'}.
  refine (
      match prog with
      | ty_lambda t' => fun _ _ _ => (existT _ _ (cast t'))
      | _ => _ (* This catchall creates cases for all the other constructors *)
      end
    );try solve[intros; solve_all].
Defined.

(* I don't think that I can directly make a match with a notation *)
(*Notation "'fancymatch' prog 'with' cases" := (match 10 with cases end) (at level 100).*)

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

Ltac escape_transport_hell :=
  repeat (rewrite (*?push_transport_through, ?compose_transport,*) ?remove_cast).

(*Theorem match_on_id_works : match_on_id' (ty_lambda ty_true) eq_refl eq_refl eq_refl
                            = existT _ _ ty_true.
Proof.
  simpl.
  escape_transport_hell.
  reflexivity.
Qed.*)
  
Theorem push_transport_through
        (P Q : QTerm -> nat -> QTerm -> QTerm -> Type)
        (f : forall ctx lvl ty tm, P ctx lvl ty tm -> Q ctx lvl ty tm)
        (ctx1 ctx2 ty1 ty2 tm1 tm2 : QTerm)
        (lvl1 lvl2 : nat)
        (pctx : ctx1 = ctx2)
        (plvl : lvl1 = lvl2)
        (pty : ty1 = ty2)
        (ptm : tm1 = tm2)
        (input : Typed ctx1 lvl1 ty1 tm1)
  : f _ _ _ _ (@cast _ _ _ _ _ _ _ _ pctx plvl pty ptm input)
    = @cast _ _ _ _ _ _ _ _  pctx plvl pty ptm (f _ _ _ _ input).
Proof.
  refine (match p with
          | eq_refl => _
          end).
  reflexivity.
Qed.

Theorem compose_transport
        (I : Type)
        (P : I -> Type)
        (i1 i2 i3 : I)
        (p : i1 = i2)
        (q : i2 = i3)
        (input : P i1)
  : transport P q (transport P p input) = transport P (eq_trans p q) input.
Proof.
  subst.
  reflexivity.
Qed.

