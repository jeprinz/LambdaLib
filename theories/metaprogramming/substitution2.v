Require Import String.
Require Import qterm.
Require Import lambdaFacts.
Require Import lambdaSolve.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

(*
In this version, I'm going to try using a single cast going directly between types
with no index.
I'm trying the approach pull_through_1 from pull_transport_through_2.v
The idea is that it will use solve_all to prove the indices equal.
*)

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
  (* extendSub : Sub ctx1 ctx2 -> Term ctx1 T -> Sub (ctx1, T) ctx2 *)
  Definition extendSub := <fun sub => fun t => fun env => (sub env, t (sub env))>.
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

Ltac solve_all := repeat (try S.unfold_all ;
                          try lambda_solve ;
                          (repeat neutral_inj_case ; lambda_solve);
                          (repeat fast_neutral_unequal_case);
                          (repeat simple_pattern_case);
                          (repeat pair_pattern_case; subst);
                          hide_evars;
                          rewrite <- ?eta, <- ?SP;
                          sort_lifts;
                          unhide_evars).

Definition cast {x y : Type} {p : x = y} : x -> y.
Proof.
  intros.
  subst.
  assumption.
Defined.

Axiom uip : forall T (t1 t2 : T) (p1 p2 : t1 = t2), p1 = p2.

Theorem remove_cast
        (T : Type)
        (p : T = T)
        (input : T)
        : @cast _ _ p input = input.
Proof.
  rewrite (uip _ _ _ p eq_refl).
  reflexivity.
Qed.

Definition Ren (sub ctx1 ctx2 : QTerm) : Type :=
  forall {lvl T t}, Var ctx1 lvl T t -> Var ctx2 lvl <`S.subTerm `sub `T> <`S.subTerm `sub `t>.

Definition idRen {ctx} : Ren S.idSub ctx ctx.
  refine (fun lvl T t x => cast x); solve_all.
Defined.

Definition liftRen {ctx1 ctx2 lvl T sub} (ren : Ren sub ctx1 ctx2)
  : Ren <`S.liftSub `sub> <`S.cons `ctx1 `lvl `T> <`S.cons `ctx2 `lvl (`S.subTerm `sub `T)>.
intros lvl2 T2 t2 x.
remember <`S.cons `ctx1 `lvl `T> as ctx in x.
generalize dependent Heqctx.
refine (match x with
        | zero  => fun _ => cast zero
        | succ x' => fun _ => cast (succ (ren _ _ _ (cast x')))
        end); solve_all.
Defined.

Definition weaken1Ren {ctx lvl T}
  : Ren S.weaken1Ren ctx <`S.cons `ctx `lvl `T>.
unfold Ren.
intros lvl' T' t' x.
refine (cast (succ x)); solve_all.
Defined.
(*
So the above works. However, somewhere deep in a solve_all, it uses reflexivity to solve a goal
like
?x [x] (`t1 [x] x) = `t2 [x] (`t1 [x] x)
where `t1 and `t2 are rocq "metavariables", and ?x is an evar.
I'm not sure if this is correct, since the evar wasn't exactly "forced" to have the value `t2.
*)

Fixpoint renTerm {ctx1 ctx2 sub lvl T t} (ren : Ren sub ctx1 ctx2)
           (prog : Typed ctx1 lvl T t) : Typed ctx2 lvl <`S.subTerm `sub `T> <`S.subTerm `sub `t>.
generalize dependent ren.
refine (match prog with
        | lambda t => fun ren => cast (lambda (renTerm _ _ _ _ _ _ (liftRen ren) t))
        | var x => fun ren => var (ren _ _ _ (cast x))
        | true => fun _ => cast true
        | false => fun _ => cast false
        end ); solve_all.
Defined.

Definition run_ren_1_statement : Prop.
  refine (renTerm (@idRen S.nil) true = cast true); solve_all.
Defined.  
Theorem run_ren_1 : run_ren_1_statement.
Proof.
  unfold run_ren_1_statement.
  simpl.
  Fail reflexivity.
Abort.

Check @cast.

Theorem compose_cast
        (A B C : Type)
        (p1 : A = B)
        (p2 : B = C)
        (input : A)
  : @cast _ _ p2 (@cast _ _ p1 input) = @cast _ _ (eq_trans p1 p2) input.
Proof.
  subst.
  reflexivity.
Qed.


Definition run_ren_1_statement' : Prop.
  refine (cast (renTerm (@idRen S.nil) true) = true); solve_all.
Defined.
Theorem run_ren_1' : run_ren_1_statement'.
Proof.
  unfold run_ren_1_statement'.
  simpl.
  rewrite compose_cast.
  rewrite remove_cast.
  reflexivity.
Qed.

(*
Trying applying a renaming to a term.
renaming = succ, starting with a context with 1 free variable
term = \x0. x1
should get renamed into \x0. x2
*)

(* TODO: solve_all should be able to infer the type, term, and level indices.
 can I get rocq to allow me to leave those as evars? *)
Definition prog1 : Typed <`S.cons `S.nil {const 0} `S.Bool> 0
                         <`S.pi `S.Bool `S.Bool>
                     <`S.lambda (`S.var_to_term (`S.succ `S.zero))>.
refine (cast (lambda (var (succ zero)))); solve_all.
Defined.

Definition prog2 : Typed <`S.cons (`S.cons `S.nil {const 0} `S.Bool) {const 0} `S.Bool> 0
                         <`S.pi `S.Bool `S.Bool>
                     <`S.lambda (`S.var_to_term (`S.succ (`S.succ `S.zero)))>.
refine (cast (lambda (var (succ (succ zero))))); solve_all.
Defined.


Axiom eq_cheat : forall {T} {x y : T}, x = y.
Axiom replace_eq : forall T (x y : T) (p : x = y), p = eq_cheat.
Import HiddenMark.
Theorem compact_cast
        (A B : Type)
        (p : A = B)
        (input : A)
  : @cast _ _ p input
    = ((Mark (@cast)) _ _ eq_cheat input).
Proof.
  rewrite (replace_eq _ _ _ p).
  rewrite MarkIsJustId.
  reflexivity.
Qed.

Ltac garbage_compact := repeat rewrite compact_cast;
                        repeat rewrite MarkIsJustId.

Theorem pull_cast_through
        (I : Type)
        (P Q : I -> Type)
        (f : forall {i}, P i -> Q i)
        (i1 i2 : I)
        (pin : P i1 = P i2)
        (realp : i1 = i2)
        (input : P i1)
  : f (@cast _ _ pin input) = @cast _ _ (f_equal Q realp) (f input).
Proof.
  subst.
  rewrite (uip _ _ _ pin eq_refl).
  reflexivity.
Qed.

Check pull_cast_through.
Search sigT.

Import SigTNotations.
Check fst.
Check @renTerm.
Definition renTerm' {args : {ctx1 : QTerm & {ctx2 : QTerm & {sub : QTerm & {lvl : nat &                                              {T : QTerm & {t : QTerm & Ren sub ctx1 ctx2}}}}}}}
           (prog : Typed (args .1) (args .2 .2 .2 .1) (args .2 .2 .2 .2 .1) (args .2 .2 .2 .2 .2 .1))
  : Typed (args .2 .1) (args .2 .2 .2 .1) <`S.subTerm {args .2 .2 .1} {args .2 .2 .2 .2 .1}>
      <`S.subTerm {args .2 .2 .1} {args .2 .2 .2 .2 .2 .1}> :=
  @renTerm (args .1) (args .2 .1) (args .2 .2 .1) (args .2 .2 .2 .1) (args .2 .2 .2 .2 .1)
           (args .2 .2 .2 .2 .2 .1) (args .2 .2 .2 .2 .2 .2) prog.

Definition run_ren_2_statement : Prop.
  refine (cast (renTerm' (_ ; (_ ; (_ ; (_ ; (_ ; (_ ; weaken1Ren)))))) prog1) = prog2); solve_all.
Defined.


Theorem run_ren_2 : run_ren_2_statement.
Proof.
  unfold run_ren_2_statement, prog1, prog2.
  Check (@renTerm).
  Check (fun ctx lvl ty tm => @renTerm ctx _ _ lvl ty tm weaken1Ren).
  garbage_compact.
  Check pull_cast_through.
  match goal with
  | |- context [?f (cast ?arg)] => idtac f
  end.
  rewrite (@pull_cast_through _ _ _
               (fun i => @renTerm (fst (fst i)) _ _ (snd (fst i)) (fst (snd i)) (snd (snd i)) weaken1Ren)).
(*                 (fun ctx lvl ty tm => @renTerm ctx _ _ lvl ty tm weaken1Ren)).*)
  simpl.
  garbage_compact.
  repeat rewrite compose_cast.
  unfold weaken1Ren.
  garbage_compact.
  Check @succ.
  repeat rewrite (@push_transport_through_var _ _ _ _
                                              (fun ctx lvl ty tm => @succ ctx ty _ tm lvl _)).
  repeat rewrite compose_castVar.
  rewrite (@push_transport_through_var_term _ _ _ _
                                            (fun ctx lvl ty tm => @var ctx ty tm lvl)).
