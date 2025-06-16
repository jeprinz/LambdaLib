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
                          ; repeat fast_neutral_unequal_case).

From Equations.Prop Require Import Equations.

(*
Definition defer_cast {ctx ty1 ty2 t1 t2 : QTerm} {lvl} {pty : ty1 = ty2} {pt : t1 = t2}
  (prog : Typed ctx lvl ty1 t1) : Typed ctx lvl ty2 t2.
  subst.
  apply prog.
Defined.
 *)
Definition defer_cast {A B : Type} {p : A = B} (a : A) : B.
  subst.
  apply a.
Defined.

Equations silly_transform_eq {ctx T t : QTerm} {lvl : nat} (prog : Typed ctx lvl T t) : Typed ctx lvl T t :=
silly_transform_eq ty_true := defer_cast ty_false;
silly_transform_eq prog := prog.

Next Obligation.
Proof.
Abort.
(*
Equations match_on_id {t : QTerm} (prog : Typed nil 2 <`pi `U `U> t) : {t' & Typed <`cons {const 1} `U> 2 U t'} :=
  match_on_id (ty_lambda t') := _;
  match_on_id ty_true := _;
  match_on_id ty_false := _.
*)
Definition silly_transform {ctx T t : QTerm} {lvl : nat} (prog : Typed ctx lvl T t) : Typed ctx lvl T t.
  refine (
      match prog in Typed ctx lvl T t return Typed ctx lvl T t with
      | ty_true => defer_cast ty_false
      | t => t
      end
    ); try solve_all.
Abort.

(* So that actually kind of works. *)

Definition match_on_id' {t : QTerm} (prog : Typed nil 2 <`pi `U `U> t) : {t' & Typed <`cons {const 1} `U> 2 U t'}.
  (*remember <`pi `U `U> as in_type.*)

  refine (
      match prog in Typed x1 x2 x3 x4 return {t' & Typed <`cons {const 1} `U> 2 U t'} with
      | ty_true => _
      | ty_false => _
      | ty_lambda t' => _
      end
    ).
Abort.
Check lift.
Theorem testOneDirectionAtLeast
        (t1 t2 : QTerm) (s : string)
        : t1 = <fun `s => `t2>
                          -> <`t1 [`s] {var s 0}> = t2.
Proof.
  intros.
  subst.
  normalize.
Abort.

Theorem direction1 : forall (t1 t2 : QTerm) s, <`t1 [`s] {var s 0}> = t2 -> t1 = <fun `s => `t2>.
Proof.
  intros.
  apply (f_equal (fun t => <fun `s => `t>)) in H.
  rewrite <- eta in H.
  assumption.
Qed.
Print eta.

Theorem direction2 : forall (t1 t2 : QTerm) s, t1 = <fun `s => `t2> -> <`t1 [`s] {var s 0}> = t2.
Proof.
  intros.
  Check eta.
  rewrite (eta s t1) in H.
  apply lamInj in H.
  assumption.
Qed.

(*
Axiom fact1 : forall (t1 t2 : QTerm) s, <`t1 [`s] {var s 0}> = t2 -> t1 = <fun `s => `t2>.
Axiom fact2 : forall (t1 t2 : QTerm) s1 s2, <`t1 [`s1] [`s2] ({var s1 0}, {var s2 0})> = t2
                                            -> t1 = <fun p => `t2 [`s1 / proj1 p] [`s1 / proj2 p]>.

Ltac solve_all_2 := repeat (subst; solve_all;
                            match goal with
                            | H : (qterm.app (lift ?s ?i ?t1) (var ?s ?i))
                                  = ?t2 |- _ => apply fact1 in H
                            | H : (qterm.app (lift ?s2 ?i2 (lift ?s1 ?i1 ?t1))
                                       (pair (var ?s1 ?i1) (var ?s2 ?i2)))
                                  = ?t2 |- _ => apply fact2 in H
                            end).
 *)
Ltac solve_all_2 := repeat (subst; solve_all; try simple_pattern_case; try pair_pattern_case).

(*TODO: can prove from UIP? *)
Axiom cast_remover : forall A (p : A = A) (a : A), @defer_cast A A p a = a.

Definition match_on_id' {ctx T t: QTerm} {lvl} (prog : Typed ctx lvl T t)
  :
  ctx = nil
  -> lvl = 0
  -> T = <`pi `Bool `Bool>
  -> {t' & Typed <`cons `nil {const 0} `Bool> 0 Bool t'}.
  refine (
      match prog with
      | ty_true => _
      | ty_false => _
      | ty_lambda t' => fun _ _ _ => (existT _ _ (defer_cast t'))
      end
    );try solve[intros; solve_all_2].
  (*
    t1 x = t2
    <->
    t1 = \x.t2
    (if x not in t1)
    
    t1 (x, y) = t2
    <->
    t1 = \p. t2 [x/fst p] [y/snd p]
    
    
    t1 (x, (y, z)) = t2
    t1 (fst x) = t2
*)
Defined.

Theorem match_on_id_works : match_on_id' (ty_lambda ty_true) eq_refl eq_refl eq_refl
                            = existT _ _ ty_true.
Proof.
  (*This won't be possible*)
  simpl.
  rewrite cast_remover.
  reflexivity.
Qed.

(*
TODO: Will using SProp improve performance everywhere? All my terms have huge equality proofs in them.
Alternatively, I could periodically rewrite equalities between x = x into refls to make them smaller.
(recursive something something?)
*)

(*
So, this works in this case. But it probably won't always work. I'll contrive an example.
 *)

Module Test2.

Axiom I : Type.
Axiom i1 i2 : I.
Axiom i1i2 : i1 = i2.

Inductive Fam : I -> Type :=
| fam1 : Fam i1
| fam2 : Fam i2.

Definition cast (A B : Type) {p : A = B} (a : A) : B.
  subst.
  apply a.
Defined.


Definition famswap {i : I} (f : Fam i) : Fam i.
  refine (
      match f with
      | fam1 => @cast _ _ _ fam2
      | fam2 => @cast _ _ _ fam1
      end
    ).
  rewrite i1i2.
  reflexivity.
  rewrite i1i2.
  reflexivity.
Defined.

Theorem famswap_works : famswap (famswap fam1) = fam1.
Proof.
  simpl.
  Fail rewrite cast_remover.
Abort.

(******)

Check f_equal.
Theorem push_cast_through
        (I : Type)
        (P Q : I -> Type)
        (f : forall i, P i -> Q i)
        (i1 i2 : I)
        (p : i1 = i2)
        (input : P i1)
  : f _ (@cast _ _ (f_equal P p) input) = @cast _ _ (f_equal Q p) (f _ input).
Proof.
  refine (match p with
          | eq_refl => _
          end).
  reflexivity.
Qed.

(*
Can I use UIP or SProp somehow to make this work better?

IDEA: Use a specialized version of cast where the equality is always over the index type.
so cast : ctx1 = ctx2 -> T1 = T2 -> t1 = t2 -> Typed ctx1 T1 t1 -> Typed ctx2 T2 t2
sort of thing.


*)

Axiom uip : forall (T : Type) (t : T) (p : t = t), p = eq_refl.
Theorem really_push_it_through_with_uip
        (I : Type)
        (P Q : I -> Type)
        (f : forall i, P i -> Q i)
        (i1 i2 : I)
        (pi : i1 = i2)
        (p2 : P i1 = P i2)
        (input : P i1)
  : f _ (@cast _ _ p2 input) = @cast _ _ (f_equal Q pi) (f _ input).
Abort.

Theorem famswap_works_2 : famswap (famswap fam1) = fam1.
Proof.
  simpl.
  Set Printing Implicit.
  Fail rewrite (@push_cast_through I Fam Fam (@famswap) i2 i1
               (@eq_ind_r I i2 (fun i : I => Fam i2 = Fam i) (@eq_refl Set (Fam i2)) i1 i1i2)
               fam2).
Abort.
  
End Test2.

Module Test3.

Axiom I : Type.
Axiom i1 i2 : I.
Axiom i1i2 : i1 = i2.

Inductive Fam : I -> Type :=
| fam1 : Fam i1
| fam2 : Fam i2.

Definition transport {T : Type} (P : T -> Type) {t1 t2 : T} (p : t1 = t2) (a : P t1) : P t2.
  subst.
  apply a.
Defined.

Definition famswap {i : I} (f : Fam i) : Fam i.
  refine (
      match f with
      | fam1 => transport Fam _ fam2
      | fam2 => transport Fam _ fam1
      end
    ).
  rewrite i1i2.
  reflexivity.
  rewrite i1i2.
  reflexivity.
Defined.

Theorem famswap_works : famswap (famswap fam1) = fam1.
Proof.
  simpl.
  Fail rewrite cast_remover.
Abort.

(******)

Check f_equal.
Theorem push_transport_through
        (I : Type)
        (P Q : I -> Type)
        (f : forall i, P i -> Q i)
        (i1 i2 : I)
        (p : i1 = i2)
        (input : P i1)
  : f _ (transport P p input) = transport Q p (f _ input).
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
Print UIP.
Axiom uip : forall T, UIP T.
Theorem remove_transport
        (I : Type)
        (P : I -> Type)
        (i : I)
        (loop : i = i)
        (input : P i)
        : transport P loop input = input.
Proof.
  rewrite (uip I i i loop eq_refl).
  reflexivity.
Qed.

Ltac escape_transport_hell :=
  repeat (rewrite ?push_transport_through, ?compose_transport, ?remove_transport).
  
Theorem famswap_works_2 : famswap (famswap fam1) = fam1.
Proof.
  simpl.
  escape_transport_hell.
  simpl.
  escape_transport_hell.
  reflexivity.
Qed.
  
End Test3.
