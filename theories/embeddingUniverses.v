Require Import String.
Require Import qterm.
Require Import lambdaFacts.
Require Import lambdaSolve.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

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

Inductive Typed : (*context*) QTerm -> (*level*) nat -> (*Type*) QTerm -> (*Term*) QTerm -> Prop :=
| ty_lambda : forall ctx A B s lvl,
    Typed ctx (S lvl) <`U> <`pi `A `B> ->
    Typed <`cons `ctx {const lvl} `A> lvl B s -> Typed ctx lvl <`pi `A `B> <`lambda `s>
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
    Typed ctx (S lvl) <`U)> A
    -> Typed <`cons `ctx {const lvl} `A> (S lvl) <`U> B -> Typed ctx (S lvl) <`U> <`pi `A `B>
| ty_U : forall ctx lvl, Typed ctx (S (S lvl)) <`U> <`U>
| ty_Lift : forall ctx lvl T, Typed ctx (S lvl) <`U> T -> Typed ctx (S (S lvl)) <`U> <`Lift `T>
| ty_lift : forall ctx lvl T t, Typed ctx lvl T t -> Typed ctx (S lvl) <`Lift `T> t
| ty_lower : forall ctx lvl T t, Typed ctx (S lvl) <`Lift `T> t -> Typed ctx lvl T t
.

Ltac solve_no_unfold := repeat (lambda_solve ; repeat neutral_inj_case ;lambda_solve
                  ; repeat fast_neutral_unequal_case). 

Ltac solve_all := repeat (unfold_all ; lambda_solve ; repeat neutral_inj_case ;lambda_solve
                          ; repeat fast_neutral_unequal_case).

Inductive In' (Prev : QTerm -> (QTerm -> Prop) -> Prop) : QTerm -> (QTerm -> Prop) -> Prop:=
| in_Pi : forall (s : QTerm -> Prop) (F : QTerm -> (QTerm -> Prop)) A B,
    In' Prev A s
    -> (forall a, s a -> In' Prev <`B `a> (F a))
    -> In' Prev <Pi `A `B> (fun f => forall a (s : s a), F a <`f `a>)
| in_Bool :  In' Prev <Bool> (fun b => b = <fun x => proj1 x> \/ b = <fun x => proj2 x>)
| in_Empty : In' Prev <Empty> (fun _ => False)
(* TODO: Put lvl in type? or get rid of them? *)
| in_type : In' Prev <U> (fun T => exists S, Prev T S)
(* TODO: Lift type. Something like: *)
| in_Lift : forall T S, Prev T S -> In' Prev <Lift `T> S
.

(* In (S n) represents the interperetation of a type at level n *)
Fixpoint In (lvl : nat) : QTerm -> (QTerm -> Prop) -> Prop :=
  match lvl with
  | O => fun _ _ => False (* TODO: Is this how I want to do it? *)
  | S lvl' => In' (In lvl')
  end.

Theorem In_function : forall lvl T S1 S2, In lvl T S1 -> In lvl T S2 -> S1 = S2.
Proof.
  intros lvl.
  induction lvl.
  - intros.
    inversion H0.
  -
    intros T S1 S2 in1.
    intros.
    generalize dependent S2.
    (* Most cases can be dealt with trivially*)
    induction in1; try(intros; inversion H; solve_all; fail).
    (* Pi X Pi case *)
    + intros S2 in2.
      inversion in2; solve_all.
      subst.
      rewrite <- (IHin1 s0 H2) in *.
      extensionality f.
      extensionality a.
      extensionality Sa.
      rewrite (H0 a Sa (F0 a) (H3 a Sa)).
      reflexivity.
    (* Lift X Lift case *)
    + intros.
      inversion H0; solve_all.
      subst.
      specialize (IHlvl _ _ _ H H2).
      auto.
Qed.

Inductive InCtx : QTerm -> QTerm -> Prop :=
| in_nil : InCtx nil nil
| in_cons : forall env ctx lvl val T s,
    InCtx env ctx
    -> In (S lvl) <`T `env> s (* is the successor here correct? *)
    -> s val
    -> InCtx <`env , `val> <`cons `ctx {const lvl} `T>.

Theorem fundamental_lemma : forall ctx T lvl t env,
    Typed ctx lvl T t
    -> InCtx env ctx
    -> exists s, In (S lvl) <`T `env> s (* TODO: S lvl? In 0 is just empty. *)
    /\ s <`t `env>.
Proof.
  intros.
  generalize dependent env.
  induction H.
  (* lambda *)
  - intros env inctx.
    specialize (IHTyped1 env inctx) as [SU [InU piAB_in_SU]].
    inversion InU; clear InU; solve_all.
    subst.
    destruct piAB_in_SU as [SPiAB In'PiAB].
    inversion In'PiAB; clear In'PiAB; solve_all.
    exists (fun f : QTerm => forall a : QTerm, s0 a -> F a <`f `a>).
    split.
    + repeat constructor; intros; eauto.
    + intros a SAa.
      specialize (H3 a SAa).
      solve_all.
      specialize (IHTyped2 <`env , `a>).
      replace <Cons `ctx {const lvl} `A> with <`cons `ctx {const lvl} `A> in IHTyped2 by (unfold cons; normalize; reflexivity).
      Check (in_cons _ _ _ _ _ s0 inctx H2).
      destruct (IHTyped2 (in_cons _ _ _ _ _ s0 inctx H2 SAa)) as [Fa' [InBFa' Fa's]].
      rewrite (In_function (S _) _ _ _ H3 InBFa').
      apply Fa's.
  (* app *)
  - intros env inctx.
    specialize (IHTyped1 env inctx) as [SPIAB [inPiAB s1Elem]].
    specialize (IHTyped2 env inctx) as [SA [inA s2Elem]].
    inversion inPiAB as [SA' F A' B' In_A'_SA' In_B'a_F'a eq | | | | ]; solve_all.
    subst.
    (*inversion in'PiAB as [ SA' F A' B' In_A'_SA' In_B'a_F'a eq | |]; solve_all; subst.*)
    replace SA' with SA in * by (symmetry; apply (In_function (S _) _ _ _ In_A'_SA' inA)).
    exists (F <`s2 `env>).
    specialize (In_B'a_F'a <`s2 `env> s2Elem).
    specialize (s1Elem <`s2 `env> s2Elem).
    normalize_in In_B'a_F'a.
    split; auto.
  (* var *)
  - intros env inctx.
    generalize dependent env.
    induction H; intros x inctx; inversion inctx; solve_all; subst; eauto.
  (* true *)
  - intros env inctx.
    eexists.
    solve_all.
    split; repeat constructor; solve [solve_all].
  (* false *)
  - intros.
    eexists.
    solve_all.
    split; repeat constructor; solve [solve_all].
  (* if *)
  - intros env inctx.
    specialize (IHTyped1 env inctx) as [S [In_Bool_S S_cond]].
    inversion In_Bool_S; solve_all.
    subst.
    destruct S_cond.
    + (*true*)
      specialize (IHTyped2 env inctx) as [S0 [In_Ttrue_S0 S0_t1]].
      exists S0.
      rewrite H2.
      split.
      * solve_all.
        replace <fun p => proj1 p> with <fun x => proj1 x> in * by solve_all.
        apply In_Ttrue_S0.
      * normalize.
        apply S0_t1.
    + (* false *)
      specialize (IHTyped3 env inctx) as [S0 [In_Tfalse_S0 S0_t1]].
      exists S0.
      rewrite H2.
      split.
      * solve_all.
        replace <fun p => proj2 p> with <fun x => proj2 x> in * by solve_all.
        apply In_Tfalse_S0.
      * normalize.
        apply S0_t1.
  (* Empty *)
  - intros.
    eexists.
    solve_all.
    split.
    + apply in_type.
    + eexists.
      apply in_Empty.
  (* Bool *)
  - intros.
    eexists.
    solve_all.
    split.
    + apply in_type.
    + eexists.
      apply in_Bool.
  (* Pi : Type*)
  - intros env inctx.
    eexists.
    unfold U.
    normalize.
    split; [apply in_type|].
    specialize (IHTyped1 env inctx) as [SAU [InUSA SAA]].
    inversion InUSA; try solve [solve_all].
    subst.
    destruct SAA as [SA InASA].
    unfold pi.
    normalize.
    eexists.
    pose (fun (a b : QTerm) => exists SB, In (S lvl) <`B (`env , `a)> SB /\ SB b) as F.
    apply in_Pi with (F := F); eauto.

    intros.
    Check in_cons.
    Check (in_cons _ _ _ _ _ _ inctx InASA H1).
    Check a.

    specialize (IHTyped2 <`env, `a> (in_cons _ _ _ _ _ _ inctx InASA H1)) as [SU [InUS BinSU]].
    solve_all.
    rewrite <- (In_function (S (S _)) _ _ _ InUSA InUS) in BinSU.
    destruct BinSU as [SB In'BSB].

    replace SB with ((fun _ => SB) a) in In'BSB by reflexivity.
    replace (F a) with SB; auto.
    unfold F.
    extensionality b.
    apply propositional_extensionality.
    split; intros; eauto.
    destruct H2.
    destruct H2.
    rewrite (In_function (S _) _ _ _ In'BSB H2).
    auto.
  (* Type n : Type (S n) *)
  - intros.
    eexists.
    split.
    + unfold U.
      normalize.
      apply in_type.
    + simpl.
      eexists.
      unfold U.
      normalize.
      apply in_type.
  (* Lift *)
  - intros.
    eexists.
    specialize (IHTyped env H0) as [s [In_U_s T_in_s]].
    split.
    + Check in_type.

      simpl.
      Check in_type.
      unfold U.
      normalize.
      apply in_type.
    + simpl.

      inversion In_U_s; solve_all; clear In_U_s; subst.
      destruct T_in_s as [S InT].
      exists S.
      unfold Lift.
      normalize.
      apply in_Lift.

      apply InT.
  - intros.
    specialize (IHTyped env H0) as [S [In_T In_S]].
    exists S.
    split.
    + solve_all.
      apply in_Lift.
      apply In_T.
    + apply In_S.
  - intros.
    specialize (IHTyped env H0) as [S [In_T In_S]].
    exists S.
    solve_all.
    inversion In_T; try solve [solve_all].
    subst.
    split.
    + solve_all.
      apply H2.
    + apply In_S.
Qed.
     
Theorem consistency : forall t, Typed nil 0 Empty t -> False.
Proof.
  intros.
  destruct (fundamental_lemma nil Empty 0 t nil H in_nil) as [S [InEmptyS H1]].
  inversion InEmptyS; inversion H0; solve_all.
  subst.
  auto.
Qed.
