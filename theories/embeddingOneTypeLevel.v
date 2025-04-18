Require Import String.
Require Import qterm.
Require Import lambdaFacts.
Require Import lambdaSolve.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Definition nil := <Nil>.
Definition cons := <fun env => fun ty => cons env ty>.

Definition zero := <fun env => proj2 env>.
Definition succ := <fun x => fun env => x (proj1 env)>.

Definition pi := <fun x => fun y => fun env => Pi (x env) (fun a => y (env , a))>.
Definition U : QTerm := <fun env => U>.
Definition Empty := <fun env => Empty>.
Definition Bool := <fun env => Bool>.

Definition var_to_term := <fun x => x>.
Definition lambda := <fun t => fun env => fun a => t (env , a)>.
Definition app := <fun t1 => fun t2 => fun env => (t1 env) (t2 env)>.
Definition true := <fun env => fun p => proj1 p>.
Definition false := <fun env => fun p => proj2 p>.
Definition ifexpr := <fun cond => fun t1 => fun t2 => fun env => (cond env) (t1 env, t2 env)>.

Definition weaken := <fun t => fun env => t (proj1 env)>.
Definition subLast := <fun t => fun toSub => fun env => t (env , toSub env)>.

Ltac unfold_all := unfold nil, cons, zero, succ, pi, U, Bool, Empty, var_to_term, lambda,
    app, weaken, subLast, true, false, ifexpr in *.

(* The deeper shallow embedding *)

Inductive VarTyped : QTerm -> QTerm -> QTerm -> Prop :=
| ty_zero : forall ctx T, VarTyped <`cons `ctx `T> <`weaken `T> zero
| ty_succ : forall ctx A T s, VarTyped ctx A s
                              -> VarTyped <`cons `ctx `T> <`weaken `A> <`succ `s>.

Inductive Typed : QTerm -> QTerm -> QTerm -> Prop :=
| ty_lambda : forall ctx A B s,
    Typed ctx <`U> <`pi `A `B> ->
    Typed <`cons `ctx `A> B s -> Typed ctx <`pi `A `B> <`lambda `s>
| ty_app : forall ctx A B s1 s2, Typed ctx <`pi `A `B> s1 -> Typed ctx A s2
                                 -> Typed ctx <`subLast `B `s2> <`app `s1 `s2>
| ty_var : forall ctx T t, VarTyped ctx T t -> Typed ctx T t
| ty_true : forall ctx, Typed ctx Bool true
| ty_false : forall ctx, Typed ctx Bool false
| ty_if : forall ctx T cond t1 t2,
    Typed ctx Bool cond ->
    Typed ctx <`subLast `T `true> t1 ->
    Typed ctx <`subLast `T `false> t2 ->
    Typed ctx <`subLast `T `cond> <`ifexpr `cond `t1 `t2>
| ty_Empty : forall ctx, Typed ctx <`U> Empty
| ty_Bool : forall ctx, Typed ctx <`U> Bool
| ty_pi : forall ctx A B,
    Typed ctx <`U> A
    -> Typed <`cons `ctx `A> <`U> B -> Typed ctx <`U> <`pi `A `B>.

Ltac solve_no_unfold := repeat (lambda_solve ; repeat neutral_inj_case ;lambda_solve
                  ; repeat fast_neutral_unequal_case). 

Ltac solve_all := repeat (unfold_all ; lambda_solve ; repeat neutral_inj_case ;lambda_solve
                  ; repeat fast_neutral_unequal_case). 

Inductive In': QTerm -> (QTerm -> Prop) -> Prop:=
| in_Pi : forall (S : QTerm -> Prop) (F : QTerm -> (QTerm -> Prop)) A B,
    In' A S
    -> (forall a, S a -> In' <`B `a> (F a))
    -> In' <Pi `A `B> (fun f => forall a (s : S a), F a <`f `a>)
| in_Bool :  In' <Bool> (fun b => b = <fun x => proj1 x> \/ b = <fun x => proj2 x>)
| in_Empty : In' <Empty> (fun _ => False).

Inductive In : QTerm -> (QTerm -> Prop) -> Prop :=
| in' : forall T S, In' T S -> In T S
| in_type : In <U> (fun T => exists S, In' T S).



Theorem In_function : forall T S1 S2, In T S1 -> In T S2 -> S1 = S2.
Proof with (try (intros; inversion H; inversion H0; solve_all; reflexivity; fail)).
  intros T S1 S2 in1.
  generalize dependent S2.
  destruct in1 as [T S in1 | typeCase].
  - induction in1 as [ S F A B In_A_S In_A_S_only In_Ba_Fa In_Ba_Fa_only | | ]...
    intros S2 in2.
    inversion in2 as [T S'' in2' | ]; solve_all.
    inversion in2' as [S' F' A' B' In_A_S' In_Ba_F'a eq extra | | ]; solve_all.
    solve_all.
    rewrite (In_A_S_only S' (in' _ _ In_A_S')) in *.
    subst.
    extensionality f.
    extensionality a.
    extensionality Sa.
    rewrite (In_Ba_Fa_only a Sa (F' a) (in' _ _ (In_Ba_F'a a Sa))).
    reflexivity.
  - intros.
    inversion H.
    inversion H0; solve_all. (* Type x anything cases*)
    reflexivity. (* Type Type case*)
Qed.

Inductive InCtx : QTerm -> QTerm -> Prop :=
| in_nil : InCtx nil nil
| in_cons : forall env ctx val T S,
    InCtx env ctx
    -> In <`T `env> S
    -> S val
    -> InCtx <`env , `val> <`cons `ctx `T>.


Theorem fundamental_lemma : forall ctx T t env,
    Typed ctx T t
    -> InCtx env ctx
    -> exists S, In <`T `env> S
    /\ S <`t `env>.
Proof.
  intros.
  generalize dependent env.
  induction H.
  (* lambda *)
  - intros env inctx.
    specialize (IHTyped1 env inctx) as [SU [InU piAB_in_SU]].
    inversion InU; clear InU; subst; [inversion H1|]; solve_all.
    destruct piAB_in_SU as [SPiAB In'PiAB].
    inversion In'PiAB; clear In'PiAB; solve_all.
    exists (fun f : QTerm => forall a : QTerm, S a -> F a <`f `a>).
    split.
    + repeat constructor; intros; eauto.
    + intros a SAa.
      specialize (H3 a SAa).
      solve_all.
      specialize (IHTyped2 <`env , `a>).
      replace <cons `ctx `A> with <`cons `ctx `A> in IHTyped2 by (unfold cons; normalize; reflexivity).
      destruct (IHTyped2 (in_cons _ _ _ _ S inctx (in' _ _ H2) SAa)) as [Fa' [InBFa' Fa's]].
      rewrite (In_function _ _ _ (in' _ _ H3) InBFa').
      apply Fa's.
  (* app *)
  - intros env inctx.
    specialize (IHTyped1 env inctx) as [SPIAB [inPiAB s1Elem]].
    specialize (IHTyped2 env inctx) as [SA [inA s2Elem]].
    inversion inPiAB as [T S in'PiAB |]; solve_all.
    inversion in'PiAB as [ SA' F A' B' In_A'_SA' In_B'a_F'a eq | |]; solve_all; subst.
    replace SA' with SA in * by (symmetry; apply (In_function _ _ _ (in' _ _ In_A'_SA') inA)).
    exists (F <`s2 `env>).
    specialize (In_B'a_F'a <`s2 `env> s2Elem).
    specialize (s1Elem <`s2 `env> s2Elem).
    normalize_in In_B'a_F'a.
    split.
    + apply in'.
      apply In_B'a_F'a.
    + apply s1Elem.
  (* var *)
  - intros env inctx.
    generalize dependent env.
    induction H; intros x inctx; inversion inctx; solve_all; eauto.
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
    inversion In_Bool_S as [T0 S0' In_Bool_S' | ]; solve_all.
    inversion In_Bool_S'; solve_all.
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
    inversion InUSA. {inversion H1; solve_all.}
    subst.
    destruct SAA as [SA InASA].
    unfold pi.
    normalize.
    eexists.
    pose (fun (a b : QTerm) => exists SB, In' <`B (`env , `a)> SB /\ SB b) as F.
    apply in_Pi with (F := F); eauto.

    intros.
    specialize (IHTyped2 <`env, `a> (in_cons _ _ _ _ _ inctx (in' _ _ InASA) H1)) as [SU [InUS BinSU]].
    solve_all.
    rewrite <- (In_function _ _ _ InUSA InUS) in BinSU.
    destruct BinSU as [SB In'BSB].

    replace SB with ((fun _ => SB) a) in In'BSB by reflexivity.
    replace (F a) with SB; auto.
    unfold F.
    extensionality b.
    apply propositional_extensionality.
    split; intros; eauto.
    destruct H2.
    destruct H2.
    rewrite (In_function _ _ _ (in' _ _ In'BSB) (in' _ _ H2)).
    auto.
Qed.
     
Theorem consistency : forall t, Typed nil Empty t -> False.
Proof.
  intros.
  destruct (fundamental_lemma nil Empty t nil H in_nil) as [S [InEmptyS H1]].
  inversion InEmptyS; inversion H0; solve_all.
  subst.
  auto.
Qed.
