Require Import String.
Require Import qterm.
Require Import lambdaFacts.
Require Import lambdaSolve.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

(* The shallow embedding. Ideally this would work with nice notations, but for now Definitions: *)

Definition nil := <Nil>.
Definition cons := <fun gamma => fun ty => cons gamma ty>.

Definition zero := <fun x => proj2 x>.
Definition succ := <fun x => fun gamma => x (proj1 gamma)>.

Definition lzero := <lzero>.
Definition lsuc := <lsuc>.
Definition arrow := <fun x => fun y => fun env => Arrow (x env) (y env)>.
(*Definition pi := <fun x => fun y => fun gamma => Pi (x gamma) (fun a => y (gamma , a))>.*)
Definition all := <fun t => fun env => All (fun x => t (env , x))>.
Definition U : QTerm := <fun env => U>.
Definition Empty := <fun env => Empty>.

Definition var_to_term := <fun x => x>.
Definition lambda := <fun t => fun gamma => fun a => t (gamma , a)>.
Definition Lambda := <fun t => fun gamma => fun a => t (gamma , a)>.
Definition app := <fun t1 => fun t2 => fun gamma => (t1 gamma) (t2 gamma)>.
Definition App := <fun t1 => fun t2 => fun gamma => (t1 gamma) (t2 gamma)>.

Definition weaken := <fun t => fun env => t (proj1 env)>.
Definition subLast := <fun t => fun toSub => fun env => t (env , toSub env)>.

Ltac unfold_all := unfold nil, cons, zero, succ, arrow, all, U, Empty, var_to_term, lambda,
    app, weaken, subLast, lzero, lsuc, App, Lambda in *.

(* The deeper shallow embedding *)

Inductive VarTyped : QTerm -> QTerm -> QTerm -> Prop :=
| ty_zero : forall ctx T, VarTyped <`cons `ctx `T> <`weaken `T> zero
| ty_succ : forall ctx A T s, VarTyped ctx A s
                              -> VarTyped <`cons `ctx `T> <`weaken `A> <`succ `s>
.

Inductive Typed : QTerm -> QTerm -> QTerm -> Prop :=
| ty_lambda : forall ctx A B s,
    Typed ctx <`arrow `A `B> s
    -> Typed <`cons `ctx `A> <`weaken `B> s
    -> Typed ctx <`arrow `A `B> <`lambda `s>
| ty_app : forall ctx A B s1 s2, Typed ctx <`arrow `A `B> s1 -> Typed ctx A s2
                                 -> Typed ctx B <`app `s1 `s2>
| ty_App : forall ctx T s ty,
    Typed ctx <`all `T> s
    -> Typed ctx U ty
    -> Typed ctx <`subLast `T `ty> <`App `s `ty>
| ty_Lambda : forall ctx T s, Typed <`cons `ctx `U> T s
                              -> Typed ctx <`all `T> <`lambda `s>
| ty_var : forall ctx T t, VarTyped ctx T t -> Typed ctx T t
| ty_arrow : forall ctx A B,
    Typed ctx U A -> Typed ctx U B -> Typed ctx U <`arrow `A `B>
| ty_all : forall ctx T,
    Typed <`cons `ctx `U> U T -> Typed ctx U <`all `T>
| ty_Empty : forall ctx, Typed ctx U Empty
.

Ltac solve_no_unfold := repeat (lambda_solve ; repeat neutral_inj_case ;lambda_solve
                  ; repeat fast_neutral_unequal_case). 

Ltac solve_all := repeat (unfold_all ; lambda_solve ; repeat neutral_inj_case ;lambda_solve
                  ; repeat fast_neutral_unequal_case). 


(*
(* The identity function is typed at U -> U*)
(*Theorem test1 : Typed nil <`pi `U0 `U0> <`lambda `zero>.*)
Theorem test1 : Typed nil <`arrow (fun env => asdf) (fun env => asdf)> <`lambda `zero>.
Proof.
  apply ty_lambda.
  apply ty_var.
  Check ty_zero.
  apply_cast ty_zero.
  unfold_all.
  lambda_solve.
Qed.

(* \ _ x . x : forall T. T -> T*)
Theorem test2 : Typed nil <`all (`arrow `zero `zero)> <`Lambda (`lambda `zero)>.
Proof.
  apply ty_Lambda.
  apply ty_lambda.
  apply ty_var.
  apply ty_zero.
Qed.

(* (\_ x . x : forall T. T -> T) Empty : Empty -> Empty*)
Theorem test3 : Typed nil <`arrow `Empty `Empty> <`App (`Lambda (`lambda `zero)) `Empty>.
Proof.
  Check ty_App.
  Check (ty_App nil <`arrow `zero `zero>).
  assert (<`App (`Lambda (`lambda `zero)) `Empty> = <`lambda `zero>). solve_all.
  rewrite H.
  apply ty_lambda.
  apply ty_var.
  apply_cast ty_zero.
  solve_all.
Qed.
*)
  
Inductive In: QTerm -> (QTerm -> Prop) -> Prop:=
| in_arrow : forall A B SA SB,
                    In A SA ->
                    In B SB ->
                    In <Arrow `A `B> (fun f => forall a, SA a -> SB <`f `a>)
| in_Empty : In <Empty> (fun _ => False)
| in_all : forall T (F : QTerm -> (QTerm -> Prop)),
    (forall (S : QTerm -> Prop), In <`T (Candidate {const S})> (F <Candidate {const S}>))
    -> In <All `T> (fun f => forall (S : QTerm -> Prop), F <Candidate {const S}> <`f {const S}>)
| in_set : forall (S : QTerm -> Prop), In <Candidate {const S}> S
| in_type : In <U> (fun t => exists (S : QTerm -> Prop), t = <Candidate {const S}>)
.

(* There is an issue with quotients allowing things that shouldn't be possible
 (probably even inconsistent). I need to fix that, and instead of constants of arbitrary
 types, I should do the solution I wrote below*)
Inductive SBP : Type :=
| ctr2 : forall {T : Type}, T -> SBP.
Axiom thing : SBP -> Prop.
(* It doesn't let me do this: *)
Fail Definition isPossible := ctr2 thing.

(* So why does it let me do this: *)
Axiom thing2 : QTerm -> Prop.
Definition isPossible2 := Lambda.const thing2.

(* It must be some sort of cheat that is accidentally allowed by the definition of quotients?
 is it allowed in the original un-quotiented term type? *)

Require Import term.
Axiom thing3 : Term -> Prop.
Check constant.
Fail Definition isPossible3 := constant thing3.

(*Ok, so yes it is the quotient type somehow accidentally allowing a thing that
  shouldn't be allowed. *)
(*
IDEA: Maybe its fine, because terms and types are completely separate.
In other words, I can have two copies of QTerm, one at level 0 and the other at level 1.
The types are at level 1, and can contain sets of terms at level 0.
The idea is that QTerm will be parametrized by a type C of constants.
This only seems to work if types don't appear in terms. In some formulations of System F,
they do, even though they are never really used.
 *)
(*
Even if that works, another issue is how the induction in the fundamental lemma will go through.
Maybe the environment will have to say that for each type we have a set of terms?
Because the induction needs to correctly capture the idea of substituting these sets
into the types.
*)


Theorem In_function : forall T S1 S2, In T S1 -> In T S2 -> S1 = S2.
Proof with (try (intros; inversion H; solve_all; reflexivity; fail)).
  intros T S1 S2 in1.
  generalize dependent S2.
  induction in1 as []...
  - 
    intros S2 in2.
    inversion in2; solve_all; subst.
    rewrite (IHin1_1 SA0 H0) in *.
    rewrite (IHin1_2 SB0 H1) in *.
    reflexivity.
  - intros.
    inversion H1; solve_all; subst.
    extensionality f.
    extensionality S.
    rewrite (H0 _ _ (H3 S)).
    reflexivity.
  - intros.
    inversion H; solve_all.
    subst.
    reflexivity.
Qed.

(*
TODO: separate context for types?
The environment for those should be pairs like normal environment,
or made specially of sets of terms?
*)

Inductive InCtx : QTerm -> QTerm -> Prop :=
| in_nil : InCtx nil nil
| in_cons : forall env ctx val T S,
    InCtx env ctx
    -> In <`T `env> S
    -> S val
    -> InCtx <`env , `val> <`cons `ctx `T>.

(*
lambda
app
App
Lambda
var
arrow
all
Empty
*)
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
    inversion InU; solve_all; subst; clear InU.
    exists (fun f : QTerm => forall a : QTerm, SA a -> SB <`f `a>).
    split.
    + repeat constructor; intros; eauto.
    + intros a SAa.
      (*specialize (H3 a SAa).*)
      solve_all.
      specialize (IHTyped2 <`env , `a>).
      replace <cons `ctx `A> with <`cons `ctx `A> in IHTyped2 by (unfold cons; normalize; reflexivity).
      Check (in_cons _ _ _ _ SA inctx H2).
      Check in_cons.
      destruct (IHTyped2 (in_cons _ _ _ _ SA inctx H2 SAa)) as [Fa' [InBFa' Fa's]].
      solve_all.
      rewrite (In_function _ _ _ H3 InBFa').
      apply Fa's.
  (* app *)
  - (*intros env inctx.
    specialize (IHTyped1 env inctx) as [SPIAB [inPiAB s1Elem]].
    specialize (IHTyped2 env inctx) as [SA [inA s2Elem]].
    (*inversion inPiAB as [T S in'PiAB | | | | ]; solve_all.*)
    inversion inPiAB; solve_all.
    (*inversion in'PiAB as [ SA' F A' B' In_A'_SA' In_B'a_F'a eq | |]; solve_all; subst.*)
    replace SA' with SA in * by (symmetry; apply (In_function _ _ _ (in' _ _ In_A'_SA') inA)).
    exists (F <`s2 `env>).
    specialize (In_B'a_F'a <`s2 `env> s2Elem).
    specialize (s1Elem <`s2 `env> s2Elem).
    normalize_in In_B'a_F'a.
    split.
    + apply in'.
      apply In_B'a_F'a.
    + apply s1Elem.*)
    give_up.
  (* App *)
  - intros env inctx.
    clear H H0.
    specialize (IHTyped1 env inctx) as [S_allT [In_allT in_s_allT]].
    unfold all in In_allT.
    normalize_in In_allT.
    inversion In_allT; solve_all.
    subst.
    clear In_allT.
    specialize (IHTyped2 env inctx) as [SU [InSU SUty]].
    inversion InSU; solve_all; subst; clear InSU.
    destruct SUty as [Sty thisSeemsWrong].
    specialize (H2 Sty).
    normalize_in H2.
    
    (*** will App and Lambda cases work? If so others probably are fine. ***)
    normalize.
    
    
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
