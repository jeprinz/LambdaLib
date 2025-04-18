Require Import String.
Require Import qterm.
Require Import lambdaFacts.
Require Import lambdaSolve.

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

Ltac unfold_all := unfold nil, cons, zero, succ, arrow, all, U, Empty, var_to_term, lambda, app, weaken, lzero, lsuc, App, Lambda in *.

(* The deeper shallow embedding *)

Inductive VarTyped : QTerm -> QTerm -> QTerm -> Prop :=
| ty_zero : forall ctx T, VarTyped <`cons `ctx `T> <`weaken `T> zero
| ty_succ : forall ctx A T s, VarTyped ctx A s
                              -> VarTyped <`cons `ctx `T> <`weaken `A> <`succ `s>
.

Inductive Typed : QTerm -> QTerm -> QTerm -> Prop :=
| ty_lambda : forall ctx A B s, Typed <`cons `ctx `A> <`weaken `B> s
                                -> Typed ctx <`arrow `A `B> <`lambda `s>
| ty_app : forall ctx A B s1 s2, Typed ctx <`arrow `A `B> s1 -> Typed ctx A s2
                                 -> Typed ctx B <`app `s1 `s2>
(*| ty_app : forall ctx A B s1 s2, Typed ctx <`pi `A `B> s1 -> Typed ctx A s2
                  -> Typed ctx <fun env => `B [env] (env , (`s2 [env]) env)> <`app `s1 `s2>*)
| ty_App : forall ctx T s ty,
                              (* Should I require that ty is typed? *)
    Typed ctx U ty
    -> Typed ctx <`all `T> s
    -> Typed ctx <fun env => `T [env] (env , `ty [env])> <`App `s `ty>
| ty_Lambda : forall ctx T s, Typed <`cons `ctx `U> T s
                              -> Typed ctx <`all `T> <`lambda `s>
| ty_var : forall ctx T t, VarTyped ctx T t -> Typed ctx T t
| ty_arrow : forall ctx A B,
    Typed ctx U A -> Typed ctx U B -> Typed ctx U <`arrow `A `B>
(*| ty_pi : forall ctx A B,
    Typed ctx <`U0> A
    -> Typed <`cons `ctx `A> <`U0> B -> Typed ctx <`U0> <`pi `A `B>*)
| ty_all : forall ctx T,
    Typed <`cons `ctx `U> U T -> Typed ctx U <`all `T>
| ty_Empty : forall ctx, Typed ctx U Empty
.

Ltac solve_no_unfold := repeat (lambda_solve ; repeat neutral_inj_case ;lambda_solve
                  ; repeat fast_neutral_unequal_case). 

Ltac solve_all := repeat (unfold_all ; lambda_solve ; repeat neutral_inj_case ;lambda_solve
                  ; repeat fast_neutral_unequal_case). 


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
  
(*
Inductive InType : QTerm -> Prop :=
| intype_arrow : forall A B,
    InType A -> InType B -> InType <arrow `A `B>
| intype_all : forall T,
.*)
Search "bind".
From stdpp Require Import option.
Search "bind".
Check option_bind.

Inductive In: QTerm -> (QTerm -> Prop) -> Prop:=
(*| in_Pi : forall (S : QTerm -> Prop) (F : forall a, (*S a ->*) QTerm -> Prop) A B,
    In A S
    -> (forall a (s : S a), In <`B `a> (F a (*s*)))
    -> In <Pi `A `B> (fun f => forall a (s : S a), F a (*s*) <`f `a>)*)
| in_arrow : forall A B SA SB,
                    In A SA ->
                    In B SB ->
                    In <arrow `A `B> (fun f => forall a, SA a -> SB <`f `a>)
| in_all : forall T (F : QTerm -> ((QTerm -> Prop) -> Prop)),
    (* might need to have another premise saying that F is a function.
     actually, maybe no I dont, because the following line enforces that F outputs only one thing. *)
    (* by using option, it means that In <T a> doesn't need to be defined for all a. *)
    (* PROBLEM: The above condition does not rule out F being empty. *)
    (forall a Fa, F a Fa -> In <`T `a> Fa)
    -> In <all `T> (fun f => forall a Fa, F a Fa -> Fa <`f `a>)
| in_Empty : In <Empty> (fun _ => False)
(* Test of thing that probably wont work: *)
| in_all2 : forall T (F : QTerm -> (QTerm -> Prop)),
    (forall (S : QTerm -> Prop), In <`T {Lambda.const S}> (F (Lambda.const S)))
    -> In <all `T> (fun f => forall (S : QTerm -> Prop), F (Lambda.const S) <`f {Lambda.const S}>)
| in_set : forall (S : QTerm -> Prop), In (Lambda.const S) S
.

Definition isItTheSame (t : QTerm) := In t (fun t' => t = t').
(* Wait.. how does that work? *)

(*
Inductive Shouldn'tBePossible : Type :=
| ctr1 : (Shouldn'tBePossible -> Prop) -> Shouldn'tBePossible
.
 *)

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
 *)
(*
Even if that works, another issue is how the induction in the fundamental lemma will go through.
Maybe the environment will have to say that for each type we have a set of terms?
Because the induction needs to correctly capture the idea of substituting these sets
into the types.
*)

Axiom hole : forall {T : Type}, T.

Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Theorem In_function : forall T S1 S2, In T S1 -> In T S2 -> S1 = S2.
Proof.
  intros T S1 S2 in1.
  generalize S2.
  clear S2.
  induction in1.
  - intros.
    inversion H.
    solve_all.
    specialize (IHin1_1 _ H1).
    specialize (IHin1_2 _ H2).
    subst.
    reflexivity.
    solve_all.
    solve_all.
  - intros.
    inversion H1.
    solve_all.
    solve_all.
    clear H4. (* TODO... do I want this? *)
    (**)
    extensionality f.
    apply propositional_extensionality.
    split.
    + intros.
      apply H2.
      
    (**)
    assert (F = F0). {
      extensionality a.
      extensionality S.
      specialize (H a S).
      specialize (H0 a S).
      specialize (H3 a S).
      apply propositional_extensionality.
      split.
      + intros.
        specialize (H H2).
        specialize (H0 H2).
        
    (**)
    extensionality fa.
    apply propositional_extensionality.
    split.
    + intros.
      rewrite <- H4.
      specialize (H0 ).



  
  induction in1 as [ S F A B In_A_S In_A_S_only In_Ba_Fa In_Ba_Fa_only | ].
  - intros S2 in2.
    inversion in2 as [S' F' A' B' In_A_S' In_Ba_F'a eq extra |].
    + (* Pi Pi *)
      solve_all.
      clear extra.
      clear in2.
      clear S2.
      specialize (In_A_S_only S' In_A_S').
      subst S'.

      assert (forall a, S a -> F a = F' a).
      {
        intros.
        apply In_Ba_Fa_only.
        apply H.
        apply In_Ba_F'a.
        apply H.
      }
      apply functional_extensionality.
      intros f.
      apply propositional_extensionality.
      split.
      * intros hyp a Sa.
        rewrite <- H.
        apply hyp.
        apply Sa.
        apply Sa.
      * intros hyp a Sa.
        rewrite H.
        apply hyp.
        apply Sa.
        apply Sa.
    +  (* Pi U *) solve_all.
  - intros.
    inversion H.
    * (* U Pi *) solve_all.
    * (* U Empty *) solve_all.
Qed.

(* Will this work? In contrast to the logical relation itself, this is QTerm -> QTerm -> Prop
instead of QTerm -> (QTerm -> Prop) -> Prop. This seems to correspond to Yiyun's paper. *)
Inductive InCtx : QTerm -> QTerm -> Prop :=
| in_nil : InCtx nil nil
| in_cons : forall env ctx val T S,
    InCtx env ctx
    -> In val S
    -> S <`T `env>
    -> InCtx <`env , `val> <`cons `ctx `T> 
.

Theorem fundamental_lemma_for_variables : forall ctx T t env,
    VarTyped ctx T t -> InCtx env ctx -> exists S, In <`t `env> S /\ S <`T `env>.
Proof.
  intros.
  generalize env, H0.
  clear H0.
  clear env.
  induction H.
  - intros.
    inversion H0.
    + solve_all.
    +
      solve_all.
      exists S.
      split.
      assumption.
      assumption.
  - intros.
    inversion H0.
    + solve_all.
    + solve_all.
      apply IHVarTyped.
      apply H2.
Qed.

Theorem fundamental_lemma_test_2 : forall ctx T t env,
    Typed ctx T t (*-> InCtx env ctx -> *)
    -> exists S, In <`T `env> S
    /\ S <`t `env>.
Proof.
  intros.
  generalize env.
  clear env.
  induction H.
  (* lambda *)
  - intros.
    apply hole.
  (* app *)
  - intros.
    specialize (IHTyped1 env).
    specialize (IHTyped2 env).
    destruct IHTyped1 as [SPIAB temp].
    destruct temp as [inPiAB s1Elem].
    destruct IHTyped2 as [SA temp].
    destruct temp as [inA s2Elem].
    inversion inPiAB.
    inversion H1 as [ SA' F A' B' In_A'_SA' In_B'a_F'a eq | ].
    (* The real case *)
    +
      unfold pi in eq.
      solve_no_unfold.
      assert (SA' = SA). {apply (In_function _ _ _ In_A'_SA' inA).}
      subst SA'.
      exists (F <`s2 `env>).
      specialize (In_B'a_F'a <`s2 `env> s2Elem).
      normalize_in In_B'a_F'a.
      split.
      apply In_B'a_F'a.
      rewrite <- H2 in s1Elem.
      specialize (s1Elem <`s2 `env> s2Elem).
      unfold app.
      normalize.
      apply s1Elem.
    (* Its not Type *)
    + solve_all.
    (* Its not empty*)
    + solve_all.
  (* var *)
  - apply hole.
  (* Pi *)
  - 
  (* U *)
  -
  (* Empty*)
  -
     

(*Definition In : QTerm -> QTerm -> Prop :=
  fun t T => exists S i, In'' i T S /\ S t.*)



Theorem fundamental_lemma : forall ctx T t env,
    Typed ctx T t -> InCtx env ctx -> In <`t `env> <`T `env>.
Proof.
  intros.
  generalize env, H0.
  clear H0.
  clear env.
  induction H.
  (* lambda *)
  - intros.
    unfold In, In'' in *.
    intros.
    eapply (cast (in_fun _ _ _ _)). unfold_all.
    solve_all.
    Unshelve. (* This focuses the goal from the argument to in_fun *)
    intros.
    lambda_solve.
    apply IHTyped.
    apply in_cons.
    apply H0.
    apply H1.
  (* app *)
  - intros.
    specialize (IHTyped1 env H1).
    specialize (IHTyped2 env H1).
    solve_all.
    inversion IHTyped1.
    (* Prove that it can't be in_U *)
    solve_all.
    (* Do the actual real proof for in_fun *)
    solve_all.
    apply H4 in IHTyped2.
    solve_all.
    exact IHTyped2.
    (* prove that it can't be in_Pi *)
    solve_all.
    (* prove that it can't be in_Empty *)
    solve_all.
  - intros.
    apply (fundamental_lemma_for_variables ctx T t env H H0).
  - intros.
    solve_all.
    apply in_Pi.
    specialize (IHTyped1 env H1).
    solve_all.
    apply IHTyped1.
    intros.
    solve_all.
    apply_cast (IHTyped2 <`env , `a>).
    solve_all.
    Unshelve.
    apply_cast (in_cons _ _ _ _ H1 H2).
    solve_all.
   - intros.
    Check in_U.
    eapply (cast (in_U _)).
    unfold U.
    lambda_solve.
  - intros.
    Check in_Empty.
    apply_cast in_Empty.
    solve_all.
Qed.


Theorem consistency : forall t,
    Typed nil Empty t -> False.
Proof.
  intros.
  pose (fundamental_lemma nil Empty t nil H in_nil) as x.
  inversion x; solve_all.
Qed.
