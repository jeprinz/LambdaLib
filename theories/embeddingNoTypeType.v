Require Import String.
Require Import qterm.
Require Import lambdaFacts.
Require Import lambdaSolve.

(*
Here I will use the library to define dependent type theory.
For now, I'll just do type : type.
*)


(* The shallow embedding. Ideally this would work with nice notations, but for now Definitions: *)

Definition nil := <Nil>.
Definition cons := <fun gamma => fun ty => cons gamma ty>.

Definition zero := <fun x => proj2 x>.
Definition succ := <fun x => fun gamma => x (proj1 gamma)>.

Definition lzero := <lzero>.
Definition lsuc := <lsuc>.
Definition pi := <fun x => fun y => fun gamma => Pi (x gamma) (fun a => y (gamma , a))>.
Definition U : QTerm := <fun env => U>.
Definition Empty := <fun env => Empty>.
Definition Bool := <fun env => Bool>.

Definition var_to_term := <fun x => x>.
Definition lambda := <fun t => fun gamma => fun a => t (gamma , a)>.
Definition app := <fun t1 => fun t2 => fun gamma => (t1 gamma) (t2 gamma)>.
Definition true := <fun env => fun p => proj1 p>.
Definition false := <fun env => fun p => proj2 p>.
Definition ifexpr := <fun cond => fun t1 => fun t2 => fun env => (cond env) (t1 env, t2 env)>.

Definition weaken := <fun t => fun env => t (proj1 env)>.
Definition subLast := <fun t => fun toSub => fun env => t (env , toSub env)>.

Ltac unfold_all := unfold nil, cons, zero, succ, pi, U, Bool, Empty, var_to_term, lambda,
    app, weaken, subLast, lzero, lsuc, true, false, ifexpr in *.

(* The deeper shallow embedding *)

Inductive VarTyped : QTerm -> QTerm -> QTerm -> Prop :=
| ty_zero : forall ctx T, VarTyped <`cons `ctx `T> <`weaken `T> zero
| ty_succ : forall ctx A T s, VarTyped ctx A s
                              -> VarTyped <`cons `ctx `T> <`weaken `A> <`succ `s>
.

Inductive Typed : QTerm -> QTerm -> QTerm -> Prop :=
| ty_lambda : forall ctx A B s, Typed <`cons `ctx `A> B s -> Typed ctx <`pi `A `B> <`lambda `s>
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
(* TODO: this should allow dependent types *)
(*
| ty_pi : forall ctx A B,
    Typed ctx <`U> A
    -> Typed <`cons `ctx `A> <`U> B -> Typed ctx <`U> <`pi `A `B>
| ty_Empty : forall ctx, Typed ctx <`U> Empty
*)
.



Ltac solve_no_unfold := repeat (lambda_solve ; repeat neutral_inj_case ;lambda_solve
                  ; repeat fast_neutral_unequal_case). 

Ltac solve_all := repeat (unfold_all ; lambda_solve ; repeat neutral_inj_case ;lambda_solve
                  ; repeat fast_neutral_unequal_case). 


(* The identity function is typed at U -> U*)
(*Theorem test1 : Typed nil <`pi `U0 `U0> <`lambda `zero>.*)
Theorem test1 : Typed nil <`pi (fun env => asdf) (fun env => asdf)> <`lambda `zero>.
Proof.
  apply ty_lambda.
  apply ty_var.
  Check ty_zero.
  apply_cast ty_zero.
  unfold_all.
  lambda_solve.
Qed.

Inductive In: QTerm -> (QTerm -> Prop) -> Prop:=
| in_Pi : forall (S : QTerm -> Prop) (F : forall a, (*S a ->*) QTerm -> Prop) A B,
    In A S
    -> (forall a (s : S a), In <`B `a> (F a (*s*)))
    -> In <Pi `A `B> (fun f => forall a (s : S a), F a (*s*) <`f `a>)
| in_Bool :  In <Bool> (fun b => b = <fun x => proj1 x> \/ b = <fun x => proj2 x>)
| in_Empty : In <Empty> (fun _ => False)
.

Axiom hole : forall {T : Type}, T.

Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Theorem In_function : forall T S1 S2, In T S1 -> In T S2 -> S1 = S2.
Proof.
  intros T S1 S2 in1.
  generalize S2.
  clear S2.
  induction in1 as [ S F A B In_A_S In_A_S_only In_Ba_Fa In_Ba_Fa_only | | ].
  - intros S2 in2.
    inversion in2 as [S' F' A' B' In_A_S' In_Ba_F'a eq extra | | ].
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
    + (* Pi Bool *) solve_all.
    +  (* Pi EMpty *) solve_all.
  - intros.
    inversion H.
    * (* Bool Pi *) solve_all.
    * (* Bool Bool *) solve_all.
    * (* Bool Empty *) solve_all.
  - intros.
    inversion H.
    * (* Empty Pi *) solve_all.
    * (* Empty Bool *) solve_all.
    * (* Empty Empty *) solve_all.
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
  -
    intros.
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

Theorem fundamental_lemma : forall ctx T t env,
    Typed ctx T t (*-> InCtx env ctx -> *)
    -> InCtx env ctx
    -> exists S, In <`T `env> S
    /\ S <`t `env>.
Proof.
  intros.
  generalize H0.
  generalize env.
  clear H0.
  clear env.
  induction H.
  (* lambda *)
  - intros.
    
    apply hole.
  (* app *)
  - intros env inctx.
    specialize (IHTyped1 env inctx).
    specialize (IHTyped2 env inctx).
    destruct IHTyped1 as [SPIAB temp].
    destruct temp as [inPiAB s1Elem].
    destruct IHTyped2 as [SA temp].
    destruct temp as [inA s2Elem].
    inversion inPiAB(*.
    inversion H1*) as [ SA' F A' B' In_A'_SA' In_B'a_F'a eq | |].
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
      unfold subLast.
      normalize.
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
  (* true *)
  - intros env inctx.
    exists (fun b => b = <fun x => proj1 x> \/ b = <fun x => proj2 x>).
    unfold Bool.
    normalize.
    split.
    apply in_Bool.
    apply or_introl.
    solve_all.
  (* false *)
  - intros.
    exists (fun b => b = <fun x => proj1 x> \/ b = <fun x => proj2 x>).
    unfold Bool.
    normalize.
    split.
    apply in_Bool.
    apply or_intror.
    solve_all.
  (* if *)
  - intros env inctx.
    specialize (IHTyped1 env inctx).
    destruct IHTyped1 as [S temp].
    destruct temp as [In_Bool_S S_cond].
    inversion In_Bool_S.
    (* Pi *)
    + solve_all.
    (* Bool *)
    + rewrite <- H2 in S_cond.
      destruct S_cond.
      * (*true*)
        specialize (IHTyped2 env inctx).
        destruct IHTyped2 as [S0 temp].
        destruct temp as [In_Ttrue_S0 S0_t1].
        exists S0.
        unfold subLast.
        normalize.
        unfold subLast, true in In_Ttrue_S0.
        normalize_in In_Ttrue_S0.
        rewrite H4.
        split.
        apply_cast In_Ttrue_S0.
        solve_all.
        (* TODO: make solve_all handle pairs! Then I can simplify this stuff. *)
        assert (<fun p => proj1 p> = <fun x => proj1 x>). solve_all.
        rewrite H3.
        reflexivity.
        unfold ifexpr.
        normalize.
        rewrite H4.
        normalize.
        apply S0_t1.
      * (* false *)
        specialize (IHTyped3 env inctx).
        destruct IHTyped3 as [S0 temp].
        destruct temp as [In_Ttrue_S0 S0_t1].
        exists S0.
        unfold subLast.
        normalize.
        unfold subLast, true in In_Ttrue_S0.
        normalize_in In_Ttrue_S0.
        rewrite H4.
        split.
        apply_cast In_Ttrue_S0.
        solve_all.
        (* TODO: make solve_all handle pairs! Then I can simplify this stuff. *)
        assert (<fun p => proj2 p> = <fun x => proj2 x>). solve_all.
        rewrite H3.
        reflexivity.
        unfold ifexpr.
        normalize.
        rewrite H4.
        normalize.
        apply S0_t1.
    (* Empty *)
    + solve_all.
Qed.
     

(*Definition In : QTerm -> QTerm -> Prop :=
  fun t T => exists S i, In'' i T S /\ S t.*)

Theorem consistency : forall t,
    Typed nil Empty t -> False.
Proof.
  intros.
  pose (fundamental_lemma nil Empty t nil H in_nil) as x.
  destruct x.
  destruct H0.
  inversion H0; solve_all.
  rewrite <- H2 in H1.
  assumption.
Qed.
