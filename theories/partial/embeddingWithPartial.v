Require Import String.
Require Import qterm.
Require Import lambdaFacts.
Require Import lambdaSolve.
Require Import partial.

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
(*
| ty_Empty : forall ctx, Typed ctx <`U> Empty
 *)
| ty_Bool : forall ctx, Typed ctx <`U> Bool
| ty_pi : forall ctx A B,
    Typed ctx <`U> A
    -> Typed <`cons `ctx `A> <`U> B -> Typed ctx <`U> <`pi `A `B>
.

Ltac solve_no_unfold := repeat (lambda_solve ; repeat neutral_inj_case ;lambda_solve
                  ; repeat fast_neutral_unequal_case). 

Ltac solve_all := repeat (unfold_all ; lambda_solve ; repeat neutral_inj_case ;lambda_solve
                  ; repeat fast_neutral_unequal_case). 


(* The identity function is typed at U -> U*)
Theorem test1 : Typed nil <`pi `Bool `Bool> <`lambda `zero>.
(*Theorem test1 : Typed nil <`pi (fun env => asdf) (fun env => asdf)> <`lambda `zero>.*)
Proof.
  apply ty_lambda.
  apply ty_pi.
  apply ty_Bool.
  apply ty_Bool.
  apply ty_var.
  Check ty_zero.
  apply_cast ty_zero.
  unfold_all.
  lambda_solve.
Qed.
Inductive Empty_type : Type :=.

Definition False_elim {T : Type} : False -> T := fun x => match x with end.
Definition In : QTerm -> Partial (QTerm -> Prop).
  Check runProg2.
  Check Pmatch.
  Check Empty_type.

  (* I think that runProg2 isn't even strong enough (although it is possible to do)
   In the case "[Pi A B] = {f | forall a, [A] a -> [B a] (f a)}"
   We need to recur on all (B a) such that [A] a. In other words, in order to even
   construct the set of terms on which we recur, we need to already have recurred once.
   I could fix this by combining the Prog datatype with the idea from runProg2.
   But things are already getting unreadable, it is not very appealing. *)
  refine (runProg2 (fun t =>
              Pmatch (fun _ : unit => t = <Bool>)
                     _ (fun _ => Preturn (existT _ (False : Type) (False_elim , fun _ =>
                               Preturn (fun b => b = <fun x => proj1 x> \/ b = <fun x => proj2 x>))))
                     (Pmatch (fun AB : QTerm * QTerm => match AB with (A , B) => t = <Pi `A `B> end)
                             _ (fun AB => match AB with (A , B) =>
                                   Preturn (existT _ (unit + {a | })) end)
                             _)
         )).







Inductive In': QTerm -> (QTerm -> Prop) -> Prop:=
| in_Pi : forall (S : QTerm -> Prop) (F : forall a, (*S a ->*) QTerm -> Prop) A B,
    In' A S
    -> (forall a (s : S a), In' <`B `a> (F a (*s*)))
    -> In' <Pi `A `B> (fun f => forall a (s : S a), F a (*s*) <`f `a>)
| in_Bool :  In' <Bool> (fun b => b = <fun x => proj1 x> \/ b = <fun x => proj2 x>)
| in_Empty : In' <Empty> (fun _ => False)
.

Inductive In : QTerm -> (QTerm -> Prop) -> Prop :=
| in' : forall T S, In' T S -> In T S
| in_type : In <U> (fun T => exists S, In' T S)
.

Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Theorem In_function : forall T S1 S2, In T S1 -> In T S2 -> S1 = S2.
Proof.
  intros T S1 S2 in1.
  generalize S2.
  clear S2.
  induction in1 as [T S in1 | typeCase].
  induction in1 as [ S F A B In_A_S In_A_S_only In_Ba_Fa In_Ba_Fa_only | | ].
  - intros S2 in2.
    inversion in2 as [T S'' in2' | ].
    inversion in2' as [S' F' A' B' In_A_S' In_Ba_F'a eq extra | | ].
    + (* Pi Pi *)
      solve_all.
      clear extra.
      clear in2.
      (*clear S''.*)
      specialize (In_A_S_only S' (in' _ _ In_A_S')).
      subst S'.

      assert (forall a, S a -> F a = F' a).
      {
        intros.
        apply In_Ba_Fa_only.
        apply H.
        apply in'.
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
    + (* Pi Type *) solve_all.
  - intros.
    inversion H.
    inversion H0.
    * (* Bool Pi *) solve_all.
    * (* Bool Bool *) solve_all.
    * (* Bool Empty *) solve_all.
    * (* Bool Type *) solve_all.
  - intros.
    inversion H.
    inversion H0.
    * (* Empty Pi *) solve_all.
    * (* Empty Bool *) solve_all.
    * (* Empty Empty *) solve_all.
    * (* Empty Type *) solve_all.
  - intros.
    inversion H.
    inversion H0; solve_all. (* Type x anything cases*)
    reflexivity. (* Type Type case*)
Qed.

(* Will this work? In contrast to the logical relation itself, this is QTerm -> QTerm -> Prop
instead of QTerm -> (QTerm -> Prop) -> Prop. This seems to correspond to Yiyun's paper. *)
(* first arg env, second arg ctx. Idk why I did it like that, its opposite other conventions
in this file. *)
Inductive InCtx : QTerm -> QTerm -> Prop :=
| in_nil : InCtx nil nil
| in_cons : forall env ctx val T S,
    InCtx env ctx
    -> In <`T `env> S
    -> S val
    -> InCtx <`env , `val> <`cons `ctx `T> 
.

Theorem fundamental_lemma_for_variables : forall ctx T t env,
    VarTyped ctx T t -> InCtx env ctx -> exists S, In <`T `env> S /\ S <`t `env>.
Proof.
  intros.
  generalize env, H0.
  clear H0.
  clear env.
  induction H.
  -
    intros env inctx.
    inversion inctx.
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
  - intros env inctx.
    unfold pi.
    normalize.
    (* We need to show the "In (Pi ...) ..." from the goal by instantiating in_Pi.
       but how can I get the In A _ argument needed? *)
    Check in_Pi.
    (* If I had that, could I do the rest?
       In Yiyun's paper, he has that (Pi A B) is well typed in the lambda constructor.
       For now, I will assume that as holes and see if the rest works. *)
    specialize (IHTyped1 env inctx).
    destruct IHTyped1 as [SU temp].
    destruct temp as [InUPiAB SPiABPiAB].
    inversion InUPiAB.
    inversion H1; solve_all. (* can't be any of the non-U cases *)
    rewrite <- H1 in SPiABPiAB.
    destruct SPiABPiAB as [SPiAB In'PiAB].
    inversion In'PiAB; try solve_all.
    assert (In' <`A `env> S) as INA.
    {
      apply H4.
    }
    (*destruct H1 as [SA In_A_SA].*)
    assert (forall a : QTerm, S a -> In' <`B (`env , `a)> (F a)) as In_Ba_Fa.
    {
      intros a sa.
      specialize (H5 a sa).
      normalize_in H5.
      apply H5.
    }
    Check in_Pi.
    Check (in_Pi S F <`A `env> <fun a => `B[a] (`env[a] , a)> H4).
    (*assert (forall a, <(fun a => `B[a] (`env[a] , a)) `a> = <`B (`env , `a)>). { intros. lambda_solve.}*)
    assert (forall a : QTerm, S a -> In' <(fun a => `B[a] (`env[a] , a)) `a> (F a)) as In_Ba_Fa_2.
    {
      intros.
      lambda_solve.
      apply In_Ba_Fa.
      apply H2.
    }
    exists (fun f : QTerm => forall a : QTerm, S a -> F a <`f `a>).
    split.
    Check (in_Pi S F <`A `env> <fun a => `B[a] (`env[a] , a)> H4 In_Ba_Fa_2).
    apply in'.
    apply (in_Pi S F <`A `env> <fun a => `B[a] (`env[a] , a)> H4 In_Ba_Fa_2).
    intros a SAa.
    Check in_cons.
    specialize (In_Ba_Fa a SAa).
    (*Check (IHTyped2 <`env , `a> (in_cons _ _ _ _ S inctx (in' _ _ H4) SAa)).*)
    Check in_cons.
    specialize (IHTyped2 <`env , `a>).
    assert (<cons `ctx `A> = <`cons `ctx `A>). unfold cons. normalize. reflexivity.
    rewrite H2 in IHTyped2.
    destruct (IHTyped2 (in_cons _ _ _ _ S inctx (in' _ _ INA) SAa)) as [Fa' temp].
    destruct temp as [InBFa' Fa's].
    unfold lambda.
    normalize.
    Check In_function.
    rewrite (In_function _ _ _ (in' _ _ In_Ba_Fa) InBFa').
    apply Fa's.
  (* app *)
  - intros env inctx.
    specialize (IHTyped1 env inctx).
    specialize (IHTyped2 env inctx).
    destruct IHTyped1 as [SPIAB temp].
    destruct temp as [inPiAB s1Elem].
    destruct IHTyped2 as [SA temp].
    destruct temp as [inA s2Elem].
    inversion inPiAB as [T S in'PiAB | TODOTODO ].
    inversion in'PiAB as [ SA' F A' B' In_A'_SA' In_B'a_F'a eq | |].
    (* The real case *)
    +
      unfold pi in eq.
      solve_no_unfold.
      assert (SA' = SA). {apply (In_function _ _ _ (in' _ _ In_A'_SA') inA).}
      subst SA'.
      exists (F <`s2 `env>).
      specialize (In_B'a_F'a <`s2 `env> s2Elem).
      normalize_in In_B'a_F'a.
      split.
      unfold subLast.
      normalize.
      apply in'.
      apply In_B'a_F'a.
      rewrite <- H4 in s1Elem.
      specialize (s1Elem <`s2 `env> s2Elem).
      unfold app.
      normalize.
      apply s1Elem.
    (* Its not Type *)
    + solve_all.
    (* Its not empty*)
    + solve_all.
    + solve_all.
  (* var *)
  - intros env inctx.
    apply (fundamental_lemma_for_variables ctx T t env H inctx).
  (* true *)
  - intros env inctx.
    exists (fun b => b = <fun x => proj1 x> \/ b = <fun x => proj2 x>).
    unfold Bool.
    normalize.
    split.
    apply in'.
    apply in_Bool.
    apply or_introl.
    solve_all.
  (* false *)
  - intros.
    exists (fun b => b = <fun x => proj1 x> \/ b = <fun x => proj2 x>).
    unfold Bool.
    normalize.
    split.
    apply in'.
    apply in_Bool.
    apply or_intror.
    solve_all.
  (* if *)
  - intros env inctx.
    specialize (IHTyped1 env inctx).
    destruct IHTyped1 as [S temp].
    destruct temp as [In_Bool_S S_cond].
    inversion In_Bool_S as [T0 S0' In_Bool_S' | TODOTODO ].
    inversion In_Bool_S'.
    (* Pi *)
    + solve_all.
    (* Bool *)
    + rewrite <- H4 in S_cond.
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
        rewrite H6.
        split.
        apply_cast In_Ttrue_S0.
        solve_all.
        (* TODO: make solve_all handle pairs! Then I can simplify this stuff. *)
        assert (<fun p => proj1 p> = <fun x => proj1 x>). solve_all.
        rewrite H2.
        reflexivity.
        unfold ifexpr.
        normalize.
        rewrite H6.
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
        rewrite H6.
        split.
        apply_cast In_Ttrue_S0.
        solve_all.
        (* TODO: make solve_all handle pairs! Then I can simplify this stuff. *)
        assert (<fun p => proj2 p> = <fun x => proj2 x>). solve_all.
        rewrite H2.
        reflexivity.
        unfold ifexpr.
        normalize.
        rewrite H6.
        normalize.
        apply S0_t1.
    (* Empty *)
    + solve_all.
    (* Type case *)
    + solve_all.
  (* Bool : Type *)
  - intros.
    exists (fun T => exists S, In' T S).
    unfold U. normalize.
    Check in_type.
    split.
    apply in_type.
    exists (fun b => b = <fun x => proj1 x> \/ b = <fun x => proj2 x>).
    unfold Bool.
    normalize.
    apply in_Bool.
  (* Pi : Type*)
  - intros env inctx.
    Check in_Pi.
    (*
      To summarize, our induction hypotheses are that:
      1) In any environment related to ctx, A has an interpreetation
      2) In any environment related to (cons ctx A), B has an interpreetation
      And we need to show that:
         In an environment related to ctx, (Pi A B) has an interpretation.


      I think that this should work, but we may need to modify in_Pi so that
      instead of
      F : QTerm -> QTerm -> Prop
      we have
      F : forall (a : QTerm), S a -> QTerm -> Prop.
      I'm not sure yet if this is needed though.
     *)
    exists (fun T => exists S, In' T S).
    unfold U. normalize.
    split.
    apply in_type.
    specialize (IHTyped1 env inctx).
    Check in_Pi.
    destruct IHTyped1 as [SAU temp].
    destruct temp as [InUSA SAA].
    inversion InUSA.
    inversion H1; solve_all.
    rewrite <- H1 in SAA.
    destruct SAA as [SA InASA].

    pose (fun (a : QTerm) (sa : SA a) => IHTyped2 <`env, `a>
                   (in_cons _ _ _ _ _ inctx (in' _ _ InASA) sa)) as thing.

    Set Nested Proofs Allowed.
    Lemma hasInterp : forall t env, (exists S, In <`U `env> S /\ S t) -> (exists S', In' t S').
    Proof.
      intros.
      destruct H.
      destruct H.
      inversion H.
      inversion H1; solve_all.
      rewrite <- H1 in H0.
      apply H0.
    Defined.

    pose (fun (a : QTerm) (sa : SA a) =>
            hasInterp _ _ (IHTyped2 <`env, `a>
                (in_cons _ _ _ _ _ inctx (in' _ _ InASA) sa))) as thing2.
    
    (*pose (fun (a : QTerm) (b : QTerm) => forall (sa : SA a),
              match (thing2 a sa) with
              | ex_intro _ SB _ => SB b
              end) as F.*)
    pose (fun (a b : QTerm) => exists SB, In' <`B (`env , `a)> SB /\ SB b) as F.
    assert (forall a (s : SA a), In' <`B (`env ,`a)> (F a)).
    {
      intros a SAa.
      destruct (thing2 a SAa) as [SB INBSB].
      assert (F a = SB).
      apply functional_extensionality.
      intros b.
      unfold F.
      apply propositional_extensionality.
      split.
      intros.
      destruct H3.
      destruct H3.
      rewrite <- (In_function _ _ _ (in' _ _ INBSB) (in' _ _ H3)) in H4.
      assumption.
      intros SBb.
      exists SB.
      split.
      assumption.
      assumption.
      rewrite <- H3 in INBSB.
      assumption.
    }
    assert (forall a : QTerm, SA a -> In' <(fun a => `B [a] (`env [a], a)) `a> (F a)).
    {
      intros a sa.
      normalize.
      apply H3.
      apply sa.
    }

    Check in_cons.
    Check (in_cons _ _ _ _ _ inctx (in' _ _ InASA)).
    Check (in_Pi SA F <`A `env> <fun a => `B[a] (`env[a] , a)> InASA H4).
    exists (fun f : QTerm => forall a : QTerm, SA a -> F a <`f `a>).
    unfold pi.
    normalize.
    apply (in_Pi SA F <`A `env> <fun a => `B[a] (`env[a] , a)> InASA H4).
Qed.
     
Theorem consistency : forall t,
    Typed nil Empty t -> False.
Proof.
  intros.
  pose (fundamental_lemma nil Empty t nil H in_nil) as x.
  destruct x.
  destruct H0.
  inversion H0; inversion H2; solve_all.
  rewrite <- H5 in H1.
  assumption.
Qed.
