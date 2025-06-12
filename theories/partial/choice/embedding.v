Require Import String.
Require Import qterm.
Require Import lambdaFacts.
Require Import lambdaSolve.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import choiceBase.
Require Import prog2.
Require Import pmatch.
Require Import automation.

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

Inductive Typed : (*context*) QTerm -> (*level*) nat -> (*Type*) QTerm -> (*Term*) QTerm -> Prop :=
| ty_lambda : forall ctx A B s lvl,
    Typed ctx (S lvl) <`U(*{const lvl}*)> <`pi `A `B> ->
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
.

Ltac solve_no_unfold := repeat (lambda_solve ; repeat neutral_inj_case ;lambda_solve
                  ; repeat fast_neutral_unequal_case). 

Ltac solve_all := repeat (unfold_all ; lambda_solve ; repeat neutral_inj_case ;lambda_solve
                          ; repeat fast_neutral_unequal_case).

Fixpoint In (level : nat) : QTerm -> option (QTerm -> Prop).
  refine (runProg (fun T =>
                     (* Pi A B *)
                     Pmatch2 (fun A B => T = <Pi `A `B>)
                            (fun A B => Rec _ _ unit (fun _ => A)
                                       (fun InA => Rec _ _ {a | InA tt a} (fun a => <`B {proj1_sig a}>)
                                       (fun InB => Ret _ _ (Some
                                       (fun f => forall a (ina : InA tt a), InB (exist _ a ina) <`f `a>)))))
                     (* Bool *)
                    (Pif (T = <Bool>)
                         (Ret _ _ (Some (fun b => b = <fun x => proj1 x> \/ b = <fun x => proj2 x>)))
                         (Ret _ _ None)))).
Defined.

Inductive InCtx : QTerm -> QTerm -> Prop :=
| in_nil : InCtx nil nil
| in_cons : forall env ctx lvl val T s,
    InCtx env ctx
    -> In (S lvl) <`T `env>  = Some s (* is the successor here correct? *)
    -> s val
    -> InCtx <`env , `val> <`cons `ctx {const lvl} `T>.

Theorem fundamental_lemma : forall ctx T lvl t env,
    Typed ctx lvl T t
    -> InCtx env ctx
    -> exists s, In (S lvl) <`T `env> = Some s (* TODO: S lvl? In 0 is just empty. *)
    /\ s <`t `env>.
Proof.
  intros.
  generalize dependent env.
  induction H.
  (* lambda *)
  - intros env inctx.
    specialize (IHTyped1 env inctx) as [SU [InU piAB_in_SU]].
    evaluate_function_in solve_all InU.

    give_up.
  (* app *)
  - intros env inctx.
    specialize (IHTyped1 env inctx) as [SPIAB [inPiAB s1Elem]].
    specialize (IHTyped2 env inctx) as [SA [inA s2Elem]].
    (* this is how fold works: *)
    unfold In in inPiAB.
    progress fold (In (S lvl) <`pi `A `B `env>) in inPiAB.
    (**)
    assert (In (S lvl) <`pi `A `B `env> =
              bind (In (S lvl) <`A `env>) (fun InA =>
              bind (collectOption (fun a => In (S lvl) <`B {proj1_sig a}>)) (fun InB =>
              (Some (fun f => forall a (ina : InA a), InB (exist _ a ina) <`f `a>))))). {
      unfold pi.
      evaluate_function solve_all.
      reflexivity.
      
    unfold pi in inPiAB.
    evaluate_function_in solve_all inPiAB.
    (* I want to be able to do (fold (In (S lvl) A)) for example here.*)
    Print runProgImpl.
    Print chooseOption.
    evaluate_function_in solve_all inA.
    rewrite inA in inPiAB.
    rewrite inPiAB in s1Elem.
    clear inPiAB inA
    eexists.
    evaluate_function solve_all.
    progress fold (In (S lvl) <`A `env>) in H1.
    (*
    (erewrite Pmatch2Def1 in inPiAB ; [| solve [solve_all]
                                 | solve [intros; solve_all] | solve [intros; solve_all]]).
     *)
    Check @runProg.
    progress fold (@runProg QTerm (QTerm -> Prop)) in inPiAB.
    progress fold In in inPiAB.
    erewrite Pmatch2Def1 in inPiAB.
    2: {
      solve_all.
    }
    2: {
      intros.
      solve_all.
    }
    2: {
      intros.
      solve_all.
    }
    (* Where I left off: I added Pmatch2 because using a product was messing up the automation.
     I haven't gotten the rewrites for Pmatch2 in the tactic correct yet. *)
    erewrite Pmatch2Def1 in inPiAB.
    Check @PmatchDef1.
    erewrite (@PmatchDef1 _ _ _ ?[t]) in inPiAB.
    3: {
      intros.
      destruct t1, t2.
      solve_all.
    }
    2: {
      solve_all.
      neutral_inj_case.

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
