Require Import String.
Require Import Lia.

(*
One idea is that I could implement lambdaFP from scratch without autosubst.
I'm going to at least consider it in this file.
 *)

Inductive Constant :=
| pi1c : Constant
| pi2c : Constant
| pairc : Constant
| constc : string -> Constant.

Inductive Term : Type :=
| lam : string -> Term -> Term
| app : Term -> Term -> Term
| const : Constant -> Term
| var : string -> nat -> Term (*nth variable with that name, going up like debruin indices*).

Fixpoint lift : string -> nat -> Term -> Term :=
  fun s k t =>
    match t with
    | lam s' t' => lam s' (lift s (if eqb s' s then S k else k) t')
    | app t1 t2 => app (lift s k t1) (lift s k t2)
    | var s' i => if andb (String.eqb s s') (negb (Nat.ltb i k))
                  then var s' (S i)
                  else var s' i
    | const c => const c
    end.

Fixpoint subst : string -> nat -> Term -> Term -> Term :=
  fun s k toSub t =>
    match t with
    | lam s' t' => if String.eqb s' s
                  then lam s' (subst s (S k) (lift s' 0 toSub) t')
                  else lam s' (subst s k (lift s' 0 toSub) t')
    | app t1 t2 => app (subst s k toSub t1) (subst s k toSub t2)
    | var s' i => if String.eqb s s'
                  then if Nat.ltb k i
                       then var s' (pred i)
                       else if Nat.eqb i k
                            then toSub
                            else var s' i
                  else var s' i
    | const c => const c
    end.

Ltac rewrite_by_lia H :=
  let eq := fresh "eq" in
  assert H as eq; [
      repeat rewrite
             ?PeanoNat.Nat.ltb_lt,
      ?PeanoNat.Nat.ltb_ge,
      ?PeanoNat.Nat.eqb_eq,
      ?PeanoNat.Nat.eqb_neq in *;
      lia
    | rewrite eq; clear eq].

Ltac prove_by_lia H :=
  let eq := fresh "eq" in
  assert H as eq; [
      repeat rewrite
             ?PeanoNat.Nat.ltb_lt,
      ?PeanoNat.Nat.ltb_ge,
      ?PeanoNat.Nat.eqb_eq,
      ?PeanoNat.Nat.eqb_neq in *;
      lia
    |].
      
Theorem subst_lift : forall s i t1 t2, subst s i t1 (lift s i t2) = t2.
Proof.
  intros.
  generalize dependent t1.
  generalize dependent i.
  induction t2.
  - intros.
    simpl.
    destruct (eqb s0 s).
    + apply f_equal.
      rewrite IHt2.
      reflexivity.
    + apply f_equal.
      rewrite IHt2.
      reflexivity.
  - intros.
    simpl.
    apply f_equal2.
    + apply IHt2_1.
    + apply IHt2_2.
  - intros.
    reflexivity.
  - intros.
    simpl.
    destruct (eqb s s0) eqn : H1.
    + simpl.
      destruct (Nat.ltb n i) eqn : H2, (Nat.ltb i n) eqn : H3.
      ++ simpl.
         rewrite PeanoNat.Nat.ltb_lt in H3, H2.
         lia.
      ++ simpl.
         rewrite H1.
         rewrite H3.
         rewrite_by_lia (Nat.eqb n i = false).
         reflexivity.
      ++ simpl.
         rewrite H1.
         rewrite_by_lia (Nat.ltb i (S n) = true).
         reflexivity.
      ++ simpl.
         rewrite H1.
         rewrite_by_lia (Nat.ltb i (S n) = true).
         reflexivity.
    + simpl.
      rewrite H1.
      reflexivity.
Qed.


Ltac contradiction_by_lia :=
  exfalso;
  repeat rewrite
         ?PeanoNat.Nat.ltb_lt,
    ?PeanoNat.Nat.ltb_ge,
    ?PeanoNat.Nat.eqb_eq,
    ?PeanoNat.Nat.eqb_neq in *;
  lia.

Ltac contradiction_by_string_equality :=
  exfalso;
  repeat rewrite ?eqb_eq, ?eqb_neq in *;
  subst;
  contradiction.

Ltac case_nat_comparisons :=
  let Hnew := fresh "Hnew" in
  try (
      match goal with
      | H : Nat.ltb ?x ?y = ?b |- _ => rewrite H
      | H : eqb ?x ?y = ?b |- _ => rewrite H
      | H : Nat.eqb ?x ?y = ?b |- _ => rewrite H
      | |- context [Nat.ltb ?x ?y] => destruct (Nat.ltb x y) eqn: Hnew
      | |- context [eqb ?x ?y] => destruct (eqb x y) eqn: Hnew
      | |- context [Nat.eqb ?x ?y] => destruct (Nat.eqb x y) eqn: Hnew
      end;
      try contradiction_by_lia;
      try contradiction_by_string_equality;
      simpl; case_nat_comparisons
    ).

Ltac fix_preds :=
  repeat match goal with
    | |- context [S (Nat.pred ?x)] =>
        rewrite_by_lia (S (Nat.pred x) = x)
    end.


Theorem lift_lift : forall s1 s2 i1 i2 t,
    lift s1 i1 (lift s2 i2 t) =
      if eqb s1 s2
      then if Nat.ltb i2 i1
           then lift s2 i2 (lift s1 (pred i1) t)
           else lift s2 (S i2) (lift s1 i1 t)
      else lift s2 i2 (lift s1 i1 t).
Proof.
  intros.
  generalize dependent i1.
  generalize dependent i2.
  induction t.
  (* lam *)
  - intros.
    simpl.
    case_nat_comparisons; fix_preds; rewrite IHt; case_nat_comparisons; reflexivity.
  (* app *)
  - intros.
    simpl.
    rewrite IHt1, IHt2.
    simpl.
    case_nat_comparisons; reflexivity.
  (* const *)
  - intros.
    simpl.
    case_nat_comparisons; reflexivity.
  (* var *)
  - intros.
    case_nat_comparisons; reflexivity.
Qed.

Theorem lift_subst : forall s1 s2 i1 i2 t1 t,
    lift s1 i1 (subst s2 i2 t1 t) =
      if eqb s1 s2
      then if Nat.ltb i1 i2
           then subst s2 (S i2) (lift s1 i1 t1) (lift s1 i1 t)
           else subst s2 i2 (lift s1 i1 t1) (lift s1 (S i1) t)
      else subst s2 i2 (lift s1 i1 t1) (lift s1 i1 t).
Proof.
  intros.
  generalize dependent t1.
  generalize dependent i1.
  generalize dependent i2.
  induction t.
  (* lam *)
  - intros.
    simpl.
    case_nat_comparisons; rewrite IHt; rewrite lift_lift; case_nat_comparisons; reflexivity.
  (* app *)
  - intros.
    simpl.
    rewrite IHt1, IHt2.
    simpl.
    case_nat_comparisons; reflexivity.
  (* const *)
  - intros.
    simpl.
    case_nat_comparisons; reflexivity.
  (* var *)
  - intros.
    case_nat_comparisons; fix_preds; reflexivity.
Qed.

(* Maybe you can't swap subst and lift in this order in general? *)
(*Theorem subst_lift : forall s1 s2 i1 i2 t1 t,
    subst s1 i1 t1 (lift s2 i2 t) =
      if eqb s1 s2
      then _
      else lift s2 i2 (subst
 *)

Theorem subst_lift_off_by_1 : forall s i t1 t,
    subst s (S i) t1 (lift s i t) = subst s i t1 (lift s (S i) t).
Proof.
  intros.
  generalize dependent i.
  generalize dependent t1.
  induction t.
  (* lam *)
  - intros.
    simpl.
    case_nat_comparisons; rewrite IHt; reflexivity.
  (* app *)
  - intros.
    simpl.
    rewrite IHt1, IHt2.
    case_nat_comparisons; reflexivity.
  (* const *)
  - intros.
    simpl.
    reflexivity.
  (* var *)
  - intros.
    simpl.
    case_nat_comparisons; reflexivity.
Qed.
Search le eq.
Ltac simplify_nat_string_eqs :=
  repeat rewrite ?eqb_eq,
    ?eqb_neq,
    ?PeanoNat.Nat.ltb_lt,
    ?PeanoNat.Nat.ltb_ge,
    ?PeanoNat.Nat.eqb_eq,
    ?PeanoNat.Nat.eqb_neq in *;
  repeat match goal with
  | H : le ?x 0 |- _ => apply Arith_base.le_n_0_eq_stt in H
  end;
  subst.
    
Theorem subst_subst : forall s1 s2 i1 i2 t1 t2 t,
    subst s1 i1 t1 (subst s2 i2 t2 t) =
      if eqb s1 s2
      then if Nat.ltb i1 i2
           then subst s2 (pred i2) (subst s1 i1 t1 t2) (subst s1 i1 (lift s2 (pred i2) t1) t)
           else subst s2 i2 (subst s1 i1 t1 t2) (subst s1 (S i1) (lift s2 i2 t1) t)
      else subst s2 i2 (subst s1 i1 t1 t2) (subst s1 i1 (lift s2 i2 t1) t).
Proof.
  intros.
  generalize dependent t1.
  generalize dependent t2.
  generalize dependent i1.
  generalize dependent i2.
  induction t.
  - intros.
    simpl.
    case_nat_comparisons; fix_preds; rewrite IHt; case_nat_comparisons;
      rewrite lift_lift; rewrite lift_subst; case_nat_comparisons; try reflexivity;
      try (
          simplify_nat_string_eqs;
          rewrite subst_lift_off_by_1;
          reflexivity).
  - simpl.
    intros.
    rewrite IHt1, IHt2.
    simpl.
    case_nat_comparisons; reflexivity.
  - intros.
    simpl.
    case_nat_comparisons; reflexivity.
  - intros.
    simpl.
    Time case_nat_comparisons; try reflexivity; try (rewrite subst_lift; reflexivity).
Qed.

Definition pair t1 t2 := (app (app (const pairc) t1) t2).
Definition pi1 t := app (const pi1c) t.
Definition pi2 t := app (const pi2c) t.
Definition constant (t : string) : Term := const (constc t).

Inductive red : Term -> Term -> Prop :=
(* Congruences *)
| red_lam : forall s a b, red a b -> red (lam s a) (lam s b)
| red_app1 : forall a b c, red a b -> red (app a c) (app b c)
| red_app2 : forall a b c, red a b -> red (app c a) (app c b)
(* Meaningful things *)
| red_beta : forall s a b, red (app (lam s a) b) (subst s 0 b a)
| red_pi1 : forall a b, red (pi1 (pair a b)) a
| red_pi2 : forall a b, red (pi2 (pair a b)) b
| red_eta : forall s t, red t (lam s (lift s 0 t))
| red_SP : forall t, red t (pair (pi1 t) (pi2 t))
.

Inductive parb : Term -> Term -> Prop :=
(* Congruences *)
| par_lam : forall s a b, parb a b -> parb (lam s a) (lam s b)
| par_app : forall {a a' b b'},
    parb a a' -> parb b b' -> parb (app a b) (app a' b')
(* Meaningful things *)
| par_beta : forall s a a' b b',
    parb a a' -> parb b b' ->
    parb (app (lam s a) b) (subst s 0 b' a')
| par_pi1 : forall a a' b,
    parb a a' -> parb (pi1 (pair a b)) a' (* TODO: the input*)
| par_pi2 : forall a b b',
    parb b b' -> parb (pi2 (pair a b)) b'
| parb_const : forall c, parb (const c) (const c)
| parb_var : forall s i, parb (var s i) (var s i).

Theorem parb_id : forall t, parb t t.
Proof.
  intros.
  induction t; repeat (try constructor; try assumption).
Qed.

Theorem parb_lift : forall t1 t2 s i,
    parb t1 t2
    -> parb (lift s i t1) (lift s i t2).
Proof.
  intros.
  generalize dependent i.
  induction H.
  (* par_lam *)
  - simpl.
    intros.
    destruct (eqb s0 s).
    + apply par_lam.
      apply IHparb.
    + apply par_lam.
      apply IHparb.
  (* par_app *)
  - intros.
    simpl.
    apply par_app.
    + apply IHparb1.
    + apply IHparb2.
  (* beta *)
  - intros.
    simpl.
    case_nat_comparisons.
    +
      rewrite lift_subst.
      case_nat_comparisons.
      apply par_beta.
      * apply IHparb1.
      * apply IHparb2.
    + rewrite lift_subst.
      case_nat_comparisons.
      apply par_beta.
      * apply IHparb1.
      * apply IHparb2.
  (* pi1 *)
  - intros.
    simpl.
    apply par_pi1.
    apply IHparb.
  (* pi2 *)
  - intros.
    apply par_pi2.
    apply IHparb.
  (* par_const *)
  - intros.
    constructor.
  - intros.
    apply parb_id.
Qed.
(* TODO: The above theorem is almost identical to parb_subst. Can I do something about that? *)

Theorem parb_subst : forall a b c d s i,
    parb a c
    -> parb b d
    -> parb (subst s i a b) (subst s i c d).
Proof.
  (* This doesn't actually follow from the other two does it *)
  intros.
  generalize dependent c.
  generalize dependent a.
  generalize dependent i.
  induction H0.
  (* par_lam *)
  - intros.
    simpl.
    case_nat_comparisons;
      apply par_lam;
      apply IHparb;
      apply parb_lift;
      assumption.
  (* par_app *)
  - intros.
    simpl.
    apply par_app.
    + apply IHparb1.
      assumption.
    + apply IHparb2.
      assumption.
  (* beta *)
  - intros.
    simpl.
    case_nat_comparisons.
    + rewrite subst_subst.
      case_nat_comparisons.
      apply par_beta.
      * apply IHparb1.
        apply parb_lift.
        assumption.
      * apply IHparb2.
        assumption.
    + rewrite subst_subst.
      case_nat_comparisons.
      apply par_beta.
      * apply IHparb1.
        apply parb_lift.
        assumption.
      * apply IHparb2.
        assumption.
  (* pi1 *)
  - intros.
    simpl.
    apply par_pi1.
    apply IHparb.
    assumption.
  (* pi2 *)
  - intros.
    apply par_pi2.
    apply IHparb.
    assumption.
  (* par_const *)
  - intros.
    constructor.
  - intros.
    simpl.
    case_nat_comparisons; try apply parb_id.
    + assumption.
Qed.

Ltac invert_singletons :=
  repeat match goal with
         | H : parb ?x ?y |- _ => inversion H; [clear H; subst]
         end.

Theorem parb_diamond : forall a b c,
    parb a b
    -> parb a c
    -> exists d, parb b d /\ parb c d.
Proof.
  intros.
  generalize dependent H0.
  generalize dependent c.
  induction H.
  (* par_lam *)
  - intros.
    inversion H0.
    (* par_lam x par_lam *)
    + subst.
      specialize (IHparb _ H4).
      destruct IHparb.
      destruct H1.
      eexists.
      split.
      
      * apply par_lam.
      apply H1.
      * apply par_lam.
        apply H2.
  (* par_app *)
  - intros.
    inversion H1.
    (* par_app x par_app *)
    + subst.
      specialize (IHparb1 _ H4) as [out1 [p1 q1]].
      specialize (IHparb2 _ H6) as [out2 [p2 q2]].
      exists (app out1 out2).
      split; apply par_app; assumption.
    (* par_app x par_beta *)
    + subst.
      inversion H; clear H; subst.
      specialize (IHparb1 _ (par_lam _ _ _ H4)) as [out1 [p1 q1]].
      specialize (IHparb2 _ H6) as [out2 [p2 q2]].
      inversion p1; clear p1; subst.
      inversion q1; clear q1; subst.
      exists (subst s 0 out2 b1).
      split.
      * apply par_beta.
        assumption.
        assumption.
      * Check parb_subst.
        apply parb_subst; assumption.
    (* par_app x par_pi1 *)
    + subst.
      invert_singletons.
      specialize (IHparb1 _ (parb_const pi1c)) as [out1 [p1 q1]].
      specialize (IHparb2 _ (par_app (par_app (parb_const pairc) H5) H7)) as [out2 [p2 q2]].
      invert_singletons.
      exists b'2.
      split.
      * apply par_pi1.
        assumption.
      * assumption.
    + subst.
      invert_singletons.
      specialize (IHparb1 _ (parb_const pi2c)) as [out1 [p1 q1]].
      specialize (IHparb2 _ (par_app (par_app (parb_const pairc) H8) H5)) as [out2 [p2 q2]].
      invert_singletons.
      exists b'1.
      split.
      * apply par_pi2.
        assumption.
      * assumption.
  (* par_beta *)
  - intros.
    inversion H1; clear H1; subst.
    (* par_beta x par_app *)
    + invert_singletons.
      specialize (IHparb1 _ H5) as [out1 [p1 q1]].
      specialize (IHparb2 _ H6) as [out2 [p2 q2]].
      exists (subst s 0 out2 out1).
      split.
      * apply parb_subst; assumption.
      * apply par_beta; assumption.
    (* par_beta x par_beta *)
    + specialize (IHparb1 _ H6) as [out1 [p1 q1]].
      specialize (IHparb2 _ H7) as [out2 [p2 q2]].
      exists (subst s 0 out2 out1).
      split.
      * apply parb_subst; assumption.
      * apply parb_subst; assumption.
  (* par_pi1 *)
  - intros.
    inversion H0; clear H0; subst.
    (* par_pi1 x par_app *)
    + invert_singletons.
      specialize (IHparb _ H7) as [out [p q]].
      exists out.
      split.
      * assumption.
      * apply par_pi1.
        assumption.
    (* par_pi1 x par_pi1 *)
    + specialize (IHparb _ H4) as [out [p q]].
      exists out.
      split; assumption.
  (* par_pi2 *)
  - intros.
    inversion H0; clear H0; subst.
    (* par_pi2 x par_app *)
    + invert_singletons.
      specialize (IHparb _ H6) as [out [p q]].
      exists out.
      split.
      * assumption.
      * apply par_pi2.
        assumption.
    (* par_pi2 x par_pi2 *)
    + specialize (IHparb _ H4) as [out [p q]].
      exists out.
      split; assumption.
  (* par_const x par_const *)
  - intros.
    invert_singletons.
    exists (const c).
    split; constructor.
  (* par_var x par_var *)
  - intros.
    invert_singletons.
    exists (var s i).
    split; constructor.
Qed.

Inductive pare : Term -> Term -> Prop :=
(* Congruences *)
| pare_lam : forall s a b, pare a b -> pare (lam s a) (lam s b)
| pare_app : forall {a a' b b'},
    pare a a' -> pare b b' -> pare (app a b) (app a' b')
| pare_const : forall c, pare (const c) (const c)
| pare_var : forall s i, pare (var s i) (var s i)
(* Meaningful things *)
| par_eta : forall s a b,
    pare a b -> pare a (lam s (app (lift s 0 b) (var s 0)))
| par_SP : forall a b,
    pare a b -> pare a (pair (pi1 b) (pi2 b))
.

Theorem pare_id : forall t, pare t t.
Proof.
  intros.
  induction t; repeat (try constructor; try assumption).
Qed.

Theorem pare_lift : forall t1 t2 s i,
    pare t1 t2
    -> pare (lift s i t1) (lift s i t2).
Proof.
  intros.
  generalize dependent i.
  induction H.
  (* pare_lam *)
  - simpl.
    intros.
    destruct (eqb s0 s).
    + apply pare_lam.
      apply IHpare.
    + apply pare_lam.
      apply IHpare.
  (* pare_app *)
  - intros.
    simpl.
    apply pare_app.
    + apply IHpare1.
    + apply IHpare2.
  (* pare_const *)
  - intros.
    apply pare_id.
  (* pare_var *)
  - intros.
    apply pare_id.
  (* par_eta *)
  - intros.
    simpl.
    case_nat_comparisons;
      rewrite lift_lift;
      case_nat_comparisons;
      apply par_eta;
      apply IHpare.
  (* par_SP *)
  - intros.
    apply par_SP.
    apply IHpare.
Qed.

Lemma cast {A B : Type} (a : A) (p : A = B) : B.
  subst.
  assumption.
Defined.

Theorem pare_subst : forall a b c d s i,
    pare a c
    -> pare b d
    -> pare (subst s i a b) (subst s i c d).
Proof.
  (* This doesn't actually follow from the other two does it *)
  intros.
  generalize dependent c.
  generalize dependent a.
  generalize dependent i.
  induction H0.
  (* pare_lam *)
  - intros.
    simpl.
    case_nat_comparisons;
      apply pare_lam;
      apply IHpare;
      apply pare_lift;
      assumption.
  (* pare_app *)
  - intros.
    simpl.
    apply pare_app.
    + apply IHpare1.
      assumption.
    + apply IHpare2.
      assumption.
  (* pare_const *)
  - intros.
    apply pare_id.
  (* pare_var *)
  - intros.
    simpl.
    case_nat_comparisons; try apply pare_id.
    assumption.
  (* par_eta *)
  - intros.
    simpl.
    case_nat_comparisons.
    + simplify_nat_string_eqs.
      Check par_eta.
      assert (fact := par_eta s _ _ (IHpare i _ _ H)).
      apply (cast fact).
      rewrite lift_subst.
      case_nat_comparisons.
      * reflexivity.
      * simplify_nat_string_eqs.
        rewrite subst_lift_off_by_1.
        reflexivity.
    + simplify_nat_string_eqs.
      Check par_eta.
      assert (fact := par_eta s0 _ _ (IHpare i _ _ H)).
      apply (cast fact).
      rewrite lift_subst.
      case_nat_comparisons;
        reflexivity.
  (* par_SP *)
  - intros.
    simpl.
    apply par_SP.
    apply IHpare.
    assumption.
Qed.

Theorem pare_diamond a b c
    (r1 : pare a b)
    (r2 : pare a c)
    : exists d, pare b d /\ pare c d.
Proof.
  intros.
  generalize dependent c.
  induction r1.
  (* par_lam *)
  - intros.
    remember (lam s a) as x.
    induction r2; inversion Heqx.
    (* par_lam x par_lam *)
    + inversion Heqx; [clear Heqx; subst].
      specialize (IHr1 _ r2) as [out [p q]].
      exists (lam s out).
      split; constructor; assumption.
    + subst.
      specialize (IHr2 eq_refl) as [out2 [p2 q2]].
      exists (lam s0 (app (lift s0 0 out2) (var s0 0))).
      split; solve [repeat (try constructor; try assumption; try apply pare_lift)].
    (* par_lam x par_SP *)
    + subst.
      specialize (IHr2 eq_refl) as [out [p q]].
      exists (pair (pi1 out) (pi2 out)).
      split; solve [repeat (try constructor; try assumption; try apply pare_lift)].
  (* par_app *)
  - intros.
    remember (app a b) as x.
    induction r2; inversion Heqx.
    (* par_app x par_app *)
    + subst.
      specialize (IHr1_1 _ r2_1) as [out1 [p1 q1]].
      specialize (IHr1_2 _ r2_2) as [out2 [p2 q2]].
      exists (app out1 out2).
      split; apply pare_app; assumption.
    (* par_app x par_eta *)
    + subst.
      specialize (IHr2 eq_refl) as [out2 [p2 q2]].
      exists (lam s (app (lift s 0 out2) (var s 0))).
      split; solve [repeat (try constructor; try assumption; try apply pare_lift)].
    (* par_app x par_Sp *)
    + subst.
      specialize (IHr2 eq_refl) as [out [p q]].
      exists (pair (pi1 out) (pi2 out)).
      split; solve [repeat (try constructor; try assumption; try apply pare_lift)].
  (* pare_const *)
  - intros.
    remember (const c) as x.
    induction r2; inversion Heqx.
    (* par_const x par_const *)
    + subst.
      exists (const c).
      split; constructor.
    (* par_const x par_eta *)
    + subst.
      specialize (IHr2 eq_refl) as [out2 [p2 q2]].
      exists (lam s (app (lift s 0 out2) (var s 0))).
      split; solve [repeat (try constructor; try assumption; try apply pare_lift)].
    (* par_const x par_Sp *)
    + subst.
      specialize (IHr2 eq_refl) as [out [p q]].
      exists (pair (pi1 out) (pi2 out)).
      split; solve [repeat (try constructor; try assumption)].
  (* pare_var *)
  - intros.
    remember (var s i) as x.
    induction r2; inversion Heqx.
    (* par_const x par_const *)
    + subst.
      exists (var s i).
      split; constructor.
    (* par_const x par_eta *)
    + subst.
      specialize (IHr2 eq_refl) as [out2 [p2 q2]].
      exists (lam s0 (app (lift s0 0 out2) (var s0 0))).
      split; solve [repeat (try constructor; try assumption; try apply pare_lift)].
    (* par_const x par_Sp *)
    + subst.
      specialize (IHr2 eq_refl) as [out [p q]].
      exists (pair (pi1 out) (pi2 out)).
      split; solve [repeat (try constructor; try assumption)].
  (* _ x par_eta *)
  - intros.
    specialize (IHr1 _ r2).
    destruct IHr1.
    destruct H.
    exists (lam s (app (lift s 0 x) (var s 0))).
    split.
    + apply pare_lam.
      apply pare_app.
      * apply pare_lift.
        assumption.
      * apply pare_var.
    + apply par_eta.
      assumption.
  (* _ x par_SP *)
  - intros.
    specialize (IHr1 _ r2) as [out [p q]].
    exists (pair (pi1 out) (pi2 out)).
    split; solve [repeat (try constructor; try assumption; try apply pare_lift)].
Qed.

(* single step beta without eta and SP *)
Inductive singb : Term -> Term -> Prop :=
(* Congruences *)
| singb_lam : forall s a b, singb a b -> singb (lam s a) (lam s b)
| singb_app1 : forall a b c, singb a b -> singb (app a c) (app b c)
| singb_app2 : forall a b c, singb b c -> singb (app a b) (app a c)
(* Meaningful things *)
| singb_beta : forall s a b, singb (app (lam s a) b) (subst s 0 b a)
| singb_pi1 : forall a b, singb (pi1 (pair a b)) a
| singb_pi2 : forall a b, singb (pi2 (pair a b)) b
.

Theorem beta_sing_par : forall a b, singb a b -> parb a b.
Proof.
  intros.
  induction H;
    solve [repeat (try constructor; try assumption; try apply parb_id)].
Qed.

From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Relations.Operators_Properties.

Check clos_refl_trans.
Check (clos_refl_trans _ singb).

Search clos_refl_trans.

Theorem beta_1ary_cong : forall a b
                                (f :  Term -> Term),
    (forall x y, singb x y -> singb (f x) (f y))
    -> clos_refl_trans _ singb a b -> clos_refl_trans _ singb (f a) (f b).
Proof.
  intros.
  induction H0.
  - constructor.
    apply H.
    assumption.
  - solve [constructor].
  - eapply rt_trans.
    eassumption.
    assumption.
Qed.

Theorem beta_lam_cong : forall s a b,
    clos_refl_trans _ singb a b -> clos_refl_trans _ singb (lam s a) (lam s b).
Proof.
  intros.
  apply beta_1ary_cong.
  - intros.
    constructor.
    assumption.
  - assumption.
Qed.

Theorem beta_2ary_cong : forall a1 a2 b1 b2
    (f : Term -> Term -> Term),
    (forall a1 a2 b, singb a1 a2 -> singb (f a1 b) (f a2 b))
    -> (forall a b1 b2, singb b1 b2 -> singb (f a b1) (f a b2))
    -> clos_refl_trans _ singb a1 a2
    -> clos_refl_trans _ singb b1 b2
    -> clos_refl_trans _ singb (f a1 b1) (f a2 b2).
Proof.
  intros.
  Check rt_trans.
  apply (rt_trans _ _ _ (f a2 b1) _).
  - induction H1.
    + constructor.
      apply H.
      assumption.
    + solve [constructor].
    + eapply rt_trans.
      eassumption.
      assumption.
  - induction H2.
    + constructor.
      apply H0.
      assumption.
    + solve [constructor].
    + eapply rt_trans.
      eassumption.
      assumption.
Qed.

Theorem beta_app_cong : forall a1 a2 b1 b2,
    clos_refl_trans _ singb a1 a2
    -> clos_refl_trans _ singb b1 b2
    -> clos_refl_trans _ singb (app a1 b1) (app a2 b2).
Proof.
  intros.
  apply beta_2ary_cong.
  - exact singb_app1.
  - exact singb_app2.
  - assumption.
  - assumption.
Qed.

Theorem beta_par_sing : forall a b, parb a b -> clos_refl_trans _ singb a b.
Proof.
  intros.
  induction H.
  - apply beta_lam_cong.
    assumption.
  - apply beta_app_cong; assumption.
    
  - Check (beta_2ary_cong).
    apply (rt_trans _ _ _ (app (lam s a') b') _).
    + Check (beta_2ary_cong a a' b b' (fun a b => app (lam s a) b)).
      refine (beta_2ary_cong a a' b b' (fun a b => app (lam s a) b) _ _ IHparb1 IHparb2);
         intros; solve [repeat first [constructor | assumption]].
    + apply rt_step.
      constructor.
  - apply (rt_trans _ _ _ (pi1 (pair a' b))).
    + refine (beta_1ary_cong a a' (fun x => pi1 (pair x b)) _ IHparb).
      intros.
      repeat constructor.
      assumption.
    + apply rt_step.
      constructor.
  - apply (rt_trans _ _ _ (pi2 (pair a b'))).
    + refine (beta_1ary_cong b b' (fun x => pi2 (pair a x)) _ IHparb).
      intros.
      repeat constructor.
      assumption.
    + apply rt_step.
      constructor.
  - solve [repeat constructor].
  - solve [repeat constructor].
Qed.

Check clos_refl_trans.
Check relation.

(* Partially referenced from "More Church-Rosser Proofs" by Tobias Nipkow *)
Definition square {A} (R S T U : relation A) : Prop :=
  forall x y z, R x y -> S x z -> exists w, T y w /\ U z w.

Theorem hindley_rosen {A} (R S : relation A)
  : square R S (clos_refl_trans _ S) (clos_refl _ R)
    -> square (clos_refl_trans _ R) (clos_refl_trans _ S) (clos_refl_trans _ S) (clos_refl_trans _ R).
Proof.
  unfold square.
  intros premise x y z Rxy Sxz.
  generalize dependent z.
  refine (clos_refl_trans_ind_left A R x
            (fun (a : A) => forall z, clos_refl_trans _ S x z -> exists w : A,
                   clos_refl_trans _ S a w /\ clos_refl_trans _ R z w)
            _ _ y Rxy).
  (* base R case *)
  - intros.
    exists z.
    split.
    + assumption.
    + solve [constructor].
  (* R step case *)
  - intros.
    specialize (H0 z0 H2) as [w [Sy0w Rz0w]].
    clear Rxy.
    assert (exists w0 : A, clos_refl_trans A S z w0 /\ clos_refl _ R w w0). {
      clear H Rz0w H2 z0 x y.
      generalize dependent z.
      refine (clos_refl_trans_ind_left A S y0
                                       (fun (a : A) => forall z, R y0 z -> exists w0 : A,
                                            clos_refl_trans A S z w0 /\ clos_refl _ R a w0)
                                       _ _ w Sy0w).
      (* base S case *)
      + intros.
        exists z.
        split; solve [repeat first [constructor | assumption]].
      + intros.
        specialize (H0 _ H2) as [w0 [Sz0w0 Ryw0]].
        clear H2.
        inversion Ryw0; clear Ryw0; subst.
        * specialize (premise _ _ _ H0 H1) as [w2 [Sw0w2 Rzw2]].
          exists w2.
          split.
          -- eapply rt_trans.
             ++ apply Sz0w0.
             ++ assumption.
          -- assumption.
        * exists z.
          split.
          -- eapply rt_trans.
             apply Sz0w0.
             apply rt_step.
             assumption.
          -- solve [constructor].
    }
    destruct H0 as [w0 [Szw0 Rww0]].
    exists w0.
    split.
    + assumption.
    + eapply rt_trans.
      * apply Rz0w.
      * Search clos_refl clos_refl_trans.
        apply clos_r_clos_rt in Rww0.
        assumption.
Qed.

Definition confluent {A} (R : relation A) : Prop :=
  square (clos_refl_trans _ R) (clos_refl_trans _ R) (clos_refl_trans _ R) (clos_refl_trans _ R).

Definition commute {A} (R S : relation A) : Prop := square R S S R.

(* Next, I need the commutative union theorem.
 Can I somehow get that frmo Hindley Rosen? *)


From Stdlib Require Import Classes.RelationClasses.
Search (relation _ -> relation _ -> relation _).

Theorem commutative_union_theorem {A} (R S : relation A)
        (Rconfluent : confluent R)
        (Sconfluent : confluent S)
        (commute : commute (clos_refl_trans _ R) (clos_refl_trans _ S))
  : confluent (relation_disjunction R S).
  unfold confluent, square in *.
  intros.
  generalize dependent z.
  Check clos_refl_trans_ind_left.
  refine (clos_refl_trans_ind_left A (relation_disjunction R S) x
                                   (fun y => forall z : A,
                                        clos_refl_trans A (relation_disjunction R S) x z ->
                                        exists w : A,
                                          clos_refl_trans A (relation_disjunction R S) y w /\
                                            clos_refl_trans A (relation_disjunction R S) z w)
                                   _ _ y H).
  - intros.
    exists z.
    split.
    + assumption.
    + apply rt_refl.
  - intros.
    
c
