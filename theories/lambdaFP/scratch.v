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
  match goal with
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
| par_app : forall a a' b b',
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

Theorem parb_subst2 : forall t1 t2 t3 s i,
    parb t1 t2
    -> parb (subst s i t3 t1) (subst s i t3 t2).
Proof.
  intros.
  generalize dependent i.
  generalize dependent t3.
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
    + rewrite subst_subst.
      case_nat_comparisons.
      apply par_beta.
      * apply IHparb1.
      * apply IHparb2.
    + rewrite subst_subst.
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

Theorem parb_subst1 : forall a b c s i,
    parb a c
    -> parb (subst s i a b) (subst s i c b).
Proof.
  intros.
  generalize dependent i.
  generalize dependent a.
  generalize dependent c.
  induction b.
  (* lam *)
  - intros.
    simpl.
    case_nat_comparisons;
      apply par_lam;
      apply IHb;
      apply parb_lift;
      assumption.
  (* app *)
  - intros.
    simpl.
    apply par_app.
    + apply IHb1.
      assumption.
    + apply IHb2.
      assumption.
  (* const *)
  - intros.
    simpl.
    apply parb_id.
  (* var *)
  - intros.
    simpl.
    case_nat_comparisons;
      try apply parb_id.
    + assumption.
Qed.

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
        apply parb_subst.
