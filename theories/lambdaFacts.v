Require Import String.
Require Import -(coercions) qterm.

(*
This file will have proofs of various facts that I need about lambda calculus to make the
unification tactic work.
These will start as Axioms>, and I will prove them eventually.

For now, I will focus on the minimal things that I need to make things work, and I'll add
as needed.
 *)

Ltac compute_subst H := repeat (try rewrite subst_app in H;
                          try (rewrite subst_lam in H; simpl in H) ;
                          try (rewrite subst_var in H; simpl in H;
                               repeat (rewrite lift_lam, lift_app, lift_var in H))).
Ltac normalize H := repeat (rewrite beta in H; compute_subst H).

(*
For now this will be an axiom. I will have to think about what property of the underlying
terms is needed to give this.
 *)

Inductive PseudoNeutral : QTerm -> Prop :=
| pn_var : forall s i, PseudoNeutral (var s i)
| pn_app : forall a b, PseudoNeutral a -> PseudoNeutral (app a b)
.

Inductive IncompatiblePseudoNeutral : QTerm -> QTerm -> Prop :=
| inc_next : forall p1 p2 t1 t2, IncompatiblePseudoNeutral p1 p2
                                 -> IncompatiblePseudoNeutral (app p1 t1) (app p2 t2)
| inc_var_app : forall s i a b, IncompatiblePseudoNeutral (var s i) (app a b)
| inc_app_var : forall s i a b, IncompatiblePseudoNeutral (app a b) (var s i)
| inc_var_var : forall s1 i1 s2 i2, not (s1 = s2 \/ i1 = i2)
                                    -> IncompatiblePseudoNeutral (var s1 i1) (var s2 i2)
.

Axiom neutralInj : forall a b c d,
    PseudoNeutral a -> PseudoNeutral c -> app a b = app c d <-> a = c /\ b = d.

Axiom neutralContradiction : forall t1 t2,
    PseudoNeutral t1 -> PseudoNeutral t2 -> IncompatiblePseudoNeutral t1 t2
    -> False.
(*
I can probably replace both of these with the single axiom that two constants applied to
arguments are unequal if they are different constants or have different numbers of arguments.
*)

Lemma subst_lift_cancel : forall t s i, subst s i (var s i) (lift s (S i) t) = t.
Proof.
  (* This seems true? Do I need to add it to qterm? *)
Admitted.
  

Theorem lamInj : forall t1 t2 s, <fun `s => `t1> = <fun `s => `t2> -> t1 = t2.
Proof.
  intros.
  apply (f_equal (fun t => <`t [`s]>)) in H.
  repeat rewrite lift_lam in H.
  repeat rewrite eqb_refl in H.
  apply (f_equal (fun t => <`t {var s 0}>)) in H.
  repeat rewrite beta in H.

  repeat rewrite subst_lift_cancel in H.
  assumption.
  (*
  pose (var s 0) as x.
  assert (<(fun `s => `t1) `x> = <(fun `s => `t2) `x>).
  rewrite H.
  reflexivity.
  unfold x in H0.
  repeat rewrite beta in H0.
   *)
  (* I don't think that this can be proven in this way. *)
Qed.

Print Assumptions lamInj.

(*Theorem varInj : forall s1 s2 i j, var s1 i = var s2 j -> s1 = s2 /\ i = j.*)
Theorem varInj : forall s1 s2, var s1 0 = var s2 0 -> s1 = s2.
Proof.
  intros.
  (*
    Need to use decidable equality on nat and string (or just LEM), and prove by contradiction
    using consistency.
   *)

  destruct (String.string_dec s1 s2).
  assumption.
  (* The notation is confusing. H is saying that the variables that looks like s1 and s2 are equal.*)
  pose consistency as c.
  destruct c as [t1 c].
  destruct c as [t2 p].
  pose (var s1 0) as x1.
  pose (var s2 0) as x2.
  assert (<(fun `s1 => fun `s2 => `x1) `t1 `t2> = <(fun `s1 => fun `s2 => `x2) `t1 `t2>) as eq.
  unfold x1, x2.
  rewrite H.
  reflexivity.
  unfold x1, x2 in eq.
  normalize eq.
  assert ((eqb s2 s1) = false).
  {
    pose (eqb_spec s2 s1) as fact.
    destruct fact.
    exfalso.
    apply n.
    apply eq_sym.
    apply e.
    reflexivity.
  }
  rewrite H0 in eq.
  simpl in eq.
  assert (forall s, (eqb s s) = true).
  {
    intro s.
    pose (eqb_spec s s) as fact.
    destruct fact.
    reflexivity.
  exfalso.
  apply n0.
  reflexivity.
  }
  rewrite H1 in eq.
  simpl in eq.
  normalize eq.
  assert ((eqb s1 s2) = false).
  {
    pose (eqb_spec s1 s2) as fact.
    destruct fact.
    exfalso.
    apply n.
    apply eq_sym.
    apply (eq_sym e).
    reflexivity.
  }
  rewrite H2 in eq.
  simpl in eq.
  rewrite subst_lift in eq.
  exfalso.
  apply p.
  rewrite subst_var in eq.
  simpl in eq.
  rewrite H1 in eq.
  apply eq.
  (* TODO: This proof can be way shorter*)
Qed.

 
Theorem pairInj : forall t1 t2 t1' t2', <`t1, `t2> = <`t1', `t2'> -> t1 = t1' /\ t2 = t2'.
Proof.
  intros.
  split.
  assert (<proj1 (`t1, `t2)> = <proj1 (`t1', `t2')>).
  {
    rewrite H.
    reflexivity.
  }
  repeat rewrite betapi1 in H0.
  assumption.
  assert (<proj2 (`t1, `t2)> = <proj2 (`t1', `t2')>).
  {
    rewrite H.
    reflexivity.
  }
  repeat rewrite betapi2 in H0.
  assumption.
Qed.

Theorem liftInj : forall s i t1 t2, lift s i t1 = lift s i t2 -> t1 = t2.
Proof.
  intros.
  pose (lift s i t1) as l.
  pose (lift s i t2) as r.
  assert (subst s i <dummy> l = subst s i <dummy> r).
  unfold l, r.
  rewrite H.
  reflexivity.
  unfold l, r in H0.
  normalize H0.
  repeat rewrite subst_lift in H0.
  assumption.
Qed.

(*
These are for the "pattern subset" case.
 *)

Theorem pattern_direction1 : forall (t1 t2 : QTerm) s, <`t1 [`s] {var s 0}> = t2 -> t1 = <fun `s => `t2>.
Proof.
  intros.
  apply (f_equal (fun t => <fun `s => `t>)) in H.
  rewrite <- eta in H.
  assumption.
Qed.
Print eta.

Theorem pattern_direction2 : forall (t1 t2 : QTerm) s, t1 = <fun `s => `t2> -> <`t1 [`s] {var s 0}> = t2.
Proof.
  intros.
  Check eta.
  rewrite (eta s t1) in H.
  apply lamInj in H.
  assumption.
Qed.
