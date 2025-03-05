Require Import String.
Require Import -(coercions) qterm.

(*
This file will have proofs of various facts that I need about lambda calculus to make the
unification tactic work.
These will start as Axioms, and I will prove them eventually.

For now, I will focus on the minimal things that I need to make things work, and I'll add
as needed.
 *)

Ltac compute_subst H := repeat (try rewrite subst_app in H;
                          try (rewrite subst_lam in H; simpl in H) ;
                          try (rewrite subst_var in H; simpl in H;
                               repeat (rewrite lift_lam, lift_app, lift_var in H))).
Ltac normalize H := repeat (rewrite beta in H; compute_subst H).



Inductive PseudoNeutral : QTerm -> Prop :=
| neu_var : forall {n i}, PseudoNeutral (var n i)
| neu_const : forall {s}, PseudoNeutral (const s)
| neu_app : forall {t1 t2}, PseudoNeutral t1 -> PseudoNeutral (app t1 t2).

Theorem lamInj : forall t1 t2 s, <fun `s => `t1> = <fun `s => `t2> -> t1 = t2.
Proof.
  intros.
  pose (var s 0) as x.
  assert (<(fun `s => `t1) `x> = <(fun `s => `t2) `x>).
  rewrite H.
  reflexivity.
  unfold x in H0.
  repeat rewrite beta in H0.
  repeat rewrite subst_id in H0.
  assumption.
Qed.

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
  rewrite H1 in eq.
  simpl in eq.
  rewrite subst_lift in eq.
  exfalso.
  apply p.
  apply eq.
Qed.

 
Theorem pairInj : forall t1 t2 t1' t2', <`t1, `t2> = <`t1', `t2'> -> t1 = t1' /\ t2 = t2'.
Proof.
  intros.
  split.
  assert (<pi1 (`t1, `t2)> = <pi1 (`t1', `t2')>).
  {
    rewrite H.
    reflexivity.
  }
  repeat rewrite betapi1 in H0.
  assumption.
  assert (<pi2 (`t1, `t2)> = <pi2 (`t1', `t2')>).
  {
    rewrite H.
    reflexivity.
  }
  repeat rewrite betapi2 in H0.
  assumption.
Qed.
