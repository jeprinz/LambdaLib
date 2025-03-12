Require Import String.
Require Import -(coercions) qterm. (* TODO: Do I ever need the coeercion? This is very strange*)
Require Import lambdaFacts.

(*
The goal of these tactics is to reduce terms to a normal form.
In order for them to work, we need to assume that the input terms have a particular form:
All QTerms should consist of lam, app, var, pair, pi1, pi2, const, and coq variables.
Any lifts should be around a coq variable.

There should not be any lifts anywhere else or subst forms anywhere at all
except during intermediate states.
*)

Ltac compute_lifts := repeat (try (rewrite lift_lam ; simpl) ;
                              try rewrite lift_app;
                              try (rewrite lift_var ; simpl)).

Ltac compute_subst := repeat (try rewrite subst_app ;
                              try rewrite subst_pair;
                              try rewrite subst_pi1;
                              try rewrite subst_pi2;
                          try (rewrite subst_lam ; simpl ; compute_lifts) ;
                          try (rewrite subst_var ; simpl);
                               compute_lifts).
(* Is there a way to not have this be repetetive with the above? *)

Ltac compute_lifts_in H := repeat (try (rewrite lift_lam in H ; simpl in H) ;
                              try rewrite lift_app in H;
                              try (rewrite lift_var in H ; simpl in H)).

Ltac compute_subst_in H := repeat (try rewrite subst_app in H;
                                   try rewrite subst_pair in H;
                                   try rewrite subst_pi1 in H;
                                   try rewrite subst_pi2 in H;
                          try (rewrite subst_lam in H ; simpl in H ; compute_lifts_in H) ;
                          try (rewrite subst_var in H; simpl in H);
                                  compute_lifts_in H).
Ltac normalize := repeat (rewrite ?beta, ?betapi1, ?betapi2; compute_subst).
Ltac normalize_in H := repeat (rewrite ?beta, ?betapi1, ?betapi2 in H; compute_subst_in H).

(*
[x] - add pairs and stuff to qterm
[ ] - find old file that had most advanced unification tactic
[ ] - port to this version
*)

(*
Ltac compute_subst' location :=
  match location with
  | "goal"%string => repeat (try rewrite subst_app ;
                          try (rewrite subst_lam ; simpl) ;
                          try (rewrite subst_var ; simpl;
                               repeat (rewrite lift_lam, lift_app, lift_var)))
  | _ => repeat (try rewrite subst_app ;
                          try (rewrite subst_lam in location ; simpl in location) ;
                          try (rewrite subst_var in location; simpl in location;
                                  repeat (rewrite lift_lam, lift_app, lift_var in location)))
  end.


Ltac handle_case t1 t2 location :=
  match t1 t2 with
  | (lam ?s ?t1) (lam ?s ?t2) => apply lamInj in location
  end.
 *)

Theorem proveEqualityInParts (A B : Type) (f1 f2 : A -> B) (a1 a2 : A)
  : f1 = f2 -> a1 = a2 -> f1 a1 = f2 a2.
Proof.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Ltac lambda_solve :=
  repeat (
      match goal with
      | H : lam ?s ?t1 = lam ?s ?t2 |- _ => apply lamInj in H
      | |- lam ?s ?t1 = lam ?s ?t2 => apply (f_equal (lam s))
      | H : lam ?s1 ?t1 = lam ?s2 ?t2 |- _ => rewrite (@alpha s1 s2 t1) in H; compute_subst_in H
      | |- lam ?s1 ?t1 = lam ?s2 ?t2 => rewrite (@alpha s1 s2 t1); compute_subst
      | H : var ?s1 0 = var ?s2 0 |- _ => apply varInj in H
      | H : @eq string ?s ?s |- _ => clear H
      | H : @eq string ?s1 ?s2 |- _ => inversion H
      | H : @eq QTerm (pair ?t1 ?t2) (pair ?t1' ?t2') |- _ => apply pairInj in H; destruct H
      (* Beta reduction cases *)
      | H : app (lam ?s ?t1) ?t2 = ?t3 |- _ => rewrite beta in H; compute_subst_in H
      | H : ?t1 = app (lam ?s ?t2) ?t3 |- _ => rewrite beta in H; compute_subst_in H
      | |- app (lam ?s ?t1) ?t2 = ?t3 => rewrite beta; compute_subst
      | |- ?t1 = app (lam ?s ?t2) ?t3 => rewrite beta; compute_subst
      (* pi-beta reduction cases *)
      | H : pi1 (pair ?t1 ?t2) = ?t3 |- _ => rewrite betapi1 in H
      | H : ?t1 = pi1 (pair ?t2 ?t3) |- _ => rewrite betapi1 in H
      | |- pi1 (pair ?t1 ?t2) = ?t3 => rewrite betapi1
      | |- ?t1 = pi1 (pair ?t2 ?t3) => rewrite betapi1
      | H : pi2 (pair ?t1 ?t2) = ?t3 |- _ => rewrite betapi2 in H
      | H : ?t1 = pi2 (pair ?t2 ?t3) |- _ => rewrite betapi2 in H
      | |- pi2 (pair ?t1 ?t2) = ?t3 => rewrite betapi2
      | |- ?t1 = pi2 (pair ?t2 ?t3) => rewrite betapi2
      (* x = t2, should subst x. TODO: need case for t1 = x *)
      | H : @eq QTerm ?t1 ?t2 |- _ => first [subst t1 | subst t2 ]
      (* If we are trying to prove an equality involving functions that are not in QTerm,
         try just f_equaling them. Hopefully the user wanted that since its the goal where
         they ran this tactic. *)
      | |- @eq ?ty ?a ?b => (lazymatch ty with (* lazymatch is needed to make it actually fail *)
                             | QTerm => fail
                             | _ => try reflexivity; apply proveEqualityInParts
                             end)
      | |- @eq QTerm ?a ?b => reflexivity
      end
    )
.

Theorem test_10
        (a b : QTerm)
  : <x `a> = <x `b>.
Proof.
  lambda_solve.
Abort.

Theorem test_lambda_solve_0
        (t : QTerm)
  : <fun x => `t> = <fun y => `t>.
Proof.
  lambda_solve.
Abort. (* This shouldn't be true, because t could have x or y in it. *)

(* We need to hide Mark in a module so that it is not definitionally equal to its definition *)
Module Type HowToHideMark.
  Parameter Mark : forall {X : Type}, X -> X. (* He hides in here where no one can see him *)
  Parameter MarkIsJustId : forall {X : Type} {x : X}, Mark x = x.
End HowToHideMark.
Module HiddenMark : HowToHideMark.
  Definition Mark {X : Type} (x : X) := x.
  Theorem MarkIsJustId {X : Type} {x : X} : Mark x = x.
  Proof.
    intros.
    reflexivity.
  Qed.
End HiddenMark.

Import HiddenMark.

Theorem mark_stuck : forall t s1 i1 s2 i2 t',
    subst s1 i1 t' (lift s2 i2 t) = subst s1 i1 t' ((Mark lift) s2 i2 t).
Proof.
  rewrite MarkIsJustId.
  reflexivity.
Qed.

Theorem swap_marked_lift : forall (s1 s2 : string) (i1 i2 : nat) (t : QTerm),
(*    (Mark lift) s1 i1 (lift s2 i2 t) =
      lift s2 (if (s1 =? s2)%string then S i2 else i2) ((Mark lift) s1 i1 t).*)
    (Mark lift) s1 i1 (lift s2 i2 t) =
      (if eqb s1 s2
       then if Nat.ltb i2 i1
            then lift s2 i2 (Mark lift s1 (pred i1) t)
            else lift s2 (S i2) (Mark lift s1 i1 t)
       else lift s2 i2 (Mark lift s1 i1 t)).
Proof.
  rewrite MarkIsJustId.
  apply lift_lift.
Qed.

Ltac fix_subst_lifts :=
  repeat (
      (* First, cancel any substs and lifts that already match*)
      repeat rewrite subst_lift;
      (* Next, mark any lifts under a subst as being the wrong one *)
      repeat rewrite mark_stuck;
      (* Next, push the marked lift down *)
      repeat (rewrite swap_marked_lift ; simpl)
    );
  (* When we are done, remove Mark *)
  repeat rewrite MarkIsJustId.

Ltac fix_subst_lifts_in H :=
  repeat (
      repeat rewrite subst_lift in H;
      repeat rewrite mark_stuck in H;
      repeat (rewrite swap_marked_lift in H ; simpl in H)
    );
  repeat rewrite MarkIsJustId in H.


Theorem test_lambda_solve_1
        (t : QTerm)
  : <fun x => `t [x]> = <fun y => `t [y]>.
Proof.
  repeat lambda_solve.
  fix_subst_lifts.
  reflexivity.
Qed.

Theorem test_lambda_solve
        (t1 t2 : QTerm)
        (H1 : <fun x => `t1 [x]> = <fun x => `t2 [x]>)
  : <fun x => `t1[x]> = <fun y => `t2[y]>.
Proof.
  repeat lambda_solve.
  fix_subst_lifts.
  apply liftInj in H1.
  rewrite H1.
  reflexivity.
Qed.

Theorem test_lambda_solve_2
        (t : QTerm)
        (H : <(fun x => x) `t> = < (fun x => x) (fun x => x)>)
        : <`t `t> = <`t>.
Proof.
  lambda_solve.
Qed.

Theorem test_lambda_solve_3
        (t1 t2 : QTerm)
        (P : QTerm -> Prop)
        (H : t1 = t2)
  : P t1 = P t2.
Proof.
  lambda_solve.
Qed.

Theorem test2 : <fun x => x> = <fun y => y>.
Proof.
  lambda_solve.
Qed.

Theorem test_shadowed_var : (lam "a" (var "a"%string 1)) = <fun x => a>.
Proof.
  lambda_solve.
Qed.

Theorem test_deeper_beta :
  <a> = <(fun x => fun y => a) b c>.
Proof.
  (* Should beta here! *)
Admitted.

(*https://coq-club.inria.narkive.com/cZ5X8JAw/making-tactic-that-return-a-value*)

Ltac print x := idtac x.

Ltac get_sub_to_make_anything term toBeMade nameRet indexRet subRet :=
  lazymatch term with
  | (var ?s ?i) => pose toBeMade as subRet; pose s as nameRet; pose i as indexRet
  | (app ?a ?b) => get_sub_to_make_anything a (lam "x" (lift "x" 0 toBeMade)) nameRet indexRet subRet
  end.

Ltac solve_neutral_unequal_case :=
  match goal with
  | H : @eq QTerm ?l ?r |- _ =>
      let t1 := fresh "t1" in
      let t2 := fresh "t2" in
      let H2 := fresh "H" in
      destruct consistency as [t1 temp]; destruct temp as [t2 H2];
      let sub1 := fresh "sub1" in
      let sub2 := fresh "sub2" in
      let s1 := fresh "s1" in
      let s2 := fresh "s2" in
      let i1 := fresh "i1" in
      let i2 := fresh "i2" in
      get_sub_to_make_anything r t2 s2 i2 sub2;
      get_sub_to_make_anything l (lift s2 i2 t1) s1 i1 sub1;
      exfalso;
      apply H2;
      let fact := fresh "fact" in
      assert (subst s2 i2 sub2 (subst s1 i1 sub1 l) = subst s2 i2 sub2 (subst s1 i1 sub1 r)) as fact;
      repeat unfold s1, s2, i1, i2, sub1, sub2 in *;
      [
        rewrite H;
        reflexivity
      |
        normalize_in fact;
        repeat fix_subst_lifts_in fact;
        apply fact
      ]
  end.

(*Compute (ltac:(get_sub_to_make_anything <a> <b>)).*)

Theorem test_unequal_neutrals
  (H : <a b> = <c>)
    : False.
Proof.
  solve_neutral_unequal_case.
  (*destruct consistency as [t1 temp]. destruct temp as [t2 H2].
  exfalso.
  apply H2.


  assert (<(a b) [a / fun x => `t1 [c] [x]] [c / `t2]>
          = <c [a / fun x => `t1 [c] [x]] [c / `t2]>).

  rewrite H.
  reflexivity.
  normalize_in H1.
  repeat fix_subst_lifts_in H1.
  apply H1.
   *)
Qed.

Theorem test_shadowed_application
        (t : QTerm) :
  <(fun x => (fun x => `t [a] [x]) [x]) a b> = <`t [a]>.
Proof.
  normalize.
  fix_subst_lifts.
  reflexivity.
Qed.

Theorem test_unequal_neutrals_3
        (H : <a b c> = <d>)
  : False.
Proof.
  solve_neutral_unequal_case.
  (*
  match goal with
  | H : @eq QTerm ?l ?r |- _ =>
      let t1 := fresh "t1" in
      let t2 := fresh "t2" in
      let H2 := fresh "H" in
      destruct consistency as [t1 temp]; destruct temp as [t2 H2];
      let sub1 := fresh "sub1" in
      let sub2 := fresh "sub2" in
      let s1 := fresh "s1" in
      let s2 := fresh "s2" in
      let i1 := fresh "i1" in
      let i2 := fresh "i2" in
      get_sub_to_make_anything r t2 s2 i2 sub2;
      get_sub_to_make_anything l (lift s2 i2 t1) s1 i1 sub1;
      exfalso;
      apply H2;
      assert (subst s2 i2 sub2 (subst s1 i1 sub1 l) = subst s2 i2 sub2 (subst s1 i1 sub1 r)) as fact
   end.
   unfold i1, i2, s1, s2, sub1, sub2.
   rewrite H.
   reflexivity.
   repeat unfold i1, i2, s1, s2, sub1, sub2 in *.
   compute_lifts_in fact.
   normalize_in fact.
   Check lift_lift.
   Unset Printing Notations.
   fix_subst_lifts_in fact.
   repeat fix_subst_lifts_in fact.
   assumption.
   (* Here is seems like I have some debruin index issue - the subst and lift would cancel if they
    had the same index. Not sure if the issue is in the axioms or the tactic. *)
   *)
Qed.

Theorem test_unequal_neutral_another
        (H : <a> = <b c d e>)
  : False.
Proof.
  solve_neutral_unequal_case.
Qed.

(*
For now this will be an axiom. I will have to think about what property of the underlying
terms is needed to give this.
 *)

Inductive PseudoNeutral : QTerm -> Prop :=
| pn_var : forall s i, PseudoNeutral (var s i)
| pn_app : forall a b, PseudoNeutral a -> PseudoNeutral (app a b)
.

Axiom neutralInj : forall a b c d,
    PseudoNeutral a -> PseudoNeutral c -> app a b = app c d -> a = c /\ b = d.

Ltac neutral_inj_case :=
  match goal with
  | H : app ?a ?b = app ?c ?d |- _ =>
      apply neutralInj in H;
      repeat constructor;
      destruct H
  end.

Theorem application_injective_test
        (a b : QTerm)
        (H : <c `a x> = <c `b x>)
  : a = b.
Proof.
  repeat neutral_inj_case.
  assumption.
Qed.
