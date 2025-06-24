Require Import String.
Require Import qterm.
Require Import lambdaFacts.
Require Import lambdaSolve.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Theorem thm : 1 = 1.
Proof.
  reflexivity.
Qed.

Theorem evarExample : True.
Proof.
  evar (x : nat).
  assert (x = x). {
    subst x.
    Fail rewrite thm.
    (* It doesn't look like rewrites just rewrite existentials arbitrarily *)
    reflexivity.
  }
  constructor.
  Unshelve.
  apply 20.
Qed.

Theorem testThing (t1 t2 : QTerm) : lift "name" 0 t1 = t2.
Proof.
  evar (et1 : QTerm).
  assert (et1 = t1) by give_up.
  rewrite <- H.
  unfold et1.
  rewrite lift_lam.
  (* So for some reason the rewrite does (incorrectly) work here, specializing the evar.
   It doesn't work if the lhs is JUST an evar. Maybe part of the pattern has to exist? *)
Abort.

Theorem equality : 1 + 1 = 2. Proof. reflexivity. Qed.

Theorem testRewrite2 (x : nat) : 1 + x = 2.
  evar (ex : nat).
  assert (ex = x).
  2: {
    rewrite <- H.
    unfold ex.
    (* The goal is now: "1 + ?ex = 2"
       The rewrite tactic below specializes ?ex to 1 *)
    rewrite equality.
    reflexivity.
  }
Abort.

Ltac hide_evars :=
  repeat match goal with
         | H : context [ ?v ] |- _ =>
             is_evar v; let H' := fresh "evar_temp" in pose (H' := v); fold H' in H
         | [ |- context [ ?v (*: QTerm*) ] ] =>
             is_evar v; let H := fresh "evar_temp" in pose (H := v); fold H
         end.

Ltac unhide_evars :=
  repeat match goal with
         | x := ?t (*: QTerm*) |- _ => is_evar t; subst x
         end.

Theorem testRewrite2 (x y z : nat) : (1 + x) + (1 + x) + (1 + y) + (1 + y) = 2.
  assert ((1 + x) + (1 + y) + (1 + y) + (1 + z) + (1 + z) = 2) as H by give_up.
  evar (ex : nat).
  assert (ex = x) by give_up.
  rewrite <- H0 in *.
  evar (ey : nat).
  assert (y = ey) by give_up.
  rewrite H1 in *.
  evar (ez : nat).
  assert (z = ez) by give_up.
  rewrite H2 in *.
  unfold ex, ey, ez in *.
  
  hide_evars.
  
  unhide_evars.
Abort.

Goal S 1 = 4.
  match goal with
  | |- context f [S ?X] =>
      idtac X;
      let ctx := fun x => context f[x] in
      idtac ctx
      (*let x := context f[0] in assert (x=x)*)
  end.
Abort.
  
Check beta.
Definition make_evar (t : QTerm) (H : <`t ((fun x => x) A)> = <B>) : True := I.

Definition amnesia_cast {A B} (H : A = B) (a : A) : B.
  subst.
  exact a.
Qed.

Ltac hide_evar_2 :=
  repeat match goal with
  | [ |- context [ ?v ] ] => is_evar v; (let H := fresh v in pose (H := v); fold H) + (let H := fresh "x" in pose (H := v); fold H)
  end.

Ltac rewriteBeta :=
  match goal with
  | |- context [app (lam ?x ?t1) ?t2] => idtac "yes"
  end.
Definition nothing {A} (a : A) : A := a.
Theorem testRewrite3 : True.
Proof.
  refine (make_evar _ _).
  hide_evar_2.
  rewriteBeta.
  Check (f_equal _).
  Check @beta.
  match goal with
  | |- context c [app (lam ?x ?t1) ?t2] =>
      let cf := fun t => context c[t] in
      (*apply (amnesia_cast (f_equal cf (@beta x t1 t2)))*)
      idtac cf
  end.
  pose (cf := fun t => ?Goal t = <B>).
  
  rewrite beta.
