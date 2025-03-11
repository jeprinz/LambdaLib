Require Import String.
Require Import qterm.
Require Import lambdaSolve.

Compute <fun x => x>.
Compute <fun y => fun z => y (fun x => x y)>.

Ltac normalize := repeat (rewrite ?lift_app, ?lift_lam, ?lift_var, ?subst_app, ?subst_lam, ?subst_var,
                           ?beta; simpl).
Ltac subst_lift_norm := repeat (rewrite ?lift_app, ?lift_lam, ?lift_var, ?subst_app, ?subst_lam,
                                 ?subst_var ; simpl).
Ltac normalize2 := repeat(rewrite ?beta ; subst_lift_norm).
Ltac ben_norm := repeat (repeat (rewrite ?beta); subst_lift_norm).
Ltac ben_norm2 := repeat (repeat (rewrite ?beta) ; repeat (rewrite ?subst_app) ;
                          repeat (rewrite ?subst_lam ; simpl) ;
                          repeat (rewrite ?subst_var ; simpl) ;
                          repeat (rewrite ?lift_lam, ?lift_app, lift_var)).
Ltac ben_norm3 := repeat (rewrite ?beta;
                          repeat (rewrite ?subst_app) ;
                          rewrite ?beta;
                          repeat (rewrite ?subst_lam ; simpl) ;
                          rewrite ?beta;
                          repeat (rewrite ?subst_var ; simpl) ;
                          rewrite ?beta;
                          repeat (rewrite ?lift_lam, ?lift_app, lift_var)).

Ltac subst_lift_norm2 := repeat (try (rewrite_strat innermost lift_app);
                                try (rewrite_strat innermost lift_lam) ; simpl ;
                                try (rewrite_strat innermost lift_var) ; simpl ;
                                try (rewrite_strat innermost subst_app);
                                try (rewrite_strat innermost subst_lam);
                                try (rewrite_strat innermost subst_var);
                                simpl).
Ltac normalize3 := repeat(rewrite ?beta ; subst_lift_norm2).
Ltac normalize4 := repeat (rewrite ?beta; repeat (rewrite ?subst_app) ;
                          repeat (rewrite ?subst_lam ; simpl) ;
                          repeat (rewrite ?subst_var ; simpl) ;
                           repeat (rewrite ?lift_lam, ?lift_app, lift_var)).

Ltac ben_norm4 := repeat (repeat (rewrite beta) ;
                          repeat (rewrite_strat innermost subst_app) ;
                          repeat ((rewrite_strat innermost subst_lam) ; simpl) ;
                          repeat ((rewrite_strat innermost subst_var) ; simpl) ;
                          repeat (rewrite ?lift_lam, ?lift_app, lift_var)).

Ltac normalize5 := repeat (rewrite beta; repeat (repeat (rewrite subst_app) ;
                          repeat (rewrite subst_lam ; simpl) ;
                          repeat (rewrite subst_var ; simpl;
                                  repeat (rewrite lift_lam, lift_app, lift_var)))
                          ).
Ltac normalize6 := repeat (rewrite beta; repeat (try rewrite subst_app ;
                          try (rewrite subst_lam ; simpl) ;
                          try (rewrite subst_var ; simpl;
                                  repeat (rewrite lift_lam, lift_app, lift_var; simpl)))
                          ).


(*****)

Theorem example1 : <(fun x => x) (fun x => x)> = <fun x => x>.
Proof.
  normalize5.
  reflexivity.
Qed.

(*
Theorem test_things : <(fun x => x) (fun y => y)> = <fun x => x>.
Proof.
  normalize.
  eapply eq_trans.
  apply alpha.
  normalize.
  reflexivity.
Qed.
*)
Theorem speed_test : <(fun f => f (f (f (f (f (f (f (f (f (f (f (f result)))))))))))) (fun x => x)>
                                = <result>.
Proof.
  (*Time lambda_solve.*)
  Time normalize6.
  (*Time ben_norm2.*)
  reflexivity.
Qed.
(*The performance seems acceptable! There is maybe half a second delay there. Could be better though.*)

Definition Y := <fun f => (fun x => f (x x)) (fun x => f (x x))>.
Definition zero := <fun s => fun z => z>.
Definition suc := <fun n => fun s => fun z => s (n s z)>.
Definition fact' := <fun f => fun n => n (fun m => `suc (f m)) `zero>.
Definition fact := <`Y `fact'>.

(*
Notation "'Y'" := <fun f => (fun x => f (x x)) (fun x => f (x x))>.
Notation "'zero'" := <fun s => fun z => z>.
Notation "'suc'" := <fun n => fun s => fun z => s (n s z)>.
Notation "'fact1'" := <fun f => fun n => n zero (fun m => suc (f m))> : .
Notation "'fact'" := <Y fact1>.
*)

(* This one works with new version of lift. It is a bit slower than before though, so maybe I should
go back in git history and see what happened. *)
Ltac normalize7 := repeat (rewrite beta; repeat (try rewrite subst_app ;
                          try (rewrite subst_lam ; simpl) ;
                          try (rewrite subst_var ; simpl;
                               repeat (try (rewrite lift_lam ; simpl) ; try rewrite lift_app ;
                                       try (rewrite lift_var; simpl))))).


Parameter subst_lam : forall (s1 s2 : string) (i : nat) (t1 t2 : QTerm),
      subst s2 i t2 (lam s1 t1) =
        (if (s1 =? s2)%string
         then lam s1 (subst s2 (S i) (lift s1 0 t2) t1)
         else lam s1 (subst s2 i (lift s1 0 t2) t1)).

(* Maybe by rewriting this axiom in a way where the if can be deferred it might make the rewrites faster? *)
Axiom subst_lam2 : forall (s1 s2 : string) (i : nat) (t1 t2 : QTerm),
    subst s2 i t2 (lam s1 t1) =
      lam s1 (subst s2 (if eqb s1 s2 then S i else i) (lift s1 0 t2) t1).

Theorem speed_test2 : <`fact `zero> = zero.
Proof.
  unfold fact, zero, fact', zero, Y.
  (* TODO: this version is much faster. I should incorporate that into lambda_solve.*)
  Print lambda_solve.
  repeat match goal with
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
      | H : @eq QTerm ?t1 ?t2 |- _ => first [subst t1 | subst t2
                                            | rewrite beta in H ; compute_subst_in H ]
      (* If we are trying to prove an equality involving functions that are not in QTerm,
         try just f_equaling them. Hopefully the user wanted that since its the goal where
         they ran this tactic. *)
      | |- @eq ?ty ?a ?b => (lazymatch ty with (* lazymatch is needed to make it actually fail *)
                             | QTerm => fail
                             | _ => try reflexivity; apply proveEqualityInParts
                             end)
      | |- @eq QTerm ?t1 ?t2 => rewrite beta in H ; compute_subst
         end.
  lambda_solve.
  Time normalize7.
  Time repeat (rewrite beta; repeat (try rewrite subst_app ;
                          try (rewrite subst_lam2 ; simpl) ;
                          try (rewrite subst_var ; simpl) ;
                               repeat (try (rewrite lift_lam ; simpl) ; try rewrite lift_app ;
                                       try (rewrite lift_var ; simpl)); simpl)).
  Time lambda_solve.
  
  Time normalize6.

  (*
  Time (
  rewrite beta;
  rewrite subst_app;
  rewrite subst_lam;
  simpl;
  rewrite beta;
  rewrite subst_app;
  rewrite subst_var;
  simpl;
  rewrite subst_app;
  rewrite subst_lam;
  simpl;
  rewrite beta;
  rewrite subst_app;
  rewrite subst_var;
  simpl;
  rewrite subst_lam;
  simpl;
  rewrite subst_lam;
  simpl;
  rewrite beta;
  rewrite subst_app;
  rewrite subst_lam;
  simpl;
  rewrite subst_lam;
  simpl;
  rewrite subst_var;
  simpl;
  rewrite subst_app;
  rewrite subst_lam;
  simpl;
  repeat rewrite subst_app;
  repeat (rewrite subst_var ; simpl);
  rewrite beta;
  rewrite subst_lam;
  simpl;
  rewrite subst_var;
  simpl;
  rewrite beta;
  rewrite subst_var;
  simpl;
  ben_norm2).


  Time ben_norm.
   *)
  reflexivity.
Time Qed.

Theorem speed_test3 : <`fact (`suc `zero)> = <`suc `zero>.
Proof.
  unfold fact.
  unfold zero.
  unfold fact'.
  unfold zero.
  unfold suc.
  unfold Y.


  (* There was an old version where this took 5 seconds. Not it takes almost 50, so I should go back and
     see whats different.*)
  Time normalize7.
  reflexivity.
  Time Qed.

Theorem speed_test4 : <`fact (`suc (`suc `zero))> = <`suc (`suc `zero)>.
Proof.
  unfold fact.
  unfold zero.
  unfold fact'.
  unfold zero.
  unfold suc.
  unfold Y.

  Time normalize5.
  reflexivity.
Time Qed.

(*
Substs should be innermost first because of
(x x)[x / [t[y/y]]]

rewite ?a, ?b, ?c 
will do any a before any b.
*)
