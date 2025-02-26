Require Import String.
Require Import qterm.

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

Theorem test_things : <(fun x => x) (fun y => y)> = <fun x => x>.
Proof.
  normalize.
  eapply eq_trans.
  apply alpha.
  normalize.
  reflexivity.
Qed.

Theorem speed_test : <(fun f => f (f (f (f (f (f (f (f (f (f (f (f result)))))))))))) (fun x => x)>
                                = <result>.
Proof.
  Time ben_norm2.
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

Ltac ben_norm4 := repeat (repeat (rewrite beta) ;
                          repeat (rewrite_strat innermost subst_app) ;
                          repeat ((rewrite_strat innermost subst_lam) ; simpl) ;
                          repeat ((rewrite_strat innermost subst_var) ; simpl) ;
                          repeat (rewrite ?lift_lam, ?lift_app, lift_var)).

Theorem speed_test2 : <`fact `zero> = zero.
Proof.

  unfold fact.
  unfold zero.
  unfold fact'.
  unfold zero.
  unfold Y.

  Time normalize4.

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

  Time normalize4.
  reflexivity.
Time Qed.

(*
Substs should be innermost first because of
(x x)[x / [t[y/y]]]

rewite ?a, ?b, ?c 
will do any a before any b.
*)
