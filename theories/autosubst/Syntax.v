Require Import core unscoped.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive tm : Type :=
  | var_tm : nat -> tm
  | pi : tm -> tm -> tm
  | U : tm
  | Empty : tm
  | Bool : tm
  | Lift : tm -> tm
  | var : nat -> tm
  | lambda : tm -> tm
  | app : tm -> tm -> tm
  | true : tm
  | false : tm
  | ifexpr : tm -> tm -> tm -> tm.

Lemma congr_pi {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : pi s0 s1 = pi t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => pi x s1) H0))
         (ap (fun x => pi t0 x) H1)).
Qed.

Lemma congr_U : U = U.
Proof.
exact (eq_refl).
Qed.

Lemma congr_Empty : Empty = Empty.
Proof.
exact (eq_refl).
Qed.

Lemma congr_Bool : Bool = Bool.
Proof.
exact (eq_refl).
Qed.

Lemma congr_Lift {s0 : tm} {t0 : tm} (H0 : s0 = t0) : Lift s0 = Lift t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => Lift x) H0)).
Qed.

Lemma congr_var {s0 : nat} {t0 : nat} (H0 : s0 = t0) : var s0 = var t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => var x) H0)).
Qed.

Lemma congr_lambda {s0 : tm} {t0 : tm} (H0 : s0 = t0) : lambda s0 = lambda t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => lambda x) H0)).
Qed.

Lemma congr_app {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : app s0 s1 = app t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => app x s1) H0))
         (ap (fun x => app t0 x) H1)).
Qed.

Lemma congr_true : true = true.
Proof.
exact (eq_refl).
Qed.

Lemma congr_false : false = false.
Proof.
exact (eq_refl).
Qed.

Lemma congr_ifexpr {s0 : tm} {s1 : tm} {s2 : tm} {t0 : tm} {t1 : tm}
  {t2 : tm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  ifexpr s0 s1 s2 = ifexpr t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => ifexpr x s1 s2) H0))
            (ap (fun x => ifexpr t0 x s2) H1))
         (ap (fun x => ifexpr t0 t1 x) H2)).
Qed.

Lemma upRen_tm_tm (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_tm (xi_tm : nat -> nat) (s : tm) {struct s} : tm :=
  match s with
  | var_tm s0 => var_tm (xi_tm s0)
  | pi s0 s1 => pi (ren_tm xi_tm s0) (ren_tm (upRen_tm_tm xi_tm) s1)
  | U => U
  | Empty => Empty
  | Bool => Bool
  | Lift s0 => Lift (ren_tm xi_tm s0)
  | var s0 => var s0
  | lambda s0 => lambda (ren_tm (upRen_tm_tm xi_tm) s0)
  | app s0 s1 => app (ren_tm xi_tm s0) (ren_tm xi_tm s1)
  | true => true
  | false => false
  | ifexpr s0 s1 s2 =>
      ifexpr (ren_tm xi_tm s0) (ren_tm xi_tm s1) (ren_tm xi_tm s2)
  end.

Lemma up_tm_tm (sigma : nat -> tm) : nat -> tm.
Proof.
exact (scons (var_tm var_zero) (funcomp (ren_tm shift) sigma)).
Defined.

Fixpoint subst_tm (sigma_tm : nat -> tm) (s : tm) {struct s} : tm :=
  match s with
  | var_tm s0 => sigma_tm s0
  | pi s0 s1 => pi (subst_tm sigma_tm s0) (subst_tm (up_tm_tm sigma_tm) s1)
  | U => U
  | Empty => Empty
  | Bool => Bool
  | Lift s0 => Lift (subst_tm sigma_tm s0)
  | var s0 => var s0
  | lambda s0 => lambda (subst_tm (up_tm_tm sigma_tm) s0)
  | app s0 s1 => app (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
  | true => true
  | false => false
  | ifexpr s0 s1 s2 =>
      ifexpr (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
        (subst_tm sigma_tm s2)
  end.

Lemma upId_tm_tm (sigma : nat -> tm) (Eq : forall x, sigma x = var_tm x) :
  forall x, up_tm_tm sigma x = var_tm x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_tm (sigma_tm : nat -> tm)
(Eq_tm : forall x, sigma_tm x = var_tm x) (s : tm) {struct s} :
subst_tm sigma_tm s = s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | pi s0 s1 =>
      congr_pi (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s1)
  | U => congr_U
  | Empty => congr_Empty
  | Bool => congr_Bool
  | Lift s0 => congr_Lift (idSubst_tm sigma_tm Eq_tm s0)
  | var s0 => congr_var (eq_refl s0)
  | lambda s0 =>
      congr_lambda (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s0)
  | app s0 s1 =>
      congr_app (idSubst_tm sigma_tm Eq_tm s0) (idSubst_tm sigma_tm Eq_tm s1)
  | true => congr_true
  | false => congr_false
  | ifexpr s0 s1 s2 =>
      congr_ifexpr (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm sigma_tm Eq_tm s1) (idSubst_tm sigma_tm Eq_tm s2)
  end.

Lemma upExtRen_tm_tm (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_tm_tm xi x = upRen_tm_tm zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_tm (xi_tm : nat -> nat) (zeta_tm : nat -> nat)
(Eq_tm : forall x, xi_tm x = zeta_tm x) (s : tm) {struct s} :
ren_tm xi_tm s = ren_tm zeta_tm s :=
  match s with
  | var_tm s0 => ap (var_tm) (Eq_tm s0)
  | pi s0 s1 =>
      congr_pi (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s1)
  | U => congr_U
  | Empty => congr_Empty
  | Bool => congr_Bool
  | Lift s0 => congr_Lift (extRen_tm xi_tm zeta_tm Eq_tm s0)
  | var s0 => congr_var (eq_refl s0)
  | lambda s0 =>
      congr_lambda
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s0)
  | app s0 s1 =>
      congr_app (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1)
  | true => congr_true
  | false => congr_false
  | ifexpr s0 s1 s2 =>
      congr_ifexpr (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1) (extRen_tm xi_tm zeta_tm Eq_tm s2)
  end.

Lemma upExt_tm_tm (sigma : nat -> tm) (tau : nat -> tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_tm_tm sigma x = up_tm_tm tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_tm (sigma_tm : nat -> tm) (tau_tm : nat -> tm)
(Eq_tm : forall x, sigma_tm x = tau_tm x) (s : tm) {struct s} :
subst_tm sigma_tm s = subst_tm tau_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | pi s0 s1 =>
      congr_pi (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s1)
  | U => congr_U
  | Empty => congr_Empty
  | Bool => congr_Bool
  | Lift s0 => congr_Lift (ext_tm sigma_tm tau_tm Eq_tm s0)
  | var s0 => congr_var (eq_refl s0)
  | lambda s0 =>
      congr_lambda
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s0)
  | app s0 s1 =>
      congr_app (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1)
  | true => congr_true
  | false => congr_false
  | ifexpr s0 s1 s2 =>
      congr_ifexpr (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1) (ext_tm sigma_tm tau_tm Eq_tm s2)
  end.

Lemma up_ren_ren_tm_tm (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_tm_tm zeta) (upRen_tm_tm xi) x = upRen_tm_tm rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_tm (xi_tm : nat -> nat) (zeta_tm : nat -> nat)
(rho_tm : nat -> nat) (Eq_tm : forall x, funcomp zeta_tm xi_tm x = rho_tm x)
(s : tm) {struct s} : ren_tm zeta_tm (ren_tm xi_tm s) = ren_tm rho_tm s :=
  match s with
  | var_tm s0 => ap (var_tm) (Eq_tm s0)
  | pi s0 s1 =>
      congr_pi (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s1)
  | U => congr_U
  | Empty => congr_Empty
  | Bool => congr_Bool
  | Lift s0 => congr_Lift (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
  | var s0 => congr_var (eq_refl s0)
  | lambda s0 =>
      congr_lambda
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s0)
  | app s0 s1 =>
      congr_app (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
  | true => congr_true
  | false => congr_false
  | ifexpr s0 s1 s2 =>
      congr_ifexpr (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s2)
  end.

Lemma up_ren_subst_tm_tm (xi : nat -> nat) (tau : nat -> tm)
  (theta : nat -> tm) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_tm_tm tau) (upRen_tm_tm xi) x = up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_tm (xi_tm : nat -> nat) (tau_tm : nat -> tm)
(theta_tm : nat -> tm)
(Eq_tm : forall x, funcomp tau_tm xi_tm x = theta_tm x) (s : tm) {struct s} :
subst_tm tau_tm (ren_tm xi_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | pi s0 s1 =>
      congr_pi (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s1)
  | U => congr_U
  | Empty => congr_Empty
  | Bool => congr_Bool
  | Lift s0 => congr_Lift (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
  | var s0 => congr_var (eq_refl s0)
  | lambda s0 =>
      congr_lambda
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s0)
  | app s0 s1 =>
      congr_app (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
  | true => congr_true
  | false => congr_false
  | ifexpr s0 s1 s2 =>
      congr_ifexpr (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s2)
  end.

Lemma up_subst_ren_tm_tm (sigma : nat -> tm) (zeta_tm : nat -> nat)
  (theta : nat -> tm)
  (Eq : forall x, funcomp (ren_tm zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_tm_tm zeta_tm)) (up_tm_tm sigma) x =
  up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_tm shift (upRen_tm_tm zeta_tm)
                (funcomp shift zeta_tm) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_tm zeta_tm shift (funcomp shift zeta_tm)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_tm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_tm (sigma_tm : nat -> tm) (zeta_tm : nat -> nat)
(theta_tm : nat -> tm)
(Eq_tm : forall x, funcomp (ren_tm zeta_tm) sigma_tm x = theta_tm x) 
(s : tm) {struct s} :
ren_tm zeta_tm (subst_tm sigma_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | pi s0 s1 =>
      congr_pi (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s1)
  | U => congr_U
  | Empty => congr_Empty
  | Bool => congr_Bool
  | Lift s0 =>
      congr_Lift (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
  | var s0 => congr_var (eq_refl s0)
  | lambda s0 =>
      congr_lambda
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s0)
  | app s0 s1 =>
      congr_app (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
  | true => congr_true
  | false => congr_false
  | ifexpr s0 s1 s2 =>
      congr_ifexpr (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s2)
  end.

Lemma up_subst_subst_tm_tm (sigma : nat -> tm) (tau_tm : nat -> tm)
  (theta : nat -> tm)
  (Eq : forall x, funcomp (subst_tm tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_tm_tm tau_tm)) (up_tm_tm sigma) x = up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_tm shift (up_tm_tm tau_tm)
                (funcomp (up_tm_tm tau_tm) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_tm tau_tm shift
                      (funcomp (ren_tm shift) tau_tm) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_tm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_tm (sigma_tm : nat -> tm) (tau_tm : nat -> tm)
(theta_tm : nat -> tm)
(Eq_tm : forall x, funcomp (subst_tm tau_tm) sigma_tm x = theta_tm x)
(s : tm) {struct s} :
subst_tm tau_tm (subst_tm sigma_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | pi s0 s1 =>
      congr_pi (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s1)
  | U => congr_U
  | Empty => congr_Empty
  | Bool => congr_Bool
  | Lift s0 =>
      congr_Lift (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
  | var s0 => congr_var (eq_refl s0)
  | lambda s0 =>
      congr_lambda
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s0)
  | app s0 s1 =>
      congr_app (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
  | true => congr_true
  | false => congr_false
  | ifexpr s0 s1 s2 =>
      congr_ifexpr (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s2)
  end.

Lemma renRen_tm (xi_tm : nat -> nat) (zeta_tm : nat -> nat) (s : tm) :
  ren_tm zeta_tm (ren_tm xi_tm s) = ren_tm (funcomp zeta_tm xi_tm) s.
Proof.
exact (compRenRen_tm xi_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_tm_pointwise (xi_tm : nat -> nat) (zeta_tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_tm zeta_tm) (ren_tm xi_tm))
    (ren_tm (funcomp zeta_tm xi_tm)).
Proof.
exact (fun s => compRenRen_tm xi_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm (xi_tm : nat -> nat) (tau_tm : nat -> tm) (s : tm) :
  subst_tm tau_tm (ren_tm xi_tm s) = subst_tm (funcomp tau_tm xi_tm) s.
Proof.
exact (compRenSubst_tm xi_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm_pointwise (xi_tm : nat -> nat) (tau_tm : nat -> tm) :
  pointwise_relation _ eq (funcomp (subst_tm tau_tm) (ren_tm xi_tm))
    (subst_tm (funcomp tau_tm xi_tm)).
Proof.
exact (fun s => compRenSubst_tm xi_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_tm (sigma_tm : nat -> tm) (zeta_tm : nat -> nat) (s : tm) :
  ren_tm zeta_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (ren_tm zeta_tm) sigma_tm) s.
Proof.
exact (compSubstRen_tm sigma_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_tm_pointwise (sigma_tm : nat -> tm) (zeta_tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_tm zeta_tm) (subst_tm sigma_tm))
    (subst_tm (funcomp (ren_tm zeta_tm) sigma_tm)).
Proof.
exact (fun s => compSubstRen_tm sigma_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm (sigma_tm : nat -> tm) (tau_tm : nat -> tm) (s : tm) :
  subst_tm tau_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (subst_tm tau_tm) sigma_tm) s.
Proof.
exact (compSubstSubst_tm sigma_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm_pointwise (sigma_tm : nat -> tm) (tau_tm : nat -> tm) :
  pointwise_relation _ eq (funcomp (subst_tm tau_tm) (subst_tm sigma_tm))
    (subst_tm (funcomp (subst_tm tau_tm) sigma_tm)).
Proof.
exact (fun s => compSubstSubst_tm sigma_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_tm_tm (xi : nat -> nat) (sigma : nat -> tm)
  (Eq : forall x, funcomp (var_tm) xi x = sigma x) :
  forall x, funcomp (var_tm) (upRen_tm_tm xi) x = up_tm_tm sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_tm (xi_tm : nat -> nat) (sigma_tm : nat -> tm)
(Eq_tm : forall x, funcomp (var_tm) xi_tm x = sigma_tm x) (s : tm) {struct s}
   : ren_tm xi_tm s = subst_tm sigma_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | pi s0 s1 =>
      congr_pi (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s1)
  | U => congr_U
  | Empty => congr_Empty
  | Bool => congr_Bool
  | Lift s0 => congr_Lift (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
  | var s0 => congr_var (eq_refl s0)
  | lambda s0 =>
      congr_lambda
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s0)
  | app s0 s1 =>
      congr_app (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
  | true => congr_true
  | false => congr_false
  | ifexpr s0 s1 s2 =>
      congr_ifexpr (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s2)
  end.

Lemma rinstInst'_tm (xi_tm : nat -> nat) (s : tm) :
  ren_tm xi_tm s = subst_tm (funcomp (var_tm) xi_tm) s.
Proof.
exact (rinst_inst_tm xi_tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_tm_pointwise (xi_tm : nat -> nat) :
  pointwise_relation _ eq (ren_tm xi_tm) (subst_tm (funcomp (var_tm) xi_tm)).
Proof.
exact (fun s => rinst_inst_tm xi_tm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_tm (s : tm) : subst_tm (var_tm) s = s.
Proof.
exact (idSubst_tm (var_tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_tm_pointwise : pointwise_relation _ eq (subst_tm (var_tm)) id.
Proof.
exact (fun s => idSubst_tm (var_tm) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_tm (s : tm) : ren_tm id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id s)).
Qed.

Lemma rinstId'_tm_pointwise : pointwise_relation _ eq (@ren_tm id) id.
Proof.
exact (fun s => eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id s)).
Qed.

Lemma varL'_tm (sigma_tm : nat -> tm) (x : nat) :
  subst_tm sigma_tm (var_tm x) = sigma_tm x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_tm_pointwise (sigma_tm : nat -> tm) :
  pointwise_relation _ eq (funcomp (subst_tm sigma_tm) (var_tm)) sigma_tm.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_tm (xi_tm : nat -> nat) (x : nat) :
  ren_tm xi_tm (var_tm x) = var_tm (xi_tm x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_tm_pointwise (xi_tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_tm xi_tm) (var_tm))
    (funcomp (var_tm) xi_tm).
Proof.
exact (fun x => eq_refl).
Qed.

Inductive ctx : Type :=
  | nil : ctx
  | cons : ctx -> nat -> tm -> ctx.

Lemma congr_nil : nil = nil.
Proof.
exact (eq_refl).
Qed.

Lemma congr_cons {s0 : ctx} {s1 : nat} {s2 : tm} {t0 : ctx} {t1 : nat}
  {t2 : tm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  cons s0 s1 s2 = cons t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => cons x s1 s2) H0))
            (ap (fun x => cons t0 x s2) H1)) (ap (fun x => cons t0 t1 x) H2)).
Qed.

Fixpoint subst_ctx (sigma_tm : nat -> tm) (s : ctx) {struct s} : ctx :=
  match s with
  | nil => nil
  | cons s0 s1 s2 => cons (subst_ctx sigma_tm s0) s1 (subst_tm sigma_tm s2)
  end.

Fixpoint idSubst_ctx (sigma_tm : nat -> tm)
(Eq_tm : forall x, sigma_tm x = var_tm x) (s : ctx) {struct s} :
subst_ctx sigma_tm s = s :=
  match s with
  | nil => congr_nil
  | cons s0 s1 s2 =>
      congr_cons (idSubst_ctx sigma_tm Eq_tm s0) (eq_refl s1)
        (idSubst_tm sigma_tm Eq_tm s2)
  end.

Fixpoint ext_ctx (sigma_tm : nat -> tm) (tau_tm : nat -> tm)
(Eq_tm : forall x, sigma_tm x = tau_tm x) (s : ctx) {struct s} :
subst_ctx sigma_tm s = subst_ctx tau_tm s :=
  match s with
  | nil => congr_nil
  | cons s0 s1 s2 =>
      congr_cons (ext_ctx sigma_tm tau_tm Eq_tm s0) (eq_refl s1)
        (ext_tm sigma_tm tau_tm Eq_tm s2)
  end.

Fixpoint compSubstSubst_ctx (sigma_tm : nat -> tm) (tau_tm : nat -> tm)
(theta_tm : nat -> tm)
(Eq_tm : forall x, funcomp (subst_tm tau_tm) sigma_tm x = theta_tm x)
(s : ctx) {struct s} :
subst_ctx tau_tm (subst_ctx sigma_tm s) = subst_ctx theta_tm s :=
  match s with
  | nil => congr_nil
  | cons s0 s1 s2 =>
      congr_cons (compSubstSubst_ctx sigma_tm tau_tm theta_tm Eq_tm s0)
        (eq_refl s1) (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s2)
  end.

Lemma substSubst_ctx (sigma_tm : nat -> tm) (tau_tm : nat -> tm) (s : ctx) :
  subst_ctx tau_tm (subst_ctx sigma_tm s) =
  subst_ctx (funcomp (subst_tm tau_tm) sigma_tm) s.
Proof.
exact (compSubstSubst_ctx sigma_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_ctx_pointwise (sigma_tm : nat -> tm) (tau_tm : nat -> tm) :
  pointwise_relation _ eq (funcomp (subst_ctx tau_tm) (subst_ctx sigma_tm))
    (subst_ctx (funcomp (subst_tm tau_tm) sigma_tm)).
Proof.
exact (fun s => compSubstSubst_ctx sigma_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_ctx (s : ctx) : subst_ctx (var_tm) s = s.
Proof.
exact (idSubst_ctx (var_tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_ctx_pointwise : pointwise_relation _ eq (subst_ctx (var_tm)) id.
Proof.
exact (fun s => idSubst_ctx (var_tm) (fun n => eq_refl) s).
Qed.

Class Up_ctx X Y :=
    up_ctx : X -> Y.

Class Up_tm X Y :=
    up_tm : X -> Y.

#[global] Instance Subst_ctx : (Subst1 _ _ _) := @subst_ctx.

#[global] Instance Subst_tm : (Subst1 _ _ _) := @subst_tm.

#[global] Instance Up_tm_tm : (Up_tm _ _) := @up_tm_tm.

#[global] Instance Ren_tm : (Ren1 _ _ _) := @ren_tm.

#[global]
Instance VarInstance_tm : (Var _ _) := @var_tm.

(*
Notation "[ sigma_tm ]" := (subst_ctx sigma_tm)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_tm ]" := (subst_ctx sigma_tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__ctx" := up_ctx (only printing)  : subst_scope.

Notation "[ sigma_tm ]" := (subst_tm sigma_tm)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_tm ]" := (subst_tm sigma_tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__tm" := up_tm (only printing)  : subst_scope.

Notation "↑__tm" := up_tm_tm (only printing)  : subst_scope.

Notation "⟨ xi_tm ⟩" := (ren_tm xi_tm)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_tm ⟩" := (ren_tm xi_tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var_tm ( at level 1, only printing)  : subst_scope.

Notation "x '__tm'" := (@ids _ _ VarInstance_tm x)
( at level 5, format "x __tm", only printing)  : subst_scope.

Notation "x '__tm'" := (var_tm x) ( at level 5, format "x __tm")  :
subst_scope.
*)
#[global]
Instance subst_ctx_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_ctx)).
Proof.
exact (fun f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => subst_ctx f_tm s = subst_ctx g_tm t')
         (ext_ctx f_tm g_tm Eq_tm s) t Eq_st).
Qed.

#[global]
Instance subst_ctx_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_ctx)).
Proof.
exact (fun f_tm g_tm Eq_tm s => ext_ctx f_tm g_tm Eq_tm s).
Qed.

#[global]
Instance subst_tm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => subst_tm f_tm s = subst_tm g_tm t')
         (ext_tm f_tm g_tm Eq_tm s) t Eq_st).
Qed.

#[global]
Instance subst_tm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s => ext_tm f_tm g_tm Eq_tm s).
Qed.

#[global]
Instance ren_tm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => ren_tm f_tm s = ren_tm g_tm t')
         (extRen_tm f_tm g_tm Eq_tm s) t Eq_st).
Qed.

#[global]
Instance ren_tm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s => extRen_tm f_tm g_tm Eq_tm s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1,
                      Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1,
                      Subst_ctx, Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_tm, Var, ids,
                                            Ren_tm, Ren1, ren1, Up_tm_tm,
                                            Up_tm, up_tm, Subst_tm, Subst1,
                                            subst1, Subst_ctx, Subst1, subst1
                                            in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_ctx_pointwise
                 | progress setoid_rewrite substSubst_ctx
                 | progress setoid_rewrite substSubst_tm_pointwise
                 | progress setoid_rewrite substSubst_tm
                 | progress setoid_rewrite substRen_tm_pointwise
                 | progress setoid_rewrite substRen_tm
                 | progress setoid_rewrite renSubst_tm_pointwise
                 | progress setoid_rewrite renSubst_tm
                 | progress setoid_rewrite renRen'_tm_pointwise
                 | progress setoid_rewrite renRen_tm
                 | progress setoid_rewrite instId'_ctx_pointwise
                 | progress setoid_rewrite instId'_ctx
                 | progress setoid_rewrite varLRen'_tm_pointwise
                 | progress setoid_rewrite varLRen'_tm
                 | progress setoid_rewrite varL'_tm_pointwise
                 | progress setoid_rewrite varL'_tm
                 | progress setoid_rewrite rinstId'_tm_pointwise
                 | progress setoid_rewrite rinstId'_tm
                 | progress setoid_rewrite instId'_tm_pointwise
                 | progress setoid_rewrite instId'_tm
                 | progress unfold up_tm_tm, upRen_tm_tm, up_ren
                 | progress cbn[subst_ctx subst_tm ren_tm]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1,
                  Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1,
                  Subst_ctx, Subst1, subst1 in *; asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_tm_pointwise;
                  try setoid_rewrite rinstInst'_tm.

Ltac renamify := auto_unfold; try setoid_rewrite_left rinstInst'_tm_pointwise;
                  try setoid_rewrite_left rinstInst'_tm.

End Core.

Module Extra.

Import Core.

#[global] Hint Opaque subst_ctx: rewrite.

#[global] Hint Opaque subst_tm: rewrite.

#[global] Hint Opaque ren_tm: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

