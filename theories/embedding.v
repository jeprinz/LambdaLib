Require Import String.
Require Import qterm.
Require Import lambdaFacts.
Require Import lambdaSolve.



(*
Here I will use the library to define dependent type theory.
For now, I'll just do type : type.
*)


(* The shallow embedding. Ideally this would work with nice notations, but for now Definitions: *)

Definition nil := <Nil>.
Definition cons := <fun gamma => fun ty => (gamma , ty)>.

Definition zero := <fun x => proj2 x>.
Definition succ := <fun x => fun gamma => x (proj1 gamma)>.

Definition lzero := <lzero>.
Definition lsuc := <lsuc>.
Definition pi := <fun x => fun y => fun gamma => Pi (x gamma) (fun a => y (gamma , a))>.
Definition U : QTerm := <fun lvl => fun env => U lvl>.
Definition Empty := <fun env => Empty>.

Definition var_to_term := <fun x => x>.
Definition lambda := <fun t => fun gamma => fun a => t (gamma , a)>.
Definition app := <fun t1 => fun t2 => fun gamma => (t1 gamma) (t2 gamma)>.

Definition weaken := <fun t => fun env => t (proj1 env)>.

Ltac unfold_all := unfold nil, cons, zero, succ, pi, U, var_to_term, lambda, app, weaken, lzero, lsuc.

(* The deeper shallow embedding *)

Inductive VarTyped : QTerm -> QTerm -> QTerm -> Prop :=
| ty_zero : forall ctx T, VarTyped <`cons `ctx `T> <`weaken `T> zero
| ty_succ : forall ctx A T s, VarTyped ctx A s
                              -> VarTyped <`cons `ctx `T> <`weaken `A> <`succ `s>
.

Inductive Typed : QTerm -> QTerm -> QTerm -> Prop :=
| ty_lambda : forall ctx A B s, Typed <`cons `ctx `A> B s -> Typed ctx <`pi `A `B> <`lambda `s>
| ty_app : forall ctx A B s1 s2, Typed ctx <`pi `A `B> s1 -> Typed ctx A s2
                                 -> Typed ctx <fun env => `B [env] (env , (`s2 [env]) env)> <`app `s1 `s2>
| ty_var : forall ctx T t, VarTyped ctx T t -> Typed ctx T t
| ty_pi : forall ctx lvl A B,
    Typed ctx <`U `lvl> A
    -> Typed <`cons `ctx `A> <`U `lvl> B -> Typed ctx <`U `lvl> <`pi `A `B>
| ty_U : forall ctx lvl, Typed ctx <`U (`lsuc `lvl)> <`U `lvl>
| ty_Empty : forall ctx lvl, Typed ctx <`U `lvl> Empty
.

Theorem cast {A B : Type} (a : A) (p : A = B) : B.
Proof.
  intros.
  rewrite <- p.
  assumption.
Qed.

(* The identity function is typed at U -> U*)
Theorem test1 : Typed nil <`pi (`U `lzero) (`U `lzero)> <`lambda `zero>.
Proof.
  apply ty_lambda.
  apply ty_var.
  eapply (cast (ty_zero _ _)).
  unfold_all.
  lambda_solve.
Qed.

(* Obviously this is not acceptable in a proof, but I'm just testing things for now *)
Unset Positivity Checking.
Inductive In : QTerm -> QTerm -> Prop :=
| in_U : forall lvl, In <U `lvl> <U (`lsuc `lvl)>

(* Is this right? How should B take a as an input? *)
| in_fun : forall A B f,
    (forall a, In a A -> In <`f `a> <`B `a>)
    -> In f <Pi `A `B>
| in_Pi : forall A B lvl,
    In A <U `lvl>
    -> (forall a, In a A -> In <`B `a> <U `lvl>)
    -> In <Pi `A `B> <U `lvl>
| in_Empty : forall lvl,
    In <Empty> <U `lvl>
.
(* TODO: should I encode PI as <Pi A B> or <Pi , A , B>?*)


Inductive InCtx : QTerm -> QTerm -> Prop :=
| in_nil : InCtx nil nil
| in_cons : forall env ctx val T,
    InCtx env ctx -> In val <`T `env> -> InCtx <`env , `val> <`cons `ctx `T> 
.

Theorem fundamental_lemma_for_variables : forall ctx T t env,
    VarTyped ctx T t -> InCtx env ctx -> In <`t `env> <`T `env>.
Proof.
  intros.
  induction H.
  - inversion H0.
    + unfold cons in H2.
      normalize_in H2.
      (* we need to be able to prove that nil != cons here, but with my representation that doesn' twork*)
Admitted.      

(* Think about the proof informally first *)
Theorem fundamental_lemma : forall ctx T t env,
    Typed ctx T t -> InCtx env ctx -> In <`t `env> <`T `env>.
Proof.
  intros.
  generalize env, H0.
  clear H0.
  clear env.
  induction H.
  - intros. unfold pi. normalize. repeat fix_subst_lifts.
    eapply (cast (in_fun _ _ _ _)). unfold_all.
    lambda_solve.
    Unshelve. (* This focuses the goal from the argument to in_fun *)
    intros.
    normalize. repeat fix_subst_lifts.
    apply IHTyped.
    apply in_cons.
    apply H0.
    apply H1.
  - intros.
    pose (IHTyped1 env H1) as Ih1.
    pose (IHTyped2 env H1) as Ih2.
    inversion Ih1.
    (* Prove that it can't be in_U *)
    unfold pi in H4.
    Check eta.
    normalize_in H4.
    solve_neutral_unequal_case.
    (* Do the actual real proof for in_fun *)
    unfold pi in H2.
    normalize_in H2.
    repeat fix_subst_lifts_in H2.
    lambda_solve.
    repeat neutral_inj_case.
    lambda_solve.
    normalize.
    fix_subst_lifts.
    apply H4 in Ih2.
    unfold app.
    normalize.
    repeat fix_subst_lifts.
    
    apply (cast Ih2).
    lambda_solve.
    fix_subst_lifts.
    reflexivity.
    (* prove that it can't be in_Pi *)
    unfold pi in H3.
    normalize_in H3.
    solve_neutral_unequal_case.
    (* prove that it can't be in_Empty *)
    unfold pi in H4.
    normalize_in H4.
    solve_neutral_unequal_case.
  - intros.
    apply (fundamental_lemma_for_variables ctx T t env H H0).
  - intros.
    unfold pi, U.
    normalize.
    repeat fix_subst_lifts.
    Check in_Pi.
    apply in_Pi.
    pose (IHTyped1 env H1) as ih1.
    unfold U in ih1.
    normalize_in ih1.
    fix_subst_lifts_in ih1.
    apply ih1.
    intros.
    normalize.
    fix_subst_lifts.
    Check in_cons.
    pose (IHTyped2 <`env , `a> (in_cons _ _ _ _ H1 H2)) as ih2.
    unfold U in ih2.
    normalize_in ih2.
    fix_subst_lifts_in ih2.
    apply ih2.
  - intros.
    Check in_U.
    eapply (cast (in_U _)).
    unfold U.
    normalize.
    fix_subst_lifts.
    lambda_solve.
  - intros.
    Check in_Empty.
    eapply (cast (in_Empty _)).
    unfold Empty, U.
    normalize.
    lambda_solve.
Qed.


Theorem consistency : forall t,
    Typed nil Empty t -> False.
Proof.
  intros.
  pose (fundamental_lemma nil Empty t nil H in_nil) as x.
  inversion x.
  unfold Empty in H2.
  normalize_in H2.
  solve_neutral_unequal_case.
  unfold Empty in H0.
  normalize_in H0.
  solve_neutral_unequal_case.
  unfold Empty in H1.
  normalize_in H1.
  solve_neutral_unequal_case.
  unfold Empty in H2.
  normalize_in H2.
  solve_neutral_unequal_case.
Qed.
