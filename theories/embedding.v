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
                                 -> Typed ctx <fun env => `B (env , `s2 env)> <`app `s1 `s2>
| ty_var : forall ctx T t, VarTyped ctx T t -> Typed ctx T t
| ty_pi : forall ctx lvl A B,
    Typed ctx <`U `lvl> A
    -> Typed ctx <`cons ctx A> B -> Typed ctx <`U `lvl> <`pi `A `B>
| ty_U : forall ctx lvl, Typed ctx <`U `lvl> <`U (`lsuc `lvl)>
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
| in_Pi : forall A B f,
    (forall a, In a A -> In <`f `a> B)
    -> In f <Pi `A `B>
.

Inductive InCtx : QTerm -> QTerm -> Prop :=
| in_nil : InCtx <nil> <nil>
| in_cons : forall env ctx val T,
    InCtx env ctx -> In val T -> InCtx <`env , `val> <`cons `ctx `T> 
.



(* Think about the proof informally first *)
Theorem fundamental_lemma : forall ctx T t env,
    Typed ctx T t -> InCtx env ctx -> In <`t `env> <`T `env>.
Proof.
  intros.
  induction H.
  - unfold pi. normalize. repeat fix_subst_lifts.
    eapply (cast (in_Pi _ _ _ _)). unfold_all.
    lambda_solve. (* I don't understand what happned to the goal from the arg to in_Pi. How
                   did it get solved? *)
  - pose (IHTyped1 H0) as Ih1.
    pose (IHTyped2 H0) as Ih2.
    inversion Ih1.
    unfold pi in H4.
    Check eta.
    normalize_in H4.

    Check lamInj.
    match goal with
    | H : lam ?s ?t1 = lam ?s ?t2 |- _ => apply lamInj in H
    end.
    lambda_solve.
    rewrite (lamInj _ _ "x") in H4.
    (* we should be able to get a contradiction! *)
    lambda_solve.
