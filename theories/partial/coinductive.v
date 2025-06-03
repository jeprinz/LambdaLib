Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

(*
Is it possible that a coinductive type could allow me to define recursive functions which make an infinite number of recursive calls?

LATER: Yes, but you can't do match on QTerm with coinductive, which you can with Partial.
*)

(* basic version without multibind from https://www21.in.tum.de/~krauss/papers/recursion.pdf *)
CoInductive Computation : forall (A : Type), Type :=
| ret : forall A, A -> Computation A
| bind : forall A B, Computation A -> (A -> Computation B) -> Computation B
| multibind : forall A B I,
    (I -> Computation A)
    -> ((I -> A) -> Computation B)
    -> Computation B
.

CoFixpoint fancyid (n : nat) : Computation nat :=
  match n with
  | O => ret _ 0
  | S m => bind _ _ (fancyid m) (fun res => ret _ (1 + res))
  end.


(*
f : nat * nat -> Prop
f (0, _) = True
f (n, S m) = not (forall n', f (n', m))
 *)

CoFixpoint f (n : nat) (m : nat) : Computation Prop :=
  match m with
  | O => ret _ True
  | S m' => multibind _ _ nat (fun n' => f n' m') (fun rec => ret _ (not (forall n', rec n')))
  end.

(* It seems to work ?! *)


Inductive eval : forall {A}, Computation A -> A -> Prop :=
| eval_ret : forall A a, eval (ret A a) a
| eval_bind : forall A B ca a f res,
    eval ca a
    -> eval (f a) res
    -> eval (bind A B ca f) res
| eval_multibind : forall A B I cas aa f res,
    (forall i, eval (cas i) (aa i))
    -> eval (f aa) res
    -> eval (multibind A B I cas f) res
.


(*This section is from https://proofassistants.stackexchange.com/questions/4696/how-to-extract-the-equality-between-the-second-projection-in-an-existential-in-c*)
(* TODO: Is there really no easier way? Does this really require UIP? *)
Section existT_inj2_uip.
  Variables (A : Type) (P : A -> Type).

  Implicit Type (x : A).
  Print sigT.

  Theorem exist_inj2_helper x (px : P x) (y : sigT P) :
      @existT _ _ x px = y
    -> exists e : x = projT1 y, eq_rect x P px _ e = projT2 y.
  Proof using Type. intros []; exists eq_refl; auto. Qed.

  Fact exists_inj2 x y (px : P x) (py : P y) :
      existT _ x px = existT _ y py
    -> exists e : x = y, eq_rect x P px _ e = py.
  Proof using Type. intros (e & ?)%exist_inj2_helper. exists e; subst; simpl; auto. Qed.

  Fact exist_inj2_uip :
    forall x (p1 p2 : P x), existT _ x p1 = existT _ x p2 -> p1 = p2.
  Proof using Type.
    intros x p1 p2 (e & He)%exists_inj2.
    rewrite (UIP _ _ _ e eq_refl) in He.
    assumption.
  Qed.
End existT_inj2_uip.

Theorem eval_function {A} (c : Computation A) (a1 a2 : A)
  : eval c a1 -> eval c a2 -> a1 = a2.
Proof.
  intros.
  generalize dependent H0.
  induction H.
  - intros.
    inversion H0.
    apply exist_inj2_uip in H2, H3.
    subst.
    reflexivity.
  - intros.
    inversion H1.
    subst.
    apply exist_inj2_uip in H3, H6, H7, H6.
    subst.
    apply IHeval2.
    rewrite (IHeval1 _ H5).
    assumption.
  - intros.
    inversion H2.
    subst.
    apply exist_inj2_uip in H8, H7, H9, H8, H8, H7.
    subst.
    apply IHeval.
    assert (aa = aa0). {
      extensionality i.
      apply H0.
      apply H6.
    }
    subst.
    assumption.
Qed.

Theorem bindDef : forall A B a f,
    eval (bind A B (ret A a) f) = eval (f a).
Proof.
  intros.
  extensionality b.
  apply propositional_extensionality.
  split.
  - intros.
    inversion H.
    clear H.
    subst.
    apply exist_inj2_uip in H1, H4, H5, H4.
    subst.
    Check (eval_bind).
    inversion H3.
    apply exist_inj2_uip in H1, H2.
    subst.
    assumption.
  - intros.
    eapply eval_bind.
    + constructor.
    + apply H.
Qed.

Theorem multibindDef : forall A B I (rec : I -> A) f,
    eval (multibind A B I (fun i => ret A (rec i)) f) = eval (f rec).
Proof.
  intros.
  extensionality b.
  apply propositional_extensionality.
  split.
  - intros.
    inversion H.
    clear H.
    subst.
    apply exist_inj2_uip in H5, H4, H5, H4, H5, H6.
    subst.
    Check (eval_bind).
    assert (rec = aa). {
      extensionality i.
      specialize (H3 i).
      inversion H3.
      apply exist_inj2_uip in H1, H2.
      subst.
      assumption.
    }
    subst.
    assumption.
  - intros.
    eapply eval_multibind.
    + constructor.
    + apply H.
Qed.    

(*
Need it to be an equivalence, and also injectivity (ceq (ret x) (ret y)) -> x = y.
*)

(* This definition needs funext and propext to make sense *)
Definition ceq {A} (c1 c2 : Computation A) : Prop := eval c1 = eval c2.

Theorem ceq_refl {A} (c : Computation A) : ceq c c.
Proof.
  reflexivity.
Qed.

Theorem ceq_sym {A} (c1 c2 : Computation A) : ceq c1 c2 -> ceq c2 c1.
Proof.
  unfold ceq.
  intros.
  auto.
Qed.

Theorem ceq_trans {A} (c1 c2 c3 : Computation A) : ceq c1 c2 -> ceq c2 c3 -> ceq c1 c3.
Proof.
  unfold ceq.
  intros.
  rewrite H.
  auto.
Qed.

Theorem ret_inj : forall A a1 a2, ceq (ret A a1) (ret A a2) -> a1 = a2.
Proof.
  intros.
  unfold ceq in H.
  assert (forall x, eval (ret A x) = (fun a => a = x)). {
    intros.
    extensionality a.
    apply propositional_extensionality.
    split.
    - intros.
      inversion H0.
      apply exist_inj2_uip in H3, H4.
      subst.
      reflexivity.
    - intros.
      subst.
      constructor.
  }
  rewrite (H0 a1) in H.
  rewrite (H0 a2) in H.
  apply (f_equal (fun f => f a1)) in H.
  rewrite <- H.
  reflexivity.
Qed.

Theorem thing_thing : fancyid 3 = ret _ 3.
Proof.
  unfold fancyid.
  simpl.
  cbv cofix.

Abort.

CoInductive counit :=  nil : counit.

Lemma unfold_counit : forall (n : counit), n = match n with nil => nil end.
Proof.
  intros.
  destruct n.
  reflexivity.
Qed.

Theorem even_simpler : (cofix id :=  nil ) = nil.
Proof.
  simpl.
  rewrite unfold_counit at 1.
  reflexivity.
Qed.

Theorem unfold_computation :
  forall A (c : Computation A), c =
                                  match c with
                                  | ret A x => ret A x
                                  | bind A B x f => bind A B x f
                                  | multibind A B T x f => multibind A B T x f
                                  end.
Proof.
Admitted.

Theorem test_fun_fancyid : eval (fancyid 3) = eval (ret _ 3).
Proof.
  unfold fancyid.
  rewrite unfold_computation at 1.
  rewrite bindDef.

(*


(*
f : nat * nat -> Prop
f (0, _) = True
f (n, S m) = not (forall n', f (n', m))
 *)

CoFixpoint f (n : nat) (m : nat) : Computation Prop :=
  match m with
  | O => ret _ True
  | S m' => multibind _ _ nat (fun n' => f n' m') (fun rec => ret _ (not (forall n', rec n')))
  end.
 *)

(* now, can I show that f 2 2 = True for example? *)

Theorem test_run_f : eval (f 2 2) = eval (ret _ True).
Proof.
  unfold f.
  
