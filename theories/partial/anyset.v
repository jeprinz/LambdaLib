Require Import Coq.Logic.ProofIrrelevance.
(* Instead of using SProp, for now I'll just use the proof irrelevance axiom.
   I'll see if this causes any issues; probably not. *)
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

(*
Starting from nonempty5.v,
I'm testing if the nonemptyness property even matters at all.
In this version, I'm also just replacing CProp with Prop.
Maybe in another version I'll try not doing that.
 *)

Definition PClassical (P : Prop) : Prop := not (not P).

Definition Preturn {A : Prop} (x : A) : PClassical A.
Proof.
  intro na.
  apply na.
  apply x.
Qed.

Theorem Pbind {A B : Prop} (pa : PClassical A) (f : A -> PClassical B) : PClassical B.
  Proof.
  unfold PClassical in *.
  intros nb.
  apply pa.
  intro a.
  apply f.
  - apply a.
  - apply nb.
Qed.


Theorem sigEq :
  forall A P S1 S2 p1 p2,
    S1 = S2 -> @eq {a : A | P a} (exist _ S1 p1) (exist _ S2 p2).
Proof.
  intros.
  subst S1.
  assert (p1 = p2).
  apply proof_irrelevance.
  subst p1.
  reflexivity.
Qed.

Theorem sigEq2:
  forall A P (x y : {a : A | P a}), proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros.
  destruct x.
  destruct y.
  simpl in H.
  apply sigEq.
  assumption.
Qed.

Theorem Plem (P : Prop) : PClassical (P \/ ~P).
Proof.
  intros n.
  apply n.
  apply or_intror.
  intros p.
  apply n.
  apply or_introl.
  apply p.
Qed.

(* Monad for choice *)
Definition Classical (A : Type) : Type := A -> Prop.

Definition Creturn {A : Type} (x : A) : Classical A := fun a => a = x.

(* TODO: Confirm that the output really has to be in PClassical. *)
Theorem CreturnInj : forall A (x y : A), Creturn x = Creturn y -> x = y.
Proof.
  intros.
  unfold Creturn in H.
  apply (@f_equal _ _ (fun f => f x)) in H.
  rewrite <- H.
  reflexivity.
Qed.

Definition Cbind {A B : Type} (pa : Classical A) (f : A -> Classical B) : Classical B :=
  fun b => exists a, pa a /\ f a b.

(* one of the monad laws *)
Theorem bindDef : forall A B (a : A) (f : A -> Classical B),
    Cbind (Creturn a) f = f a.
Proof.
  intros.
  simpl.
  extensionality b.
  apply propositional_extensionality.
  split.
  - intros.
    simpl in H.
    unfold Cbind, Creturn in H.
    destruct H.
    destruct H.
    subst.
    assumption.
  - intros.
    unfold Cbind, Creturn.
    exists a.
    split; auto.
Qed.

(* TODO: Should P output a CProp? *)
Definition choose (T : Type) (P : T -> Prop) (H : PClassical (exists t, P t)): Classical T := P.

Theorem choice_spec (T : Type) (P : T -> Prop) (H : PClassical (exists t, P t))
  : Cbind (choose T P H) (fun t => Creturn (P t)) = Creturn True.
Proof.
  simpl.
  extensionality X.
  apply propositional_extensionality.
  split.
  - intros.
    destruct H0.
    destruct H0.
    unfold choose in H0.
    unfold Creturn in H1.
    subst.
    apply propositional_extensionality; split; auto.
  - intros.
    unfold Cbind, Creturn, choose, PClassical in *.
    subst.
    destruct H.
    apply (Pbind H0); clear H0; intros H0.
    apply Preturn.
    exists x.
    subst.
    split.
    + apply Preturn.
      assumption.
    + apply Preturn.
      apply propositional_extensionality; split; auto.
Qed.

Theorem monadlaw2 (T : Type) (t : Classical T) : Cbind t Creturn = t.
Proof.
  apply sigEq2.
  extensionality x.
  simpl.
  apply CProp_Ext.
  - intros.
    simpl in *.
    apply unwrap.
    apply (Pbind H); clear H; intros H.
    destruct H as [a [ta p]].
    apply (Pbind p); clear p; intros p.
    subst.
    apply Preturn.
    assumption.
  - intros.
    simpl in *.
    apply Preturn.
    exists x.
    split; auto.
    apply Preturn.
    reflexivity.
Qed.

Theorem writeInTermsOfBind (T : Type) (t1 t2 : Classical T)
        (H : Cbind t1 Creturn = Cbind t2 Creturn)
  : t1 = t2.
Proof.
  repeat rewrite monadlaw2 in H.
  assumption.
Qed.

Theorem choiceInd (A B : Type) (P : A -> Prop)
        {H : PClassical (exists a, P a)}
        {rest : A -> Classical B}
        {v : Classical B}
        (premise : forall x, P x -> rest x = v)
  : Cbind (choose _ P H) rest = v.
Proof.
  apply sigEq2.
  simpl.
  extensionality b.
  apply CProp_Ext.
  - intros.
    apply unwrap.
    simpl in *.
    apply (Pbind H0); clear H0; intros H0.
    destruct H0.
    destruct H0.
    apply (Pbind H0); clear H0; intros H0.
    specialize (premise x H0).
    subst.
    apply Preturn.
    assumption.
  - intros.
    simpl in *.
    apply (Pbind H); clear H; intros H.
    apply Preturn.
    destruct H.
    exists x.
    split.
    + apply Preturn.
      assumption.
    + specialize (premise x H).
      subst.
      assumption.
Qed.
(*
(* Is it possible to prove something like this? *)
Theorem choiceInd2 : forall (T : Type) (P : T -> Prop) (Q : T -> CProp) x,
    (forall t, P t -> isTrue (Q t)) -> isTrue (Cbind (@choose T P x) Q).
Abort.
(* Maybe something like this: *)
Theorem choice_spec (T : Type) (P : T -> CProp) (H : PClassical (exists t, P t))
  : isTrue (Cbind (choose T P H) P).
 *)

Inductive whileR {A B : Type} (step : A -> A + B) : A -> B -> Prop :=
| while_base : forall a b, step a = inr b -> whileR step a b
| while_step : forall a a' b, step a = inl a'
                              -> whileR step a' b
                              -> whileR step a b
.

Theorem whileRFunction : forall A B step a b1 b2,
    @whileR A B step a b1 
    -> @whileR A B step a b2
    -> b1 = b2.
Proof.
  intros.
  induction H; inversion H0.
  - rewrite H in H1.
    inversion H1.
    subst.
    reflexivity.
  - rewrite H in H1.
    inversion H1.
  - rewrite H in H2.
    inversion H2.
  - rewrite H in H2.
    inversion H2.
    subst.
    specialize (IHwhileR H3).
    subst.
    reflexivity.
Qed.

Definition Partial (T : Type) : Type := Classical (option T).

Definition while {A B : Type} (a : A) (step : A -> A + B) : Partial B.
  refine (choose _ (fun ob => match ob with
                              | None => ~ exists b, whileR step a b
                              | Some b => whileR step a b
                              end) _).
  apply (Pbind (Plem (exists b, whileR step a b))); intros.
  destruct H.
  - destruct H.
    apply Preturn.
    exists (Some x).
    assumption.
  - apply Preturn.
    exists None.
    assumption.
Defined.

Theorem whileBase (A B : Type) step (a : A) (b : B)
        (H : step a = inr b)
  : while a step = Creturn (Some b).
Proof.
  apply writeInTermsOfBind.
  rewrite bindDef.
  unfold while.
  Check @choiceInd.
  (* TODO: why are these next two lines like this *)
  rewrite @choiceInd with (v := Creturn (Some b)).
  reflexivity.
  intros.
  apply f_equal.
  destruct x.
  Check (while_base _ _ _ H).
  Check whileRFunction.
  - rewrite (whileRFunction _ _ _ _ _ _ (while_base _ _ _ H) H0).
    reflexivity.
  - apply while_base in H.
    exfalso.
    apply H0.
    exists b.
    assumption.
Qed.

Theorem whileStep (A B : Type) step (a a' : A)
        (H : step a = inl a')
  : @while A B a step = while a' step.
Proof.
  apply writeInTermsOfBind.
  Check choiceInd.
  unfold while.
  erewrite choiceInd; try reflexivity.
  symmetry.
  erewrite choiceInd; try reflexivity.
  intros.
  symmetry.
  apply f_equal.

  destruct x, x0.
  - rewrite (whileRFunction _ _ _ _ _ _ (while_step _ _ _ _ H H1) H0).
    reflexivity.
  - destruct H1.
    inversion H0.
    + rewrite H in H1.
      inversion H1.
    + rewrite H in H1.
      inversion H1.
      subst.
      exists b.
      assumption.
  - destruct H0.
    exists b.
    apply while_step with (a' := a'); assumption.
  - reflexivity.
Qed.
