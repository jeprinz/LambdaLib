Require Import Coq.Logic.ProofIrrelevance.
(* Instead of using SProp, for now I'll just use the proof irrelevance axiom.
   I'll see if this causes any issues; probably not. *)
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Definition Partial (A : Type) : Type :=
  {S : A -> Prop | forall x y, S x -> S y -> x = y}.


Definition Preturn {A : Type} (x : A) : Partial A.
  refine (exist _ (fun y => y = x) _).
  intros.
  congruence.
Defined.

Definition Pempty {A : Type} : Partial A.
  refine (exist _ (fun x => False) _).
  intros.
  exfalso.
  assumption.
Defined.

Theorem partialEq :
  forall A S1 S2 p1 p2,
    S1 = S2 -> @eq (Partial A) (exist _ S1 p1) (exist _ S2 p2).
Proof.
  intros.
  subst S1.
  assert (p1 = p2).
  apply proof_irrelevance.
  subst p1.
  reflexivity.
Qed.

Theorem partialEq2:
  forall A (x y : Partial A), proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros.
  destruct x.
  destruct y.
  simpl in H.
  apply partialEq.
  assumption.
Qed.

(* TODO: make better names for all these*)
Theorem itIsReturn :
  forall T (S : T -> Prop) (p : forall x y, S x -> S y -> x = y) (t : T),
    S t -> (exist _ S p) = Preturn t.
Proof.
  intros.
  apply partialEq.
  apply functional_extensionality.
  intros.
  apply propositional_extensionality.
  split.
  - intros.
    apply p.
    assumption.
    assumption.
  - intros.
    subst.
    assumption.
Qed.

Theorem returnIsIt :
  forall T (S : T -> Prop) (p : forall x y, S x -> S y -> x = y) (t : T),
    (exist _ S p) = Preturn t
    -> S t.
Proof.
  intros.
  apply (@f_equal (Partial T) (T -> Prop) (@proj1_sig _ _) _ _) in H.
  simpl in H.
  rewrite H.
  reflexivity.
Qed.

Theorem PreturnInj : forall A (x y : A), Preturn x = Preturn y -> x = y.
Proof.
  intros.
  pose (@f_equal _ _ (@proj1_sig _ _) _ _ H) as fact.
  simpl in fact.
  assert ((fun y => y = x) x).
  reflexivity.
  rewrite fact in H0.
  assumption.
Qed.

Definition Pbind {A B : Type} (pa : Partial A) (f : A -> Partial B) : Partial B.
  refine (exist _ (fun b => exists a, proj1_sig pa a /\ proj1_sig (f a) b) _).
  intros.
  destruct H as [a temp].
  destruct temp as [paa fax].
  destruct H0 as [a' temp].
  destruct temp as [paa' fa'y].
  assert (aa' := proj2_sig pa a a' paa paa').
  subst a'.
  apply (proj2_sig (f a) x y fax fa'y).
Defined.

Theorem bindDef1 : forall A B {f : A -> Partial B}, Pbind Pempty f = Pempty.
Proof.
  intros.
  apply partialEq.
  apply functional_extensionality.
  intros.
  apply propositional_extensionality.
  split.
  - intros.
    destruct H.
    destruct H.
    simpl in H.
    assumption.
  - intros. exfalso. assumption.
Qed.

Theorem bindDef2 : forall A B (a : A) (f : A -> Partial B),
    Pbind (Preturn a) f = f a.
Proof.
  intros.
  apply partialEq2.
  apply functional_extensionality.
  intros.
  apply propositional_extensionality.
  split.
  - intros.
    simpl in H.
    destruct H.
    destruct H.
    subst x0.
    assumption.
  - intros.
    simpl.
    exists a.
    split.
    reflexivity.
    assumption.
Qed.

Definition Pif {A : Type} (P : Prop) (a1 a2 : A) : Partial A.
  refine (exist _ (fun a => (P /\ a = a1) \/ ((not P) /\ a = a2)) _).
  intros.
  destruct H.
  destruct H.
  destruct H0.
  destruct H0.
  subst.
  reflexivity.
  destruct H0.
  contradiction.
  destruct H.
  destruct H0.
  destruct H0.
  contradiction.
  destruct H0.
  subst.
  reflexivity.
Defined.

Theorem PifDef1 : forall (A : Type) P (a1 a2 : A), P -> Pif P a1 a2 = Preturn a1.
Proof.
  intros.
  apply partialEq.
  apply functional_extensionality.
  intros.
  apply propositional_extensionality.
  split.
  - intros.
    destruct H0.
    destruct H0.
    assumption.
    destruct H0.
    contradiction.
  - intros.
    subst.
    apply or_introl.
    split.
    assumption.
    reflexivity.
Qed.

Theorem PifDef2 : forall (A : Type) P (a1 a2 : A), not P -> Pif P a1 a2 = Preturn a2.
Proof.
  intros.
  apply partialEq.
  apply functional_extensionality.
  intros.
  apply propositional_extensionality.
  split.
  - intros.
    destruct H0.
    + destruct H0.
      contradiction.
    + destruct H0.
      assumption.
  - intros.
    subst.
    apply or_intror.
    split.
    assumption.
    reflexivity.
Qed.
(* Does multibind actually work? *)
(* Maybe this will need (rest : (A -> Classical B) -> Partial C)*)
Definition Pmultibind {A B C : Type} (f : A -> Partial B) (rest : (A -> B) -> Partial C) : Partial C.
  (*refine (exist _ (fun c => forall (g : A -> B), (forall a, (Preturn (g a)) = f a) -> rest g = Preturn c) _).*)
  refine (exist _ (fun c => exists (g : A -> B), (forall a, (Preturn (g a) = f a)) /\ rest g = Preturn c) _).
  intros.
  destruct H.
  destruct H0.
  destruct H.
  destruct H0.
  apply PreturnInj.
  assert (x0 = x1). {
    extensionality a.
    specialize (H a).
    specialize (H0 a).
    rewrite <- H in H0.
    apply PreturnInj in H0.
    symmetry.
    assumption.
  }
  subst.
  rewrite <- H1.
  rewrite <- H2.
  reflexivity.
Defined.

Theorem multibindDef {A B C : Type} : forall f rest,
    @Pmultibind A B C (fun a => Preturn (f a)) rest = rest f.
Proof.
  intros.
  apply partialEq2.
  extensionality c.
  apply propositional_extensionality.
  split.
  - intros.
    destruct H.
    destruct H.
    assert (x = f). {
      extensionality a.
      specialize (H a).
      apply PreturnInj.
      apply H.
    }
    subst.
    rewrite H0.
    simpl.
    reflexivity.
  - intros.
    simpl.
    exists f.
    split.
    + intros.
      reflexivity.
    + Check itIsReturn.
      remember (rest f) as thing.
      destruct thing.
      simpl in H.
      apply itIsReturn.
      assumption.
Qed.      


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
