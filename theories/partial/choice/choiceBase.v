Require Import Classical.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

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

(* These are how it works in the lean4 standard library *)
Axiom choose : forall (T : Type) (P : T -> Prop) {_ : exists t, P t}, T.
Axiom chooseSpec : forall T P x, P (@choose T P x).
(* Apparently by Diaconescu's theorem you can derive LEM from this (see lean stdlib) *)

Theorem choiceInd : forall (T : Type) (P Q : T -> Prop) x,
    (forall t, P t -> Q t) -> Q (@choose T P x).
Proof.
  intros.
  apply H.
  apply chooseSpec.
Qed.

Theorem choiceIndHyp : forall T P t p, t = @choose T P p -> P t.
Proof.
  intros.
  generalize dependent H.
  apply choiceInd.
  intros.
  subst.
  assumption.
Qed.

Definition Pif {A : Type} (P : Prop) (a1 a2 : A) : A.
  Search (Prop -> Type).
  Check (sum {a : A | P} {a : A | ~ P}).
  refine (choose A (fun a => P /\ a = a1 \/ ~P /\ a = a2)).
  destruct (classic P).
  - exists a1.
    auto.
  - exists a2.
    auto.
Defined.

Theorem PifDef1 : forall (A : Type) P (a1 a2 : A), P -> Pif P a1 a2 = a1.
Proof.
  intros.
  unfold Pif.
  evar (exists t : A, P /\ t = a1 \/ ~ P /\ t = a2).
  destruct (chooseSpec A (fun a : A => P /\ a = a1 \/ ~ P /\ a = a2) e).
  - destruct H0.
    unfold e in H1.
    erewrite H1.
    reflexivity.
  - destruct H0.
    contradiction.
Qed.

Theorem PifDef2 : forall (A : Type) P (a1 a2 : A), (P -> False) -> Pif P a1 a2 = a2.
Proof.
  intros.
  unfold Pif.
  apply choiceInd.
  intros.
  destruct H0.
  - destruct H0.
    contradiction.
  - destruct H0.
    assumption.
Qed.

Check choose.
(* Using choice, returns the element of T satisfying P if it exists, otherwise None *)
Definition chooseOption (T : Type) (P : T -> Prop) : option T.
  refine (choose (option T)
                 (fun ot => match ot with
                            | Some t => P t
                            | None => ~exists t, P t
                            end)).
  destruct (classic (exists t, P t)).
  - destruct H.
    exists (Some x).
    assumption.
  -  exists None.
     assumption.
  (*
  refine (choose (option T)
                 (fun ot => ((~exists t, P t) /\ ot = None) \/ (exists t, P t /\ ot = Some t))).
  destruct (classic (exists t, P t)).
  - destruct H.
    exists (Some x).
    apply or_intror.
    eauto.
  - exists None.
    apply or_introl.
    eauto.
   *)
Defined.

Theorem chooseOptionSpec1 : forall T P t,
    chooseOption T P = Some t -> P t.
Proof.
  intros T P t.
  unfold chooseOption.
  Check choiceInd.
  apply choiceInd.
  intros.
  destruct t0.
  - inversion H0.
    subst.
    assumption.
  - inversion H0.
  (*
  destruct H.
  - destruct H.
    subst.
    inversion H0.
  - destruct H.
    destruct H.
    subst.
    inversion H0.
    subst.
    assumption.
   *)
Qed.  

Theorem chooseOptionSpec2 : forall T P,
    chooseOption T P = None -> ~exists t, P t.
Proof.
  intros T P.
  unfold chooseOption.
  apply choiceInd.
  intros.
  destruct t.
  - inversion H0.
  - assumption.
  (*
  destruct H.
  - destruct H.
    assumption.
  - destruct H.
    destruct H.
    subst.
    inversion H0.
   *)
Qed.
    
Definition collectOption {A B : Type} (f : A -> option B) : option (A -> B) :=
  (chooseOption (A -> B) (fun f' => forall a, (Some (f' a)) = f a)).

Definition collectOption2 {A : Type} {B : A -> Type} {C : Type}
           (f : forall (a : A), B a -> option C) : option (forall a, B a -> C) :=
  chooseOption (forall a, B a -> C) (fun f' => forall a b, Some (f' a b) = f a b).

Theorem collectOptionDef {A : Type} {B : Type}
        (f : A -> B)
  : collectOption (fun a => Some (f a)) = Some f.
Proof.
  unfold collectOption, chooseOption.
  apply choiceInd.
  intros.
  destruct t.
  - assert (b = f). {
      extensionality a.
      specialize (H a).
      inversion H.
      reflexivity.
    }
    congruence.
  - exfalso.
    apply H.
    exists f.
    intros.
    reflexivity.
Qed.

Theorem collectOption2Def {A : Type} {B : A -> Type} {C : Type}
        (f : forall (a : A), B a -> C) :
  collectOption2 (fun a b => Some (f a b)) = Some f.
Proof.
  unfold collectOption2, chooseOption.
  apply choiceInd.
  intros.
  destruct t.
  - assert (c = f). {
      extensionality a.
      extensionality b.
      specialize (H a b).
      inversion H.
      reflexivity.
    }
    subst.
    reflexivity.
  - exfalso.
    apply H.
    exists f.
    intros.
    reflexivity.
Qed.

(* Is this really not in the standard library? *)
Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
  match a with
  | Some a' => f a'
  | None => None
  end.
