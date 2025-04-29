Require Import Coq.Logic.ProofIrrelevance.
(* Instead of using SProp, for now I'll just use the proof irrelevance axiom.
   I'll see if this causes any issues; probably not. *)
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Definition Classical (A : Type) : Type :=
  {S : A -> Prop | (forall x y, S x -> S y -> x = y) /\ not (forall x, not (S x))}.

Definition Preturn {A : Type} (x : A) : Classical A.
  refine (exist _ (fun y => y = x) _).
  intros.
  split.
  - intros.
    congruence.
  - intros p.
    specialize (p x).
    contradiction.
Defined.

Theorem classicalEq :
  forall A S1 S2 p1 p2,
    S1 = S2 -> @eq (Classical A) (exist _ S1 p1) (exist _ S2 p2).
Proof.
  intros.
  subst S1.
  assert (p1 = p2).
  apply proof_irrelevance.
  subst p1.
  reflexivity.
Qed.

Theorem classicalEq2:
  forall A (x y : Classical A), proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros.
  destruct x.
  destruct y.
  simpl in H.
  apply classicalEq.
  assumption.
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

Definition Pbind {A B : Type} (pa : Classical A) (f : A -> Classical B) : Classical B.
  refine (exist _ (fun b => exists a, proj1_sig pa a /\ proj1_sig (f a) b) _).
  destruct pa as [Sa [same nonempty]].
  simpl.
  split.
  - intros.
    destruct H as [a1 [Ssaa1 fa1x]].
    destruct H0 as [a2 [Ssaa2 fa2y]].
    specialize (same _ _ Ssaa1 Ssaa2).
    subst.
    destruct (proj2_sig (f a2)) as [unique _].
    specialize (unique x y fa1x fa2y).
    assumption.
  - intros p.
    apply nonempty.
    intros a Sax.
    remember (f a) as fa.
    destruct fa as [SB [unique nonemptyB]].
    apply nonemptyB.
    intros b SBb.
    specialize (p b).
    apply p.
    exists a.
    split.
    + apply Sax.
    + rewrite <- Heqfa.
      simpl.
      apply SBb.
Defined.

Theorem bindDef : forall A B (a : A) (f : A -> Classical B),
    Pbind (Preturn a) f = f a.
Proof.
  intros.
  apply classicalEq2.
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

Definition propBind {T : Type} (P : T -> Prop) (pa : Classical T) : Prop :=
  Preturn True = (Pbind pa (fun a => Preturn (P a))).

Theorem propBindDef {T : Type} (t : T) (P : T -> Prop) :
  propBind P (Preturn t) = P t.
Proof.
  unfold propBind.
  rewrite bindDef.
  apply propositional_extensionality.
  split.
  - intros.
    apply PreturnInj in H.
    rewrite <- H.
    apply I.
  - intros.
    apply (f_equal Preturn).
    apply propositional_extensionality.
    split; auto.
Qed.

Theorem doesClassicalImplyNormal (P : Prop) : Classical P -> P.
Proof.
  intros [S [unique nonempty]].
  (*I don't think so*)
Abort.

Theorem sortOfThough (P : Prop) : Classical P -> ~~P.
Proof.
  intros.
  intros np.
  destruct X as [S [unique nonempty]].
  apply nonempty.
  intros x Sx.
  apply np.
  apply x.
Qed.

Theorem thing (P : Prop) : ~ (~ (P \/ ~P)).
Proof.
  intros n.
  apply n.
  apply or_intror.
  intros p.
  apply n.
  apply or_introl.
  apply p.
Qed.

Theorem lem (P : Prop) : Classical (P \/ not P).
Proof.
  refine (exist _ (fun pornotp => True) _).
  split.
  - intros.
    exact (proof_irrelevance _ x y).
  - intros nn.
    assert ((~True) = False). {
      apply propositional_extensionality.
      split; auto.
    }
    rewrite H in nn.
    apply nn.
    + apply or_intror.
      intros p.
      apply nn.
      apply or_introl.
      apply p.
Defined.

Theorem ind {T : Type} : forall (P : Classical T -> Prop),
    (forall (a : T), P (Preturn a)) -> forall (q : Classical T), (P q).
Proof.
Abort.

(*
Definition Pif {A : Type} (P : Prop) (a1 a2 : Classical A) : Classical A.
  refine (exist _ (fun a => (P /\ proj1_sig a1 a) \/ ((not P) /\ proj1_sig a2 a)) _).
 *)

(*
Theorem PifDef1 : forall (A : Type) P (a1 a2 : A), P -> Pif P a1 a2 = Preturn a1.
Proof.
  intros.
  apply classicalEq.
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
  apply classicalEq.
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
*)
(* We do need partiality for general recursion. Will this work? *)
Definition Partial (T : Type) : Type := Classical (option T).
  
Inductive Prog (A B : Type) : Type :=
| Ret : Partial B -> Prog A B
| Rec : A -> (B -> Prog A B) -> Prog A B (* TODO: The input should be Partial A instead of just A *)
.

(*TODO : could this inductive have just a B parameter instead of Partial B? *)
Inductive runProgR {A B : Type} (def : A -> Partial (Prog A B)) : Prog A B -> Partial B -> Prop :=
| retR : forall b, runProgR def (Ret _ _ b) b
| recR : forall a b res rest defa,
    def a = Preturn (Some defa)
    -> runProgR def defa (Preturn (Some b))
    -> runProgR def (rest b) res
    -> runProgR def (Rec _ _ a rest) res
.

Theorem runProgFunction {A B : Type} {def : A -> Partial (Prog A B)} {p : Prog A B} {b1 b2 : Partial B}
  (rp1 : runProgR def p b1) (rp2 : runProgR def p b2) : b1 = b2.
Proof.
  intros.
  generalize rp2.
  generalize b2.
  clear rp2.
  clear b2.
  induction rp1.
  - intros.
    inversion rp2.
    subst.
    reflexivity.
  - intros.
    inversion rp2.
    subst.
    apply IHrp1_2.
    rewrite H in H2.
    apply PreturnInj in H2.
    subst.
    inversion H2.
    subst.
    specialize (IHrp1_1 _ H3).
    apply PreturnInj in IHrp1_1.
    subst.
    inversion IHrp1_1.
    subst.
    assumption.
Qed.

Definition runProgImpl {A B : Type} (def : A -> Partial (Prog A B)) (p : Prog A B) : Partial B.
  refine (exist _ (fun b => runProgR def p (Preturn b)) _).
  split.
  - intros.
    assert (eq := runProgFunction H H0).
    apply PreturnInj.
    assumption.
  - intros none.
    
Defined.

Definition runProg {A B : Type} (def : A -> Partial (Prog A B)) (a : A) : Partial B :=
  Pbind (def a) (fun a' => 
                   runProgImpl def a').

Theorem runProgDefinitionRet {A B : Type} (def : A -> Partial (Prog A B)) (b : Partial B)
  : runProgImpl def (Ret _ _ b) = b.
Proof.
  destruct b.
  apply partialEq.
  apply functional_extensionality.
  intros b.
  apply propositional_extensionality.
  split.
  - intros.
    inversion H.
    reflexivity.
  - intros.
    assert (exist _ x e = Preturn b). {
      apply itIsReturn.
      assumption.
    }
    rewrite H0.
    apply retR.
    (* TODO: would this proof be simpler with definition proof irrelevance? *)
Qed.

Theorem runProgDefinitionRec {A B : Type} {def : A -> Partial (Prog A B)} {a : A} {rest : B -> Prog A B}
  : runProgImpl def (Rec _ _ a rest) =
      Pbind (def a) (fun a' =>
      Pbind (runProgImpl def a') (fun b =>
          runProgImpl def (rest b))).
Proof.
  apply partialEq.
  apply functional_extensionality.
  intros b.
  apply propositional_extensionality.
  split.
  - intros.
    inversion H.
    subst.
    exists defa.
    split.
    rewrite H2.
    reflexivity.
    exists b0.
    split.
    apply H3.
    apply H5.
  - intros.
    destruct H.
    destruct H.
    destruct H0.
    destruct H0.

    Check recR.
    assert (def a = Preturn x). {
      induction (def a).
      apply itIsReturn.
      simpl in H.
      assumption.
    }
    eapply (@recR _ _ _ _ _ _ _ x H2).
    simpl in H0, H1.
    apply H0.
    apply H1.
Qed.
 
