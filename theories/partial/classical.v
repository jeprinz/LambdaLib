Require Import Coq.Logic.ProofIrrelevance.
(* Instead of using SProp, for now I'll just use the proof irrelevance axiom.
   I'll see if this causes any issues; probably not. *)
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Definition Classical (A : Type) : Type :=
  {S : A -> Prop | exists! a, S a}.

Definition Preturn {A : Type} (x : A) : Classical A.
  refine (exist _ (fun y => y = x) _).
  intros.
  exists x.
  split.
  - reflexivity.
  - intros.
    congruence.
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

Theorem itIsReturn :
  forall T (S : T -> Prop) (p : exists! t, S t) (t : T),
    S t -> (exist _ S p) = Preturn t.
Proof.
  intros.
  apply classicalEq.
  apply functional_extensionality.
  intros.
  apply propositional_extensionality.
  split.
  - intros.
    destruct p as [t' [St' unique]].
    assert (e1 := unique _ H).
    assert (e2 := unique _ H0).
    congruence.
  - intros.
    subst.
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
  destruct pa as [Sa [a [Saa Saprop]]].
  simpl.
  remember (f a) as fa.
  destruct fa as [Sfa [fa' [Sfafa Sfaprop]]].
  exists fa'.
  split.
  - exists a.
    split.
    + apply Saa.
    + rewrite <- Heqfa.
      simpl.
      apply Sfafa.
  - intros b [a' [Saa' H]].
    specialize (Saprop _ Saa').
    subst.
    assert (proj1_sig (f a') fa'). {
      rewrite <- Heqfa.
      simpl.
      apply Sfafa.
    }
    
    destruct (proj2_sig (f a')) as [b' [fa'b' b'Unique]].
    rewrite <- (b'Unique _ H0) in *.
    rewrite <- (b'Unique _ H).
    reflexivity.
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

Theorem ind {T : Type} : forall (P : Classical T -> Prop),
    (forall (a : T), P (Preturn a)) -> forall (q : Classical T), (P q).
Proof.
  intros.
  remember q as q'.
  destruct q as [S [a [aInS property]]].
  assert (q' = (Preturn a)). {
    subst.
    apply classicalEq.
    extensionality a'.
    apply propositional_extensionality.
    split.
    - intros.
      symmetry.
      apply property; assumption.
    - intros.
      subst.
      assumption.
  }
  rewrite H0.
  apply H.
Qed.

Definition choice {A B : Type} (R : A -> B -> Prop)
      (Rfunction : forall a, exists! b, R a b)
  : A -> Classical B.
Proof.
  intros a.
  refine (exist _ (fun b => R a b) _).
  specialize (Rfunction a) as [b property].
  exists b.
  assumption.
Defined.

Theorem choiceSpec (A B : Type) (R : A -> B -> Prop)
        (Rfunction : forall a, exists! b, R a b)
  : forall a, propBind (fun b => R a b) (choice R Rfunction a).
Proof.
  intros.
  unfold propBind, choice.
  simpl.
Abort.

Definition choice2 {A B : Type} (f : forall (a : A), exists (b : B), True)
           (contractible : forall (b1 b2 : B), b1 = b2)
  : A -> Classical B.
  intros a.
  refine (exist _ (fun b => True) _).
  specialize (f a).
  destruct f.
  exists x.
  split; auto.
Qed.
Search "hprop".
(* This will be useful *)
Check eq_sigT_hprop_iff.
Search (forall (x y : _), x = y).
(* We do need partiality for general recursion. Will this work? *)
Definition Partial (T : Type) : Type := Classical (option T).
  
Inductive Prog (A B : Type) : Type :=
| Ret : Partial B -> Prog A B
| Rec : A -> (B -> Prog A B) -> Prog A B (* TODO: The input should be Partial A instead of just A *)
.

(* For now I'll keep it a little simpler and not have def output a partial. *)
Inductive runProgR {A B : Type} (def : A -> Prog A B) : Prog A B -> B -> Prop :=
| retR : forall b, runProgR def (Ret _ _ (Preturn (Some b))) b
| recR : forall a b res rest,
    runProgR def (def a) b
    -> runProgR def (rest b) res
    -> runProgR def (Rec _ _ a rest) res
.

Theorem runProgFunction {A B : Type} {def : A -> Prog A B} {p : Prog A B} {b1 b2 : B}
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
    apply (f_equal (fun f => f (Some b))) in H0.
    assert (Some b = Some b2). {
      rewrite H0.
      reflexivity.
    }
    inversion H.
    congruence.
  - intros.
    inversion rp2.
    subst.
    apply IHrp1_2.
    specialize (IHrp1_1 _ H1).
    subst.
    assumption.
Qed.

Require Import Classical.
Check classic.

Definition runProgImpl {A B : Type} (def : A -> Prog A B) (p : Prog A B) : Partial B.
  refine (exist _ (fun b => match b with
                            | Some b' => runProgR def p b'
                            | None => ~ exists b', runProgR def p b'
                            end) _).
  intros.
  destruct (classic (exists b, runProgR def p b)).
  - destruct H as [b rp].
    exists (Some b).
    split.
    + apply rp.
    + intros.
      destruct x'.
      * rewrite (runProgFunction rp H).
        reflexivity.
      * exfalso.
        apply H.
        exists b.
        apply rp.
  - exists None.
    split.
    + apply H.
    + intros.
      destruct x'.
      * exfalso.
        apply H.
        exists b.
        apply H0.
      * reflexivity.
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

  
Lemma lemmaThing (A : Type) (P : A -> Prop) (H : exists a, P a)
  : exists (P' : A -> Prop), exists! a, P' a.
Proof.
  destruct H.
  exists (fun a => a = x).
  exists x.
  split.
  - reflexivity.
  - intros.
    congruence.
Qed.

Lemma doesThisWorkProbablyNot (A : Type) (thing : exists (P : A -> Prop), True) : A -> Prop.
Proof.
  intros.
  

Theorem indefiniteDescription (A : Type) (P : A -> Prop) (H : exists a, P a)
  : Classical { a : A | P a }.
Proof.
  refine (exist _ (fun aPa => (proj1_sig aPa)) _).

Definition Pif {A : Type} (P : Prop) (a1 a2 : Classical A) : Classical A.
  refine (exist _ (fun a => (P /\ proj1_sig a1 a) \/ ((not P) /\ proj1_sig a2 a)) _).
  (* This doesn't seem to be possible.
   But maybe it somehow can work by using Diaconescu's theorem? *)

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
 
