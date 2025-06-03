Require Import Classical.
Require Import FunctionalExtensionality.

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

Theorem PifDef2 : forall (A : Type) P (a1 a2 : A), ~P -> Pif P a1 a2 = a2.
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

(* Is this really not in the standard library? *)
Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
  match a with
  | Some a' => f a'
  | None => None
  end.

Inductive Prog (A B : Type) : Type :=
| Ret : option B -> Prog A B
| Rec : forall (P : A -> Prop), ((forall a, P a -> B) -> Prog A B) -> Prog A B
.

Inductive runProgR {A B : Type} (def : A -> Prog A B) : Prog A B -> B -> Prop :=
| retR : forall b, runProgR def (Ret _ _ (Some b)) b
| recR : forall P (recVals : forall a, P a -> B)
                 (res : B) (rest : (forall a, P a -> B) -> Prog A B),
    (* if for all inputs a satisfying P, recVals describes the recursive calls *)
    (forall a (pa : P a), runProgR def (def a) (recVals a pa))
    (* and given the results of those recursive calls, the program outputs res *)
    -> runProgR def (rest recVals) res
    (* then overall res *)
    -> runProgR def (Rec _ _ P rest) res
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
    reflexivity.
  - intros.
    inversion rp2.
    subst.
    apply IHrp1.
    assert (rest1 = rest). {
      apply exist_inj2_uip in H2.
      assumption.
    }
    subst.
    assert (recVals = recVals0). {
      extensionality a.
      extensionality pa.
      specialize (H a pa).
      specialize (H3 a pa).
      apply H0.
      apply H3.
    }
    subst.
    assumption.
Qed.

Definition runProgImpl {A B : Type} (def : A -> Prog A B) (p : Prog A B) : option B.
  refine (chooseOption B (fun b => runProgR def p b)).
  (*
  refine (choose (option B) (fun ob =>
                               (exists b, runProgR def p b /\ ob = Some b)
                               \/
                                 (ob = None /\ ~exists b, runProgR def p b))).
  destruct (classic (exists b, runProgR def p b)).
  - destruct H.
    exists (Some x).
    apply or_introl.
    eauto.
  - exists None.
    apply or_intror.
    eauto.
   *)
Defined.

Definition runProg {A B : Type} (def : A -> Prog A B) (a : A) : option B :=
  (runProgImpl def (def a)).

Theorem runProgDefinitionRet {A B : Type} (def : A -> Prog A B) (b : B)
  : runProgImpl def (Ret _ _ (Some b)) = Some b.
  unfold runProgImpl, chooseOption.
  apply choiceInd.
  intros.
  destruct t.
  - inversion H.
    subst.
    reflexivity.
  - exfalso.
    apply H.
    exists b.
    constructor.
  (*
  intros.
  unfold runProgImpl.
  apply choiceInd.
  intros.
  destruct H.
  - destruct H as [b0 [H1 H2]].
    inversion H1.
    subst.
    reflexivity.
  - destruct H.
    exfalso.
    apply H0.
    exists b.
    constructor.
   *)
Qed.
Check collectOption.




(* lemma:
x = choose P -> P x
*)



     
 Theorem runProgDefinitionRec2 {A B : Type} {def : A -> Prog A B}
        {P : A -> Prop}
        {rest : (forall a, P a -> B) -> Prog A B}
        {recVals : forall a, P a -> B}
        (recValsCorrect : forall a (pa : P a), runProg def a = Some (recVals a pa))
  : runProgImpl def (Rec _ _ P rest) = runProgImpl def (rest recVals).
 Proof.
   unfold runProg, runProgImpl, chooseOption in *.
   repeat apply choiceInd.
   intros.
   assert (forall a (pa : P a), runProgR def (def a) (recVals a pa)). {
     intros.
     specialize (recValsCorrect a pa).
     symmetry in recValsCorrect.
     Check choiceIndHyp.
     apply choiceIndHyp in recValsCorrect.
     assumption.
   }
   clear recValsCorrect.
   (*H1 could have just been the input to runProgDefinitionRec2*)
   destruct t0.
   - inversion H0; clear H0.
     apply exist_inj2_uip in H3.
     subst.
     assert (recVals = recVals0). {
       extensionality a.
       extensionality pa.
       exact (runProgFunction (H1 a pa) (H4 a pa)).
     }
     subst.
     destruct t.
     + rewrite (runProgFunction H6 H).
       reflexivity.
     + exfalso.
       apply H.
       exists b.
       apply H6.
   - destruct t.
     + exfalso.
       apply H0.
       exists b.
       econstructor.
       * apply H1.
       * assumption.
     + reflexivity.
 Qed.
 
Theorem runProgDefinitionRec {A B : Type} {def : A -> Prog A B}
        {P : A -> Prop}
        {rest : (forall a, P a -> B) -> Prog A B}
  : runProgImpl def (Rec _ _ P rest) =
      bind ((collectOption2 (fun a pa => runProg def a)) : option (forall a, P a -> B))
           (fun f => runProgImpl def (rest f)).
Proof.
  repeat unfold runProgImpl, runProg, collectOption2, chooseOption.
  repeat apply choiceInd.
  intros.
  destruct t.
  - 
    assert (forall a (pa : P a), runProgR def (def a) (b a pa)). {
      intros.
      specialize (H a pa).
      apply choiceIndHyp in H.
      assumption.
    }
    clear H.
    simpl.
    apply choiceInd.
    intros.
    destruct t0.
    inversion H0; clear H0; subst.
    + apply exist_inj2_uip in H3.
      subst.
      assert (b = recVals). {
        extensionality a.
        extensionality pa.
        exact (runProgFunction (H1 a pa) (H4 a pa)).
      }
      subst.
      destruct t.
      * rewrite (runProgFunction H H6).
        reflexivity.
      * exfalso.
        apply H.
        exists b0.
        assumption.
    + destruct t.
      * exfalso.
        apply H0.
        exists b0.
        econstructor.
        apply H1.
        apply H.
      * reflexivity.
  - simpl.
    destruct t0.
    + exfalso.
      inversion H0.
      apply H.
      apply exist_inj2_uip in H2.
      subst.
      exists recVals.
      intros.
      apply choiceInd.
      intros.
      destruct t.
      * specialize (H3 a b0).
        rewrite (runProgFunction H3 H1).
        reflexivity.
      * exfalso.
        apply H.
        exists recVals.
        intros.
        apply choiceInd.
        intros.
        destruct t.
        -- rewrite (runProgFunction (H3 a0 b1) H2).
           reflexivity.
        -- exfalso.
           apply H1.
           exists (recVals a b0).
           apply H3.
    + reflexivity.
Qed.    
