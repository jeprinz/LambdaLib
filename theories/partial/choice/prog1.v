Require Import Classical.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import choiceBase.

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




(*
As an example to test recursion with infinite recursive calls per call,
take the function
f : nat * nat -> Prop
f (0, _) = True
f (S n, _) = not (forall m, f (n, m))

The goal is to see if I can automate the running of this function.
The output should not just be True or False, but should be a proposition expression built out
of the recurrence.
 *)

Definition fImpl : nat * nat -> Prog (nat * nat) Prop :=
  fun nm => match nm with
            | (O, _) => Ret _ _ (Some True)
            | (S n, m) => Rec _ _
                                         (fun nm => fst nm = n)
                                         (fun rec => Ret _ _ (Some
                                 (not (forall m, rec (n, m) eq_refl))))
            end.

Definition exampleInfFun : nat * nat -> option Prop.
  refine (runProg fImpl).
Defined.

(* Now to try to run the function: *)
Theorem runExampleFun : exampleInfFun (1, 5) = Some False.
  unfold exampleInfFun, runProg.
  simpl.
  rewrite runProgDefinitionRec.

  assert ((fun (a : nat * nat) (_ : fst a = 0) => runProg fImpl a) = fun _ _ => Some True). {
    extensionality nm.
    extensionality p.
    destruct nm as [n m].
    simpl in p.
    subst.
    unfold runProg.
    simpl.
    rewrite runProgDefinitionRet.
    reflexivity.
  }
  rewrite H.
  rewrite collectOption2Def.
  simpl.
  rewrite runProgDefinitionRet.
  assert ((~ (nat -> True)) = False). {
    apply propositional_extensionality.
    split.
    - intros.
      apply H0.
      auto.
    - intros.
      exfalso.
      assumption.
  }
  rewrite H0.
  reflexivity.
Qed.
