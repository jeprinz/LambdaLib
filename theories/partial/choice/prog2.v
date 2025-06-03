Require Import Classical.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import choiceBase.

(*
prog1.v worked fine, but it required some manual tactics to get the recursive case to go though.
I'll try a different version here.
*)
Inductive Prog (A B : Type) : Type :=
| Ret : option B -> Prog A B
| Rec : forall (I : Type) (args : I -> A), ((I -> B) -> Prog A B) -> Prog A B
.

Inductive runProgR {A B : Type} (def : A -> Prog A B) : Prog A B -> B -> Prop :=
| retR : forall b, runProgR def (Ret _ _ (Some b)) b
| recR : forall I
                (args : I -> A)
                (recVals : I -> B)
                (res : B)
                (rest : (I -> B) -> Prog A B),
    (* if for all inputs a satisfying P, recVals describes the recursive calls *)
    (forall (i : I), runProgR def (def (args i)) (recVals i))
    (* and given the results of those recursive calls, the program outputs res *)
    -> runProgR def (rest recVals) res
    (* then overall res *)
    -> runProgR def (Rec _ _ I args rest) res
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
    apply exist_inj2_uip in H2.
    subst.
    apply IHrp1.
    assert (rest1 = rest). {
      apply exist_inj2_uip in H4.
      assumption.
    }
    subst.
    assert (recVals = recVals0). {
      extensionality i.
      specialize (H i).
      specialize (H5 i).
      apply H0.
      apply H5.
    }
    subst.
    assumption.
Qed.

Definition runProgImpl {A B : Type} (def : A -> Prog A B) (p : Prog A B) : option B.
  refine (chooseOption B (fun b => runProgR def p b)).
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
Qed.
     
Theorem runProgDefinitionRec2 {A B : Type} {def : A -> Prog A B}
        {I : Type}
        {args : I -> A}
        {rest : (I -> B) -> Prog A B}
        {recVals : I -> B}
        (recValsCorrect : forall (i : I), runProg def (args i) = Some (recVals i))
  : runProgImpl def (Rec _ _ I args rest) = runProgImpl def (rest recVals).
 Proof.
   unfold runProg, runProgImpl, chooseOption in *.
   repeat apply choiceInd.
   intros.
   assert (forall (i :  I), runProgR def (def (args i)) (recVals i)). {
     intros.
     specialize (recValsCorrect i).
     symmetry in recValsCorrect.
     Check choiceIndHyp.
     apply choiceIndHyp in recValsCorrect.
     assumption.
   }
   clear recValsCorrect.
   (*H1 could have just been the input to runProgDefinitionRec2*)
   destruct t0.
   - inversion H0; clear H0.
     apply exist_inj2_uip in H3, H5.
     subst.
     assert (recVals = recVals0). {
       extensionality i.
       exact (runProgFunction (H1 i) (H6 i)).
     }
     subst.
     destruct t.
     + rewrite (runProgFunction H7 H).
       reflexivity.
     + exfalso.
       apply H.
       exists b.
       apply H7.
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
        {I : Type}
        {args : I -> A}
        {rest : (I -> B) -> Prog A B}
  : runProgImpl def (Rec _ _ I args rest) =
      bind ((collectOption (fun i => runProg def (args i))) : option (I -> B))
           (fun f => runProgImpl def (rest f)).
Proof.
  repeat unfold runProgImpl, runProg, collectOption, chooseOption.
  repeat apply choiceInd.
  intros.
  destruct t.
  -
    assert (forall i, runProgR def (def (args i)) (b i)). {
      intros.
      specialize (H i).
      apply choiceIndHyp in H.
      assumption.
    }
    clear H.
    simpl.
    apply choiceInd.
    intros.
    destruct t0.
    inversion H0; clear H0; subst.
    + apply exist_inj2_uip in H3, H5.
      subst.
      assert (b = recVals). {
        extensionality i.
        exact (runProgFunction (H1 i) (H6 i)).
      }
      subst.
      destruct t.
      * rewrite (runProgFunction H H7).
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
      apply exist_inj2_uip in H2, H4.
      subst.
      exists recVals.
      intros.
      apply choiceInd.
      intros.
      destruct t.
      * specialize (H5 a).
        rewrite (runProgFunction H5 H1).
        reflexivity.
      * exfalso.
        apply H.
        exists recVals.
        intros.
        apply choiceInd.
        intros.
        destruct t.
        -- rewrite (runProgFunction (H5 a0) H2).
           reflexivity.
        -- exfalso.
           apply H1.
           exists (recVals a).
           apply H5.
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
Check Rec.

Definition fImpl : nat * nat -> Prog (nat * nat) Prop :=
  fun nm => match nm with
            | (O, _) => Ret _ _ (Some True)
            | (S n, m) => Rec _ _ _
                                  (fun (i : nat) => (n, i))
                                         (fun rec => Ret _ _ (Some
                                 (not (forall m, rec m))))
            end.

Definition exampleInfFun : nat * nat -> option Prop.
  refine (runProg fImpl).
Defined.

(* Now to try to run the function: *)
Theorem runExampleFun : exampleInfFun (1, 5) = Some False.

  repeat (try unfold exampleInfFun, runProg;
          try rewrite runProgDefinitionRet;
          try rewrite runProgDefinitionRec;
          try rewrite collectOptionDef;
          simpl).

  assert ((~ (nat -> True)) = False). {
    apply propositional_extensionality.
    split.
    - intros.
      apply H.
      auto.
    - intros.
      exfalso.
      assumption.
  }
  rewrite H.
  reflexivity.
Qed.
