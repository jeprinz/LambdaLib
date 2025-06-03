Require Import Coq.Logic.ProofIrrelevance.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import partialBase.


Inductive Prog (A B : Type) : Type :=
| Ret3 : Partial B -> Prog A B
| Rec3 : forall (P : A -> Prop), ((forall a, P a -> B) -> Prog A B) -> Prog A B
(* Unfortunately, the following won't work. It is necessary to be able to know the set of elements of A
on which recursive calls are made. *)
(*| Rec3' : ((A -> B) -> Prog3 A B) -> Prog3 A B*)
.

(*
I doubt that this will work.
How will I get recVals for recursive calls?
The function may not even be computable.
I could replace recVals with a relation or something, but the issue is the type of "rest".
*)
Inductive runProgR {A B : Type} (def : A -> Partial (Prog A B)) : Prog A B -> B -> Prop :=
| retR3 : forall b, runProgR def (Ret3 _ _ (Preturn b)) b
| recR3 : forall P (recVals : forall a, P a -> B)
                 (res : B) (rest : (forall a, P a -> B) -> Prog A B),
    (* if for all inputs a satisfying P, recVals describes the recursive calls *)
    (forall a (pa : P a), exists prog,
       def a = Preturn prog /\ runProgR def prog (recVals a pa))
    (* and given the results of those recursive calls, the program outputs res *)
    -> runProgR def (rest recVals) res
    (* then overall res *)
    -> runProgR def (Rec3 _ _ P rest) res
.

Theorem runProgFunction {A B : Type} {def : A -> Partial (Prog A B)} {p : Prog A B} {b1 b2 : B}
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
    apply (f_equal (fun f => f b)) in H0.
    rewrite H0.
    reflexivity.
  - (* problem: why is there only 1 IH? There should be 1 for each of the recursive calls. *)
    intros.
    inversion rp2.
    subst.
    apply IHrp1.
    assert (rest1 = rest). {
      apply exist_inj2_uip in H1.
      assumption.
    }
    subst.
    assert (recVals = recVals0). {
      extensionality a.
      extensionality pa.
      specialize (H a pa).
      specialize (H2 a pa).
      apply H1.
      apply H5.
    }
    subst.
    assumption.
Qed.

Definition runProgImpl3 {A B : Type} (def : A -> Partial (Prog3 A B)) (p : Prog3 A B) : Partial B.
  refine (exist _ (fun b => runProg3R def p b) _).
  intros.
  assert (eq := runProgFunction3 H H0).
  assumption.
Defined.

Definition runProg3 {A B : Type} (def : A -> Partial (Prog3 A B)) (a : A) : Partial B :=
  Pbind (def a) (fun a' => 
                   runProgImpl3 def a').

Theorem runProgDefinitionRet3 {A B : Type} (def : A -> Partial (Prog3 A B)) (b : Partial B)
  : runProgImpl3 def (Ret3 _ _ b) = b.
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
    apply retR3.
    (* TODO: would this proof be simpler with definition proof irrelevance? *)
Qed.

Theorem runProgDefinitionRec3 {A B : Type} {def : A -> Partial (Prog3 A B)}
        {P : A -> Prop}
        {rest : (forall a, P a -> B) -> Prog3 A B}
        {recVals : forall a, P a -> B}
        {defVals : forall a, P a -> Prog3 A B}
        (defValsCorrect : forall a (pa : P a), def a = Preturn (defVals a pa))
        (recValsCorrect : forall a (pa : P a), runProg3 def a = Preturn (recVals a pa))
  : runProgImpl3 def (Rec3 _ _ P rest) = runProgImpl3 def (rest recVals).
Proof.
  apply partialEq.
  extensionality b.
  apply propositional_extensionality.
  split.
  - intros.
    inversion H.
    subst.
    apply exist_inj2_uip in H1.
    subst.
    assert (recVals = recVals0). {
      extensionality a.
      extensionality pa.
      specialize (recValsCorrect a pa).
      unfold runProg3 in recValsCorrect.
      specialize (H2 a pa).
      rewrite H2 in recValsCorrect.
      rewrite bindDef2 in recValsCorrect.
      apply returnIsIt in recValsCorrect.
      specialize (H3 a pa).
      assert (eq := runProgFunction3 recValsCorrect H3).
      assumption.
    }
    subst.
    assumption.
  - intros.
    Check @recR3.
    Check (@recR3 _ _  def P recVals).
    apply recR3 with (recVals := recVals) (defa := defVals).
    assumption.
    intros.
    specialize (recValsCorrect a pa).
    specialize (defValsCorrect a pa).
    unfold runProg3 in recValsCorrect.
    rewrite defValsCorrect in recValsCorrect.
    rewrite bindDef2 in recValsCorrect.
    apply returnIsIt in recValsCorrect.
    assumption.
    assumption.
Qed.
