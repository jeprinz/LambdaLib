Require Import Classical.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import choiceBase.

(*
in this file, i'm doing a version that uses a default value so there doesn't need to be
and option monad. i'm hoping this will make things way simpler.
*)
Inductive Prog (A B : Type) : Type :=
| Ret : B -> Prog A B
| Rec : forall (I : Type) (args : I -> A), ((I -> B) -> Prog A B) -> Prog A B
.

Inductive runProgR {A B : Type} (def : A -> Prog A B) : Prog A B -> B -> Prop :=
| retR : forall b, runProgR def (Ret _ _ b) b
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

Definition chooseDefault (T : Type) (P : T -> Prop) (default : T) : T.
  refine (choose T (fun t => P t \/ ((~exists t, P t) /\ t = default))).
  destruct (classic (exists t, P t)).
  - destruct H.
    exists x.
    apply or_introl.
    assumption.
  - exists default.
    apply or_intror.
    easy.
Defined.

Definition runProgImpl {A B : Type} (def : A -> Prog A B) (p : Prog A B) (default : B) : B.
  refine (chooseDefault B (fun b => runProgR def p b) default).
Defined.

Definition runProg {A B : Type} (def : A -> Prog A B) (a : A) (default : B) : B :=
  (runProgImpl def (def a) default).

Theorem runProgDefinitionRet {A B : Type} (def : A -> Prog A B) (b : B) default
  : runProgImpl def (Ret _ _ b) default = b.
  unfold runProgImpl, chooseDefault.
  apply choiceInd.
  intros.
  destruct H.
  - inversion H.
    subst.
    reflexivity.
  - destruct H.
    subst.
    exfalso.
    apply H.
    exists b.
    constructor.
Qed.

(*
can't i simplify things way further here?
do i even need the Prog datatype at all if i have this default concept?

like,

runProg : (default : B) -> ((reccall : A -> B) -> A -> B) -> A -> B

the reason why you can't normally define general recursion by a fixpoint is becuase with

runProg : ((reccall : A -> option B) -> A -> option B) -> A -> option B

there is nothing to stop it from doing something like checking if the recursive call outputs
Some or None, which doesn't make sense for a recursive function.



does this work?

runProg d f a = f (runProg d f)



before any of that, does my original idea for this file even work?

*)

Theorem runProgDefinitionRec {A B : Type} {def : A -> Prog A B}
        {I : Type}
        {args : I -> A}
        {rest : (I -> B) -> Prog A B}
        {default}
  : runProgImpl def (Rec _ _ I args rest) default =
           runProgImpl def (rest (fun i => runProg def (args i) default)) default.
Proof.
  repeat unfold runProgImpl, runProg, chooseDefault.
  repeat apply choiceInd.
  intros.
  destruct H.
  - inversion H.
    
    
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
