Require Import Coq.Logic.ProofIrrelevance.
(* Instead of using SProp, for now I'll just use the proof irrelevance axiom.
   I'll see if this causes any issues; probably not. *)
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Check sig.
Check {x : nat | x = 2}.
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

Inductive Prog (A B : Type) : Type :=
| Ret : Partial B -> Prog A B
| Rec : A -> (B -> Prog A B) -> Prog A B
.

Inductive runProgR {A B : Type} (def : A -> Prog A B) : Prog A B -> Partial B -> Prop :=
| retR : forall b, runProgR def (Ret _ _ b) b
| recR : forall a b res rest,
    runProgR def (def a) (Preturn b)
    -> runProgR def (rest b) res
    -> runProgR def (Rec _ _ a rest) res
.

Theorem runProgFunction {A B : Type} {def : A -> Prog A B} {p : Prog A B} {b1 b2 : Partial B}
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
    specialize (IHrp1_1 _ H1).
    apply PreturnInj in IHrp1_1.
    subst.
    assumption.
Qed.

Definition runProgImpl {A B : Type} (def : A -> Prog A B) (p : Prog A B) : Partial B.
  refine (exist _ (fun b => runProgR def p (Preturn b)) _).
  intros.
  assert (eq := runProgFunction H H0).
  apply PreturnInj.
  assumption.
Defined.

Definition runProg {A B : Type} (def : A -> Prog A B) (a : A) : Partial B :=
  runProgImpl def (def a).

Theorem runProgDefinitionRet {A B : Type} (def : A -> Prog A B) (b : Partial B)
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

Theorem runProgDefinitionRec {A B : Type} {def : A -> Prog A B} {a : A} {rest : B -> Prog A B}
  : runProgImpl def (Rec _ _ a rest) =
      Pbind (runProgImpl def (def a)) (fun b =>
          runProgImpl def (rest b)).
Proof.
  apply partialEq.
  apply functional_extensionality.
  intros b.
  apply propositional_extensionality.
  split.
  - intros.
    inversion H.
    subst.
    exists b0.
    split.
    apply H2.
    apply H4.
  - intros.
    destruct H.
    destruct H.
    apply (@recR _ _ _ _ x).
    assumption.
    assumption.
Qed.

Definition facProg : nat -> Prog nat nat :=
  fun n => match n with
           | O => Ret _ _ (Preturn 1)
           | S n' => Rec _ _ n' (fun x => Ret _ _ (Preturn (n * x)))
           end.

Definition factorial : nat -> Partial nat :=
  runProg facProg.

Theorem factorialTest : factorial 1 = Preturn 1.
Proof.
  unfold factorial, runProg.
  unfold facProg at 2.
  rewrite runProgDefinitionRec.
  assert ((fun b : nat => runProgImpl facProg (Ret nat nat (Preturn (1 * b))))
          = fun b => Preturn (1 * b)). {
    apply functional_extensionality.
    intros.
    rewrite runProgDefinitionRet.
    reflexivity.
  }
  rewrite H.
  clear H.
  unfold facProg at 2.
  rewrite runProgDefinitionRet.
  rewrite bindDef2.
  simpl.
  reflexivity.
Qed.

Theorem factorialTest' : factorial 1 = Preturn 1.
Proof.
  unfold factorial, runProg.
  unfold facProg at 2.
  rewrite runProgDefinitionRec.
  unfold facProg at 2.
  rewrite runProgDefinitionRet.
  rewrite bindDef2.
  rewrite runProgDefinitionRet.
  reflexivity.
Qed.

Theorem factorialTest3 : factorial 6 = Preturn 720.
Proof.
  unfold factorial, runProg.
  unfold facProg, runProg.
  repeat rewrite ?runProgDefinitionRet, ?runProgDefinitionRec, ?bindDef2.
  simpl.
  reflexivity.
Qed.
(* Turns out I was being silly below, I don't need funext if I just evaluate in the correct order. *)

(*
The issue: although this all works, we need to rewrite under "fun b => ..." binders.
This requires function extensionality.
I have no problem using this axiom, but the rewrite tactic doesn't use it automatically!!
This means that I can't automate the running of these function, at least not obviously.

SEE: https://rocq-prover.org/doc/v8.12/refman/addendum/generalized-rewriting.html
There is something about rewriting under binders in there!
Also see: https://discourse.rocq-prover.org/t/how-to-utilize-extensionality-when-rewriting/1065/3
I'll try the code from that forum

Also, look at https://rocq-prover.org/doc/V8.11.0/refman/changes.html
"New tactic under to rewrite under binders, given an extensionality lemma"
*)

(*The next few definitions are adapted from the above forum post*)
From Coq Require Import Setoid Morphisms.

Instance proper_all T : Proper (pointwise_relation T eq ==> eq) (all (A := T)).
Proof.
  intros x y Heq.
  unfold all.
  apply propositional_extensionality.
  split.
  intros.
  rewrite <- Heq.
  apply H.
  intros.
  rewrite Heq.
  apply H.
Qed.
Instance propext_subrel : subrelation iff eq.
Proof. intros A B Hequiv. apply propositional_extensionality, Hequiv. Qed.


Lemma forall_ext_prop_test {T : Type} {A B : T -> Prop} :
  (forall x: T, A x <-> B x) ->
  (forall x: T, A x) = forall x: T, B x.
Proof.
  intros Heq.
  setoid_rewrite Heq.
  easy.
Qed.

Definition function (A B : Type) (f : A -> B) : A -> B := f.
Check respectful.
Instance proper_test A B : Proper (pointwise_relation A eq ==> eq) (function A B).
Proof.
  intros f g H.
  unfold pointwise_relation in H.
  extensionality x.
  apply H.
Qed.

(* So that makes it work with forall, but what about fun? *)


(*Instance proper_test2 A B : Proper (pointwise_relation A eq ==>
    pointwise_relation B eq ==> Basics.flip Basics.impl) 1.*)

From Coq Require Import ssreflect.

Lemma test_rewrite_under_fun_1
      (f : nat -> nat)
      (eq : forall x, f (x + 2) = f (x + 1))
  : (fun x => f (x + 2)) = (fun x => f (x + 1)).
Proof.
  under functional_extensionality do rewrite eq.
  Fail setoid_rewrite eq.
  replace x@(fun x => ?t) with (fun x => t).
  assert (function _ _ (fun x : nat => f (x + 2)) = function _ _ (fun x : nat => f (x + 1))).
  setoid_rewrite eq.
  reflexivity.
  apply H.
Qed.
(*so it seems that this works, but only if I write this stupid "function" thing
in front of my functions. How about a version specific to Pbind? *)
Check @Pbind.
Instance proper_bind A B a : Proper (pointwise_relation A eq ==> eq) (@Pbind A B a).
Proof.
  intros f g H.
  unfold pointwise_relation in H.
  apply functional_extensionality in H.
  rewrite H.
  reflexivity.
Qed.
  
Theorem factorialTest' : factorial 1 = Preturn 1.
Proof.
  unfold factorial, runProg.
  unfold facProg at 2.
  rewrite runProgDefinitionRec.
  Fail setoid_rewrite runProgDefinitionRet.
  assert ((fun b : nat => runProgImpl facProg (Ret nat nat (Preturn (1 * b))))
          = function _ _ ((fun b : nat => runProgImpl facProg (Ret nat nat (Preturn (1 * b)))))).
  reflexivity.
  rewrite H.
  setoid_rewrite runProgDefinitionRet.
  rewrite bindDef2.
  unfold function.
  simpl.
  reflexivity.
Qed.
  
(*
ANOTHER IDEA:
 *)



Check runProgDefinitionRet.
Theorem runProgDefinitionRet2 {A B : Type} (def : A -> Prog A B) (b : Partial B)
  : runProgImpl = fun def
