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

Theorem factorialTest1 : factorial 1 = Preturn 1.
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
  unfold factorial, runProg, facProg.
  repeat rewrite ?runProgDefinitionRet, ?runProgDefinitionRec, ?bindDef2.
  simpl.
  reflexivity.
Qed.

(*
A construct that is Pif but with a unique choice of a value
*)

Check Pif.

Definition uniqueToPartial {T : Type} (P : T -> Prop) (u : exists t, unique P t) : Partial T.
  refine (exist _ P _).
  intros.
  destruct u.
  destruct H1.
  assert (H3 := H2 _ H).
  assert (H4 := H2 _ H0).
  subst.
  reflexivity.
Defined.

Theorem uniqueToSame {T : Type} (P : T -> Prop) (u : exists t, unique P t) :
  forall t1 t2, P t1 -> P t2 -> t1 = t2.
Proof.
  intros.
  destruct u.
  destruct H1.
  assert (u1 := H2 _ H).
  assert (u2 := H2 _ H0).
  subst.
  reflexivity.
Qed.
  
Definition Pmatch {T A : Type} (P : T -> Prop)
           (branch1 : T -> Partial A) (branch2 : Partial A) : Partial A.
  refine (exist _ (fun a =>
                     (exists t, unique P t /\ proj1_sig (branch1 t) a)
                     \/
                       (not (exists t, unique P t) /\ proj1_sig branch2 a))
                _).
  intros.
  destruct H.
  destruct H.
  destruct H.
  destruct H0.
  destruct H0.
  destruct H0.
  destruct H.
  destruct H0.
  specialize (H3 _ H0).
  subst.
  apply (proj2_sig (branch1 x1) _ _ H1 H2).

  destruct H0.
  exfalso.
  apply H0.
  eexists.
  apply H.

  destruct H0.
  destruct H.
  destruct H0.
  destruct H0.
  exfalso.
  apply H.
  eexists.
  apply H0.

  destruct H.
  destruct H0.
  apply (proj2_sig branch2 _ _ H1 H2).
Defined.

Check PifDef1.
Theorem PmatchDef1 {T A : Type} (P : T -> Prop)
        (branch1 : T -> Partial A) (branch2 : Partial A)
        (u : exists t, unique P t)
(*  : Pmatch P branch1 branch2 = Pbind (uniqueToPartial P u) (fun t => branch1 t).*)
  : Pmatch P branch1 branch2 = Pbind (exist _ P (uniqueToSame P u)) (fun t => branch1 t).
Proof.
  apply partialEq.
  extensionality a.
  apply propositional_extensionality.
  split.
  - intros.
    destruct H.
    + destruct H.
      destruct H.
      simpl.
      destruct H.
      eexists.
      split.
      apply H.
      apply H0.
    + destruct H.
      contradiction.
  - intros.
    destruct H.
    destruct H.
    apply or_introl.
    destruct u.
    eexists.
    split.
    apply u.
    simpl in H.
    destruct u.
    specialize (H2 _ H).
    subst.
    assumption.
Qed.

Theorem PmatchDef2 {T A : Type} (P : T -> Prop)
        (branch1 : T -> Partial A) (branch2 : Partial A)
        (ne : not (exists t, unique P t))
  : Pmatch P branch1 branch2 = branch2.
Proof.
  destruct branch2.
  apply partialEq.
  simpl.
  extensionality a.
  apply propositional_extensionality.
  split.
  - intros.
    destruct H.
    destruct H.
    destruct H.
    exfalso.
    apply ne.
    eexists.
    apply H.
    destruct H.
    assumption.
  - intros.
    apply or_intror.
    split.
    assumption.
    assumption.
Qed.


(*
While the above idea works, I think there might be a better way to think of it as composed
of other things.
I could define a unique choice principle, saying that
partialOfUnique : (exists unique x, P x) -> Partial _

And then
forall t, P t -> partialOfUnique P _ = return t
*)

Definition summon {T : Type} (P : T -> Prop) (u : forall t1 t2, P t1 -> P t2 -> t1 = t2) : Partial T.
  refine (exist _ P u).
Defined.

(* This is just the "isItReturn" above *)
Theorem substantiate {T : Type} (P : T -> Prop) (t : T) (H : P t)
        (u : forall t1 t2, P t1 -> P t2 -> t1 = t2)
  : summon P u = Preturn t.
Proof.
  apply partialEq.
  extensionality y.
  apply propositional_extensionality.
  split.
  - intros.
    specialize (u _ _ H H0).
    subst.
    reflexivity.
  - intros.
    subst.
    assumption.
Qed.

(* Can I define Pmatch in terms of Pif and summon?
 I need Pif to take Partials for the branches instead of just As.
 I also need the branches to be (P -> Parital A) and (not P -> Partial A)
 so they can use the knowledge of the proposition in their definitions. *)
(*Definition Pmatch2 {T A : Type} (P : T -> Prop)
           (branch1 : T -> Partial A) (branch2 : Partial A) : Partial A.
  refine (Pif (exists t, unique P t) (Pbind (summon P )) branch2).*)

(* Example of using Pmatch: map [0, x] to x and otherwise 0 *)

Require Import List.
Import ListNotations.
Check [ 1 ; 2 ].
Definition functionUsingMatch : list nat -> Partial nat
  := (fun l => Pmatch (fun y => l = [0 ; y]) (fun y => Preturn y) (Preturn 0)).

Theorem testFunctionUsingMatch1 :
  functionUsingMatch [0 ; 5] = Preturn 5.
  unfold functionUsingMatch.
  Check PmatchDef1.
  erewrite PmatchDef1.
  Unshelve.
  erewrite itIsReturn.
  Unshelve.
  rewrite bindDef2.
  reflexivity.
  reflexivity.
  exists 5.
  split.
  reflexivity.
  intros.
  inversion H.
  reflexivity.
Qed.

Theorem testFunctionUsingMatch2 :
  functionUsingMatch [1 ; 5] = Preturn 0.
  unfold functionUsingMatch.
  erewrite PmatchDef2.
  reflexivity.
  intros H.
  destruct H.
  destruct H.
  inversion H.
Qed.

(* So this works on some level. But how can this be automated usefully? 
   Also, it seems like the statement that the predicate in Pmatch matches at most one thing
   should be an input to Pmatch itself. It seems wrong to have the "else" case trigger if there is
   more than one match, which is the current setup.
   Also, this would make the defining equations simpler, which would probably make automation simpler.
*)
