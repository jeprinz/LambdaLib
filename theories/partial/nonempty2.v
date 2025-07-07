Require Import Stdlib.Logic.ProofIrrelevance.
(* Instead of using SProp, for now I'll just use the proof irrelevance axiom.
   I'll see if this causes any issues; probably not. *)
From Stdlib Require Import FunctionalExtensionality.
Require Import Stdlib.Logic.PropExtensionality.

(*
My idea is to have the monad of nonempty sets. Maybe that corresponds to choice, and
maybe it still gets classical stuff?

nonemepty1.v worked OK, but it had sort polymorphism issues.
In this file, I'm going to make an inductive and get sort polymorphism to work
 *)

Polymorphic Definition sort'@{s | u |} (T : Type@{s|u}):= Type@{s|u}.
(*Polymorphic Definition sort@{s ; u} := Type@{s;u}.*)
(* This second syntax is the current version of rocq *)
Check (sort' nat).
Check (sort' True).

Polymorphic Inductive Test@{s | u|} : Type@{s | u}.
Check Test@{Type | Type}.
Check Test@{Prop | Type}.

Polymorphic Definition test2@{s|u|} : Type@{s|u} := Test@{s|u}.
Check test2@{Type|Type}.
Check test2@{Prop|Type}.

Polymorphic Definition test3@{s|u|} := Test@{s|u}.
Check test3@{Type|Type}.
Check test3@{Prop|Type}.
Check exist.
(*
To make this polymorphic properly, I need to use my own inductive definition and not
just use sig.
TODO: Make that in a separate file.
 *)
Inductive Classical_for_example (A : Type) : Prop :=
| classical_ex : forall (S : A -> Prop), not (forall x, not (S x)) -> Classical_for_example A
.

Check (prod nat nat).
Check (prod True True).
Print prod.

Inductive prod2 (A B : Type) : Type :=  pair2 : Prop -> A -> B -> prod2 A B.
Check (prod2 nat nat).
Check (prod2 True True).

Polymorphic Record RClassical@{s|u|} (A : Type@{s|u}) : Type@{s|u} :=
  {
    S : A -> Prop
  }.

Check (RClassical True).

(* TODO: update rocq version, version 9 has different syntax for sort polymorphism *)
Polymorphic Inductive Classical@{s|u|} (A : Type@{s|u}) : (*Type@{s|_}*) :=
| classical : forall (S : A -> Prop), not (forall x, not (S x)) -> Classical A
.

Check Classical.
Check (Classical nat).
Check (Classical True).
(* TODO: Is that the best way to express non-emptyness with a double negation? *)

Definition Preturn {A : Type} (x : A) : Classical A.
  refine (exist _ (fun y => y = x) _).
  intros.
  intros p.
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
  destruct pa as [Sa nonempty].
  simpl.
  intros p.
  apply nonempty.
  intros a Sax.
  remember (f a) as fa.
  destruct fa as [SB nonemptyB].
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

Definition Cmap {A B : Type} (f : A -> B) (c : Classical A) : Classical B
  := Pbind c (fun a => Preturn (f a)).
Theorem CmapDef : forall A B f a, @Cmap A B f (Preturn a) = Preturn (f a).
Proof.
  unfold Cmap.
  intros.
  rewrite bindDef.
  reflexivity.
Qed.

(*
TODO: Would it be better to just use normal bind + return, and then have
a function (Classical Prop -> Prop)?
*)
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
  intros [S unique].
  (* No *)
Abort.

Theorem sortOfThough (P : Prop) : Classical P -> ~~P.
Proof.
  intros.
  intros np.
  destruct X as [S nonempty].
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
  intros nn.
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

Theorem lem2 (P : Prop) : Classical (P + not P).
Proof.
  refine (exist _ (fun pornotp => True) _).
  intros nn.
  assert ((~True) = False). {
    apply propositional_extensionality.
    split; auto.
  }
  rewrite H in nn.
  apply nn.
  + apply inr.
    intros p.
    apply nn.
    apply inl.
    apply p.
Defined.

Definition choose (T : Type) (P : T -> Prop) (H : exists t, P t): Classical T.
  refine (exist _ P _).
  intros p.
  destruct H as [t Pt].
  specialize (p t).
  contradiction.
Defined.

Theorem choice_spec' (T : Type) (P : T -> Prop) (H : exists t, P t)
  : Pbind (choose T P H) (fun t => Preturn (P t)) = Preturn True.
Proof.
  apply classicalEq2.
  simpl.
  extensionality X.
  apply propositional_extensionality.
  split.
  - intros.
    destruct H0.
    destruct H0.
    subst.
    apply propositional_extensionality; split; auto.
  - intros.
    subst.
    destruct H.
    exists x.
    split; auto.
    apply propositional_extensionality; split; auto.
Qed.

Theorem choice_spec (T : Type) (P : T -> Prop) (H : exists t, P t)
  : propBind P (choose T P H).
  apply classicalEq2.
  simpl.
  extensionality X.
  apply propositional_extensionality.
  split.

  - intros.
    subst.
    destruct H.
    exists x.
    split; auto.
    apply propositional_extensionality; split; auto.
  - intros.
    destruct H0.
    destruct H0.
    subst.
    apply propositional_extensionality; split; auto.
Qed.
    
Theorem ind {T : Type} : forall (P : Classical T -> Prop),
    (forall (a : T), P (Preturn a)) -> forall (q : Classical T), (P q).
Proof.
  intros.
  destruct q.
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

(* better name? *)
Definition seqOption (A B : Type) (f : A -> Partial B) : Partial (A -> Classical B).
  refine (exist _ (fun g =>
                     ((exists a, f a = Preturn None) /\ g = None)
                     \/
                       (exists g', g = Some g' /\ forall a, f a = Cmap Some (g' a))) _).
Abort.
(*Maybe a better design would be to put a double negation all the way around the outside of the prop part
of classical? *)


(*
The question is: can I do general recursion somehow?
 *)

(*
I think that my definition of choose needs to actually have the monad around
the inputs as well as the output, so I can use it correctly.
*)
Definition choose2 (T : Type) (P : T -> Prop) (H : Classical (exists t, P t)): Classical T.
  refine (exist _ P _).
  intros p.
  destruct H as [t Pt].
  apply Pt.
  intros.
  destruct x.
  specialize (p x).
  contradiction.
Defined.

Theorem choice_spec2 (T : Type) (P : T -> Prop) (H : exists t, P t)
  : Pbind (choose T P H) (fun t => Preturn (P t)) = Preturn True.
Proof.
  apply classicalEq2.
  simpl.
  extensionality X.
  apply propositional_extensionality.
  split.
  - intros.
    destruct H0.
    destruct H0.
    subst.
    apply propositional_extensionality; split; auto.
  - intros.
    subst.
    destruct H.
    exists x.
    split; auto.
    apply propositional_extensionality; split; auto.
Qed.

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

(* Using choice, returns the element of T satisfying P if it exists, otherwise None *)
Definition chooseOption (T : Type) (P : T -> Prop) : Classical (option T).
  Check choose.
  refine (choose2 (option T)
                 (fun ot => match ot with
                            | Some t => P t
                            | None => ~exists t, P t
                            end) _).
  Check lem.
  apply (Pbind (lem2 (exists t, P t))).
  intros doesOrDoesNot.
  destruct doesOrDoesNot.
  - destruct e.
    exists (Some x).
    assumption.
  -  exists None.
     assumption.
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
 Qed.

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

Theorem runProgDefinitionRet {A B : Type} (def : A -> Prog A B) (b : option B)
  : runProgImpl def (Ret _ _ b) = b.
  unfold runProgImpl, chooseOption.
  apply choiceInd.
  intros.
  destruct t.
  - inversion H.
    subst.
    reflexivity.
  - destruct b.
    + exfalso.
      apply H.
      exists b.
      constructor.
    + reflexivity.
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
