Require Import Coq.Logic.ProofIrrelevance.
(* Instead of using SProp, for now I'll just use the proof irrelevance axiom.
   I'll see if this causes any issues; probably not. *)
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Classical.

(*
My idea is to have the monad of nonempty sets. Maybe that corresponds to choice, and
maybe it still gets classical stuff?

In this version of the file, I'm going to just assume LEM
 *)

Definition Classical (A : Type) : Type :=
  {S : A -> Prop | exists a, S a}.

Definition Creturn {A : Type} (x : A) : Classical A.
  refine (exist _ (fun y => y = x) _).
  intros.
  exists x.
  reflexivity.
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

Theorem CreturnInj : forall A (x y : A), Creturn x = Creturn y -> x = y.
Proof.
  intros.
  pose (@f_equal _ _ (@proj1_sig _ _) _ _ H) as fact.
  simpl in fact.
  assert ((fun y => y = x) x). {
    reflexivity.
  }
  rewrite fact in H0.
  assumption.
Qed.

Definition Cbind {A B : Type} (pa : Classical A) (f : A -> Classical B) : Classical B.
  refine (exist _ (fun b => (exists a, proj1_sig pa a /\ proj1_sig (f a) b)) _).
  destruct pa as [Sa nonempty].
  simpl.
  destruct nonempty.
  remember (f x) as fx.
  destruct fx.
  destruct e.
  exists x1.
  exists x.
  split; auto.
  rewrite <- Heqfx.
  simpl.
  assumption.
Defined.

Theorem bindDef : forall A B (a : A) (f : A -> Classical B),
    Cbind (Creturn a) f = f a.
Proof.
  intros.
  apply classicalEq2.
  simpl.
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

(*
I think that in order for this to work, I need all of the equalities to be inside Classical
as well.
But then, can I transport along an equality (Classical (x = y))?
Maybe I can if the thing that I'm transporting is itself in Classical?
In other words,
Ctransport : (P : T -> Classical Type) -> (Classical (x = y)) -> P x -> Classical (P y)

But even if all of that worked, would that really be at all compelling? It kind of makes any
idea about using this in a practical way seem unrealistic.
*)

Definition Cmap {A B : Type} (f : A -> B) (c : Classical A) : Classical B
  := Cbind c (fun a => Creturn (f a)).
Theorem CmapDef : forall A B f a, @Cmap A B f (Creturn a) = Creturn (f a).
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
  Creturn True = (Cbind pa (fun a => Creturn (P a))).

Theorem propBindDef {T : Type} (t : T) (P : T -> Prop) :
  propBind P (Creturn t) = P t.
Proof.
  unfold propBind.
  rewrite bindDef.
  apply propositional_extensionality.
  split.
  - intros.
    apply CreturnInj in H.
    rewrite <- H.
    apply I.
  - intros.
    apply (f_equal Creturn).
    apply propositional_extensionality.
    split; auto.
Qed.


Theorem classicalOfPropImpliesNormal (P : Prop) : Classical P -> P.
Proof.
  intros [S unique].
  destruct unique.
  apply x.
Qed.

Definition choose (T : Type) (P : T -> Prop) (H : exists t, P t): Classical T.
  refine (exist _ P _).
  destruct H as [t Pt].
  exists t.
  assumption.
Defined.

Theorem choice_spec' (T : Type) (P : T -> Prop) (H : exists t, P t)
  : Cbind (choose T P H) (fun t => Creturn (P t)) = Creturn True.
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
    (forall (a : T), P (Creturn a)) -> forall (q : Classical T), (P q).
Proof.
  intros.
  destruct q.
Abort.

(*
Definition Pif {A : Type} (P : Prop) (a1 a2 : Classical A) : Classical A.
  refine (exist _ (fun a => (P /\ proj1_sig a1 a) \/ ((not P) /\ proj1_sig a2 a)) _).
 *)

(*
Theorem PifDef1 : forall (A : Type) P (a1 a2 : A), P -> Pif P a1 a2 = Creturn a1.
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

Theorem PifDef2 : forall (A : Type) P (a1 a2 : A), not P -> Pif P a1 a2 = Creturn a2.
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
                     ((exists a, f a = Creturn None) /\ g = None)
                     \/
                       (exists g', g = Some g' /\ forall a, f a = Cmap Some (g' a))) _).
Abort.
(*Maybe a better design would be to put a double negation all the way around the outside of the prop part
of classical? *)


(*
The question is: can I do general recursion somehow?
 *)

(* Unfortunately, sort polymorphism isn't good enough to make Classical P be able 
 to be in Prop, so I have to make a whole separate definition.
 This definition can be simpler (but it doesn't have to be, it could be identitcal to Classical) *)

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
  refine (choose (option T)
                 (fun ot => match ot with
                            | Some t => P t
                            | None => ~exists t, P t
                            end) _).
  destruct (classic (exists t, P t)).
  - destruct H.
    exists (Some x).
    assumption.
  - exists None.
    assumption.
Defined.

Check @choose.

Theorem choiceInd : forall (T : Type) (P Q : T -> Prop) x,
    (forall t, P t -> Q t) -> Cbind (@choose T P x) (fun t => Creturn (Q t)) = Creturn True.
Proof.
  intros.
  apply classicalEq2.
  simpl.
  (*the exists comes from Cbind. It needs to have a double negation on it.*)
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
    destruct x.
    exists x.
    split; auto.
    apply propositional_extensionality; split; auto.
Qed.

Theorem choiceInd2 (T : Type) (P : T -> Prop) (Q : Classical T -> Prop) x
        (H : forall t, P t -> Q (Creturn t))
  : Q (choose T P x).
Proof.
  (* I don't think that this works.
   Does this work for the original Classical monad with exactly one element in the set? *)
Abort.

Theorem chooseIsRet (T : Type) (P : T -> Prop) (H : exists t, P t) x
        (eq : choose T P H = Creturn x)
  : P x.
Proof.
  apply (@f_equal _ _ (@proj1_sig _ _)) in eq.
  simpl in eq.
  subst.
  reflexivity.
Qed.

Theorem chooseIsRet2 (T : Type) (P : T -> Prop) (H : exists t, P t) x
        (hasToBex : forall y, P y -> y = x)
  : choose T P H = Creturn x.
Proof.
  apply classicalEq2.
  simpl.
  extensionality y.
  apply propositional_extensionality.
  split.
  - intros.
    apply hasToBex.
    assumption.
  - intros.
    subst.
    destruct H.
    specialize (hasToBex x0 H).
    subst.
    assumption.
Qed.

Theorem bindChoose A B (a : A) (f : A -> Classical B) P H
        (forall x, P x -> )
  : Cbind (choose A P H) f = f a.
Proof.
  apply classicalEq2.
  simpl.
  extensionality b.
  apply propositional_extensionality.
  split.
  - intros.
    destruct H0.
    destruct H0.
Abort.
  
Theorem chooseOptionSpec1 : forall T P t,
    chooseOption T P = Creturn (Some t) -> P t.
Proof.
  intros T P t.
  (*apply choiceInd.*)
  intros.
  apply chooseIsRet in H.
  assumption.
Qed.  

Theorem chooseOptionSpec2 : forall T P,
    chooseOption T P = Creturn None -> ~exists t, P t.
Proof.
  intros.
  apply chooseIsRet in H.
  assumption.
Qed.

Inductive Prog (A B : Type) : Type :=
| Ret : option B -> Prog A B
| Rec : A -> (B -> Prog A B) -> Prog A B
.

Inductive runProgR {A B : Type} (def : A -> Prog A B) : Prog A B -> B -> Prop :=
| retR : forall b, runProgR def (Ret _ _ (Some b)) b
| recR : forall (arg : A)
                (rec :  B)
                (res : B)
                (rest : B -> Prog A B),
    (runProgR def (def arg) rec)
    -> runProgR def (rest rec) res
    -> runProgR def (Rec _ _ arg rest) res
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
    specialize (IHrp1_1 _ H1).
    subst.
    specialize (IHrp1_2 _ H3).
    assumption.
Qed.

Definition runProgImpl {A B : Type} (def : A -> Prog A B) (p : Prog A B) : Classical (option B).
  refine (chooseOption B (fun b => runProgR def p b)).
Defined.

Definition runProg {A B : Type} (def : A -> Prog A B) (a : A) : Classical (option B) :=
  (runProgImpl def (def a)).

Theorem runProgDefinitionRet {A B : Type} (def : A -> Prog A B) (b : option B)
  : runProgImpl def (Ret _ _ b) = Creturn b.
  unfold runProgImpl, chooseOption.
  intros.
  apply chooseIsRet2.
  intros.
  destruct y.
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

(* Is this really not in the standard library? *)
Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
  match a with
  | Some a' => f a'
  | None => None
  end.

Theorem runProgDefinitionRec {A B : Type} {def : A -> Prog A B} {a : A} {rest : B -> Prog A B}
  : runProgImpl def (Rec _ _ a rest) =
      Cbind (runProgImpl def (def a)) (fun ob =>
                                         match ob with
                                         | None => Creturn None
                                         | Some b => runProgImpl def (rest b)
                                         end).
Proof.
  repeat unfold runProgImpl, runProg, chooseOption.
  (* One idea could be to prove a theorem about (Cbind (choose ...) ...) *)
  apply chooseIsRet.
     
Theorem runProgDefinitionRec {A B : Type} {def : A -> Prog A B}
        {arg : I -> A}
        {rest : B -> Prog A B}
  : runProgImpl def (Rec _ _ arg rest) =
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
