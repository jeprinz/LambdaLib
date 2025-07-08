Require Import Coq.Logic.ProofIrrelevance.
(* Instead of using SProp, for now I'll just use the proof irrelevance axiom.
   I'll see if this causes any issues; probably not. *)
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

(*
My idea is to have the monad of nonempty sets. Maybe that corresponds to choice, and
maybe it still gets classical stuff?

In this version of the file, all the props are under PClassical
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
Definition PClassical (P : Prop) : Prop := not (not P).

Definition Preturn {A : Prop} (x : A) : PClassical A.
Proof.
  intro na.
  apply na.
  apply x.
Qed.

Theorem Pbind {A B : Prop} (pa : PClassical A) (f : A -> PClassical B) : PClassical B.
  Proof.
  unfold PClassical in *.
  intros nb.
  apply pa.
  intro a.
  apply f.
  - apply a.
  - apply nb.
Qed.

Definition Pmap {A B : Prop} (f : A -> B) (a : PClassical A) : PClassical B :=
  Pbind a (fun a => Preturn (f a)).

Theorem Plem (P : Prop) : PClassical (P \/ ~P).
Proof.
  intros n.
  apply n.
  apply or_intror.
  intros p.
  apply n.
  apply or_introl.
  apply p.
Qed.

Theorem classical_True : PClassical True = True.
Proof.
  apply (PropExtensionalityFacts.PropExt_imp_ProvPropExt propositional_extensionality).
  easy.
Qed.

Theorem classical_False : PClassical False = False.
Proof.
  apply (PropExtensionalityFacts.PropExt_imp_RefutPropExt propositional_extensionality).
  intros p.
  apply p.
  easy.
Qed.

Theorem collapsePClassical {T : Prop} {P : Prop -> Prop}
  : PClassical (P (PClassical T) = P T).
Proof.
  apply (Pbind (Plem T)).
  intros.
  apply Preturn.
  destruct H.
  + rewrite (PropExtensionalityFacts.PropExt_imp_ProvPropExt propositional_extensionality H) in *.
    rewrite classical_True.
    reflexivity.
  + rewrite (PropExtensionalityFacts.PropExt_imp_RefutPropExt propositional_extensionality H) in *.
    rewrite classical_False.
    reflexivity.
Qed.    

Definition Classical (A : Type) : Type :=
  {S : A -> Prop | PClassical (exists a, S a)}.

Definition Creturn {A : Type} (x : A) : Classical A.
  refine (exist _ (fun y => PClassical (y = x)) _).
  intros.
  intros p.
  apply p.
  exists x.
  apply Preturn.
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

Theorem CreturnInj : forall A (x y : A), Creturn x = Creturn y -> PClassical (x = y).
Proof.
  intros.
  pose (@f_equal _ _ (@proj1_sig _ _) _ _ H) as fact.
  simpl in fact.
  assert ((fun y => PClassical (y = x)) x). {
    apply Preturn.
    reflexivity.
  }
  rewrite fact in H0.
  assumption.
Qed.

Definition Cbind {A B : Type} (pa : Classical A) (f : A -> Classical B) : Classical B.
  refine (exist _ (fun b => PClassical (exists a, proj1_sig pa a /\ proj1_sig (f a) b)) _).
  destruct pa as [Sa nonempty].
  apply (Pbind nonempty).
  intros.
  simpl.
  destruct H.
  remember (f x) as fx.
  destruct fx.
  apply (Pbind p).
  intros.
  apply Preturn.
  destruct H0.
  exists x1.
  apply Preturn.
  exists x.
  split; auto.
  rewrite <- Heqfx.
  simpl.
  assumption.
Defined.

Theorem Ptransport (T : Type) (P : T -> Prop) x y
    (H : PClassical (x = y))
  : PClassical (P x) -> PClassical (P y).
Proof.
  intros.
  apply (Pbind H); intros; clear H.
  apply (Pbind H0); intros; clear H0.
  subst.
  apply Preturn.
  apply H.
Qed.
  
Theorem bindDef : forall A B (a : A) (f : A -> Classical B),
    PClassical (Cbind (Creturn a) f = f a).
Proof.
  intros.
  apply (Pmap (classicalEq2 _ _ _)).
  simpl.
  Check collapsePClassical.
  apply (Ptransport _ _ _ _ collapsePClassical).
  Check eq_rect_r.
  apply (Pmap (eq_rect_r 
  eapply (Pbind collapsePClassical).
  intros.
  eapply Pmap.
  intros.
  rewrite H.
  apply H0.
  
  apply (Pmap (functional_extensionality _ _)).
  
  apply Preturn.
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


(*
I think that my definition of choose needs to actually have the monad around
the inputs as well as the output, so I can use it correctly.
 *)
Definition choose2 (T : Type) (P : T -> Prop) (H : PClassical (exists t, P t)): Classical T.
  refine (exist _ P _).
  intros p.
  apply H.
  intros x.
  destruct x.
  specialize (p x).
  contradiction.
Defined.

Theorem choice_spec2 (T : Type) (P : T -> Prop) (H : exists t, P t)
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
  apply (Pbind (Plem (exists t, P t))).
  intros doesOrDoesNot.
  destruct doesOrDoesNot.
  - destruct H.
    apply Preturn.
    exists (Some x).
    assumption.
  - apply Preturn.
    exists None.
    assumption.
Defined.

Check @choose.

Theorem choiceInd : forall (T : Type) (P Q : T -> Prop) x,
    (forall t, P t -> Q t) -> Cbind (@choose2 T P x) (fun t => Creturn (Q t)) = Creturn True.
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
    destruct H.
    exists x.
    split; auto.
    apply propositional_extensionality; split; auto.
Qed.

Theorem chooseOptionSpec1 : forall T P t,
    chooseOption T P = Creturn (Some t) -> P t.
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
