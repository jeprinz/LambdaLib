Require Import Classical.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import choiceBase.

(*
in this file, i'm tyring a version where you can just directly write a function in terms
of a recursive thing.
*)

Inductive runProgR {A B : Type} (prog : (A -> B) -> A -> B) : A -> B -> Prop :=
| c :forall (S : A -> Prop) a b (par : A -> B),
    (forall a' b', S a' -> par a' = b' -> runProgR prog a' b')
    -> (forall (f : A -> B), (forall a, S a -> par a = (f a)) -> prog f a = b)
    -> runProgR prog a b
.

Theorem runProgFunction {A B : Type} {a : A} {prog : (A -> B) -> A -> B} {b1 b2 : B}
  (rp1 : runProgR prog a b1) (rp2 : runProgR prog a b2) : b1 = b2.
Proof.
  intros.
  generalize rp2.
  generalize b2.
  clear rp2.
  clear b2.
  induction rp1.
  intros.
  inversion rp2.
  subst.
  (* idea:
       - show that par and par0 correspond on intersection of S and S0
       - find f : A -> B that is the union of par and par0 (using choice)
       - show that both b and b2 are equal to prog f a for this f, using H1 and H3.
   *)
  assert (forall a, S a -> S0 a -> par a = par0 a) as paragree. {
    intros.
    specialize (H2 a0 (par0 a0) H5 eq_refl).
    specialize (H0 a0 (par a0) H4 eq_refl (par0 a0) H2).
    assumption.
  }
  pose (f := fun a => Pif (S a) (par a) (Pif (S0 a) (par0 a) b)).
  assert (forall a, S a -> par a = f a) as fAgreesPar. {
    intros.
    unfold f.
    rewrite (PifDef1 _ _ _ _ H4).
    reflexivity.
  }
  assert (forall a, S0 a -> par0 a = f a) as fAgreesPar0. {
    intros.
    destruct (classic (S a0)).
    - rewrite <- paragree; auto.
    - unfold f.
      rewrite (PifDef2 _ _ _ _ H5).
      rewrite (PifDef1 _ _ _ _ H4).
      reflexivity.
  }
  specialize (H1 f fAgreesPar).
  specialize (H3 f fAgreesPar0).
  rewrite <- H1, H3.
  reflexivity.
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

Definition runProg {A B : Type} (prog : (A -> B) -> A -> B) (default : B) (a : A) : B.
  refine (chooseDefault B (fun b => runProgR prog a b) default).
Defined.

Theorem runProgDef {A B : Type} (prog : (A -> B) -> A -> B) (default : B) (a : A) 
  : runProg prog default a = prog (runProg prog default) a.
Proof.

  (*
    i don't this that this works as is.
    suppose that there is abad : A, such that (runProg prog d abad = d)
    then suppose that (prog f a' = 1 + abad).
    then (runProg prog d a' = default),
    but actually this theorm wants it to be (1 + default).

    i thiink that i can fix this by adjusting the definition of runProgR,
    basically make it include the defaults itself and be total.
    add a second constructor that inputs the negation of the premises of the first constructor
    and then says it outputs a default there.
    using lem, this will trivially be total.
*)
