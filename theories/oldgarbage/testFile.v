Require Import String.
Require Import qterm.

Ltac normalize := repeat (rewrite beta; repeat (repeat (rewrite subst_app) ;
                          repeat (rewrite subst_lam ; simpl) ;
                          repeat (rewrite subst_var ; simpl;
                                  repeat (rewrite lift_lam, lift_app, lift_var)))
                          ).

Compute <fun x => fun y => x y>.

Definition t1 := <fun x => x>.
Definition t2 := <fun y => `t1 y>.
Compute t2.

Theorem example : <(fun x => x) (fun x => x)> = <fun x => x>.
Proof.
  normalize.
  reflexivity.
Qed.


























Definition IsA (t : QTerm) : Prop := t = <a>.

Definition IsB (t : QTerm) : Prop := t = <b>.

Definition Arrow (A : QTerm -> Prop) (B : QTerm -> Prop) (t : QTerm) : Prop :=
  forall (x : QTerm), A x -> B <`t `x>.

Theorem typing_example : Arrow IsA IsB <fun x => b>.
Proof.
  unfold Arrow, IsA, IsB.
  intros.
  normalize5.
  reflexivity.
Qed.

Definition SameArrow T := Arrow T T.

Compute <Pi A (fun a => B)>.

Inductive Well_Typed : QTerm -> QTerm -> QTerm -> Prop:=
| app : forall t1 t2 A B ctx, Well_Typed ctx <Pi `A `B> t1 -> Well_Typed ctx A t2
                        -> Well_Typed ctx B <`t1 `t2>.


