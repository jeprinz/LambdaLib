Require Import String.
Require Import List.


Inductive Constant :=
| pi1c : Constant
| pi2c : Constant
| pairc : Constant.

Inductive Term : Type :=
| lam : string -> Term -> Term
| app : Term -> Term -> Term
| const : Constant -> Term
| var : string -> nat -> Term. (*nth variable with that name, going up like debruin indices*)

Fixpoint lift (t : Term) (x : string) : Term :=
  match t with
  | lam x body => lam x (lift body x)
  | app t1 t2 => app (lift t1 x) (lift t2 x)
  | const c => const c (* const (liftConst c x)*)
  | var y n => if eqb y x then var y (S n) else var y n
  end.
 
Fixpoint subst (t : Term) (x : string) (i : nat) (toSub : Term) : Term :=
  match t with
  | lam y body =>
      if eqb x y
      then lam y (subst body x (S i) (lift toSub x))
      else lam y (subst body x i toSub)
  | app t1 t2 => app (subst t1 x i toSub) (subst t2 x i toSub)
  | const c => const c
  | var y n => if andb (eqb y x) (Nat.eqb n i) then toSub else var y n
  end.

Definition pair t1 t2 := (app (app (const pairc) t1) t2).
Definition pi1 t := app (const pi1c) t.
Definition pi2 t := app (const pi2c) t.

Inductive step : Term -> Term -> Prop :=
| beta : forall {s t1 t2}, step (app (lam s t1) t2) (subst t1 s 0 t2)
| betapi1 : forall {t1 t2}, step (pi1 (pair t1 t2)) t1
| betapi2 : forall {t1 t2}, step (pi2 (pair t1 t2)) t2
| eta : forall {s t}, step t (lam s (app (lift t s) (var s 0)))
| SP : forall {t}, step t (pair (pi1 t) (pi2 t))
(* congruence steps *)
| lam_cong : forall {s t t'}, step t t' -> step (lam s t) (lam s t')
| app_cong1 : forall {t1 t1' t2}, step t1 t1' -> step (app t1 t2) (app t1' t2)
| app_cong2 : forall {t1 t2 t2'}, step t2 t2' -> step (app t1 t2) (app t1 t2').

(*
Theorem subst_lift (t1 t2 : Term) (s1 s2 : string) (index : nat)
  : subst t1 s1 index (lift t2 s2) = 

Fixpoint lift_cong {s : string} {t1 t2 : Term} (r : step t1 t2)
  : step (lift t1 s) (lift t2 s).
Proof.
  induction r.
  - simpl.
    apply beta.
*)
