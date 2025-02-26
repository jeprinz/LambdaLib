Require Import String.
Require Import List.

(*
In this file I'm going to try defining terms with syntactic substitution and lifting.
I will also define the relation directly to be an equivalence relation.
The idea is to shunt proofs that these things all work out to lambda-FP, which will be
implemented in autosubst, so I can deal with actually proving that this works there.

Also keep in mind that when I go to define e.g. app over the quotiented terms, I will need to
prove "forall a b c d : A, R a b -> R c d -> R (app a c) (app b d)",
so it is better to build the congruence rules into the relation like this.
*)

Inductive Constant :=
| pi1c : Constant
| pi2c : Constant
| pairc : Constant.

Inductive Term : Type :=
| lam : string -> Term -> Term
| app : Term -> Term -> Term
| const : Constant -> Term
| var : string -> nat -> Term (*nth variable with that name, going up like debruin indices*)
| lift : string -> Term -> Term
(* the var info, the term being subbed for the var, the term being subbed into *)
| subst : string -> nat -> Term -> Term -> Term.


Definition pair t1 t2 := (app (app (const pairc) t1) t2).
Definition pi1 t := app (const pi1c) t.
Definition pi2 t := app (const pi2c) t.

Inductive convertible : Term -> Term -> Prop :=
| alpha : forall s1 s2 t, convertible (lam s1 t) (lam s2 (subst s1 0 (var s2 0) t))
| beta : forall {s t1 t2}, convertible (app (lam s t1) t2) (subst s 0 t2 t1)
| betapi1 : forall {t1 t2}, convertible (pi1 (pair t1 t2)) t1
| betapi2 : forall {t1 t2}, convertible (pi2 (pair t1 t2)) t2
| eta : forall {s t}, convertible t (lam s (app (lift s t) (var s 0)))
| SP : forall {t}, convertible t (pair (pi1 t) (pi2 t))
(* congruence convertibles *)
| lam_cong : forall s t t', convertible t t' -> convertible (lam s t) (lam s t')
| app_cong : forall t1 t1' t2 t2',
    convertible t1 t1' -> convertible t2 t2' -> convertible (app t1 t2) (app t1' t2')
| lift_cong : forall s t t', convertible t t' -> convertible (lift s t) (lift s t')
| subst_cong : forall s i t1 t1' t2 t2',
    convertible t1 t1' -> convertible t2 t2'
    -> convertible (subst s i t1 t2) (subst s i t1' t2')
(* equivalence relation *)
| conv_refl : forall t, convertible t t
| conv_trans : forall t1 t2 t3, convertible t1 t2 -> convertible t2 t3 -> convertible t1 t3
| conv_sym : forall t1 t2, convertible t1 t2 -> convertible t2 t1
(* small step substitution and lifting *)
| lift_app : forall s t1 t2, convertible (lift s (app t1 t2)) (app (lift s t1) (lift s t2))
| lift_lam : forall s1 s2 t, convertible (lift s1 (lam s2 t)) (lam s2 (lift s1 t))
| lift_var : forall (s1 s2 : string) (i : nat),
    convertible (lift s1 (var s2 i))
      (if String.eqb s1 s2
      then var s2 (S i)
       else var s2 i)
| subst_app : forall s i t t1 t2,
    convertible (subst s i t (app t1 t2)) (app (subst s i t t1) (subst s i t t2))
| subst_lam : forall s1 s2 i t1 t2,
    convertible (subst s2 i t2 (lam s1 t1))
                (if String.eqb s1 s2
                 then lam s1 (subst s2 (S i) (lift s2 t2) t1)
                 else lam s1 (subst s2 i t2 t1))
| subst_var : forall x y n i toSub, convertible (subst x i toSub (var y n))
    (if andb (String.eqb y x) (Nat.eqb n i) then toSub else var y n)
.

Theorem pi1_cong : forall t t', convertible t t' -> convertible (pi1 t) (pi1 t').
Proof.
  intros.
  apply app_cong.
  apply conv_refl.
  apply H.
Qed.

Theorem pi2_cong : forall t t', convertible t t' -> convertible (pi2 t) (pi2 t').
Proof.
  intros.
  apply app_cong.
  apply conv_refl.
  apply H.
Qed.

Theorem pair_cong : forall t1 t1' t2 t2',
    convertible t1 t1' -> convertible t2 t2' -> convertible (pair t1 t2) (pair t1' t2').
Proof.
  intros.
  apply app_cong.
  apply app_cong.
  apply conv_refl.
  apply H.
  apply H0.
Qed.
