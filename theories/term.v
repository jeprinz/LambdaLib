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
| pairc : Constant
| stringc : string -> Constant.

Inductive Term : Type :=
| lam : string -> Term -> Term
| app : Term -> Term -> Term
| const : Constant -> Term
| var : string -> nat -> Term (*nth variable with that name, going up like debruin indices*)
| lift : string -> nat -> Term -> Term
(* the var info, the term being subbed for the var, the term being subbed into *)
| subst : string -> nat -> Term -> Term -> Term.

Definition pair t1 t2 := (app (app (const pairc) t1) t2).
Definition pi1 t := app (const pi1c) t.
Definition pi2 t := app (const pi2c) t.
Definition constant (s : string) : Term := const (stringc s).

Inductive convertible : Term -> Term -> Prop :=
| alpha : forall s1 s2 t, convertible (lam s1 t) (lam s2 (subst s1 0 (var s2 0) (lift s2 0 t)))
| beta : forall {s t1 t2}, convertible (app (lam s t1) t2) (subst s 0 t2 t1)
| betapi1 : forall {t1 t2}, convertible (pi1 (pair t1 t2)) t1
| betapi2 : forall {t1 t2}, convertible (pi2 (pair t1 t2)) t2
| eta : forall {s t}, convertible t (lam s (app (lift s 0 t) (var s 0)))
| SP : forall {t}, convertible t (pair (pi1 t) (pi2 t))
(* congruence convertibles *)
| lam_cong : forall s t t', convertible t t' -> convertible (lam s t) (lam s t')
| app_cong : forall t1 t1' t2 t2',
    convertible t1 t1' -> convertible t2 t2' -> convertible (app t1 t2) (app t1' t2')
| lift_cong : forall s i t t', convertible t t' -> convertible (lift s i t) (lift s i t')
| subst_cong : forall s i t1 t1' t2 t2',
    convertible t1 t1' -> convertible t2 t2'
    -> convertible (subst s i t1 t2) (subst s i t1' t2')
(* equivalence relation *)
| conv_refl : forall t, convertible t t
| conv_trans : forall t1 t2 t3, convertible t1 t2 -> convertible t2 t3 -> convertible t1 t3
| conv_sym : forall t1 t2, convertible t1 t2 -> convertible t2 t1
(* small step substitution and lifting *)
| lift_app : forall s i t1 t2, convertible (lift s i (app t1 t2)) (app (lift s i t1) (lift s i t2))
| lift_lam : forall s1 i s2 t,
    convertible (lift s1 i (lam s2 t)) (lam s2 (lift s1 (if eqb s1 s2 then S i else i) t))
(* TODO: Surely this is wrong? Shouldn't it compare the two indices? In fact, shouldn't 
lift TAKE an index? Check Nipkow paper. *)
| lift_var : forall (s1 s2 : string) (i k : nat),
    convertible (lift s1 k (var s2 i))
      (if andb (String.eqb s1 s2) (negb (Nat.ltb i k))
      then var s2 (S i)
       else var s2 i)
| lift_const : forall s1 i s2, convertible (lift s1 i (const s2)) (const s2)
| subst_app : forall s i t t1 t2,
    convertible (subst s i t (app t1 t2)) (app (subst s i t t1) (subst s i t t2))
(* Is this right now? *)
| subst_lam : forall s1 s2 i t1 t2,
    convertible (subst s2 i t2 (lam s1 t1))
                (if String.eqb s1 s2
                 then lam s1 (subst s2 (S i) (lift s1 0 t2) t1)
                 else lam s1 (subst s2 i (lift s1 0 t2) t1))
| subst_var : forall s1 s2 k i toSub, convertible (subst s1 k toSub (var s2 i))
     (if String.eqb s1 s2
        then if Nat.ltb k i then var s2 (i - 1) else if Nat.eqb i k then toSub
        else var s2 i else var s2 i)
| subst_const : forall s1 s2 i t, convertible (subst s1 i t (const s2)) (const s2)
(* extra facts *)
| subst_id : forall s i t, convertible (subst s i (var s i) t) t
| subst_lift : forall s i t1 t2, convertible (subst s i t1 (lift s i t2)) t2
(* Hopefully this is right now *)
| lift_lift : forall s1 s2 i1 i2 t,
    convertible (lift s1 i1 (lift s2 i2 t))
                (if eqb s1 s2
                 then if Nat.ltb i2 i1
                      then lift s2 i2 (lift s1 (pred i1) t)
                      else lift s2 (S i2) (lift s1 i1 t)
                 else lift s2 i2 (lift s1 i1 t))
    (*convertible (lift s1 i1 (lift s2 i2 t))
                (lift s2 (if eqb s1 s2 then S i2 else i2) (lift s1 i1 t))*)
(*| subst_subst : forall s1 i1 t1 s2 i2 t2 t,
    convertible (subst s1 i1 t1 (subst s2 i2 t2 t)) (subst s2 ????*)
(* lift_lift ???*)                                           
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

(*
For now, consistency will be an axiom. Eventually I will prove it by mapping this whole system
into lambda-FP, following Støvring.
*)

Axiom consistency : exists t1 t2, not (convertible t1 t2).

(*TODO ^^^^^^^*)
