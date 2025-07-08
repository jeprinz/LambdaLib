Require Import lambdaFP.
Require Import core unscoped.
Require Import String.

(*
In this file, I will
[ ] - define the reduction relations that I need
[ ] - prove confluence
[ ] - prove any other properties that I need
 *)

Compute (lam (var_tm 0)).

Check subst_tm.
Check var_tm.
Compute (subst_tm var_tm (lam (var_tm 1))).
Check ids.
Check scons.
Compute (subst_tm (scons (const "a") ids) (lam (var_tm 1))).
Axiom b : tm.
(*Compute (b[b..]).*)

(* Can't figure out how to make the fancy notations work. *)

Check ren_tm.
Print tm.
(* Single step reduction *)
Inductive red : tm -> tm -> Prop :=
(* Congruences *)
| red_lam : forall a b, red a b -> red (lam a) (lam b)
| red_app1 : forall a b c, red a b -> red (app a c) (app b c)
| red_app2 : forall a b c, red a b -> red (app c a) (app c b)
| red_pair1 : forall a b c, red a b -> red (pair a c) (pair b c)
| red_pair2 : forall a b c, red a b -> red (pair c a) (pair c b)
| red_fst : forall a b, red a b -> red (fst a) (fst b)
| red_snd : forall a b, red a b -> red (snd a) (snd b)
(* Meaningful things *)
| beta : forall a b, red (app (lam a ) b) (subst_tm (scons b ids) a)
| pi1 : forall a b, red (fst (pair a b)) a
| pi2 : forall a b, red (snd (pair a b)) b
| eta : forall t, red t (lam (ren_tm shift t))
| SP : forall t, red t (pair (fst t) (snd t))
.

From Stdlib Require Import Relations.Relation_Operators.
Check clos_refl_trans.

Definition conv := clos_refl_trans tm red.

(* If I had proven this, can I use it to get consistency in term.v? *)
Axiom consistent : exists t1 t2, not (conv t1 t2).
(* It will be easier to work with specific terms *)
Axiom consistent_specific : not (conv (const "A") (const "B")).

Require Import term.
