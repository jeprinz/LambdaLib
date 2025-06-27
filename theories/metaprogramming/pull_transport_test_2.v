

(*
An idea is, can I just recalculate the equality for the cast being on the other side?
 *)

Definition cast {x y : Type} (p : x = y) : x -> y.
Proof.
  intros.
  subst.
  assumption.
Defined.

Axiom uip : forall T (t1 t2 : T) (p1 p2 : t1 = t2), p1 = p2.

Theorem pull_through_1
        (I : Type)
        (P Q : I -> Type)
        (f : forall {i}, P i -> Q i)
        (i1 i2 : I)
        (pin : P i1 = P i2)
        (*pout : Q i1 = Q i2*)
        (realp : i1 = i2)
        (input : P i1)
  : f (cast pin input) = cast (f_equal Q realp) (f input).
Proof.
  subst.
  (*rewrite (uip _ _ _ pout eq_refl).*)
  rewrite (uip _ _ _ pin eq_refl).
  reflexivity.
Qed.

(*
The idea is that I can just recompute realp with solve_all whenever I want to use this rewrite.
*)

Definition transport {T : Type} (P : T -> Type) {t1 t2 : T} (p : t1 = t2) (a : P t1) : P t2.
  subst.
  apply a.
Defined.

Theorem pull_through_1
        (I : Type)
        (P Q : I -> Type)
        (f : forall {i}, P i -> Q i)
        (i1 i2 : I)
        (p : i1 = i2)
        (input : P i1)
  : f (transport P p input) = transport Q p (f input).
Proof.
  refine match p with
         | eq_refl => _
         end.
  reflexivity.
Qed.

Axiom Fam : nat -> Type.
Axiom f1 : forall {n}, Fam (10 + n) -> Fam (n - 20).

(*
Theorem test_1
        (p : 15 = 25)
        (input : Fam 15)
  : f1 (transport Fam p input) = transport Fam p (f1 input).
Proof.
  Check (transport Fam p input).
  Check (f1 (transport _ p input)).
  Fail rewrite pull_through_1.
  rewrite 
*)
