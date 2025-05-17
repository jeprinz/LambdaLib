Require Import partial.

Inductive Term : Type :=
| const : nat -> Term
| var : nat -> Term
| app : Term -> Term -> Term
| lam : Term -> Term.

Inductive Value : Type :=
| vnum : nat -> Value
| vlam : Term -> Value
.

Axiom subst0 : Term -> Value -> Term.
Axiom subst0' : Term -> Term -> Term.

Definition eval : Term -> Partial Value.
  refine (runProg (fun t => Preturn (match t with
                                     | const x => Ret _ _ (Preturn (vnum x))
                                     | var n => Ret _ _ Pempty
                                     | lam t => Ret _ _ (Preturn (vlam t))
                                     | (app t1 t2) => Rec _ _ t1 (fun v1 =>
                                                      Rec _ _ t2 (fun v2 =>
                                                                    match v1 with
                                                                    | vlam t =>  Rec _ _ (subst0 t v2) (fun v => Ret _ _ (Preturn v))
                                                                    | _ => Ret _ _ Pempty
                                                                    end))
                                     end))).
Defined.

Fixpoint transform (t : Term) : Term :=
  match t with
  | app (lam t1) t2 => subst0' t1 t2
  | app t1 t2 => app (transform t1) (transform t2)
  | _ => t
  end.

Definition R : Value * Value -> Partial Prop.
  refine (runProg (fun v => Preturn match v with
                                    | (vnum n1, vnum n2) => Ret _ _ (Preturn (n1 = n2))
                                    | (vlam t1, vlam t2) => _ (* forall v1 v2, R v1 v2 = Preturn True
                                                                 -> R (eval (subst0 t1 v1)) (eval (subst0 t2 v2))*)
                                                              (* forall v, R (eval (subst0 t1 v)) (eval (subst0 t2 v))*)
                                    | (v1 , v2) => Ret _ _ (Preturn False)
                                    end) ).
Admitted.

Theorem fact : forall t, Pbind (eval t) (fun v1 => Pbind (eval (transform t)) (fun v2 => R (v1, v2))) = Preturn True.
Abort.

Definition nonempty {A : Type} (p : Partial A) : Prop :=
  match p with
  | exist _ s isprop => exists x, s x
  end.

Definition R'' : Value * Value -> Partial Prop.
  refine (runProg2 (fun vv => match vv with
                              | (vnum n1, vnum n2) => Preturn (@existT Type _ False (False_rect _, fun _ => Preturn (n1 = n2)))
                              | (vlam t1, vlam t2) => Preturn (@existT Type _ {vv1v2 | match vv1v2 with
                                                                                       | (v, v1, v2) => eval (subst0 t1 v) = Preturn v1
                                                                                                        /\ eval (subst0 t1 v) = Preturn v2
                                                                                       end} (fun vv1v2p => match vv1v2p with
                                                                                                           | exist _ (v , v1, v2) _ => (v1, v2)
                                                                                                           end,
                                                                                               fun rec => Preturn (all rec)))
                              | (v1, v2) => Preturn (@existT Type _ False (False_rect _, fun _ => Preturn False))
                              end)).
Defined.

Definition R''' : Value * Value -> Partial Prop.
  refine (runProg2 (fun vv => match vv with
                              | (vnum n1, vnum n2) => Preturn (@existT Type _ False (False_rect _, fun _ => Preturn (n1 = n2)))
                              | (vlam t1, vlam t2) => Preturn (@existT Type _ (sum {v1v2r1r2 | match v1v2r1r2 with
                                                                                       | (v1, v2, r1, r2) => eval (subst0 t1 v1) = Preturn r1
                                                                                                        /\ eval (subst0 t1 v2) = Preturn r2
                                                                                          end} (Value * Value))
                                                                       (fun v1v2r1r2 => match v1v2r1r2 with
                                                                                        | inl (exist _ (v1, v2 , r1, r2) _) => (r1, r2)
                                                                                        | inr (v1, v2) => (v1, v2)
                                                                                        end,
                                                                          fun rec => Preturn (forall v1 v2,
                                                              (rec (inr (v1, v2))) -> exists r1 r2,
                                                                              forall prf,  rec (inl (exist _ (v1, v2, r1, r2) prf)))))
                              | (v1, v2) => Preturn (@existT Type _ False (False_rect _, fun _ => Preturn False))
                              end)).
Defined.

(*Inductive Empty : Type :=.*)

Definition runProg3 {A B : Type}
           (def : A -> Partial {T : Type & prod (T -> Partial A) ((T -> B) -> Partial B)})
           (a : A)
  : Partial B.
Admitted.

Check existT.
Check False_rect.
Definition R'' : Value * Value -> Partial Prop.
  refine (runProg3 (fun vv => match vv with
                              | (vnum n1, vnum n2) => Preturn (@existT Type _ False (False_rect _, fun _ => Preturn (n1 = n2)))
                              | (vlam t1, vlam t2) => Preturn
                                                        (@existT Type _ Value
                                                                 (fun v => Pbind (eval (subst0 t1 v))
                                                                                 (fun v1 => Pbind (eval (subst0 t2 v))
                                                                                                  (fun v2 => Preturn (v1, v2))),
                                                                    (fun rec => Preturn (forall v, rec v))))
                              | (v1, v2) => Preturn (@existT Type _ False (False_rect _, fun _ => Preturn False))
                              end)).
Defined.

Theorem fact' : forall t, Pbind (eval t) (fun v1 => Pbind (eval (transform t)) (fun v2 => R' (v1, v2))) = Preturn True.
Abort.


Definition facProg : nat -> Partial (Prog nat nat) :=
  fun n => Preturn (match n with
           | O => Ret _ _ (Preturn 1)
           | S n' => Rec _ _ n' (fun x => Ret _ _ (Preturn (n * x)))
           end).

Definition factorial : nat -> Partial nat :=
  runProg facProg.
