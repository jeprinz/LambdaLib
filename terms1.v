Require Import String.
Require Import List.

Module Type Constants.
  Parameter Constant : Type.
  (*I'm not sure if I should have these, or assume that metavariables are in empty context.*)
  (* Parameter liftConst : Constant -> string -> Constant.
  Parameter substCons : Constant -> string -> nat -> Term -> ???? *)
End Constants.

Module Syntax (Constants : Constants).

Import Constants.
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

End Syntax.

Module BetaEtaSPConstants : Constants.
  Inductive Constant' :=
  | pi1 : Constant'
  | pi2 : Constant'
  | pair : Constant'.
  Definition Constant := Constant'.
End BetaEtaSPConstants.

Module LambdaBESP := Syntax (BetaEtaSPConstants).

(* Include LambdaBESP. *)

