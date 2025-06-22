Require Import String.
Require Import -(coercions) qterm. (* TODO: Do I ever need the coeercion? This is very strange*)
Require Import lambdaFacts.
Require Import Lia.

(*
The goal of these tactics is to reduce terms to a normal form.
In order for them to work, we need to assume that the input terms have a particular form:
All QTerms should consist of lam, app, var, pair, pi1, pi2, const, and coq variables.
Any lifts should be around a coq variable.

There should not be any lifts anywhere else or subst forms anywhere at all
except during intermediate states.
 *)


(* We need to hide Mark in a module so that it is not definitionally equal to its definition *)
Module Type HowToHideMark.
  Parameter Mark : forall {X : Type}, X -> X.
  Parameter MarkIsJustId : forall {X : Type} {x : X}, Mark x = x.
End HowToHideMark.
Module HiddenMark : HowToHideMark.
  Definition Mark {X : Type} (x : X) := x. (* He hides in here where no one can see him *)
  Theorem MarkIsJustId {X : Type} {x : X} : Mark x = x.
  Proof.
    intros.
    reflexivity.
  Qed.
End HiddenMark.

Import HiddenMark.

Theorem mark_stuck : forall t s1 i1 s2 i2 t',
    subst s1 i1 t' (lift s2 i2 t) = subst s1 i1 t' ((Mark lift) s2 i2 t).
Proof.
  rewrite MarkIsJustId.
  reflexivity.
Qed.

Theorem swap_marked_lift : forall (s1 s2 : string) (i1 i2 : nat) (t : QTerm),
    (Mark lift) s1 i1 (lift s2 i2 t) =
      (if eqb s1 s2
       then if Nat.ltb i2 i1
            then lift s2 i2 (Mark lift s1 (pred i1) t)
            else lift s2 (S i2) (Mark lift s1 i1 t)
       else lift s2 i2 (Mark lift s1 i1 t)).
Proof.
  rewrite MarkIsJustId.
  apply lift_lift.
Qed.

Ltac fix_subst_lift :=
  first [
      (* First, see if a lift can be immediately canceled with a subst *)
      rewrite subst_lift
    |
      (* If not, mark a lift under a subst *)
      rewrite mark_stuck;
      (* Next, push the marked lift down. It is crucial that this fails if it can't,
       because that implies that the lift was not found. If it didn't fail, then this tactic
       could succeed but only re-order lifts, which would cause an infinite loop if inside
       a repeat tactical. *)
      (rewrite swap_marked_lift; simpl); repeat (rewrite swap_marked_lift; simpl);
      (* Finally, recur. It only succeeds if subst_lift eventually works. *)
      fix_subst_lift
    ];
  (* When we are done, remove Mark. *)
  repeat rewrite MarkIsJustId.

Ltac fix_subst_lifts := repeat fix_subst_lift.

Ltac fix_subst_lift_in H :=
  first [
      rewrite subst_lift in H
    |
      rewrite mark_stuck in H;
      (rewrite swap_marked_lift in H; simpl in H); repeat (rewrite swap_marked_lift in H; simpl in H);
      fix_subst_lift_in H
    ];
  repeat rewrite MarkIsJustId in H.

Ltac fix_subst_lifts_in H := repeat fix_subst_lift_in H.
  

Theorem test_not_infinite_loop :
  <X [a] [b] [c/d]> = <Y>.
Proof.
  Fail fix_subst_lift.
Abort.

(*
Due to an annoying problem with rewrite specializing metavariables, I need this workaround.
For now, I'll only implement it for metavars in the goal (which is the common case)
If necessary, I'll also implmenent it for metavars in hypotheses.
Here is my stackexchange question where someone gave me this bit of Ltac:
https://proofassistants.stackexchange.com/questions/5112/in-rocq-how-to-prevent-rewrite-from-specializing-existential-variables?noredirect=1#comment10128_5112
 *)

Ltac hide_evars_in_goal :=
  repeat match goal with
         | [ |- context [ ?v : QTerm ] ] => is_evar v; let H := fresh v in pose (H := v); fold H
         end.

Ltac unhide_evars_in_goal :=
  repeat match goal with
         | x := ?t : QTerm |- _ => is_evar t; subst x
         end.

Ltac compute_lifts := repeat (try (rewrite lift_lam ; simpl) ;
                              try rewrite lift_app;
                              try rewrite lift_pair;
                              try rewrite lift_pi1;
                              try rewrite lift_pi2;
                              try (rewrite lift_var ; simpl)).

Ltac compute_subst := repeat (try rewrite subst_app ;
                              try rewrite subst_pair;
                              try rewrite subst_pi1;
                              try rewrite subst_pi2;
                          try (rewrite subst_lam ; simpl ; compute_lifts) ;
                          try (rewrite subst_var ; simpl);
                               compute_lifts); fix_subst_lifts.
(* Is there a way to not have this be repetetive with the above? *)

Ltac compute_lifts_in H := repeat (try (rewrite lift_lam in H ; simpl in H) ;
                                   try rewrite lift_app in H;
                                   try rewrite lift_pair in H;
                                   try rewrite lift_pi1 in H;
                                   try rewrite lift_pi2 in H;
                              try (rewrite lift_var in H ; simpl in H)).

Ltac compute_subst_in H := repeat (try rewrite subst_app in H;
                                   try rewrite subst_pair in H;
                                   try rewrite subst_pi1 in H;
                                   try rewrite subst_pi2 in H;
                          try (rewrite subst_lam in H ; simpl in H ; compute_lifts_in H) ;
                          try (rewrite subst_var in H; simpl in H);
                                  compute_lifts_in H); fix_subst_lifts_in H.
Ltac normalize := hide_evars_in_goal;
                  repeat (rewrite ?beta, ?betapi1, ?betapi2; compute_subst);
                  unhide_evars_in_goal.
Ltac normalize_in H := repeat (rewrite ?beta, ?betapi1, ?betapi2 in H; compute_subst_in H).

(*
[x] - add pairs and stuff to qterm
[ ] - find old file that had most advanced unification tactic
[ ] - port to this version
*)

(*
Ltac compute_subst' location :=
  match location with
  | "goal"%string => repeat (try rewrite subst_app ;
                          try (rewrite subst_lam ; simpl) ;
                          try (rewrite subst_var ; simpl;
                               repeat (rewrite lift_lam, lift_app, lift_var)))
  | _ => repeat (try rewrite subst_app ;
                          try (rewrite subst_lam in location ; simpl in location) ;
                          try (rewrite subst_var in location; simpl in location;
                                  repeat (rewrite lift_lam, lift_app, lift_var in location)))
  end.


Ltac handle_case t1 t2 location :=
  match t1 t2 with
  | (lam ?s ?t1) (lam ?s ?t2) => apply lamInj in location
  end.
 *)

Theorem proveEqualityInParts (A B : Type) (f1 f2 : A -> B) (a1 a2 : A)
  : f1 = f2 -> a1 = a2 -> f1 a1 = f2 a2.
Proof.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Ltac lambda_solve_step :=
  (
      match goal with
      | H : lam ?s ?t1 = lam ?s ?t2 |- _ => apply lamInj in H
      | |- lam ?s ?t1 = lam ?s ?t2 => apply (f_equal (lam s))
      | H : lam ?s1 ?t1 = lam ?s2 ?t2 |- _ => rewrite (@alpha s1 s2 t1) in H; compute_subst_in H
      | |- lam ?s1 ?t1 = lam ?s2 ?t2 => rewrite (@alpha s1 s2 t1);
                                        hide_evars_in_goal; compute_subst; unhide_evars_in_goal
      | H : var ?s1 0 = var ?s2 0 |- _ => apply varInj in H
      | H : const ?t1 = const ?t2 |- _ => apply constInj in H
      | H : @eq string ?s ?s |- _ => clear H
      | H : @eq string ?s1 ?s2 |- _ => inversion H
      | H : @eq QTerm (pair ?t1 ?t2) (pair ?t1' ?t2') |- _ => apply pairInj in H; destruct H
      | H : @eq QTerm ?t1 ?t2 |- _ => first [
                                         rewrite beta in H ; compute_subst_in H
                                       | rewrite betapi1 in H
                                       | rewrite betapi2 in H                    
                                       | subst t1
                                       | subst t2 ]
      (* If we are trying to prove an equality involving functions that are not in QTerm,
         try just f_equaling them. Hopefully the user wanted that since its the goal where
         they ran this tactic. *)
      | |- @eq ?ty ?a ?b => (lazymatch ty with (* lazymatch is needed to make it actually fail *)
                             | QTerm => fail
                             | _ => try reflexivity; apply proveEqualityInParts
                             end)
      | |- @eq QTerm ?a ?b => first [ reflexivity]
      | H : _ |- _ => first [
                   rewrite beta in H ; compute_subst_in H
                 | rewrite betapi1 in H ; compute_subst_in H
                 | rewrite betapi2 in H ; compute_subst_in H
                 ]
      | |- _ =>
          hide_evars_in_goal;
          first [
              rewrite beta ; compute_subst
            | rewrite betapi1 ; compute_subst
            | rewrite betapi2 ; compute_subst
            ];
          unhide_evars_in_goal
      end
    )
.

Ltac lambda_solve := repeat lambda_solve_step.

Theorem test_10
        (a b : QTerm)
  : <x `a> = <x `b>.
Proof.
  lambda_solve.
Abort.

Theorem test_lambda_solve_0
        (t : QTerm)
  : <fun x => `t> = <fun y => `t>.
Proof.
  lambda_solve.
Abort. (* This shouldn't be true, because t could have x or y in it. *)


Theorem test_lambda_solve_1
        (t : QTerm)
  : <fun x => `t [x]> = <fun y => `t [y]>.
Proof.
  repeat lambda_solve.
Qed.

Theorem test_lambda_solve
        (t1 t2 : QTerm)
        (H1 : <fun x => `t1 [x]> = <fun x => `t2 [x]>)
  : <fun x => `t1[x]> = <fun y => `t2[y]>.
Proof.
  lambda_solve.
  apply liftInj in H1.
  rewrite H1.
  reflexivity.
Qed.

Theorem test_lambda_solve_2
        (t : QTerm)
        (H : <(fun x => x) `t> = < (fun x => x) (fun x => x)>)
        : <`t `t> = <`t>.
Proof.
  lambda_solve.
Qed.

Theorem test_lambda_solve_3
        (t1 t2 : QTerm)
        (P : QTerm -> Prop)
        (H : t1 = t2)
  : P t1 = P t2.
Proof.
  lambda_solve.
Qed.

Theorem test2 : <fun x => x> = <fun y => y>.
Proof.
  lambda_solve.
Qed.

Theorem test_shadowed_var : (lam "a" (var "a"%string 1)) = <fun x => a>.
Proof.
  lambda_solve.
Qed.

Theorem test_deeper_beta :
  <a> = <(fun x => fun y => a) b c>.
Proof.
  lambda_solve.
Qed.

(*https://coq-club.inria.narkive.com/cZ5X8JAw/making-tactic-that-return-a-value*)

Ltac print x := idtac x.

Ltac get_sub_to_make_anything term toBeMade nameRet indexRet subRet :=
  lazymatch term with
  | (var ?s ?i) => pose toBeMade as subRet; pose s as nameRet; pose i as indexRet
  | (app ?a ?b) => get_sub_to_make_anything a (lam "x" (lift "x" 0 toBeMade)) nameRet indexRet subRet
  end.

(* TODO: This is one of the main performance problems. I can make this much faster if I
make it work similar to the other neutral case, using PseudoNeutral. *)
Ltac solve_neutral_unequal_case :=
  match goal with
  | H : @eq QTerm ?l ?r |- _ =>
      let t1 := fresh "t1" in
      let t2 := fresh "t2" in
      let H2 := fresh "H" in
      destruct consistency as [t1 temp]; destruct temp as [t2 H2];
      let sub1 := fresh "sub1" in
      let sub2 := fresh "sub2" in
      let s1 := fresh "s1" in
      let s2 := fresh "s2" in
      let i1 := fresh "i1" in
      let i2 := fresh "i2" in
      get_sub_to_make_anything r t2 s2 i2 sub2;
      get_sub_to_make_anything l (lift s2 i2 t1) s1 i1 sub1;
      exfalso;
      apply H2;
      let fact := fresh "fact" in
      assert (subst s2 i2 sub2 (subst s1 i1 sub1 l) = subst s2 i2 sub2 (subst s1 i1 sub1 r)) as fact;
      repeat unfold s1, s2, i1, i2, sub1, sub2 in *;
      [
        rewrite H;
        reflexivity
      |
        normalize_in fact;
        repeat fix_subst_lifts_in fact;
        apply fact
      ]
  end.

(*Compute (ltac:(get_sub_to_make_anything <a> <b>)).*)

Theorem test_unequal_neutrals
  (H : <a b> = <c>)
    : False.
Proof.
  solve_neutral_unequal_case.
Qed.

Theorem test_shadowed_application
        (t : QTerm) :
  <(fun x => (fun x => `t [a] [x]) [x]) a b> = <`t [a]>.
Proof.
  normalize.
  fix_subst_lifts.
  reflexivity.
Qed.

Theorem test_unequal_neutrals_3
        (H : <a b c> = <d>)
  : False.
Proof.
  solve_neutral_unequal_case.
Qed.

Theorem test_unequal_neutral_another
        (H : <a> = <b c d e>)
  : False.
Proof.
  solve_neutral_unequal_case.
Qed.

(*
For now this will be an axiom. I will have to think about what property of the underlying
terms is needed to give this.
 *)

Inductive PseudoNeutral : QTerm -> Prop :=
| pn_var : forall s i, PseudoNeutral (var s i)
| pn_app : forall a b, PseudoNeutral a -> PseudoNeutral (app a b)
.

Inductive IncompatiblePseudoNeutral : QTerm -> QTerm -> Prop :=
| inc_var_app : forall s i a b, IncompatiblePseudoNeutral (var s i) (app a b)
| inc_app_var : forall s i a b, IncompatiblePseudoNeutral (app a b) (var s i)
| inc_var_var : forall s1 i1 s2 i2, not (s1 = s2 /\ i1 = i2)
                                    -> IncompatiblePseudoNeutral (var s1 i1) (var s2 i2)
.

Axiom neutralInj : forall a b c d,
    PseudoNeutral a -> PseudoNeutral c -> app a b = app c d <-> a = c /\ b = d.

Axiom neutralContradiction : forall t1 t2,
    PseudoNeutral t1 -> PseudoNeutral t2 -> IncompatiblePseudoNeutral t1 t2
    -> False.

Ltac neutral_inj_case :=
  match goal with
  | H : app ?a ?b = app ?c ?d |- _ =>
      apply neutralInj in H; [ | solve [repeat constructor] | solve [repeat constructor]];
      destruct H
  | |- app ?a ?b = app ?c ?d =>
      apply neutralInj; [solve [repeat constructor] | solve [repeat constructor] | ] ; split
  end.

Theorem application_injective_test
        (a b : QTerm)
        (H : <c `a x> = <c `b x>)
  : a = b.
Proof.
  repeat neutral_inj_case.
  assumption.
Qed.

Theorem application_injective_goal_test
        (a b c d : QTerm)
  : <CONST `a `b> = <CONST `c `d>.
Proof.
  repeat neutral_inj_case.
  reflexivity.
Abort.

Ltac fast_neutral_unequal_case :=
  match goal with
  | H : ?t1 = ?t2 |- _ =>
      exfalso;
      (*
      apply (neutralContradiction t1 t2);
      repeat constructor*)
      exact (neutralContradiction t1 t2 ltac:(repeat constructor)
                            ltac:(repeat constructor) ltac:(repeat constructor))
  end.

Theorem test_unequal_neutrals_3_v2
        (H : <a b c> = <d>)
  : False.
Proof.
  (*Time solve_neutral_unequal_case.*)
  Time fast_neutral_unequal_case.
Qed.

Theorem test_unequal_neutral_another_v2
        (H : <a> = <b c d e>)
  : False.
Proof.
  (*Time solve_neutral_unequal_case.*)
  Time fast_neutral_unequal_case.
Qed.

Theorem test_fast_fails_correctly
        (H : <(fun x => x) a> = <b>)
  : True.
Proof.
  Fail fast_neutral_unequal_case.
  auto.
Qed.
(*
Another case that I need to figure out is when I want to apply a function to an argument,
where the types only line up up to lambda_solve.
 *)

Definition type_of {T : Type} (t : T) := T.

Theorem cast {A B : Type} (a : A) (p : A = B) : B.
Proof.
  intros.
  rewrite <- p.
  assumption.
Qed.

(* See https://stackoverflow.com/questions/69229094/is-it-possible-to-turn-unification-errors-into-goals-in-coq
for a library that already has something like this *)
Ltac apply_cast H :=
  let H' := fresh "H'" in
  pose H as H';
  repeat (
      match type of H' with
      | forall x : ?T, ?rest => let x := fresh "argument" in
                                evar (x : T);
                                specialize (H' x);
                                unfold x in H';
                                clear x
      end
    );
  apply (cast H');
  clear H'.

(*
NOTE: There is a potential big problem here: if one of the evars that gets instantiated as an
argument is a QTerm, then doing something like rewrite lift_lam on an evar will specialize that
evar to be a lambda! This will create nonsense and also infinite loops.
*)

Theorem test_function_application_solve_types
        (P : nat -> string -> QTerm -> Type)
        (x : forall n s, P n s (<(fun x => x) (fun x => x)>))
        (y : nat)
  : P 10 "a"%string <fun y => y>.
Proof.
  apply_cast x.
  lambda_solve.
Qed.

(*
Plan for tactic to solve pattern cases:
First, start with the non-pair case.
- make a tactic which can try to take a term, and rewrite it in the form t[x] for some given x.
 *)

Search (nat -> nat -> Prop).
Locate "<>".
(*
The ideas is that UnWeaken t1 s i t2 -> t1 = t2 [s@i]
I only need this to work for patterns like t [x...r] x y (z, w) (q, r) = t2,
where t is a metavar, and the rest are vars.
 *)
Check lift_lift.
Inductive UnWeaken : QTerm -> string -> nat -> QTerm -> Prop :=
| uw_lift_itself : forall t s i, UnWeaken (lift s i t) s i t
| uw_other_var : forall s1 i1 s2 i2, (or (s1 <> s2) (lt i1 i2)) -> UnWeaken (var s1 i1) s2 i2 (var s1 i1)
| uw_app : forall t1 t2 t1' t2' s i,
    UnWeaken t1 s i t1'
    -> UnWeaken t2 s i t2'
    -> UnWeaken (app t1 t2) s i (app t1' t2')
| uw_pair : forall t1 t2 t1' t2' s i,
    UnWeaken t1 s i t1'
    -> UnWeaken t2 s i t2'
    -> UnWeaken (pair t1 t2) s i (pair t1' t2')
| uw_lift_lift : forall t t' s1 i1 s2 i2,
    eqb s2 s1 = false \/ Nat.eqb i1 i2 = false (* if they are equal, then other constructor handles it*)
    -> UnWeaken t s2 (if (eqb s2 s1) then if (Nat.ltb i1 i2) then pred i2 else i2 else i2) t'
    (*UnWeaken t s2 (if (eqb s2 s1)
                   then if (Nat.ltb i1 i2) then pred i2 else
                          if Nat.eqb i1 i2 then 15 else 20(*i2*)
                   else i2) t'*)
             (* some conditions relating s1 s2 i1 i2*)
    -> UnWeaken (lift s1 i1 t)
                (* This chunk is from lift_lift*)
                s2
                i2
                (lift s1
                      (if (eqb s2 s1) then if (Nat.ltb i1 i2) then i1 else pred i1 else i1)
                      (*(if (eqb s2 s1)
                       then if (Nat.ltb i1 i2) then i1 else if Nat.eqb i1 i2 then i1 else 30(*pred i1*)
                       else i1)*)
                      t')

.

Theorem nat_gt_lt_lemma : forall a b, Nat.ltb a b = false -> Nat.eqb a b = false
                                      -> Nat.ltb (Nat.pred a) b = false
                                         /\ S (pred a) = a.
Proof.
  intros.
  apply PeanoNat.Nat.ltb_nlt in H.
  apply PeanoNat.Nat.eqb_neq in H0.
  rewrite PeanoNat.Nat.ltb_nlt.
  lia.
Qed.

Theorem UnWeaken_prop : forall {t1 s i t2}, UnWeaken t1 s i t2 -> lift s i t2 = t1.
Proof.
  intros.
  induction H.
  - reflexivity.
  - normalize.
    Check eqb_neq.
    destruct H.
    + 
      assert ((s2 =? s1)%string = false). {
        rewrite eqb_neq.
        easy.
      }
      rewrite H0.
      simpl.
      reflexivity.
    +
      Search [lt Nat.ltb].
      Check PeanoNat.Nat.ltb_lt.
      assert ((Nat.ltb i1 i2)%bool = true). {
        rewrite PeanoNat.Nat.ltb_lt.
        assumption.
      }
      rewrite H0.
      simpl.
      Search (andb).
      rewrite Bool.andb_false_r.
      reflexivity.
  - lambda_solve.
    normalize.
    reflexivity.
  - subst.
    normalize.
    reflexivity.
  - subst t.
    Check lift_lift.
    rewrite lift_lift.
    destruct (eqb s2 s1).
    + destruct (Nat.ltb i1 i2) eqn:F.
      * rewrite F.
        reflexivity.
      * Check PeanoNat.Nat.lt_lt_pred.
        destruct H; try easy.
        -- destruct (nat_gt_lt_lemma _ _ F H).
           rewrite H1, H2.
           reflexivity.
    + reflexivity.
Qed.

(* rewrites a premise (t1 x = t2) into (t1' [x] x = t2*)
Ltac simple_pattern_case :=
  match goal with
  | H : qterm.app ?t1 (var ?s ?i) = ?t2 |- _ =>
      let unweaken := fresh "unweaken" in
      let t1' := open_constr:((_:QTerm)) in
      assert (UnWeaken t1 s i t1') as unweaken; [
        solve [repeat (constructor; try easy)]
        |
          try rewrite <- (UnWeaken_prop unweaken) in *;
          clear unweaken
        ];
      simpl in H;
      apply pattern_direction1 in H
  (*
  | H : qterm.app ?t1 (pair ?l ?r) = ?t2 |- _ =>
      let t' := fresh "t'" in
      let F := fresh "F" in
      pose (t' := <fun x => fun y => `t1 [x] [y] (x, y)>);
      assert (t1 = <fun p => `t' [p] (proj1 p) (proj2 p)>); [
          subst t';
          normalize;
          rewrite <- SP;
          rewrite <- eta;
          reflexivity
        |
          
        ]
   *)
  end.

Theorem pattern_case_first_test
        (t1 t2 : QTerm)
        (H : <`t1 [x] C1 C2 x> = t2)
  : <`t1 C1 C2> = <fun x => `t2>.
Proof.
  simple_pattern_case.
  easy.
Qed.


(* Might I as not well just use this kind of approach to do the whole thing at once?
Something like PatternCase : QTerm -> 
PatternCase t1 x t2 res -> (t1 = t2 -> x = res)
Where x is the metavar all the way at the left?
I'll at least do the simpler version first.
 *)

Ltac constructor_loop :=
  constructor; solve [easy; constructor_loop].

Theorem pattern_case
        (t1 t2 : QTerm)
        (H : <`t1 [x] x> = t2)
  : t1 = <fun x => `t2>.
Proof.
  simple_pattern_case.
  assumption.
Qed.

Theorem pattern_case_2
        (t1 t2 : QTerm)
        (H : <`t1 [x] [y] x> = t2)
  : <`t1 [y]> = <fun x => `t2>.
Proof.
  simple_pattern_case.
  assumption.
Qed.

Theorem pattern_case_3
        (t1 t2 : QTerm)
        (H : <`t1 [y] [x] x y> = t2)
  : <`t1> = <fun x => fun y => `t2>.
Proof.
  simple_pattern_case.
  simple_pattern_case.
  assumption.
Qed.

Theorem pattern_case_4
        (t1 t2 : QTerm)
        (H : <{lift "x" 1 <`t1 [x]>} x> = t2)
  : <`t1 [x]> = <fun x => `t2>.
Proof.
  simple_pattern_case.
  assumption.
Qed.

Theorem pattern_case_5
        (t1 t2 : QTerm)
        (H: <`t1 [x] x x> = t2)
  : True.
  Fail simple_pattern_case. (* testing to make sure it doesn't change the proof state. *)
  auto.
Qed.

(*
If FindSubTo t1 t2 sub, then sub t1 = t2.
*)
Check subst.
Inductive FindSubTo : QTerm -> QTerm -> (QTerm -> QTerm) -> Prop :=
| fst_var : forall i s out, FindSubTo (var s i) out (subst s i out)
(* It should be possible to handle fst and snd cases if I need to *)
| fst_pair : forall t1 t2 out sub1 sub2,
    FindSubTo t1 <proj1 `out> sub1
    -> FindSubTo (sub1 t2) <proj2 `out> sub2
    (*-> FindSubTo t2 <proj2 `out> sub2*)
    -> FindSubTo (pair t1 t2) out (fun t => sub2 (sub1 t))
.

Ltac pair_pattern_case :=
  match goal with
  | H : ?t1 (pair ?l ?r) = ?t3 |- _ =>
      let temp := fresh "temp" in
      let sub := open_constr:((_:QTerm -> QTerm)) in
      apply (f_equal (fun t => <`t [p]>)) in H;
      compute_subst_in H;
      assert (FindSubTo (pair l r) <p> sub) as temp; [
          repeat (compute_subst; constructor)
        |
          apply (f_equal (fun t => sub t)) in H;
          compute_subst_in H;
          repeat rewrite <- SP in H;
          clear temp
        ]
  end.

(*
The above pair_pattern_case tactic kind of works.
However, it leaves behind substitutions. The idea is that if
t1 (x, y) = t2, then
t1 = \p. t2 [x / fst p] [y / snd p]
The issue is that the automation in lambda_solve isn't really designed for substituions to be more than
ephemeral; they are supposed to be gone after compute_substs.
The problem shows up in pattern_case_pair_2, where the substitutions can't be dealt with.

Instead, I'm going to try, given:
t1 ... (a, b) = t2,
substitute  t1 := fun ... p => t1' ... (fst p) (snd p)
globally substitute out t1, and just work with t1' instead.
*)

(*
Given something like (t a b c), and given evars original, new, and toSub,
FindPairCaseSub (t a b c) original new toSub
->
original = t
toSub = fun a b c p => new a b c (fst p) (snd p)
new = fun a b c l r => original a b c (l, r)

and we get as a theorem that original = toSub


(t a b c) => find t' such that t = fun a b c p => t' a b c (fst p) (snd p)
(t a b) =>   find t' such that t = fun a b   p => t' a b   (fst p) (snd p)
 *)
(*
Inductive FindPairCaseSub : QTerm -> QTerm -> QTerm -> QTerm -> Prop :=
| fpcs_app : forall,
    FindPairCaseSub rest original new toSub
    -> FindPairCaseSub (app rest arg) original new <fun x => `toSub [x] x>
.
 *)
(*
GetMVAndArgs (t [x] a [y] b c) t [a, x, b, y, c]
 *)
Inductive GetMVAndArgs : QTerm -> QTerm -> list (QTerm + (string * nat)) -> Prop :=

.

Theorem pattern_case_pair
        (t1 t2 : QTerm)
        (H : <`t1 [x] [y] (x, y)> = t2)
  : <`t1> = <fun p => `t2 [p] [x/ proj1 p] [y / proj2 p]>.
Proof.
  pair_pattern_case.
  Time simple_pattern_case.
  assumption.
Qed.  

Theorem pattern_case_pair_2
        (t1 t2 : QTerm)
        (H : <`t1 [x] [y] [z] [w] (x, y) (z, w)> = t2)
  : <`t1> = <fun p1 => fun p2 => `t2 [p1] [p2] [x/ proj1 p1] [y / proj2 p1] [z / proj1 p2] [z / proj2 p2]>.
Proof.
  pair_pattern_case.
  simple_pattern_case.
  pair_pattern_case.
  simple_pattern_case.
  compute_subst_in H.
  subst.
  lambda_solve.
  (*
    The problem is that there are substs that will stick around.
    I didn't really design the automation to handle that; instead, metavars are supposed to
    be in closed scope.
   *)
Abort.
(*
So the pair case needs to be fixed to work more generally.
For now though, I'll just work with it.
*)

(* Pi injectivity should work, but I think it requires the special cases *)
Theorem pi_injectivity
        (A B A' B': QTerm)
        (H : <fun env => Pi (`A [env] env) (fun a => `B [env] [a] (env, a))>
           = <fun env => Pi (`A' [env] env) (fun a => `B' [env] [a] (env, a))>)
  : A = A' /\ B = B'.
  lambda_solve.
  repeat neutral_inj_case.
  lambda_solve.
  simple_pattern_case.
  lambda_solve.
  Time pair_pattern_case.
  simple_pattern_case.
  lambda_solve.
  repeat rewrite <- eta.
  auto.
Qed.
(* TODO: This needs to work. *)

Theorem simpler_thing_that_is_needed_first
        (t1 t2 : QTerm)
        (H : <fun x => `t1 [x]> = <fun x => `t2 [x]>)
  : t1 = t2.
Proof.
  lambda_solve.
  apply (f_equal (fun t => <`t [x/DUMMY]>)) in H.
  normalize_in H.
  assumption.
  (* TODO: This needs to work as part of lambda_solve*)
Qed.

(*
Idea to maybe improve performance:
Could I wrap lambda_solve in a procedure which makes a local theorem, uses lambda_solve,
and then finishes the theorem with Qed so that the proof term is not remembered?
That way it would not have such long equality proof terms in things.
Does this still sneak the term in there somewhere?
*)


(* Testing hide_evars_in_goal *)

Theorem test_hide_evars (t : QTerm) :
  <`t A> = <B>.
Proof.
  evar (et : QTerm).
  assert (t = et) by give_up.
  rewrite H.
  unfold et.
  hide_evars_in_goal.
  Fail rewrite beta.
Abort.
(* So it works in this situation. But what if the evar resulted from another goal rather
than being user defined? *)

Definition evar_maker2 {t : QTerm}
           (H : <`t A> = <(fun x => x) B>)
  : True := I.

Theorem test_hide_evars_2 : True.
Proof.
  refine (evar_maker2 _).
  Print hide_evars_in_goal.
  (* This is a possible solution. Would be very annoying though to redo
    all the rewrites like this. *)
  repeat match goal with
  | |-  context [ app (lam ?x ?body) ?t2 ] => rewrite (@beta x body t2)
  end.
  hide_evars_in_goal.
  Fail Fail rewrite beta.
  (* It doesn't work!!!! I'm not sure how to fix this.*)
Abort.

Theorem equality : 1 + 1 = 2. Proof. reflexivity. Qed.

Definition evar_maker (n : nat) (H : 1 + n = 2) : True := I.
Theorem testRewrite' : True.
Proof.
  refine (evar_maker _ _).
  (* Here the goal is "1 + ?Goal = 2"
     the rewrite specializes ?Goal to 1*)
  (*pose (H := ?Goal).*)
  Fail Fail rewrite equality.
Abort.
