Require Import choiceBase.
Require Import prog2.
Require Import pmatch.

Ltac evaluate_function solve_tactic :=
  repeat (
      unfold runProg;
      rewrite ?runProgDefinitionRet, ?runProgDefinitionRec, ?collectOptionDef;
      try (erewrite PmatchDef1 ; [| solve [solve_tactic] | solve [intros; solve_tactic]]);
      try (erewrite PmatchDef2 ; [|intros; solve [solve_tactic]]);
      try (erewrite PifDef1 ; [| solve [solve_tactic]]);
      try (erewrite PifDef2 ; [| intros; solve [solve_tactic]]);
      simpl
    ).

Ltac evaluate_function_in solve_tactic H :=
  repeat (
      unfold runProg in H;
      rewrite ?runProgDefinitionRet, ?runProgDefinitionRec, ?collectOptionDef in H;
      try (erewrite PmatchDef1 in H ; [| solve [solve_tactic] | solve [intros; solve_tactic]]);
      try (erewrite PmatchDef2 in H ; [|intros; solve [solve_tactic]]);
      try (erewrite PifDef1 in H ; [| solve [solve_tactic]]);
      try (erewrite PifDef2 in H ; [| intros; solve [solve_tactic]]);
      simpl in H
    ).
