(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
From stdpp Require Import base strings gmap stringmap fin_maps.
From iris.base_logic Require Import upred derived.
From iris.base_logic.lib Require Import iprop own.
From iris.algebra Require Import ofe cmra gmap_view.
From iris.proofmode Require Import tactics.

From shack Require Import lang progdef subtype typing eval heap modality interp.

Section proofs.
  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.

  (* Iris semantic context *)
  Context `{!sem_heapGS Θ}.

  Hypothesis Δsdt_wf: ∀ A vars σ, Forall wf_ty σ → Forall wf_constraint (Δsdt A vars σ).
  Hypothesis Δsdt_subst_ty: ∀ A vars σ0 σ,
    subst_constraints σ (Δsdt A vars σ0) = Δsdt A vars (subst_ty σ <$> σ0).
  Hypothesis Δsdt_bounded: ∀ A vars σ n,
    Forall (bounded n) σ →
    Forall (bounded_constraint n) (Δsdt A vars σ).

  Lemma expr_soundness (Δ: list constraint) rigid (Σ: list (interp Θ)) kd e Γ Ω ty val :
    map_Forall (λ _, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _, wf_cdef_mono) pdefs →
    Forall wf_constraint Δ →
    wf_lty Γ →
    expr_eval Ω e = Some val →
    expr_has_ty Δ Γ rigid kd e ty →
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σ Δ -∗
    interp_local_tys Σ Γ Ω -∗
    interp_type ty Σ val.
  Proof.
    move => ??? wflty he h; move: Ω val he.
    induction h as [| | | kd op e1 e2 hop he1 hi1 he2 hi2 |
        kd op e1 e2 hop he1 hi1 he2 hi2 | kd e1 e2 h1 hi1 h2 hi2 | kd e0 h hi |
        kd v vty hv | | kd exp S T hS hi hwf hok hsub | kd exp S T hS hi hwf hok hsub]
        => Ω val he; iIntros "#wfΣ #Σcoherency #Hlty".
    - inv he; rewrite interp_type_unfold /=; by eauto.
    - inv he; rewrite interp_type_unfold /=; by eauto.
    - inv he; rewrite interp_type_unfold /=; by eauto.
    - inv he.
      case heq1 : (expr_eval Ω e1) => [v1 | ]; rewrite heq1 in H0; last by done.
      apply hi1 in heq1.
      iDestruct (heq1 with "wfΣ Σcoherency Hlty") as "hv1".
      rewrite interp_type_unfold /=.
      iDestruct "hv1" as (z1) "%hz1".
      rewrite hz1 in H0.
      case heq2 : (expr_eval Ω e2) => [v2 | ]; rewrite heq2 in H0; last by done.
      apply hi2 in heq2.
      iDestruct (heq2 with "wfΣ Σcoherency Hlty") as "hv2".
      rewrite interp_type_unfold /=.
      iDestruct "hv2" as (z2) "%hz2".
      rewrite hz2 in H0.
      case: H0 => <-.
      rewrite interp_type_unfold /= /interp_int.
      move: hop; rewrite /is_bool_op; destruct op => //= _; by iExists _.
    - inv he.
      case heq1 : (expr_eval Ω e1) => [v1 | ]; rewrite heq1 in H0; last by done.
      apply hi1 in heq1.
      iDestruct (heq1 with "wfΣ Σcoherency Hlty") as "hv1".
      rewrite interp_type_unfold /=.
      iDestruct "hv1" as (z1) "%hz1".
      rewrite hz1 in H0.
      case heq2 : (expr_eval Ω e2) => [v2 | ]; rewrite heq2 in H0; last by done.
      apply hi2 in heq2.
      iDestruct (heq2 with "wfΣ Σcoherency Hlty") as "hv2".
      rewrite interp_type_unfold /=.
      iDestruct "hv2" as (z2) "%hz2".
      rewrite hz2 in H0.
      case: H0 => <-.
      rewrite interp_type_unfold /= /interp_bool.
      move: hop; rewrite /is_bool_op; destruct op => //= _; by iExists _.
    - inv he.
      case heq1 : (expr_eval Ω e1) => [v1 | ]; rewrite heq1 in H0; last by done.
      apply hi1 in heq1.
      iDestruct (heq1 with "wfΣ Σcoherency Hlty") as "hv1".
      rewrite interp_type_unfold /=.
      iDestruct "hv1" as (b1) "%hb1".
      rewrite hb1 in H0.
      case heq2 : (expr_eval Ω e2) => [v2 | ]; rewrite heq2 in H0; last by done.
      apply hi2 in heq2.
      iDestruct (heq2 with "wfΣ Σcoherency Hlty") as "hv2".
      rewrite interp_type_unfold /=.
      iDestruct "hv2" as (b2) "%hb2".
      rewrite hb2 in H0.
      case: H0 => <-.
      rewrite interp_type_unfold /= /interp_bool.
      by iExists _.
    - inv he.
      case heq : (expr_eval Ω e0) => [v0 | ]; rewrite heq in H0; last by done.
      apply hi in heq.
      iDestruct (heq with "wfΣ Σcoherency Hlty") as "hv".
      rewrite interp_type_unfold /=.
      iDestruct "hv" as (b) "%hb".
      rewrite hb in H0.
      case: H0 => <-.
      rewrite interp_type_unfold /= /interp_bool.
      by iExists _.
    - inv he.
      iDestruct "Hlty" as "[? Hlty]".
      iDestruct ("Hlty" with "[//]") as (?) "[% H]".
      rewrite H0 in H; by case: H => ->.
    - inv he.
      iDestruct "Hlty" as "[Hthis Hv]".
      rewrite /interp_this_type interp_this_unseal /interp_this_def /=.
      iDestruct "Hthis" as (?? thisdef tdef ????) "[%H [#hmixed [#hconstr [#hinst [hdyn hloc]]]]]".
      destruct H as ([= <-] & hthisdef & htdef & hl & ? & hin & hfields & hdom).
      rewrite /this_type interp_class_unfold //=; last first.
      { by apply wflty. }
      destruct Γ as [[this σthis] Γ]; simpl in *.
      iExists _,t,thisdef,tdef,_, _, _, _.
      iSplit; first done.
      iSplit; first by iApply "hmixed".
      iSplit; first by iApply "hconstr".
      iSplit; last by iSplit.
      iModIntro; iNext.
      iClear "wfΣ Σcoherency hmixed hdyn hloc Hv".
      assert (hl0 : length thisdef.(generics) = length σ).
      { apply inherits_using_wf in hin => //.
        destruct hin as (?&?&?&h).
        by inv h; simplify_eq.
      }
      assert (hl1: length σ = length σthis).
      { rewrite /interp_list !fmap_length in hl.
        by rewrite hl.
      }
      move : hl0 hl1.
      generalize thisdef.(generics); clear.
      move => l hl0 hl1.
      iInduction l as [ | hd tl hi] "IH" forall (σ σthis hl0 hl1) "hinst".
      { by destruct σ; destruct σthis. }
      destruct σ as [ | ty0 σ] => //=.
      destruct σthis as [ | ty1 σthis] => //=.
      case: hl0 => hl0.
      case: hl1 => hl1.
      rewrite list_equivI.
      iSplitL.
      + iSpecialize ("hinst" $! 0).
        rewrite /= option_equivI.
        destruct hd; iIntros (w).
        * iSplit; iIntros "h"; first by iRewrite -"hinst".
          by iRewrite "hinst".
        * iIntros "h"; by iRewrite -"hinst".
        * iIntros "h"; by iRewrite "hinst".
      + iApply "IH" => //.
        iModIntro; rewrite /interp_list list_equivI; iIntros (k).
        by iSpecialize ("hinst" $! (S k)).
    - apply hi in he.
      iApply subtype_is_inclusion => //.
      + by apply expr_has_ty_wf in hS.
      + by iApply he.
    - apply hi in he.
      iApply subtype_is_inclusion => //.
      + by apply expr_has_ty_wf in hS.
      + by iApply he.
  Qed.
End proofs.

Print Assumptions expr_soundness.
