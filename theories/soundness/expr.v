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

From shack Require Import lang progdef subtype.
From shack Require Import eval heap modality interp typing.

Section proofs.
  (* assume a given set of class definitions and their SDT annotations. *)
  Context `{SDTCVS: SDTClassVarianceSpec}.

  (* Iris semantic context *)
  Context `{!sem_heapGS Θ}.

  Lemma expr_soundness (Δ: list constraint) rigid (Σthis: interp Θ)
    (Σ: list (interp Θ)) kd e Γ Ω ty val :
    map_Forall (λ _, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _, wf_cdef_mono) pdefs →
    map_Forall (λ _ : string, wf_cdef_constraints_wf) pdefs →
    map_Forall (λ _ : string, wf_cdef_constraints_no_this) pdefs →
    map_Forall (λ _ : string, wf_cdef_constraints_bounded) pdefs →
    Forall wf_constraint Δ →
    wf_lty Γ →
    expr_eval Ω e = Some val →
    expr_has_ty Δ Γ rigid kd e ty →
    □ interp_as_mixed Σthis -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis Σ Δ -∗
    interp_local_tys Σthis Σ Γ Ω -∗
    interp_type ty Σthis Σ val.
  Proof.
    move => ?????? wflty he h; move: Ω val he.
    induction h as [| | | kd op e1 e2 hop he1 hi1 he2 hi2 |
        kd op e1 e2 hop he1 hi1 he2 hi2 | kd e1 e2 h1 hi1 h2 hi2 |
        kd e0 h hi | kd v vty hv | | kd exp S T hS hi hwf hok hsub |
        kd exp S T hS hi hwf hok hsub | kd e t hwf hb hsub ]
        => Ω val he; iIntros "#wfThis #wfΣ #Σcoherency #Hlty".
    - case: he => <-; rewrite interp_type_unfold /=; by eauto.
    - case: he => <-; rewrite interp_type_unfold /=; by eauto.
    - case: he => <-; rewrite interp_type_unfold /=; by eauto.
    - simpl in he.
      case heq1 : (expr_eval Ω e1) => [v1 | ]; rewrite heq1 in he; last by done.
      apply hi1 in heq1.
      iDestruct (heq1 with "wfThis wfΣ Σcoherency Hlty") as "hv1".
      rewrite interp_type_unfold /=.
      iDestruct "hv1" as (z1) "%hz1".
      rewrite hz1 in he.
      case heq2 : (expr_eval Ω e2) => [v2 | ]; rewrite heq2 in he; last by done.
      apply hi2 in heq2.
      iDestruct (heq2 with "wfThis wfΣ Σcoherency Hlty") as "hv2".
      rewrite interp_type_unfold /=.
      iDestruct "hv2" as (z2) "%hz2".
      rewrite hz2 in he.
      case: he => <-.
      move: hop; rewrite /is_bool_op; destruct op => //= _; by iExists _.
    - simpl in he.
      case heq1 : (expr_eval Ω e1) => [v1 | ]; rewrite heq1 in he; last by done.
      apply hi1 in heq1.
      iDestruct (heq1 with "wfThis wfΣ Σcoherency Hlty") as "hv1".
      rewrite interp_type_unfold /=.
      iDestruct "hv1" as (z1) "%hz1".
      rewrite hz1 in he.
      case heq2 : (expr_eval Ω e2) => [v2 | ]; rewrite heq2 in he; last by done.
      apply hi2 in heq2.
      iDestruct (heq2 with "wfThis wfΣ Σcoherency Hlty") as "hv2".
      rewrite interp_type_unfold /=.
      iDestruct "hv2" as (z2) "%hz2".
      rewrite hz2 in he.
      case: he => <-.
      rewrite interp_type_unfold /= /interp_bool.
      move: hop; rewrite /is_bool_op; destruct op => //= _; by iExists _.
    - simpl in he.
      case heq1 : (expr_eval Ω e1) => [v1 | ]; rewrite heq1 in he; last by done.
      apply hi1 in heq1.
      iDestruct (heq1 with "wfThis wfΣ Σcoherency Hlty") as "hv1".
      rewrite interp_type_unfold /=.
      iDestruct "hv1" as (b1) "%hb1".
      rewrite hb1 in he.
      case heq2 : (expr_eval Ω e2) => [v2 | ]; rewrite heq2 in he; last by done.
      apply hi2 in heq2.
      iDestruct (heq2 with "wfThis wfΣ Σcoherency Hlty") as "hv2".
      rewrite interp_type_unfold /=.
      iDestruct "hv2" as (b2) "%hb2".
      rewrite hb2 in he.
      case: he => <-.
      by iExists _.
    - simpl in he.
      case heq : (expr_eval Ω e0) => [v0 | ]; rewrite heq in he; last by done.
      apply hi in heq.
      iDestruct (heq with "wfThis wfΣ Σcoherency Hlty") as "hv".
      rewrite interp_type_unfold /=.
      iDestruct "hv" as (b) "%hb".
      rewrite hb in he.
      case: he => <-.
      by iExists _.
    - simpl in he.
      iDestruct "Hlty" as "[? Hlty]".
      iDestruct ("Hlty" with "[//]") as (?) "[% H]".
      rewrite he in H; by case: H => ->.
    - case: he => <-.
      iDestruct "Hlty" as "[Hthis Hv]".
      by rewrite interp_type_unfold /=.
    - apply hi in he.
      iApply subtype_is_inclusion => //.
      + by apply expr_has_ty_wf in hS.
      + by iApply he.
    - apply hi in he.
      iApply subtype_is_inclusion => //.
      + by apply expr_has_ty_wf in hS.
      + by iApply he.
    - by iDestruct (inconsistency with "wfThis wfΣ Σcoherency") as "hFalse".
  Qed.
End proofs.

Print Assumptions expr_soundness.
