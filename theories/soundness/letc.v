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

From shack Require Import lang progdef subtype eval heap modality interp.
From shack.soundness Require Import expr defs.

Section proofs.
  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.

  (* Iris semantic context *)
  Context `{!sem_heapGS Θ}.

  Lemma let_soundness C Δ kd rigid Γ lhs e ty:
    wf_cdefs pdefs →
    wf_lty Γ →
    Forall wf_constraint Δ →
    expr_has_ty Δ Γ rigid kd e ty →
    ∀ Σ st st' n,
    length Σ = rigid →
    cmd_eval C st (LetC lhs e) st' n →
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σ (<[lhs:=ty]> Γ) st'.1.
  Proof.
    move => wfpdefs ?? hty Σ st st' n hrigid hc.
    iIntros "hΣ hΣΔ".
    inv hc.
    iIntros "[? #Hle]".
    rewrite updN_zero /=.
    iFrame.
    iDestruct (expr_soundness with "hΣ hΣΔ Hle") as "#?" => //; try (by apply wfpdefs).
    by iApply interp_local_tys_update.
  Qed.
End proofs.
