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
From shack.soundness Require Import defs.

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

  Lemma sub_soundness C Δ kd Γ rigid Γ0 Γ1 c:
    wf_cdefs pdefs →
    wf_lty Γ →
    bounded_lty rigid Γ →
    Forall wf_constraint Δ →
    Forall (bounded_constraint rigid) Δ →
    lty_sub Δ kd Γ1 Γ0 →
    bounded_lty rigid Γ0 →
    cmd_has_ty C Δ kd rigid Γ c Γ1 →
    ∀ Σ st st' n,
    length Σ = rigid →
    cmd_eval C st c st' n →
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σ Δ -∗
    □ (⌜wf_lty Γ⌝ →
       ⌜bounded_lty rigid Γ⌝ →
       ⌜Forall wf_constraint Δ⌝ →
       ⌜Forall (bounded_constraint rigid) Δ⌝ →
       ∀ (a : list (interp Θ)) (a0 a1 : local_env * heap) (a2 : nat),
         ⌜length a = rigid⌝ -∗
         ⌜cmd_eval C a0 c a1 a2⌝ -∗
         □ interp_env_as_mixed a -∗
         □ Σinterp a Δ -∗
         heap_models a0.2 ∗ interp_local_tys a Γ a0.1 -∗
         |=▷^a2 heap_models a1.2 ∗ interp_local_tys a Γ1 a1.1) -∗
    heap_models st.2 ∗ interp_local_tys Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σ Γ0 st'.1.
  Proof.
    move => wfpdefs wflty blty hΔ hΔb hsub hb h Σ st st' n hrigid hc.
    iIntros "#hΣ #hΣΔ #HI".
    iIntros "H".
    iSpecialize ("HI" $! wflty blty hΔ hΔb _ _ _ _ hrigid with "[//] hΣ hΣΔ H").
    iApply updN_mono_I; last done.
    iIntros "[Hh #Hrty]". iFrame.
    iDestruct (interp_local_tys_is_inclusion with "hΣ hΣΔ Hrty") as "Hrty'" => //; try by apply wfpdefs.
    + apply cmd_has_ty_wf in h; try (assumption || by apply wfpdefs).
    + rewrite Forall_forall => i hi v.
      by apply _.
  Qed.
End proofs.
