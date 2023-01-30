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

From shack Require Import lang progdef subtype ok.
From shack Require Import eval heap modality interp typing.
From shack.soundness Require Import defs.

Section proofs.
  (* assume a given set of class definitions and their SDT annotations. *)
  Context `{SDTCVS: SDTClassVarianceSpec}.

  (* Iris semantic context *)
  Context `{!sem_heapGS Θ}.

  Lemma sub_soundness C cdef Δ kd Γ rigid Γ0 Γ1 c:
    wf_cdefs pdefs →
    wf_lty Γ →
    bounded_lty rigid Γ →
    Forall wf_constraint Δ →
    Forall (bounded_constraint rigid) Δ →
    pdefs !! C = Some cdef →
    lty_sub Δ kd Γ1 Γ0 →
    bounded_lty rigid Γ0 →
    cmd_has_ty C Δ kd rigid Γ c Γ1 →
    ∀ t0 t0def Σt0 σ0,
    pdefs !! t0 = Some t0def →
    length Σt0 = length t0def.(generics) →
    inherits_using t0 C σ0 →
    ∀ Σ st st' n,
    length Σ = rigid →
    rigid ≥ length cdef.(generics) →
    cmd_eval C st c st' n →
    let Σthis := interp_exact_tag interp_type t0 Σt0 in
    ⌜interp_list interp_nothing Σt0 σ0 ≡ take (length cdef.(generics)) Σ⌝ -∗
    □ interp_env_as_mixed Σt0 -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis Σ Δ -∗

    □ (⌜wf_lty Γ⌝ →
       ⌜bounded_lty rigid Γ⌝ →
       ⌜Forall wf_constraint Δ⌝ →
       ⌜Forall (bounded_constraint rigid) Δ⌝ →
       ∀ Σ st st' n
       (_: length Σ = rigid)
       (_: rigid ≥ length (generics cdef))
       (_: cmd_eval C st c st' n),
       ⌜interp_list interp_nothing Σt0 σ0 ≡ take (length cdef.(generics)) Σ⌝ -∗
       □ interp_env_as_mixed Σt0 -∗
       □ interp_env_as_mixed Σ -∗
       □ Σinterp (interp_exact_tag interp_type t0 Σt0) Σ Δ -∗
       heap_models st.2 ∗
         interp_local_tys (interp_exact_tag interp_type t0 Σt0) Σ Γ st.1 -∗
       |=▷^n heap_models st'.2 ∗
         interp_local_tys (interp_exact_tag interp_type t0 Σt0) Σ Γ1 st'.1) -∗

    heap_models st.2 ∗ interp_local_tys Σthis Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σthis Σ Γ0 st'.1.
  Proof.
    move => wfpdefs wflty blty hΔ hΔb hcdef hsub hb h.
    move => t0 t0def Σt0 σ0 ht0def hlenΣt0 hin_t0_C.
    move => Σ st st' n hrigid hge hc Σthis.
    iIntros "%hΣeq #hΣt0 #hΣ #hΣΔ #HI H".
    iSpecialize ("HI" $! wflty blty hΔ hΔb).
    iSpecialize ("HI" $! Σ _ _ _ hrigid hge hc hΣeq with "hΣt0 hΣ hΣΔ H").
    iApply updN_mono_I; last done.
    iIntros "[Hh #Hrty]".
    iFrame.
    iAssert (□ interp_as_mixed Σthis)%I as "#hΣthis".
    { iModIntro; iIntros (w) "hw".
      iLeft; iRight; iRight.
      iExists t0, Σt0, t0def; iSplit; first done.
      by iApply (exact_subtype_is_inclusion_aux with "hΣt0 hw").
    }
    iDestruct (interp_local_tys_is_inclusion with "hΣthis hΣ hΣΔ Hrty") as "Hrty'" => //; try by apply wfpdefs.
    + apply cmd_has_ty_wf in h; try (assumption || by apply wfpdefs).
    + rewrite Forall_forall => i hi v.
      by apply _.
  Qed.
End proofs.
