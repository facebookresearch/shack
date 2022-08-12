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
From shack.soundness Require Import expr defs.

Section proofs.
  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.
  (* assume some SDT constraints and their properties *)
  Context `{SDTCS: SDTClassSpec}.

  (* Iris semantic context *)
  Context `{!sem_heapGS Θ}.

  (* Helping the inference with this notation that hides pdefs *)
  Local Notation "Δ ⊢ s <: t" := (@subtype _ _ Δ Plain s t) (at level 70, s at next level, no associativity).
  Local Notation "Δ ⊢ s <D: t" := (@subtype _ _ Δ Aware s t) (at level 70, s at next level, no associativity).

  Definition typ_of_rtk k :=
    match k with
    | RCTag t => ClassT t [] (* not used *)
    | RCInt => IntT
    | RCBool => BoolT
    | RCNull => NullT
    | RCNonNull => NonNullT
    end.

  Lemma rtc_prim_soundness C Δ kd rigid Γ0 Γ1 v tv rtk thn els:
    match rtk with
    | RCTag _ => False
    | _ => True
    end →
    wf_cdefs pdefs →
    wf_lty Γ0 →
    bounded_lty rigid Γ0 →
    Forall wf_constraint Δ →
    Forall (bounded_constraint rigid) Δ →
    ctxt Γ0 !! v = Some tv →
    cmd_has_ty C Δ kd rigid (<[v:=InterT tv (typ_of_rtk rtk)]> Γ0) thn Γ1 →
    cmd_has_ty C Δ kd rigid Γ0 els Γ1 →
    ∀ Σ st st' n,
    length Σ = rigid →
    cmd_eval C st (RuntimeCheckC v rtk thn els) st' n →
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σ Δ -∗
    □ ( ⌜wf_lty (<[v:=InterT tv (typ_of_rtk rtk)]> Γ0)⌝ →
        ⌜bounded_lty rigid (<[v:=InterT tv (typ_of_rtk rtk)]> Γ0)⌝ →
        ⌜Forall wf_constraint Δ⌝ →
        ⌜Forall (bounded_constraint rigid) Δ⌝ →
        ∀ (a : list (interp Θ)) (a0 a1 : local_env * heap) (a2 : nat),
          ⌜length a = rigid⌝ -∗
          ⌜cmd_eval C a0 thn a1 a2⌝ -∗
          □ interp_env_as_mixed a -∗
          □ Σinterp a Δ -∗
          heap_models a0.2 ∗
          interp_local_tys a (<[v:=InterT tv (typ_of_rtk rtk)]> Γ0) a0.1 -∗
          |=▷^a2 heap_models a1.2 ∗ interp_local_tys a Γ1 a1.1) -∗
    □ (⌜wf_lty Γ0⌝ →
       ⌜bounded_lty rigid Γ0⌝ →
       ⌜Forall wf_constraint Δ⌝ →
       ⌜Forall (bounded_constraint rigid) Δ⌝ →
       ∀ (a : list (interp Θ)) (a0 a1 : local_env * heap) (a2 : nat),
         ⌜length a = rigid⌝ -∗
         ⌜cmd_eval C a0 els a1 a2⌝ -∗
         □ interp_env_as_mixed a -∗
         □ Σinterp a Δ -∗
         heap_models a0.2 ∗ interp_local_tys a Γ0 a0.1 -∗
         |=▷^a2 heap_models a1.2 ∗ interp_local_tys a Γ1 a1.1) -∗
     heap_models st.2 ∗ interp_local_tys Σ Γ0 st.1 -∗
     |=▷^n heap_models st'.2 ∗ interp_local_tys Σ Γ1 st'.1.
  Proof.
    move => hkind wfpdefs wflty blty hΔ hΔb hv hthn hels Σ st st' n hrigid hc.
    iIntros "#hΣ #hΣΔ #Hthn #Hels".
    inv hc; last first.
    { iIntros "[Hh H]".
      iApply "Hels" => //.
      by iSplit.
    }
    iClear "Hels".
    iIntros "H".
    assert (hwf: wf_lty (<[v:=InterT tv (typ_of_rtk rtk)]> Γ0)).
    { apply insert_wf_lty => //.
      constructor; first by apply wflty in hv.
      destruct rtk; (by elim hkind || by constructor).
    }
    assert (hbounded: bounded_lty (length Σ) (<[v:=InterT tv (typ_of_rtk rtk)]> Γ0)).
    { apply insert_bounded_lty => //.
      constructor; first by apply blty in hv.
      destruct rtk; (by elim hkind || by constructor).
    }
    iModIntro; iNext.
    iApply ("Hthn" $! hwf hbounded hΔ hΔb with "[//]") => //.
    clear H8.
    iDestruct "H" as "[H #Hle]".
    iDestruct "Hle" as "[Hthis Hle]".
    iDestruct ("Hle" $! v with "[//]") as (?) "[%Hlev Hv]".
    destruct rtk; try (by elim hkind).
    - destruct H7 as (z & hz).
      rewrite Hlev in hz; simplify_eq.
      iFrame.
      iSplit => /=; first done.
      iIntros (w tw).
      rewrite lookup_insert_Some.
      iIntros "%Hw".
      destruct Hw as [[<- <-] | [hne hw]]; last by iApply "Hle".
      iExists (IntV z); rewrite Hlev; iSplitR; first done.
      rewrite interp_inter_unfold /=; iSplit; first done.
      rewrite !interp_type_unfold /=.
      by iExists z.
    - destruct H7 as (b & hb).
      rewrite Hlev in hb; simplify_eq.
      iFrame.
      iSplit => /=; first done.
      iIntros (w tw).
      rewrite lookup_insert_Some.
      iIntros "%Hw".
      destruct Hw as [[<- <-] | [hne hw]]; last by iApply "Hle".
      iExists (BoolV b); rewrite Hlev; iSplitR; first done.
      rewrite interp_inter_unfold /=; iSplit; first done.
      rewrite !interp_type_unfold /=.
      by iExists b.
    - rewrite /= Hlev in H7; simplify_eq.
      iFrame.
      iSplit => /=; first done.
      iIntros (w tw).
      rewrite lookup_insert_Some.
      iIntros "%Hw".
      destruct Hw as [[<- <-] | [hne hw]]; last by iApply "Hle".
      iExists NullV; rewrite Hlev; iSplitR; first done.
      rewrite interp_inter_unfold /=; iSplit; first done.
      by rewrite !interp_type_unfold.
    - simpl in H7.
      iFrame.
      iAssert (interp_local_tys Σ Γ0 st.1) as "#Hle_"; first by iSplit.
      iAssert (interp_type MixedT Σ val) as "Hmixed".
      { destruct wfpdefs.
        assert (hsub : Δ ⊢ tv <: MixedT) by apply SubMixed.
        iApply subtype_is_inclusion => //.
        by apply wflty in hv.
      }
      replace (interp_local_tys Σ (<[v:=InterT tv NonNullT]> Γ0) st.1) with
              (interp_local_tys Σ (<[v:=InterT tv NonNullT]> Γ0) (<[v := val]>st.1)); last first.
      { f_equal.
        destruct st as [[? ll] ?]; simpl in *.
        move : Hlev.
        rewrite /insert /local_env_insert /=; clear => h.
        f_equal.
        induction ll as [| s w ws Hs IH] using map_ind => //=.
        rewrite lookup_insert_Some in h.
        destruct h as [[-> ->] | [hneq hv]].
        * by rewrite insert_insert.
        * by rewrite insert_commute // IH.
      }
      iApply interp_local_tys_update => //.
      rewrite interp_mixed_unfold interp_inter_unfold.
      iSplit; first done.
      iDestruct "Hmixed" as "[? | %hnull]".
      { by rewrite interp_nonnull_unfold. }
      rewrite hnull in Hlev.
      by rewrite Hlev in H7.
  Qed.
End proofs.
