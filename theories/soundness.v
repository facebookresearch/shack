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
From shack.soundness Require Import getc setc newc call priv_call sub.
From shack.soundness Require Import rtc_tag rtc_prim.
From shack.soundness Require Import dyn_getc dyn_setc dyn_call.

Section proofs.
  (* assume a given set of class definitions and their SDT annotations. *)
  Context `{SDTCVS: SDTClassVarianceSpec}.

  (* Iris semantic context *)
  Context `{!sem_heapGS Θ}.

  Lemma cmd_soundness_ C Δ kd rigid Γ cmd Γ' :
    wf_cdefs pdefs →
    wf_lty Γ →
    bounded_lty rigid Γ →
    ok_ty Δ (this_type Γ) →
    Forall wf_constraint Δ →
    Forall (bounded_constraint rigid) Δ →
    cmd_has_ty C Δ kd rigid Γ cmd Γ' →
    ∀ Σ st st' n,
    length Σ = rigid →
    cmd_eval C st cmd st' n →
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σ Γ st.1 -∗ |=▷^n
        heap_models st'.2 ∗ interp_local_tys Σ Γ' st'.1.
  Proof.
    move => wfpdefs wflty blty hokthis hΔ hΔb.
    iLöb as "IH" forall (C Δ kd rigid Γ cmd Γ' wflty blty hokthis hΔ hΔb).
    iIntros "%hty" (Σ st st' n hrigid hc) "#hΣ #hΣΔ".
    iInduction hty as [ Γ Δ kd rigid |
        Δ kd rigid Γ0 Γ1 hthis hwf |
        Δ kd rigid Γ1 Γ2 Γ3 fstc sndc hfst hi1 hsnd hi2 |
        Δ kd rigid Γ lhs e ty he |
        Δ kd rigid Γ1 Γ2 cond thn els hcond hthn hi1 hels hi2 |
        Δ kd rigid Γ lhs t targs name fty hrecv hf |
        Δ kd rigid Γ lhs recv t targs name fty orig hrecv hf |
        Δ kd rigid Γ fld rhs fty t σ hrecv hf hrhs |
        Δ kd rigid Γ recv fld rhs fty orig t σ hrecv hrhs hf |
        Δ kd rigid Γ lhs t otargs targs args fields htargs hwf hb hok hf hdom harg |
        Δ kd rigid Γ lhs recv t targs name orig mdef args hrecv hhasm hvis hdom hi |
        Δ kd rigid Γ lhs t targs name mdef args hrecv hhasm hvis hdom hi |
        Δ kd rigid Γ c Γ0 Γ1 hsub hb h hi |
        Δ kd rigid Γ0 Γ1 v tv t def thn els hv hdef hthn hi0 hels hi1 |
        Δ kd rigid Γ0 Γ1 v tv thn els hv hthn hi0 hels hi1 |
        Δ kd rigid Γ0 Γ1 v tv thn els hv hthn hi0 hels hi1 |
        Δ kd rigid Γ0 Γ1 v tv thn els hv hthn hi0 hels hi1 |
        Δ kd rigid Γ0 Γ1 v tv thn els hv hthn hi0 hels hi1 |
        Δ kd rigid Γ1 Γ2 cond thn els hcond hthn hi1 hels hi2 |
        Δ kd rigid Γ lhs recv name he hnotthis |
        Δ kd rigid Γ recv fld rhs hrecv hrhs hnotthis |
        Δ kd rigid Γ lhs recv name args hrecv hi hnotthis |
        Δ kd rigid Γ0 cmd Γ1 hthis hwf hb hsub
      ] "IHty" forall (Σ st st' n hrigid hc) "hΣ hΣΔ".
    - (* Skip *)
      inv hc.
      rewrite updN_zero.
      by iIntros "?".
    - (* Error *) by inv hc.
    - (* Seq *)
      inv hc. iIntros "H".
      iSpecialize ("IHty" $! wflty blty hokthis hΔ hΔb Σ _ _ _ refl_equal with "[//] hΣ hΣΔ H").
      rewrite Nat.iter_add.
      iApply (updN_mono_I with "[] IHty").
      destruct wfpdefs.
      iApply "IHty1" => //.
      + by apply cmd_has_ty_wf in hfst.
      + by apply cmd_has_ty_bounded in hfst.
      + by apply cmd_has_ty_preserves_this in hfst as <-.
    - (* Let *)
      inv hc.
      iIntros "[? #Hle]".
      rewrite updN_zero /=.
      iFrame.
      iDestruct (expr_soundness with "hΣ hΣΔ Hle") as "#?" => //; try (by apply wfpdefs).
      by iApply interp_local_tys_update.
    - (* If *)
      inv hc.
      + iIntros "H". by iApply "IHty".
      + iIntros "H". by iApply "IHty1".
    - by iApply get_priv_soundness.
    - by iApply get_pub_soundness.
    - by iApply set_priv_soundness.
    - by iApply set_pub_soundness.
    - by iApply new_soundness.
    - by iApply call_soundness.
    - by iApply priv_call_soundness.
    - by iApply sub_soundness.
    - by iApply rtc_tag_soundness.
    - by iApply rtc_prim_soundness => //.
    - by iApply rtc_prim_soundness => //.
    - by iApply rtc_prim_soundness => //.
    - by iApply rtc_prim_soundness => //.
    - (* Dynamic ifC *)
      inv hc.
      + iIntros "H". by iApply "IHty".
      + iIntros "H". by iApply "IHty1".
    - by iApply dyn_get_soundness.
    - by iApply (dyn_set_soundness _ _ _ _ _ recv).
    - by iApply dyn_call_soundness.
    - destruct wfpdefs.
      by iDestruct (inconsistency with "hΣ hΣΔ") as "hFalse".
  Qed.

  Lemma cmd_soundness C Δ kd Σ Γ cmd Γ' :
    wf_cdefs pdefs →
    wf_lty Γ →
    ok_ty Δ (this_type Γ) →
    bounded_lty (length Σ) Γ →
    Forall wf_constraint Δ →
    Forall (bounded_constraint (length Σ)) Δ →
    cmd_has_ty C Δ kd (length Σ) Γ cmd Γ' →
    ∀ st st' n, cmd_eval C st cmd st' n →
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σ Γ' st'.1.
  Proof.
    intros.
    by iApply cmd_soundness_.
  Qed.

End proofs.

Print Assumptions cmd_soundness.

Definition main_lty tag := {|
  type_of_this := (tag, []);
  ctxt := ∅
|}.

Definition main_le := {|
  vthis := 1%positive;
  lenv := ∅;
|}.

Definition main_cdef methods := {|
  generics := [];
  constraints := [];
  superclass := None;
  classfields := ∅;
  classmethods := methods;
|}.

Definition main_heap tag : heap := {[1%positive := (tag, ∅)]}.

(* Critical lemma to generate the initial iris state and boot strap
 * all the reasoning.
 * We suppose the existence of an empty class, with a single allocated
 * value of this type.
 *)
Lemma sem_heap_init
  `{PDC: ProgDefContext}
  `{SDTCC: SDTClassConstraints}
  `{SDTCS: SDTClassSpec}
  `{!sem_heapGpreS Θ}:
  ∀ MainTag methods, pdefs !! MainTag = Some (main_cdef methods) →
  ⊢@{iPropI Θ} |==> ∃ _: sem_heapGS Θ, (heap_models (main_heap MainTag) ∗ interp_local_tys [] (main_lty MainTag) main_le).
Proof.
  move => MainTag methods hpdefs.
  set (empty := ∅ : gmap loc (prodO tagO (laterO (gmapO string (sem_typeO Θ))))).
  assert (hl : empty !! 1%positive = None) by (by rewrite /empty lookup_empty).
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) empty)) as (γI) "HI";
    first by apply gmap_view_auth_valid.
  iMod (own_update with "HI") as "[? ?]";
    first by apply (gmap_view_alloc _ 1%positive DfracDiscarded (MainTag, Next ∅)).
  iExists (SemHeapGS _ _ γI).
  iModIntro; iSplit.
  - iExists _.
    iSplit; first done.
    iSplit; first by (iPureIntro; by set_solver).
    iModIntro; iIntros (k t vs) "%H".
    rewrite /main_heap lookup_singleton_Some in H.
    destruct H as [<- [= <- <-]].
    iExists ∅; iSplit.
    + by rewrite lookup_insert.
    + iSplit; first done.
      iIntros (v t); rewrite !lookup_empty option_equivI.
      iNext.
      by iIntros "?".
  - rewrite /main_lty /main_le; iSplit => /=.
    + rewrite /interp_this_type interp_this_unseal /interp_this_def /=.
      iExists 1%positive, MainTag, _, _, (gen_targs (length (main_cdef methods).(generics))), [] , ∅, ∅; iSplitR.
      { iPureIntro.
        repeat split => //.
        * by eapply InheritsRefl.
        * move => h.
          by inv h; simplify_eq.
        * by rewrite !dom_empty_L.
      }
      iSplit.
      { iModIntro; iNext; iIntros (n ? h).
        by rewrite lookup_nil in h.
      }
      iSplit.
      { iModIntro; iNext; iIntros (n ? h).
        by rewrite lookup_nil in h.
      }
      iSplit => //.
      iSplit.
      { iIntros (f vis ty orig hf).
        rewrite /main_cdef in hpdefs.
        inv hf.
        { by rewrite hpdefs in H; injection H; intros; subst. }
        { by rewrite hpdefs in H; injection H; intros; subst. }
      }
      by rewrite mapsto_eq /mapsto_def /loc_mapsto_def.
    + iIntros (v t H).
      by rewrite !lookup_empty in H.
Qed.
