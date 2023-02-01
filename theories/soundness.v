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

From shack Require Import lang progdef subtype ok typing.
From shack Require Import eval heap modality interp.
From shack.soundness Require Import expr defs.
From shack.soundness Require Import getc setc newc call priv_call sub.
From shack.soundness Require Import rtc_tag rtc_prim.
From shack.soundness Require Import dyn_getc dyn_setc dyn_call.

Section proofs.
  (* assume a given set of class definitions and their SDT annotations. *)
  Context `{SDTCVS: SDTClassVarianceSpec}.

  (* Iris semantic context *)
  Context `{!sem_heapGS Θ}.

  Lemma cmd_soundness_ C cdef Δ kd rigid Γ cmd Γ' :
    wf_cdefs pdefs →
    wf_lty Γ →
    bounded_lty rigid Γ →
    Forall wf_constraint Δ →
    Forall (bounded_constraint rigid) Δ →
    pdefs !! C = Some cdef →
    ∀ t tdef Σt σ,
    pdefs !! t = Some tdef →
    length Σt = length tdef.(generics) →
    inherits_using t C σ →
    cmd_has_ty C Δ kd rigid Γ cmd Γ' →
    ∀ Σ st st' n,
    length Σ = rigid →
    rigid ≥ length cdef.(generics) →
    cmd_eval C st cmd st' n →
    let Σthis := interp_exact_tag interp_type t Σt in
    ⌜interp_list interp_nothing Σt σ ≡ take (length cdef.(generics)) Σ⌝ -∗
    □ interp_env_as_mixed Σt -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σthis Σ Γ st.1 -∗ |=▷^n
        heap_models st'.2 ∗ interp_local_tys Σthis Σ Γ' st'.1.
  Proof.
    move => wfpdefs.
    iLöb as "IH" forall (C cdef Δ kd rigid Γ cmd Γ').
    iIntros (wflty blty hΔ hΔb hcdef t0 t0def Σt0 σ0 ht0def hlenΣt0 hin_t0_C_σ hty).
    iInduction hty as [ Γ Δ kd rigid |
        Δ kd rigid Γ0 Γ1 hwf hbounded |
        Δ kd rigid Γ1 Γ2 Γ3 fstc sndc hfst hi1 hsnd hi2 |
        Δ kd rigid Γ lhs e ty he |
        Δ kd rigid Γ1 Γ2 cond thn els hcond hthn hi1 hels hi2 |
        Δ kd rigid _cdef Γ lhs name fty _hcdef hf |
        Δ kd rigid Γ lhs recv exact_ t targs name fty orig hrecv hf hex |
        Δ kd rigid _cdef Γ lhs recv name fty orig hrecv _hcdef hf |
        Δ kd rigid _cdef Γ fld rhs fty _hcdef hf hrhs |
        Δ kd rigid Γ recv fld rhs fty orig exact_ t σ hrecv hf hex hrhs |
        Δ kd rigid _cdef Γ recv fld rhs fty orig hrecv _hcdef hf hrhs |
        Δ kd rigid Γ lhs t otargs targs args fields htargs hwf hb hok hf hdom harg |
        Δ kd rigid Γ lhs recv exact_ t targs name orig mdef args hrecv hhasm hex hvis hdom hargs |
        Δ kd rigid _cdef Γ lhs name mdef args _hcdef hm hvis hdom hargs |
        Δ kd rigid Γ c Γ0 Γ1 hsub hb h |
        Δ kd rigid Γ0 Γ1 v tv t def thn els hv hdef hthn hi0 hels hi1 |
        Δ kd rigid Γ0 Γ1 v tv thn els hv hthn hi0 hels hi1 |
        Δ kd rigid Γ0 Γ1 v tv thn els hv hthn hi0 hels hi1 |
        Δ kd rigid Γ0 Γ1 v tv thn els hv hthn hi0 hels hi1 |
        Δ kd rigid Γ0 Γ1 v tv thn els hv hthn hi0 hels hi1 |
        Δ kd rigid Γ1 Γ2 cond thn els hcond hthn hi1 hels hi2 |
        Δ kd rigid Γ lhs recv name he hnotthis |
        Δ kd rigid Γ recv fld rhs hrecv hrhs hnotthis |
        Δ kd rigid Γ lhs recv name args hrecv hi hnotthis |
        Δ kd rigid Γ0 cmd Γ1 hwf hb hsub
      ] "IHty"; iIntros (Σ st st' n hrigid hge hc) "%hΣeq #hΣt0 #hΣ #hΣΔ".
    - (* Skip *)
      inv hc.
      rewrite updN_zero.
      by iIntros "?".
    - (* Error *) by inv hc.
    - (* Seq *)
      inv hc. iIntros "H".
      iSpecialize ("IHty" $! wflty blty hΔ hΔb Σ _ _ _ refl_equal hge H3 hΣeq with "hΣt0 hΣ hΣΔ H").
      rewrite Nat.iter_add.
      iApply (updN_mono_I with "[] IHty").
      destruct wfpdefs.
      iApply "IHty1" => //.
      + by apply cmd_has_ty_wf in hfst.
      + by eapply cmd_has_ty_bounded in hfst.
    - (* Let *)
      inv hc.
      iIntros "[? #Hle]".
      rewrite updN_zero /=.
      iFrame.
      iAssert (□ interp_as_mixed (interp_exact_tag interp_type t0 Σt0))%I as "#hΣthis".
      { iModIntro; iIntros (w) "hw".
        iLeft; iRight; iRight.
        iExists t0, Σt0, t0def; iSplit; first done.
        by iApply (exact_subtype_is_inclusion_aux with "hΣt0 hw").
      }
      iDestruct (expr_soundness with "hΣthis hΣ hΣΔ Hle") as "#?" => //; try (by apply wfpdefs).
      by iApply interp_local_tys_update.
    - (* If *)
      inv hc.
      + iIntros "H". by iApply "IHty".
      + iIntros "H". by iApply "IHty1".
    - iAssert (□ interp_as_mixed (interp_exact_tag interp_type t0 Σt0))%I as "#hΣthis".
      { iModIntro; iIntros (w) "hw".
        iLeft; iRight; iRight.
        iExists t0, Σt0, t0def; iSplit; first done.
        by iApply (exact_subtype_is_inclusion_aux with "hΣt0 hw").
      }
      simplify_eq.
      by iApply (get_priv_soundness C cdef).
    - iAssert (□ interp_as_mixed (interp_exact_tag interp_type t0 Σt0))%I as "#hΣthis".
      { iModIntro; iIntros (w) "hw".
        iLeft; iRight; iRight.
        iExists t0, Σt0, t0def; iSplit; first done.
        by iApply (exact_subtype_is_inclusion_aux with "hΣt0 hw").
      }
      by iApply get_pub_soundness.
    - simplify_eq.
      iAssert (□ interp_as_mixed (interp_exact_tag interp_type t0 Σt0))%I as "#hΣthis".
      { iModIntro; iIntros (w) "hw".
        iLeft; iRight; iRight.
        iExists t0, Σt0, t0def; iSplit; first done.
        by iApply (exact_subtype_is_inclusion_aux with "hΣt0 hw").
      }
      by iApply (get_this_soundness C).
    - simplify_eq.
      by iApply (set_priv_soundness C).
    - by iApply (set_pub_soundness C cdef).
    - simplify_eq.
      by iApply (set_this_soundness C cdef).
    - iAssert (□ interp_as_mixed (interp_exact_tag interp_type t0 Σt0))%I as "#hΣthis".
      { iModIntro; iIntros (w) "hw".
        iLeft; iRight; iRight.
        iExists t0, Σt0, t0def; iSplit; first done.
        by iApply (exact_subtype_is_inclusion_aux with "hΣt0 hw").
      }
      by iApply new_soundness.
    - by iApply ((call_soundness C cdef)).
    - simplify_eq.
      by iApply ((priv_call_soundness C cdef)).
    - by iApply (sub_soundness C cdef).
    - by iApply (rtc_tag_soundness C cdef).
    - by iApply (rtc_prim_soundness C cdef) => //.
    - by iApply (rtc_prim_soundness C cdef) => //.
    - by iApply (rtc_prim_soundness C cdef) => //.
    - by iApply (rtc_prim_soundness C cdef) => //.
    - (* Dynamic ifC *)
      inv hc.
      + iIntros "H". by iApply "IHty".
      + iIntros "H". by iApply "IHty1".
    - iAssert (□ interp_as_mixed (interp_exact_tag interp_type t0 Σt0))%I as "#hΣthis".
      { iModIntro; iIntros (w) "hw".
        iLeft; iRight; iRight.
        iExists t0, Σt0, t0def; iSplit; first done.
        by iApply (exact_subtype_is_inclusion_aux with "hΣt0 hw").
      }
      by iApply (dyn_get_soundness C).
    - iAssert (□ interp_as_mixed (interp_exact_tag interp_type t0 Σt0))%I as "#hΣthis".
      { iModIntro; iIntros (w) "hw".
        iLeft; iRight; iRight.
        iExists t0, Σt0, t0def; iSplit; first done.
        by iApply (exact_subtype_is_inclusion_aux with "hΣt0 hw").
      }
      by iApply (dyn_set_soundness _ _ _ _ _ recv).
    - by iApply (dyn_call_soundness C).
    - destruct wfpdefs.
      iAssert (□ interp_as_mixed (interp_exact_tag interp_type t0 Σt0))%I as "#hΣthis".
      { iModIntro; iIntros (w) "hw".
        iLeft; iRight; iRight.
        iExists t0, Σt0, t0def; iSplit; first done.
        by iApply (exact_subtype_is_inclusion_aux with "hΣt0 hw").
      }
      by iDestruct (inconsistency with "hΣthis hΣ hΣΔ") as "hFalse".
  Qed.

  Lemma cmd_soundness C cdef Δ kd Γ cmd Γ' Σ :
    wf_cdefs pdefs →
    wf_lty Γ →
    bounded_lty (length Σ) Γ →
    Forall wf_constraint Δ →
    Forall (bounded_constraint (length Σ)) Δ →
    pdefs !! C = Some cdef →
    ∀ t tdef Σt σ,
    pdefs !! t = Some tdef →
    length Σt = length tdef.(generics) →
    inherits_using t C σ →
    cmd_has_ty C Δ kd (length Σ) Γ cmd Γ' →
    ∀ st st' n,
    length Σ ≥ length cdef.(generics) →
    cmd_eval C st cmd st' n →
    let Σthis := interp_exact_tag interp_type t Σt in
    ⌜interp_list interp_nothing Σt σ ≡ take (length cdef.(generics)) Σ⌝ -∗
    □ interp_env_as_mixed Σt -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σthis Σ Γ st.1 -∗ |=▷^n
        heap_models st'.2 ∗ interp_local_tys Σthis Σ Γ' st'.1.
  Proof.
    intros.
    by iApply (cmd_soundness_ C cdef).
  Qed.

End proofs.

Print Assumptions cmd_soundness.

Definition main_lty : local_tys := ∅.

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
  `{SDTCVS: SDTClassVarianceSpec}
  `{!sem_heapGpreS Θ}:
  ∀ MainTag methods, pdefs !! MainTag = Some (main_cdef methods) →
  ⊢@{iPropI Θ} |==> ∃ _: sem_heapGS Θ, (heap_models (main_heap MainTag) ∗
      interp_local_tys (interp_exact_tag interp_type MainTag []) [] main_lty main_le).
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
    + rewrite interp_exact_tag_unseal /interp_exact_tag_def /=.
      iExists 1%positive, (main_cdef methods), ∅, ∅; iSplitR.
      { iPureIntro.
        repeat split => //.
        * move => h.
          by inv h; simplify_eq.
        * by rewrite !dom_empty_L.
      }
      iSplit.
      { iModIntro; iNext; iIntros (n ? h).
        by rewrite lookup_nil in h.
      }
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
