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

From shack Require Import lang progdef subtype eval.
From shack Require Import heap modality interp typing.
From shack.soundness Require Import expr defs.

Section proofs.
  (* assume a given set of class definitions and their SDT annotations. *)
  Context `{SDTCVS: SDTClassVarianceSpec}.

  (* Iris semantic context *)
  Context `{!sem_heapGS Θ}.

  Lemma set_priv_soundness C Δ kd cdef rigid Γ fld rhs fty:
    wf_cdefs pdefs →
    wf_lty Γ →
    Forall wf_constraint Δ →
    pdefs !! C = Some cdef →
    cdef.(classfields) !! fld = Some (Private, fty) →
    expr_has_ty Δ Γ rigid kd rhs fty →
    ∀ t tdef Σt σ,
    pdefs !! t = Some tdef →
    length Σt = length tdef.(generics) →
    inherits_using t C σ →
    ∀ Σ st st' n,
    length Σ = rigid →
    rigid ≥ length cdef.(generics) →
    cmd_eval C st (SetC ThisE fld rhs) st' n →
    let Σthis := interp_exact_tag interp_type t Σt in
    ⌜interp_list interp_nothing Σt σ ≡ take (length cdef.(generics)) Σ⌝ -∗
    □ interp_env_as_mixed Σt -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σthis Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σthis Σ Γ st'.1.
  Proof.
    move => wfpdefs.
    destruct wfpdefs.
    move => wflty ? hcdef hf hrhs.
    move => t tdef Σt σ htdef hlenΣt hin_t_C.
    move => Σ st st' n hrigid hge hc Σthis.
    elim/cmd_eval_setI : hc => {n}.
    move => Ω h vis fty0 orig l v t0 vs vs' heval heval_rhs hheap ->.
    move => hf0 hvis /=.
    iIntros "%hΣeq #hΣt #hΣ #hΣΔ".
    iIntros "[Hh #Hle]" => /=.
    iSplitL; last done.
    destruct Ω as [vthis Ω].
    case: heval heval_rhs => -> heval_rhs {vthis}.
    iAssert (□ interp_as_mixed Σthis)%I as "#hΣthis".
    { iModIntro; iIntros (w) "hw".
      iLeft; iRight; iRight.
      iExists t, Σt, tdef; iSplit; first done.
      by iApply (exact_subtype_is_inclusion_aux with "hΣt hw").
    }
    iApply (heap_models_update_priv _ _ _ _ t0 C $! hΣeq with "hΣt hΣ hΣΔ") => //.
    - by subst.
    - by iDestruct "Hle" as "[Hthis Hle]".
    - by iApply expr_soundness.
  Qed.

  Lemma set_pub_soundness C cdef Δ kd rigid Γ recv fld rhs fty exact_ t σ orig:
    wf_cdefs pdefs →
    wf_lty Γ →
    Forall wf_constraint Δ →
    pdefs !! C = Some cdef →
    expr_has_ty Δ Γ rigid kd recv (ClassT exact_ t σ) →
    has_field fld t Public fty orig →
    (is_true exact_ ∨ no_this fty) →
    expr_has_ty Δ Γ rigid kd rhs (subst_fty exact_ t σ fty) →
    ∀ t0 t0def Σt0 σ0,
    pdefs !! t0 = Some t0def →
    length Σt0 = length t0def.(generics) →
    inherits_using t0 C σ0 →
    ∀ Σ st st' n,
    length Σ = rigid →
    cmd_eval C st (SetC recv fld rhs) st' n →
    let Σthis0 := interp_exact_tag interp_type t0 Σt0 in
    ⌜interp_list interp_nothing Σt0 σ0 ≡ take (length cdef.(generics)) Σ⌝ -∗
    □ interp_env_as_mixed Σt0 -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis0 Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σthis0 Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σthis0 Σ Γ st'.1.
  Proof.
    move => wfpdefs wflty ? hcdef hrecv hf hex hrhs.
    move => t0 t0def Σt0 σ0 ht0def hlenΣt0 hin0.
    move => Σ st st' n hrigid hc.
    elim/cmd_eval_setI : hc => {n}.
    move => Ω h vis fty0 orig0 l v t1 vs vs' heval heval_rhs hheap ->.
    move => hf0 hvis Σthis0.
    iIntros "%heqΣ #hΣt0 #hΣ #hΣΔ".
    iIntros "[Hh #Hle]" => /=.
    iSplitL; last done.
    assert (ht: wf_ty (ClassT exact_ t σ)) by (by apply expr_has_ty_wf in hrecv).
    iAssert (□ interp_as_mixed Σthis0)%I as "#hΣthis".
    { iModIntro; iIntros (w) "hw".
      iLeft; iRight; iRight.
      iExists t0, Σt0, t0def; iSplit; first done.
      by iApply (exact_subtype_is_inclusion_aux with "hΣt0 hw").
    }
    iApply ((heap_models_update_pub _ _ _ _ _ _ exact_ t σ)
      with "hΣt0 hΣ") => //=; try (by apply wfpdefs).
    - iApply expr_soundness => //; by apply wfpdefs.
    - iApply expr_soundness => //; by apply wfpdefs.
  Qed.
End proofs.
