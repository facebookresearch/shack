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
  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.
  (* assume some SDT constraints and their properties *)
  Context `{SDTCS: SDTClassSpec}.

  (* Iris semantic context *)
  Context `{!sem_heapGS Θ}.

  Lemma set_priv_soundness C Δ kd rigid Γ fld rhs fty t σ:
    wf_cdefs pdefs →
    wf_lty Γ →
    Forall wf_constraint Δ →
    type_of_this Γ = (t, σ) →
    has_field fld t Private fty C →
    expr_has_ty Δ Γ rigid kd rhs (subst_ty σ fty) →
    ∀ Σ st st' n,
    length Σ = rigid →
    cmd_eval C st (SetC ThisE fld rhs) st' n →
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σ Γ st'.1.
  Proof.
    move => wfpdefs wflty ? hthis hf hrhs Σ st st' n hrigid hc.
    elim/cmd_eval_setI : hc => {n}.
    move => Ω h l v t0 vs vs' heval heval_rhs hheap -> hvis.
    iIntros "#hΣ #hΣΔ".
    iIntros "[Hh #Hle]" => /=.
    iSplitL; last done.
    destruct Γ as [[tthis σthis]  Γ].
    destruct Ω as [vthis Ω].
    injection hthis; intros; subst; clear hthis.
    assert (ht: wf_ty (ClassT true t σ)).
    { eapply wf_ty_exact; by apply wflty. }
    iApply (heap_models_update Δ _ _ _ _ _ false t σ) => //=; try (by apply wfpdefs).
    - iDestruct "Hle" as "[Hthis Hle]".
      rewrite /= /interp_this_type interp_this_unseal /interp_this_def /=.
      iDestruct "Hthis" as (l' t1 def1 σ0 σt fields ifields) "(%H & #hmixed & #? & #hinst & #hdyn & #Hl)".
      destruct H as ([= <-] & hdef1 & ? & hin & hfields & hidom).
      iExists l, t1, def1, σ0, σt, fields, ifields.
      repeat iSplit => //.
      by case: heval => ->.
    - iApply expr_soundness => //; by apply wfpdefs.
  Qed.

  Lemma set_pub_soundness C Δ kd rigid Γ recv fld rhs fty exact_ t σ orig:
    wf_cdefs pdefs →
    wf_lty Γ →
    Forall wf_constraint Δ →
    expr_has_ty Δ Γ rigid kd recv (ClassT exact_ t σ) →
    has_field fld t Public fty orig →
    expr_has_ty Δ Γ rigid kd rhs (subst_ty σ fty) →
    ∀ Σ st st' n,
    length Σ = rigid →
    cmd_eval C st (SetC recv fld rhs) st' n →
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σ Γ st'.1.
  Proof.
    move => wfpdefs wflty ? hrecv hf hrhs Σ st st' n hrigid hc.
    elim/cmd_eval_setI : hc => {n}.
    move => Ω h l v t0 vs vs' heval heval_rhs hheap -> hvis.
    iIntros "#hΣ #hΣΔ".
    iIntros "[Hh #Hle]" => /=.
    iSplitL; last done.
    assert (ht: wf_ty (ClassT exact_ t σ)) by (by apply expr_has_ty_wf in hrecv).
    assert (htt: wf_ty (ClassT true t σ)).
    { by eapply wf_ty_exact. }
    iApply (heap_models_update _ _ _ _ _ _ exact_ t σ) => //=; try (by apply wfpdefs).
    - iApply expr_soundness => //; by apply wfpdefs.
    - iApply expr_soundness => //; by apply wfpdefs.
  Qed.
End proofs.
