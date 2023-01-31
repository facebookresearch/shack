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

  (* Helping the inference with this notation that hides pdefs *)
  Local Notation "Δ ⊢ s <: t" := (@subtype _ _ Δ Plain s t) (at level 70, s at next level, no associativity).
  Local Notation "Δ ⊢ s <D: t" := (@subtype _ _ Δ Aware s t) (at level 70, s at next level, no associativity).

  Lemma dyn_get_soundness C Δ kd rigid Γ lhs recv name:
    wf_cdefs pdefs →
    wf_lty Γ →
    Forall wf_constraint Δ →
    expr_has_ty Δ Γ rigid kd recv DynamicT →
    match recv with
    | ThisE => False
    | _ => True
    end →
    ∀ Σthis Σ st st' n,
    length Σ = rigid →
    cmd_eval C st (GetC lhs recv name) st' n →
    □ interp_as_mixed Σthis -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σthis Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σthis Σ (<[lhs:=DynamicT]> Γ) st'.1.
  Proof.
    move => wfpdefs ?? hrecv hnotthis Σthis Σ st st' n hrigid hc.
    iIntros "#hΣthis #hΣ #hΣΔ".
    elim/cmd_eval_getI : hc.
    move => {n}.
    move => Ω h vis fty orig l t vs v heval hheap hvs hf hvis.
    iIntros "[Hh #Hle]"; simpl.
    iModIntro. (* keep the later *)
    iDestruct (expr_soundness with "hΣthis hΣ hΣΔ Hle") as "#He" => //; try (by apply wfpdefs).
    rewrite interp_dynamic_unfold.
    iDestruct "He" as "[H | He]".
    { iDestruct "H" as (z) "%H".
      discriminate H.
    }
    iDestruct "He" as "[H | He]".
    { iDestruct "H" as (b) "%H".
      discriminate H.
    }
    iDestruct "He" as "[H | He]".
    { iDestruct "H" as "%H".
      discriminate H.
    }
    rewrite interp_sdt_equiv; last by apply wfpdefs.
    iDestruct "He" as (dyntag Σdyn dyndef [hdyndef hdynlen]) "(#HΣdyn & #hmixed1 & #hΣ1 & He)".
    iDestruct "He" as (? t0 def def0 ? Σt ??) "(%H & #hmixed & #hconstr & #hf0 & #hdyn & H◯)".
    destruct H as ([= <-] & hdef & hdef0 & hlenΣt & hinherits & hfields & hidom).
    simplify_eq.
    assert (hl0: length (generics dyndef) = length σ).
    { apply inherits_using_wf in hinherits; try (by apply wfpdefs).
      destruct hinherits as (?&?&?&hh&?).
      apply wf_tyI in hh as (? & ? & ? & ?); by simplify_eq.
    }
    iAssert (⌜t0 = t⌝ ∗ heap_models h ∗ ▷ interp_type DynamicT Σthis Σt v)%I with "[Hh]" as "[%Ht [Hh Hv]]".
    { iDestruct "Hh" as (sh) "(H● & %hdom & #Hh)".
      iDestruct (sem_heap_own_valid_2 with "H● H◯") as "#HΦ".
      iDestruct ("Hh" with "[//]") as (iFs) "[H H▷]".
      iRewrite "H" in "HΦ".
      rewrite option_equivI prod_equivI /=.
      iDestruct "HΦ" as "[%Ht HΦ]".
      fold_leibniz; subst.
      iSplitR; first done.
      iSplitL. { iExists _. iFrame. by iSplit. }
      (* the field must be public, since we can't access it from This *)
      destruct vis; simpl in hvis; last by destruct recv.
      assert (hsub: def0.(constraints) ++ Δsdt t0 ⊢ fty <D: DynamicT).
      { destruct wfpdefs.
        apply wf_fields_dyn in hdef0.
        assert (h1 := hfields).
        apply hdef0 in h1.
        apply hfields in hf.
        apply h1 in hf.
        by apply hf.
      }
      destruct wfpdefs.
      assert (hwfc: Forall wf_constraint def0.(constraints)) by by apply wf_constraints_wf in hdef0.
      assert (hwfd: Forall wf_constraint (Δsdt t0)).
      { rewrite Forall_lookup; by apply Δsdt_wf. }
      assert (hwf_ : Forall wf_constraint (def0.(constraints) ++ Δsdt t0)).
      { apply Forall_app; by split.  }
      iNext.
      iAssert (□ interp_as_mixed interp_nothing)%I as "#hnothing".
      { iModIntro; by iIntros (w) "hw". }
      (* Show that Σt |= Δt ∧ Δsdt^t *)
      pose (Σthis0 := interp_exact_tag interp_type t0 Σt).
      (* TODO export this proof *)
      iAssert (□ interp_as_mixed Σthis0)%I as "#hΣthis0".
      { iModIntro; iIntros (w) "#hw".
        iLeft; iRight; iRight.
        iExists t0, Σt, def0; iSplit; first done.
        by iApply (exact_subtype_is_inclusion_aux with "hmixed hw").
      }
      iAssert (□ Σinterp interp_nothing Σt (Δsdt t0))%I as "#hΣt_Δt_sdt_t".
      { by iApply (Σt_models_sdt with "hnothing hf0 hmixed1 hΣ1 HΣdyn hmixed hconstr"). }
      iAssert (□ Σinterp Σthis0 Σt (constraints def0 ++ Δsdt t0))%I as "#hconstr_".
      { iAssert (□ Σinterp interp_nothing Σt (constraints def0 ++ Δsdt t0))%I as "#hconstr_".
        { iModIntro.
          by iApply Σinterp_app.
        }
        (* TODO ? extract Σinterp no this ? *)
        assert (hnothis: Forall no_this_constraint (def0.(constraints) ++ Δsdt t0)).
        { apply Forall_app; split.
          - by apply wf_constraints_no_this in hdef0.
          - rewrite Forall_lookup => k c hc.
            by apply Δsdt_no_this in hc.
        }
        rewrite Forall_lookup in hnothis.
        iModIntro; iIntros (k c hc w) "#hw".
        assert (hnoc: no_this_constraint c) by by apply hnothis in hc.
        destruct hnoc as [].
        rewrite (interp_type_no_this _ _ _  Σthis0 interp_nothing); last done.
        rewrite (interp_type_no_this _ _ _  Σthis0 interp_nothing); last done.
        by iApply "hconstr_".
      }
      iSpecialize ("hdyn" $! name Public fty orig hf).
      iDestruct "H▷" as "[%hdf h]".
      iDestruct "hdyn" as (iF) "(#hiF & #hiff)".
      iRewrite -"HΦ" in "hiF".
      iSpecialize ("h" $! name _ with "[hiF]"); first done.
      iDestruct "h" as (w) "[%hw hiw]".
      simplify_eq.
      iAssert (□ interp_type fty Σthis0 Σt v)%I as "#hfty".
      { iModIntro.
        rewrite -interp_type_subst_this // hlenΣt.
        by iApply "hiff".
      }
      iDestruct (subtype_is_inclusion _ hwf_ wf_parent wf_mono
        wf_constraints_wf wf_constraints_no_this wf_constraints_bounded
        wf_fields_wf _ _ Σt _ _ hsub v
        with "hΣthis0 hmixed hconstr_ hfty") as "hsub".
      { by apply has_field_wf in hf. }
      by rewrite !interp_dynamic_unfold.
    }
    subst.
    iNext.
    iFrame.
    iApply interp_local_tys_update => //.
    by rewrite !interp_dynamic_unfold.
  Qed.
End proofs.
