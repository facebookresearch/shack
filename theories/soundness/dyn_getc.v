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
    ∀ Σ st st' n,
    length Σ = rigid →
    cmd_eval C st (GetC lhs recv name) st' n →
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σ (<[lhs:=DynamicT]> Γ) st'.1.
  Proof.
    move => wfpdefs ?? hrecv hnotthis Σ st st' n hrigid hc.
    iIntros "#hΣ #hΣΔ".
    inv hc.
    iIntros "[Hh #Hle]"; simpl.
    iModIntro. (* keep the later *)
    iDestruct (expr_soundness with "hΣ hΣΔ Hle") as "#He" => //; try (by apply wfpdefs).
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
    iDestruct "He" as (dyntag Σdyn dyndef hdyndef) "(#HΣdyn & #hmixed1 & #hΣ1 & He)".
    iDestruct "He" as (?? def def0 ????) "(%H & #hmixed & #hconstr & #hf0 & #hdyn & H◯)".
    destruct H as ([= <-] & hdef & hdef0 & hlen & ? & hinherits & hfields & hidom).
    simplify_eq.
    assert (hl0: length (generics dyndef) = length σ).
    { apply inherits_using_wf in hinherits; try (by apply wfpdefs).
      destruct hinherits as (?&?&?&hh).
      inv hh; by simplify_eq.
    }
    iAssert (⌜t0 = t⌝ ∗ heap_models h ∗ ▷ interp_type DynamicT Σt v)%I with "[Hh]" as "[%Ht [Hh Hv]]".
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
      destruct H9 as (vis & fty & orig & hf & hvc).
      destruct vis; last by destruct recv.
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
      (* Show that Σt |= Δt ∧ Δsdt^t *)
      iAssert (□ Σinterp Σt (Δsdt t0))%I as "#hΣt_Δt_sdt_t".
      { by iApply (Σt_models_sdt with "hf0 hmixed1 hΣ1 HΣdyn hmixed hconstr"). }
      iAssert (□ Σinterp Σt (constraints def0 ++ Δsdt t0))%I as "hconstr_".
      { iModIntro.
        by iApply Σinterp_app.
      }
      iSpecialize ("hdyn" $! name Public fty orig hf).
      iDestruct "H▷" as "[%hdf h]".
      iRewrite -"HΦ" in "hdyn".
      iSpecialize ("h" $! name _ with "[hdyn]"); first done.
      iDestruct "h" as (w) "[%hw hiw]".
      simplify_eq.
      iDestruct (subtype_is_inclusion _ hwf_ wf_parent wf_mono wf_constraints_wf wf_constraints_bounded _ Σt _ _ hsub v) as "hsub".
      { by apply has_field_wf in hf. }
      by iApply "hsub".
    }
    subst.
    iNext.
    iFrame.
    iApply interp_local_tys_update => //.
    by rewrite !interp_dynamic_unfold.
  Qed.
End proofs.
