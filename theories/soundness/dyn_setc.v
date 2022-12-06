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

  (* Helping the inference with this notation that hides pdefs *)
  Local Notation "Δ ⊢ s <: t" := (@subtype _ _ Δ Plain s t) (at level 70, s at next level, no associativity).
  Local Notation "Δ ⊢ s <D: t" := (@subtype _ _ Δ Aware s t) (at level 70, s at next level, no associativity).

  (* Iris semantic context *)
  Context `{!sem_heapGS Θ}.

  Lemma dyn_set_soundness C Δ kd rigid Γ recv fld rhs:
    wf_cdefs pdefs →
    wf_lty Γ →
    Forall wf_constraint Δ →
    expr_has_ty Δ Γ rigid kd recv DynamicT →
    expr_has_ty Δ Γ rigid kd rhs DynamicT →
    match recv with
    | ThisE => False
    | _ => True
    end →
    ∀ Σ st st' n,
    length Σ = rigid →
    cmd_eval C st (SetC recv fld rhs) st' n →
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σ Γ st'.1.
  Proof.
    move => wfpdefs wflty ? hrecv hrhs hnotthis Σ st st' n hrigid hc.
    elim/cmd_eval_setI : hc.
    move => {n}.
    move => Ω h l v t vs vs' heval_recv heval_rhs hheap -> hvis.
    iIntros "#hΣ #hΣΔ".
    iIntros "[Hh #Hle]" => /=.
    iSplitL; last done.
    iAssert (interp_type DynamicT Σ (LocV l)) as "#Hl".
    { iApply expr_soundness => //; by apply wfpdefs. }
    rewrite interp_dynamic_unfold.
    iDestruct "Hl" as "[H | Hl]".
    { iDestruct "H" as (z) "%H".
      discriminate H.
    }
    iDestruct "Hl" as "[H | Hl]".
    { iDestruct "H" as (b) "%H".
      discriminate H.
    }
    iDestruct "Hl" as "[H | He]".
    { iDestruct "H" as "%H".
      discriminate H.
    }
    rewrite interp_sdt_equiv; last by apply wfpdefs.
    iDestruct "He" as (dyntag Σdyn dyndef [hdyndef hdynlen]) "(#HΣdyn & #hmixed1 & #hΣ1 & He)".
    iDestruct "He" as (?? def def0 ????) "(%H & #hmixed & #hconstr & #hf0 & #hdyn & H◯)".
    destruct H as ([= <-] & hdef & hdef0 & ? & hinherits & hfields & hidom).
    simplify_eq.
    (* This is based on heap_models_update, but specialized for Dynamic *)
    destruct hvis as (vis & fty & orig & hf & hv).
    destruct vis; last by destruct recv.
    iDestruct "Hh" as (sh) "[hown [%hdom #h]]".
    iExists sh.
    iDestruct (sem_heap_own_valid_2 with "hown H◯") as "#Hv".
    iSplitL "hown"; first by iFrame.
    iSplitR.
    { iPureIntro.
      by rewrite hdom dom_insert_lookup_L.
    }
    iModIntro.
    iIntros (l'' t'' vs'') "%Heq".
    rewrite lookup_insert_Some in Heq.
    destruct Heq as [[<- [= <- <-]] | [hne hl]]; last first.
    { iApply "h".
      by iPureIntro.
    }
    iSpecialize ("h" $! l t vs with "[//]").
    iDestruct "h" as (iFs) "[#hsh hmodels]".
    iExists iFs; iSplit; first done.
    iRewrite "Hv" in "hsh".
    rewrite !option_equivI prod_equivI /=.
    iDestruct "hsh" as "[%ht #hifs]".
    fold_leibniz; subst.
    iSpecialize ("hdyn" $! fld Public fty orig hf).
    rewrite later_equivI. iNext.
    iAssert (⌜is_Some (iFs !! fld)⌝)%I as "%hiFs".
    { iRewrite -"hifs".
      by iRewrite "hdyn".
    }
    rewrite /heap_models_fields.
    iDestruct "hmodels" as "[%hdomv #hmodfs]".
    iSplit.
    { iPureIntro.
      by rewrite -hdomv dom_insert_lookup // -elem_of_dom hdomv elem_of_dom.
    }
    iIntros (f' iF') "#hf'".
    destruct (decide (fld = f')) as [-> | hne]; last first.
    { rewrite lookup_insert_ne //.
      by iApply "hmodfs".
    }
    rewrite lookup_insert.
    iExists v; iSplitR; first done.
    iRewrite -"hifs" in "hf'".
    iRewrite "hdyn" in "hf'".
    rewrite !option_equivI discrete_fun_equivI.
    iSpecialize ("hf'" $! v).
    iRewrite -"hf'".
    iAssert (interp_type DynamicT Σ v) as "#Hve".
    { iApply expr_soundness => //; by apply wfpdefs. }
    assert (hl0: length (generics dyndef) = length σ).
    { apply inherits_using_wf in hinherits; try (by apply wfpdefs).
      destruct hinherits as (?&?&?&hh).
      apply wf_tyI in hh as (? & ? & ? & ?); by simplify_eq.
    }
    assert (hsub: def0.(constraints) ++ Δsdt t ⊢ DynamicT <D: fty).
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
    assert (hwfd: Forall wf_constraint (Δsdt t)).
    { rewrite Forall_lookup; by apply Δsdt_wf. }
    assert (hwf_ : Forall wf_constraint (def0.(constraints) ++ Δsdt t)).
    { apply Forall_app; by split.  }
    (* Show that Σt |= Δt ∧ Δsdt^t *)
    iAssert (□ Σinterp Σt (Δsdt t))%I as "#hΣt_Δt_sdt_t".
    { by iApply (Σt_models_sdt with "hf0 hmixed1 hΣ1 HΣdyn hmixed hconstr"). }
    iAssert (□ Σinterp Σt (constraints def0 ++ Δsdt t))%I as "hconstr_".
    { iModIntro.
      by iApply Σinterp_app.
    }
    iApply (subtype_is_inclusion _ hwf_ wf_parent wf_mono wf_constraints_wf wf_constraints_bounded _ Σt _ _ hsub v) => //.
    by rewrite !interp_dynamic_unfold.
  Qed.
End proofs.
