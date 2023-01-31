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
    ∀ Σthis Σ st st' n,
    length Σ = rigid →
    cmd_eval C st (SetC recv fld rhs) st' n →
    □ interp_as_mixed Σthis -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σthis Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σthis Σ Γ st'.1.
  Proof.
    move => wfpdefs wflty ? hrecv hrhs hnotthis Σthis Σ st st' n hrigid hc.
    elim/cmd_eval_setI : hc.
    move => {n}.
    move => Ω h vis fty orig l v t vs vs' heval_recv heval_rhs hheap -> hf hvis.
    iIntros "#hΣthis #hΣ #hΣΔ".
    iIntros "[Hh #Hle]" => /=.
    iSplitL; last done.
    iAssert (interp_type DynamicT Σthis Σ (LocV l)) as "#Hl".
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
    iDestruct "He" as (? t0 def def0 ? Σt ??) "(%H & #hmixed & #hconstr & #hf0 & #hdyn & H◯)".
    destruct H as ([= <-] & hdef & hdef0 & hlenΣt & hinherits & hfields & hidom).
    simplify_eq.
    (* This is based on heap_models_update, but specialized for Dynamic *)
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
    rewrite later_equivI.
    iNext.
    iDestruct "hdyn" as (iF) "(#hdyn & #hiff)".
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
    iAssert (interp_type DynamicT Σthis Σ v) as "#Hve".
    { iApply expr_soundness => //; by apply wfpdefs. }
    assert (hl0: length (generics dyndef) = length σ).
    { apply inherits_using_wf in hinherits; try (by apply wfpdefs).
      destruct hinherits as (?&?&?&hh&?).
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
    iAssert (□ interp_as_mixed interp_nothing)%I as "#hnothing".
    { iModIntro; by iIntros (w) "hw". }
    iAssert (□ Σinterp interp_nothing Σt (Δsdt t))%I as "#hΣt_Δt_sdt_t".
    { by iApply (Σt_models_sdt with "hnothing hf0 hmixed1 hΣ1 HΣdyn hmixed hconstr"). }
    pose (Σthis0 := interp_exact_tag interp_type t Σt).
    iAssert (□ interp_as_mixed Σthis0)%I as "#hΣthis0".
    { iModIntro; iIntros (w) "#hw".
      iLeft; iRight; iRight.
      iExists t, Σt, def0; iSplit; first done.
      by iApply (exact_subtype_is_inclusion_aux with "hmixed hw").
    }
    iAssert (□ Σinterp Σthis0 Σt (constraints def0 ++ Δsdt t))%I as "#hconstr_".
    { iAssert (□ Σinterp interp_nothing Σt (constraints def0 ++ Δsdt t))%I as "#hconstr_".
      { iModIntro.
        by iApply Σinterp_app.
      }
      (* TODO ? extract Σinterp no this ? *)
      assert (hnothis: Forall no_this_constraint (def0.(constraints) ++ Δsdt t)).
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
    iApply "hiff".
    iAssert (interp_type fty Σthis0 Σt v -∗
             interp_type (subst_gen t def0 fty) interp_nothing Σt v)%I as "hfty".
    { iIntros "hfty".
      by rewrite -interp_type_subst_this // hlenΣt.
    }
    iApply "hfty".
    iApply (subtype_is_inclusion _ hwf_ wf_parent wf_mono wf_constraints_wf
      wf_constraints_no_this wf_constraints_bounded wf_fields_wf
      _ _ Σt _ _ hsub v with "hΣthis0 hmixed hconstr_"); first done.
    by rewrite !interp_dynamic_unfold.
  Qed.
End proofs.
