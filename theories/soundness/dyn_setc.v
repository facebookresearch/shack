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
  (* assume some SDT constraints *)
  Context `{SDTCC: SDTClassConstraints}.
  (* assume the good properties of SDT constraints *)
  Context `{SDTCP: SDTClassSpec}.

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
    inv hc.
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
    iDestruct "He" as (dyntag Σdyn dyndef hpure) "(#HΣdyn & #hmixed1 & He)".
    destruct hpure as [hdyndef hsupdyn].
    iDestruct "He" as (?? def def0 ????) "(%H & #hmixed & #hconstr & #hf0 & #hdyn & H◯)".
    destruct H as ([= <-] & hdef & hdef0 & hlen & ? & hinherits & hfields & hidom).
    simplify_eq.
    (* This is based on heap_models_update, but specialized for Dynamic *)
    destruct H10 as (vis & fty & orig & hf & hv).
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
      inv hh; by simplify_eq.
    }
    pose (Δdyn0 := Δsdt t def0.(generics) (gen_targs (length def0.(generics)))).
    pose (Δdyn := Δsdt dyntag dyndef.(generics) σ).
    assert (hnewcond: Δentails Aware (def0.(constraints) ++ Δdyn) Δdyn0).
    { apply inherits_using_extends_dyn in hinherits => //; try by apply wfpdefs.
      destruct hinherits as (def0' & ? & hdef0' & ? & hwf); simplify_eq.
      move => k c hc.
      by apply hwf with k.
    }
    assert (hsub: def0.(constraints) ++ Δdyn0 ⊢ DynamicT <D: fty).
    { destruct wfpdefs.
      assert (h0 := hinherits).
      apply inherits_using_dyn_parent in h0 => //.
      destruct h0 as (def0' & dyndef' & hdef0' & hdyndef' & hsd); simplify_eq.
      apply hsd in hsupdyn.
      apply wf_fields_dyn in hdef0.
      rewrite /wf_cdef_fields_dyn_wf hsupdyn in hdef0.
      assert (h1 := hfields).
      apply hdef0 in h1.
      apply hfields in hf.
      apply h1 in hf.
      by apply hf.
    }
    assert (hsub' : def0.(constraints) ++ Δdyn ⊢ DynamicT <D: fty).
    { eapply subtype_constraint_trans; first by apply hsub.
      move => i c hc.
      rewrite lookup_app in hc.
      destruct (constraints def0 !! i) as [[??] | ] eqn:h0.
      - rewrite h0 in hc; case: hc => <-.
        eapply subtype_weaken.
        + apply SubConstraint.
          apply elem_of_list_lookup_2 with i.
          by apply h0.
        + by set_solver.
      - rewrite h0 in hc.
        by eapply hnewcond.
    }
    destruct wfpdefs.
    assert (hwfc: Forall wf_constraint def0.(constraints)) by by apply wf_constraints_wf in hdef0.
    assert (hwfd: Forall wf_constraint Δdyn).
    { apply Δsdt_wf.
      apply inherits_using_wf in hinherits => //.
      destruct hinherits as (? & ? & ? & hwf); simplify_eq.
      by apply wf_ty_class_inv in hwf.
    }
    assert (hwf_ : Forall wf_constraint (def0.(constraints) ++ Δdyn)).
    { apply Forall_app; by split.  }
    assert (hwfσ : Forall wf_ty σ).
    { apply inherits_using_wf in hinherits => //.
      destruct hinherits as (? & ? & ? & hh).
      by apply wf_ty_class_inv in hh.
    }
    iAssert (interp_env_as_mixed (interp_list Σt σ)) as "hmixed0".
    { iIntros (k phi hk w) "hphi".
      apply list_lookup_fmap_inv in hk as [ty0 [-> hty0]].
      rewrite -(interp_type_unfold Σt MixedT w).
      iApply (submixed_is_inclusion_aux Σt ty0 w) => //.
      rewrite Forall_lookup in hwfσ.
      by apply hwfσ in hty0.
    }
    iAssert (□ Σinterp Σt Δdyn)%I as "#hconstr_dyn".
    { iClear "Hle hdyn H◯ Hv hifs hmodfs hf' Hve".
      iModIntro; iIntros (i c0 hc w) "#h".
      rewrite /Δdyn -(subst_ty_gen_targs (length dyndef.(generics)) σ) // in hc.
      rewrite -Δsdt_subst_ty in hc.
      apply list_lookup_fmap_inv in hc as [c [-> hc]] => /=.
      assert (hbc : bounded_constraint (length σ) c).

      { rewrite -hl0.
        move : (bounded_gen_targs (length dyndef.(generics))) => hh.
        apply Δsdt_bounded with (A := dyntag) (vars := dyndef.(generics)) in hh.
        rewrite Forall_lookup in hh.
        by apply hh in hc.
      }
      destruct hbc as [].
      rewrite !interp_type_subst //.
      by iApply ((Δsdt_variance_interp _ _ _ _ wf_mono wf_parent hdyndef)
      with "hmixed0 hmixed1 hf0 HΣdyn").
    }
    iAssert (□ Σinterp Σt (constraints def0 ++ Δdyn))%I as "hconstr_".
    { iModIntro.
      by iApply Σinterp_app.
    }
    iApply (subtype_is_inclusion _ hwf_ wf_parent wf_mono _ Σt _ _ hsub' v) => //.
    by rewrite !interp_dynamic_unfold.
  Qed.
End proofs.
