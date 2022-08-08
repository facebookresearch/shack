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

  (* Iris semantic context *)
  Context `{!sem_heapGS Θ}.

  Hypothesis Δsdt_wf: ∀ A vars σ, Forall wf_ty σ → Forall wf_constraint (Δsdt A vars σ).
  Hypothesis Δsdt_subst_ty: ∀ A vars σ0 σ,
    subst_constraints σ (Δsdt A vars σ0) = Δsdt A vars (subst_ty σ <$> σ0).
  Hypothesis Δsdt_bounded: ∀ A vars σ n,
    Forall (bounded n) σ →
    Forall (bounded_constraint n) (Δsdt A vars σ).
  Hypothesis Δsdt_lift: ∀ n A vars σ,
    lift_constraints n (Δsdt A vars σ) = Δsdt A vars (lift_ty n <$> σ).
  Hypothesis Δsdt_variance: ∀ Δ kd A vars σ0 σ1,
    subtype_targs Δ kd vars σ0 σ1 →
    Δentails kd (Δ ++ Δsdt A vars σ1) (Δsdt A vars σ0).

  (* Helping the inference with this notation that hides pdefs *)
  Local Notation "Δ ⊢ s <: t" := (@subtype _ Δ Plain s t) (at level 70, s at next level, no associativity).
  Local Notation "Δ ⊢ s <D: t" := (@subtype _ Δ Aware s t) (at level 70, s at next level, no associativity).

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
    iIntros "hΣ hΣΔ".
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
    iDestruct "He" as (dyntag Σdyn dyndef hpure) "[#HΣdyn He]".
    destruct hpure as [hdyndef hsupdyn].
    rewrite interp_tag_equiv; last by apply wfpdefs.
    iDestruct "He" as (?? def def0 ????) "(%H & #hmixed & #hconstr & #hf0 & #hdyn & H◯)".
    destruct H as ([= <-] & hdef & hdef0 & hlen & ? & hinherits & hfields & hidom).
    simplify_eq.
    assert (hl0: length (generics dyndef) = length σ).
    { apply inherits_using_wf in hinherits; try (by apply wfpdefs).
      destruct hinherits as (?&?&?&hh).
      inv hh; by simplify_eq.
    }
    pose (Δdyn0 := Δsdt t0 def0.(generics) (gen_targs (length def0.(generics)))).
    pose (Δdyn := Δsdt dyntag dyndef.(generics) σ).
    assert (hnewcond: Δentails Aware (def0.(constraints) ++ Δdyn) Δdyn0).
    { apply inherits_using_extends_dyn in hinherits => //; try by apply wfpdefs.
      destruct hinherits as (def0' & ? & hdef0' & ? & hwf); simplify_eq.
      move => k c hc.
      by apply hwf with k.
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
      assert (hsub: def0.(constraints) ++ Δdyn0 ⊢ fty <D: DynamicT).
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
      assert (hsub' : def0.(constraints) ++ Δdyn ⊢ fty <D: DynamicT).
      { eapply subtype_constraint_trans; first by apply hsub.
        move => i c hc.
        rewrite lookup_app in hc.
        destruct (constraints def0 !! i) as [[??] | ] eqn:h0.
        - rewrite h0 in hc; case: hc => <-.
          eapply subtype_weaken; [ done | done | | ].
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
      iNext.
      assert (hwfσ : Forall wf_ty σ).
      { apply inherits_using_wf in hinherits => //.
        destruct hinherits as (? & ? & ? & hh).
        by apply wf_ty_class_inv in hh.
      }
      iAssert (interp_env_as_mixed Σdyn) as "hmixed1"; first by admit.
      iAssert (interp_env_as_mixed (interp_list Σt σ)) as "hmixed0".
      { iIntros (k phi hk w) "hphi".
        apply list_lookup_fmap_inv in hk as [ty0 [-> hty0]].
        rewrite -(interp_type_unfold Σt MixedT w).
        iApply (submixed_is_inclusion_aux Σt ty0 w) => //.
        rewrite Forall_lookup in hwfσ.
        by apply hwfσ in hty0.
      }
      iAssert (□ Σinterp Σt Δdyn)%I as "#hconstr_dyn".
      { iClear "Hle hconstr hdyn H◯ Hh HΦ H H▷".
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
        by iApply ((Δsdt_variance_interp Δsdt_wf Δsdt_subst_ty Δsdt_bounded
          Δsdt_lift Δsdt_variance _ _ _ _ wf_mono wf_parent hdyndef)
          with "hmixed0 hmixed1 hf0 HΣdyn").
      }
      iAssert (□ Σinterp Σt (constraints def0 ++ Δdyn))%I as "hconstr_".
      { iModIntro.
        by iApply Σinterp_app.
      }
      iSpecialize ("hdyn" $! name Public fty orig hf).
      iDestruct "H▷" as "[%hdf h]".
      iRewrite -"HΦ" in "hdyn".
      iSpecialize ("h" $! name _ with "[hdyn]"); first done.
      iDestruct "h" as (w) "[%hw hiw]".
      simplify_eq.
      iDestruct (subtype_is_inclusion _ _ _ _ hwf_ wf_parent wf_mono _ Σt _ _ hsub' v) as "hsub".
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
