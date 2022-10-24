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
  (* assume some SDT constraints and their properties *)
  Context `{SDTCS: SDTClassSpec}.

  (* Helping the inference with this notation that hides pdefs *)
  Local Notation "Δ ⊢ s <: t" := (@subtype _ _ Δ Plain s t) (at level 70, s at next level, no associativity).
  Local Notation "Δ ⊢ s <D: t" := (@subtype _ _ Δ Aware s t) (at level 70, s at next level, no associativity).

  (* Iris semantic context *)
  Context `{!sem_heapGS Θ}.

  Lemma new_soundness oσ σ C Δ kd rigid Γ lhs t args fields:
    wf_cdefs pdefs →
    wf_lty Γ →
    Forall wf_constraint Δ →
    wf_ty (ClassT t σ) →
    ok_ty Δ (ClassT t σ) →
    has_fields t fields →
    dom fields = dom args →
    (∀ (f : string) (fty : visibility * lang_ty * tag) (arg : expr),
       fields !! f = Some fty →
       args !! f = Some arg →
       expr_has_ty Δ Γ rigid kd arg (subst_ty σ fty.1.2)) →
    ∀ Σ st st' n,
    length Σ = rigid →
    cmd_eval C st (NewC lhs t oσ args) st' n →
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σ (<[lhs:=ClassT t σ]> Γ) st'.1.
  Proof.
    move => wfpdefs wflty hΔ hwf hok hf hdom harg Σ st st' n hrigid hc.
    iIntros "#hΣ #hΣΔ".
    inv hc.
    iIntros "[Hh #Hle]"; simpl.
    (* we need one modality to semantic heap *)
    iDestruct "Hh" as (sh) "(H● & %Hdom & #Hh)".
    assert (hnew: sh !! new = None).
    { apply (not_elem_of_dom (D:=gset loc)).
      by rewrite Hdom not_elem_of_dom.
    }
    set (iFs :=
      (λ(ty: lang_ty), (interp_car (interp_type ty Σ))) <$>
      ((λ x, subst_ty σ x.1.2) <$>
      fields)
    ).
    iMod ((sem_heap_own_update new) with "H●") as "[H● #H◯]" => //;
    first by apply (sem_heap_view_alloc _ new t iFs).
    iIntros "!> !>". (* kill the modalities *)
    iAssert (interp_type (ClassT t σ) Σ (LocV new)) with "[]" as "#Hl".
    { rewrite interp_class_unfold //; last by apply wfpdefs.
      assert (hwf' := hwf).
      inv hwf'.
      iExists new, t, def, def, (gen_targs (length def.(generics))), (interp_list Σ σ), fields, iFs.
      iSplit.
      { iPureIntro.
        repeat split => //.
        + by rewrite /interp_list fmap_length.
        + by econstructor.
        + by rewrite /iFs /= !dom_fmap_L.
      }
      assert (wf_σ : Forall wf_ty σ) by by apply wf_ty_class_inv in hwf.
      iSplit.
      { iModIntro; iNext.
        iIntros (i ? heq v) "hphi".
        rewrite /interp_list in heq.
        apply list_lookup_fmap_inv in heq as [phi [-> heq]].
        assert (hsub: Δ ⊢ phi <: MixedT) by eauto.
        destruct wfpdefs.
        iDestruct (subtype_is_inclusion _ hΔ wf_parent wf_mono wf_constraints_wf wf_constraints_bounded _ _ _ _ hsub v with "hΣ hΣΔ hphi") as "hsub".
        + by eauto.
        + by rewrite interp_mixed_unfold.
      }
      assert (hconstraints: ∀ i c,
      subst_constraints σ def.(constraints) !! i = Some c → Δ ⊢ c.1 <D: c.2
      ).
      { rewrite /subst_constraints => i ? hin.
        apply list_lookup_fmap_inv in hin as [c [-> hin]].
        rewrite /subst_constraint /=.
        inv hok; simplify_eq.
        apply H6 in hin.
        apply subtype_weaken with (Δ' := (Δ ++ subst_constraints σ def.(constraints))) in hin => //;
        last by set_solver.
        apply subtype_constraint_elim in hin => //.
        move => j ? hj.
        rewrite /subst_constraints in hj.
        apply list_lookup_fmap_inv in hj as [cc [-> hj]].
        rewrite /subst_constraint /=.
        by eauto.
      }
      iSplit.
      { iModIntro; iNext.
        iIntros (i c heq v) "h".
        assert (hsub: Δ ⊢ (subst_ty σ c.1) <D: (subst_ty σ c.2)).
        { destruct wfpdefs.
          apply subtype_constraint_elim with (Δ' := subst_constraints σ def.(constraints)) => //.
          apply subtype_weaken with (Δ := subst_constraints σ def.(constraints)); last by set_solver.
          eapply subtype_subst => //.
          eapply SubConstraint.
          apply elem_of_list_lookup_2 in heq.
          by rewrite (surjective_pairing c) in heq.
        }
        destruct wfpdefs.
        rewrite -!interp_type_subst.
        { iApply (subtype_is_inclusion _ hΔ wf_parent wf_mono wf_constraints_wf wf_constraints_bounded _ _ _ _ hsub v with "hΣ hΣΔ") => //.
          apply wf_ty_subst => //.
          apply wf_constraints_wf in H1.
          rewrite /wf_cdef_constraints_wf Forall_lookup in H1.
          apply H1 in heq.
          by apply heq.
        }
        { apply wf_constraints_bounded in H1.
          rewrite /wf_cdef_constraints_bounded Forall_lookup -H2 in H1.
          apply H1 in heq.
          by apply heq.
        }
        { apply wf_constraints_bounded in H1.
          rewrite /wf_cdef_constraints_bounded Forall_lookup -H2 in H1.
          apply H1 in heq.
          by apply heq.
        }
      }
      iSplit.
      { iModIntro; iNext.
        iApply iForall3_interp_gen_targs => //.
        by rewrite /interp_list fmap_length.
      }
      iSplit; last done.
      iIntros (f vis ty orig hff).
      rewrite /iFs /=.
      assert (hbσ: bounded (length σ) ty).
      { apply has_field_bounded in hff; try (by apply wfpdefs).
        destruct hff as (?&?&hh); simplify_eq.
        by rewrite H2.
      }
      apply hf in hff.
      rewrite !lookup_fmap hff /= option_equivI.
      iPureIntro.
      move => x.
      by apply interp_type_subst.
    }
    iSplitL; last by iApply interp_local_tys_update.
    iExists _. iFrame. iSplit; first by rewrite !dom_insert_L Hdom.
    iModIntro. iIntros (???) "Hlook".
    rewrite lookup_insert_Some.
    iDestruct "Hlook" as %[[<- [= <- <-]]|[Hℓ Hlook]]; last first.
    { rewrite lookup_insert_ne; last done.
      by iApply "Hh".
    }
    iExists _. rewrite lookup_insert.
    iSplitR; first done.
    rewrite /heap_models_fields.
    iSplitR.
    {
      apply dom_map_args in H8.
      by rewrite /iFs !dom_fmap_L H8 -hdom.
    }
    iNext.
    iIntros (f iF) "hiF".
    iAssert (⌜f ∈ dom fields⌝)%I as "%hfield".
    {
      rewrite !lookup_fmap.
      rewrite elem_of_dom.
      destruct (fields !! f) => //=.
      by rewrite option_equivI.
    }
    assert (h0: is_Some (args !! f)).
    {
      apply elem_of_dom.
      by rewrite -hdom.
    }
    destruct h0 as [a0 ha0].
    assert (h1: is_Some (vargs !! f)).
    {
      apply elem_of_dom.
      apply dom_map_args in H8.
      by rewrite H8 -hdom.
    }
    destruct h1 as [v0 hv0].
    assert (h2: is_Some (fields !! f)) by (by apply elem_of_dom).
    destruct h2 as [fty hty].
    iExists v0; iSplitR; first done.
    rewrite lookup_fmap.
    assert (heval0: expr_eval Ω a0 = Some v0).
    { rewrite (map_args_lookup _ _ _ args vargs H8 f) in hv0.
      by rewrite ha0 in hv0.
    }
    assert (hty0: expr_has_ty Δ Γ (length Σ) kd a0 (subst_ty σ fty.1.2)) by (by apply harg with f).
    rewrite !lookup_fmap hty /= option_equivI.
    rewrite discrete_fun_equivI.
    iSpecialize ("hiF" $! v0).
    iRewrite -"hiF".
    iDestruct (expr_soundness Δ (length Σ) Σ kd a0 with "hΣ hΣΔ Hle") as "#Ha0" => //; by apply wfpdefs.
  Qed.
End proofs.
