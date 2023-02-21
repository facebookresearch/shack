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

From shack Require Import lang progdef subtype ok.
From shack Require Import eval heap modality interp typing.
From shack.soundness Require Import expr defs.

Section proofs.
  (* assume a given set of class definitions and their SDT annotations. *)
  Context `{SDTCVS: SDTClassVarianceSpec}.

  (* Helping the inference with this notation that hides pdefs *)
  Local Notation "Δ ⊢ s <: t" := (@subtype _ _ Δ Plain s t) (at level 70, s at next level, no associativity).
  Local Notation "Δ ⊢ s <D: t" := (@subtype _ _ Δ Aware s t) (at level 70, s at next level, no associativity).

  (* Iris semantic context *)
  Context `{!sem_heapGS Θ}.

  Lemma new_soundness oσ σ C Δ kd rigid Γ lhs t args fields:
    wf_cdefs →
    wf_lty Γ →
    Forall wf_constraint Δ →
    wf_ty (ClassT true t σ) →
    ok_ty Δ (ClassT true t σ) →
    has_fields t fields →
    dom fields = dom args →
    (∀ (f : string) (fty : visibility * lang_ty * tag) (arg : expr),
       fields !! f = Some fty →
       args !! f = Some arg →
        expr_has_ty Δ Γ rigid kd arg (subst_fty true t σ fty.1.2)) →
    ∀ Σthis Σ st st' n,
    length Σ = rigid →
    cmd_eval C st (NewC lhs t oσ args) st' n →
    □ interp_as_mixed Σthis -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σthis Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σthis Σ (<[lhs:=ClassT true t σ]> Γ) st'.1.
  Proof.
    move => wfpdefs wflty hΔ hwf hok hf hdom harg Σthis Σ st st' n hrigid hc.
    iIntros "#hΣthis #hΣ #hΣΔ".
    elim/cmd_eval_newI : hc => {n}.
    move => Ω h new vargs hheap hvargs.
    iIntros "[Hh #Hle]"; simpl.
    (* we need one modality to semantic heap *)
    iDestruct "Hh" as (sh) "(H● & %Hdom & #Hh)".
    assert (hnew: sh !! new = None).
    { apply (not_elem_of_dom (D:=gset loc)).
      by rewrite Hdom not_elem_of_dom.
    }
    assert (hwf' := hwf).
    apply wf_tyI in hwf' as (def & hpdef & hlen & wf_σ).
    set (iFs :=
        (λ x, (interp_car (interp_type (subst_gen t def x.1.2) interp_nothing (interp_list Σthis Σ σ)))) <$>
      fields).
    iMod ((sem_heap_own_update new) with "H●") as "[H● #H◯]" => //;
    first by apply (sem_heap_view_alloc _ new t iFs).
    iIntros "!> !>". (* kill the modalities *)
    iAssert (interp_type (ClassT true t σ) Σthis Σ (LocV new)) with "[]" as "#Hl".
    { rewrite interp_exact_tag_unfold.
      rewrite interp_exact_tag_unseal /interp_exact_tag_def /=.
      iExists new, def, fields, iFs.
      iSplit.
      { iPureIntro.
        repeat split => //.
        by rewrite /iFs /= !dom_fmap_L.
      }
      assert (hconstraints: ∀ i c,
        subst_constraints σ def.(constraints) !! i = Some c → Δ ⊢ c.1 <D: c.2
      ).
      { rewrite /subst_constraints => i ? hin.
        apply list_lookup_fmap_inv in hin as [c [-> hin]].
        rewrite /subst_constraint /=.
        apply ok_tyI in hok as (def' & hdef' & ? & hok); simplify_eq.
        apply hok in hin.
        apply subtype_weaken with (Δ' := (Δ ++ subst_constraints σ def'.(constraints))) in hin => //;
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
        assert (hno: no_this_constraint c).
        { destruct wfpdefs.
          apply wf_constraints_no_this in hpdef.
          rewrite /wf_cdef_constraints_no_this Forall_lookup in hpdef.
          by apply hpdef in heq.
        }
        destruct hno as [].
        destruct wfpdefs.
        rewrite (interp_type_no_this _ _ _ _ Σthis); last done.
        rewrite (interp_type_no_this _ _ _ _ Σthis); last done.
        rewrite -!interp_type_subst.
        { iApply (subtype_is_inclusion _ hΔ wf_parent wf_mono
            wf_constraints_wf wf_constraints_no_this wf_constraints_bounded
            wf_fields_wf _ _ _ _ _ hsub v with "hΣthis hΣ hΣΔ") => //.
          apply wf_ty_subst => //.
          apply wf_constraints_wf in hpdef.
          rewrite /wf_cdef_constraints_wf Forall_lookup in hpdef.
          apply hpdef in heq.
          by apply heq.
        }
        { apply wf_constraints_bounded in hpdef.
          rewrite /wf_cdef_constraints_bounded Forall_lookup -hlen in hpdef.
          apply hpdef in heq.
          by apply heq.
        }
        { apply wf_constraints_bounded in hpdef.
          rewrite /wf_cdef_constraints_bounded Forall_lookup -hlen in hpdef.
          apply hpdef in heq.
          by apply heq.
        }
      }
      iSplit; last done.
      iIntros (f vis ty orig hff).
      rewrite /iFs /=.
      assert (hbσ: bounded (length σ) ty).
      { apply has_field_bounded in hff; try (by apply wfpdefs).
        destruct hff as (?&?&hh); simplify_eq.
        by rewrite hlen.
      }
      apply hf in hff.
      iModIntro; iNext.
      iExists _; iSplit.
      { by rewrite !lookup_fmap hff /= option_equivI. }
      iIntros (w); iSplit; by iIntros.
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
      apply dom_map_args in hvargs.
      by rewrite /iFs !dom_fmap_L hvargs -hdom.
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
      apply dom_map_args in hvargs.
      by rewrite hvargs -hdom.
    }
    destruct h1 as [v0 hv0].
    assert (h2: is_Some (fields !! f)) by (by apply elem_of_dom).
    destruct h2 as [fty hty].
    iExists v0; iSplitR; first done.
    rewrite lookup_fmap.
    assert (heval0: expr_eval Ω a0 = Some v0).
    { rewrite (map_args_lookup _ _ _ args vargs hvargs f) in hv0.
      by rewrite ha0 in hv0.
    }
    assert (hty0: expr_has_ty Δ Γ rigid kd a0 (subst_fty true t σ fty.1.2)) by (by apply harg with f).
    rewrite hty /= option_equivI discrete_fun_equivI.
    iSpecialize ("hiF" $! v0).
    iRewrite -"hiF".
    rewrite /subst_fty in hty0.
    iDestruct (expr_soundness Δ rigid Σthis Σ kd a0 with "hΣthis hΣ hΣΔ Hle") as "#Ha0" => //; try by apply wfpdefs.
    rewrite interp_type_subst; last first.
    { case: fty hty {hty0} => [[vis fty]] orig hty.
      apply hf in hty.
      apply bounded_subst_this => /=.
      - apply has_field_bounded in hty; [ | by apply wfpdefs | by apply wfpdefs].
        destruct hty as (? & ? & hb); simplify_eq.
        by rewrite hlen.
      - constructor.
        by apply bounded_gen_targs.
    }
    assert (hlen0 : length σ = length (interp_list Σthis Σ σ)).
    { by rewrite /interp_list fmap_length. }
    rewrite hlen0 interp_type_subst_this; [ | done | by rewrite -hlen0].
    assert (hlen1: length (interp_list Σthis Σ σ) = length (generics def)) by by rewrite -hlen0.
    rewrite /subst_gen.
    rewrite -interp_type_subst_this //.
    by rewrite hlen1.
  Qed.
End proofs.
