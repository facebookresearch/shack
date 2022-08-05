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
    pose (Δdyn0 := Δsdt def0.(generics) (gen_targs (length def0.(generics)))).
    pose (Δdyn := Δsdt dyndef.(generics) σ).
    assert (hnewcond: ∀ k c, Δdyn0 !! k = Some c → def0.(constraints) ++ Δdyn ⊢ c.1 <D: c.2).
    { apply inherits_using_extends_dyn in hinherits; try by apply wfpdefs.
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
      { apply Forall_app; by split.
      }
      iNext.
      iAssert (□ Σinterp Σt Δdyn)%I as "#hconstr_dyn".
      { iClear "Hle hmixed hconstr hdyn H◯ Hh HΦ H H▷".
        iModIntro; iIntros (i c hc w) "#h".
        apply Δsdt_lookup_Some in hc as (k & var & ty & hvk & htk & hk).
        iDestruct ("HΣdyn" $! k var hvk) as (ϕ) "[hϕ hiϕ]"; iClear "HΣdyn".
        case : var hvk hk => hvk.
        - case => [-> | ->] /=.
          * iDestruct ("hiϕ" $! w) as "[h0 _]"; iClear "hiϕ".
            rewrite !interp_dynamic_unfold; iApply "h0"; iClear "h0".
            replace ty with (subst_ty σ (GenT k)); last by rewrite /= htk.
            rewrite interp_type_subst; last first.
            { apply lookup_lt_Some in htk.
              by constructor.
            }
            iAssert (Σdyn !! k ≡ Some (interp_type (GenT k) Σdyn))%I as "hϕi".
            { destruct (Σdyn !! k) as [? | ] eqn:heq.
              - rewrite !option_equivI.
                iPureIntro => w'.
                by rewrite interp_generic_unfold /interp_generic heq /=.
              - apply lookup_ge_None_1 in heq.
                apply lookup_lt_Some in htk.
                rewrite hlen hl0 in heq.
                apply lt_not_le in htk.
                by apply htk in heq.
            }
            iRewrite "hϕ" in "hϕi".
            rewrite !option_equivI.
            iRewrite "hϕi".
            assert (hmono : mono dyndef.(generics) (GenT k)).
            { by constructor. }
            by iApply interp_with_mono.
          * iDestruct ("hiϕ" $! w) as "[_ h0]"; iClear "hiϕ".
            replace ty with (subst_ty σ (GenT k)); last by rewrite /= htk.
            rewrite interp_type_subst; last first.
            { apply lookup_lt_Some in htk.
              by constructor.
            }
            rewrite !interp_dynamic_unfold.
            iDestruct ("h0" with "h") as "h1"; iClear "h0 h".
            iAssert (Σdyn !! k ≡ Some (interp_type (GenT k) Σdyn))%I as "hϕi".
            { destruct (Σdyn !! k) as [? | ] eqn:heq.
              - rewrite !option_equivI.
                iPureIntro => w'.
                by rewrite interp_generic_unfold /interp_generic heq /=.
              - apply lookup_ge_None_1 in heq.
                apply lookup_lt_Some in htk.
                rewrite hlen hl0 in heq.
                apply lt_not_le in htk.
                by apply htk in heq.
            }
            iRewrite "hϕ" in "hϕi".
            rewrite !option_equivI.
            iRewrite "hϕi" in "h1"; iClear "hϕi".
            iDestruct (neg_interp_variance with "hf0") as "hf1"; iClear "hf0".
            assert (hmono : mono (neg_variance <$> dyndef.(generics)) (GenT k)).
            { constructor.
              by rewrite list_lookup_fmap hvk.
            }
            by iApply interp_with_mono.
        - move => ->.
          iSpecialize ("hiϕ" $! w).
          rewrite /= !interp_dynamic_unfold; iApply "hiϕ".
          replace ty with (subst_ty σ (GenT k)); last by rewrite /= htk.
          rewrite interp_type_subst; last first.
          { apply lookup_lt_Some in htk.
            by constructor.
          }
          iAssert (Σdyn !! k ≡ Some (interp_type (GenT k) Σdyn))%I as "hϕi".
          { destruct (Σdyn !! k) as [? | ] eqn:heq.
            - rewrite !option_equivI.
              iPureIntro => w'.
              by rewrite interp_generic_unfold /interp_generic heq /=.
            - apply lookup_ge_None_1 in heq.
              apply lookup_lt_Some in htk.
              rewrite hlen hl0 in heq.
              apply lt_not_le in htk.
              by apply htk in heq.
          }
          iRewrite "hϕ" in "hϕi".
          rewrite !option_equivI.
          iRewrite "hϕi".
          assert (hmono : mono dyndef.(generics) (GenT k)).
          { by constructor. }
          by iApply interp_with_mono.
        - move => ->.
          iSpecialize ("hiϕ" $! w).
          replace ty with (subst_ty σ (GenT k)); last by rewrite /= htk.
          rewrite interp_type_subst; last first.
          { apply lookup_lt_Some in htk.
            by constructor.
          }
          rewrite !interp_dynamic_unfold.
          iDestruct ("hiϕ" with "h") as "h1".
          iAssert (Σdyn !! k ≡ Some (interp_type (GenT k) Σdyn))%I as "hϕi".
          { destruct (Σdyn !! k) as [? | ] eqn:heq.
            - rewrite !option_equivI.
              iPureIntro => w'.
              by rewrite interp_generic_unfold /interp_generic heq /=.
            - apply lookup_ge_None_1 in heq.
              apply lookup_lt_Some in htk.
              rewrite hlen hl0 in heq.
              apply lt_not_le in htk.
              by apply htk in heq.
          }
          iRewrite "hϕ" in "hϕi".
          rewrite !option_equivI.
          iRewrite "hϕi" in "h1"; iClear "hϕi".
          iDestruct (neg_interp_variance with "hf0") as "hf1"; iClear "hf0".
          assert (hmono : mono (neg_variance <$> dyndef.(generics)) (GenT k)).
          { apply MonoVCoGen.
            by rewrite list_lookup_fmap hvk.
          }
          by iApply interp_with_mono.
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
      iDestruct (subtype_is_inclusion _ hwf_ wf_parent wf_mono _ Σt _ _ hsub' v) as "hsub".
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
