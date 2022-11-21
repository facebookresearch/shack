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

  Lemma dyn_call_soundness C Δ kd rigid Γ lhs recv name args:
    wf_cdefs pdefs →
    wf_lty Γ →
    ok_ty Δ (this_type Γ) →
    Forall wf_constraint Δ →
    expr_has_ty Δ Γ rigid kd recv DynamicT →
    (∀ (x : string) (arg : expr),
       args !! x = Some arg →
       expr_has_ty Δ Γ rigid kd arg DynamicT) →
    match recv with
    | ThisE => False
    | _ => True
    end →
    ∀ Σ st st' n,
    length Σ = rigid →
    cmd_eval C st (CallC lhs recv name args) st' n →
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σ Δ -∗
    □ (▷ (∀ (a : tag) (a0 : list constraint) (a1 : subtype_kind)
            (a2 : nat) (a3 : local_tys) (a4 : cmd)
            (a5 : local_tys),
            ⌜wf_lty a3⌝ -∗
            ⌜bounded_lty a2 a3⌝ -∗
            ⌜ok_ty a0 (this_type a3)⌝ -∗
            ⌜Forall wf_constraint a0⌝ -∗
            ⌜Forall (bounded_constraint a2) a0⌝ -∗
            ∀ (_ : cmd_has_ty a a0 a1 a2 a3 a4 a5)
              (x0 : list (interp Θ)) (x1 x2 : local_env * heap)
              (x3 : nat) (_ : length x0 = a2) (_ : cmd_eval a x1 a4 x2 x3),
              □ interp_env_as_mixed x0 -∗
              □ Σinterp x0 a0 -∗
              heap_models x1.2 ∗ interp_local_tys x0 a3 x1.1 -∗
              |=▷^x3 heap_models x2.2 ∗ interp_local_tys x0 a5 x2.1)) -∗
    heap_models st.2 ∗ interp_local_tys Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗
          interp_local_tys Σ (<[lhs:=DynamicT]> Γ) st'.1.
  Proof.
    move => wfpdefs wflty hokthis hΔ hrecv hi hnotthis Σ st st' n hrigid hc.
    iIntros "#hΣ #hΣΔ #IH".
    inv hc; simpl.
    assert (wfpdefs0 := wfpdefs).
    destruct wfpdefs0.
    iIntros "[Hh #Hle]".
    (* make the script more resilient. Should provide a proper inversion
     * lemma but this is the next best thing.
     *)
    rename H3 into heval_recv.
    rename H4 into hmap.
    rename H5 into hheap.
    rename H6 into hhasm0.
    rename H9 into hmdom.
    rename H13 into heval_body.
    rename H14 into heval_ret.
    iDestruct (expr_soundness Δ _ Σ _ recv with "hΣ hΣΔ Hle") as "#Hl" => //.
    rewrite interp_dynamic_unfold //.
    iDestruct "Hl" as "[H | Hl]".
    { iDestruct "H" as (z) "%Hz".
      discriminate Hz.
    }
    iDestruct "Hl" as "[H | Hl]".
    { iDestruct "H" as (b) "%Hb".
      discriminate Hb.
    }
    iDestruct "Hl" as "[H | He]".
    { iDestruct "H" as "%Hn".
      discriminate Hn.
    }
    rewrite interp_sdt_equiv; last by apply wfpdefs.
    iDestruct "He" as (dyntag Σdyn dyndef [hdyndef hdynlen]) "(#HΣdyn & #hmixed1 & #hΣ1 & He)".
    iDestruct "He" as (?? def def0 ????) "(%H & #hmixed & #hconstr & #hf0 & #hdyn & H◯)".
    destruct H as ([= <-] & hdef & hdef0 & ? & ht0_dyn_σ & hfields & hidom).
    simplify_eq.
    iDestruct "Hh" as (sh) "(H● & %Hdom & #Hh)".
    iDestruct (sem_heap_own_valid_2 with "H● H◯") as "#HΦ".
    iDestruct ("Hh" with "[//]") as (?) "[H H▷]".
    iRewrite "H" in "HΦ".
    rewrite option_equivI prod_equivI /=.
    iDestruct "HΦ" as "[%Ht HΦ]".
    fold_leibniz; subst.
    (* Get the origin definition of the method *)
    assert (h0 := hhasm0).
    apply has_method_from_def in h0 => //.
    destruct h0 as (odef & omdef & hodef & homdef & _ & [σ0 [ht0_orig_σ0 ->]]).
    simplify_eq.
    apply cmd_eval_subst in heval_body.
    rewrite expr_eval_subst in heval_ret.
    (* Fetch the dynamic check fact about omdef *)
    assert (h0 := hodef).
    apply wf_mdefs_dyn in h0.
    assert (hwfdyn_m := homdef).
    apply h0 in hwfdyn_m.
    destruct hwfdyn_m as (rty & wfrty & hbody & hret).
    clear h0.
    (* Helper facts *)
    assert (hok0 : (ok_ty def0.(constraints)) (ClassT orig σ0)).
    { apply inherits_using_ok in ht0_orig_σ0 => //.
      by destruct ht0_orig_σ0 as (? & ? & hok); simplify_eq.
    }
    assert (hokσ0 : Forall (ok_ty def0.(constraints)) σ0).
    { by apply ok_ty_class_inv in hok0. }
    assert (hh: length σ0 = length (generics odef) ∧ wf_ty (ClassT orig σ0)).
    { apply inherits_using_wf in ht0_orig_σ0 => //.
      destruct ht0_orig_σ0 as (? & ? & ? & hwf); split => //.
      inv hwf; by simplify_eq.
    }
    destruct hh as [hl0 hwf0].
    assert (hwfσ0: Forall wf_ty σ0) by by apply wf_ty_class_inv in hwf0.
    iModIntro; iNext.
    (* Show that Σt |= Δt ∧ Δsdt^t *)
    iAssert (□ Σinterp Σt (Δsdt t0))%I as "#hΣt_Δt_sdt_t".
    { by iApply (Σt_models_sdt with "hf0 hmixed1 hΣ1 HΣdyn hmixed hconstr"). }
    (* Build premises of "IH" *)
    iAssert (Σinterp (interp_list Σt σ0) (constraints odef))%I as "hΣtΔo".
    { iIntros (k c hc v) "hv".
      inv hok0; simplify_eq.
      assert (hc' := hc).
      apply H4 in hc'.
      iDestruct (subtype_is_inclusion with "hmixed hconstr") as "hh"; try assumption.
      { by apply wf_constraints_wf in hdef0. }
      { by exact hc'. }
      { apply wf_ty_subst => //.
        apply wf_constraints_wf in hodef.
        rewrite /wf_cdef_constraints_wf Forall_lookup in hodef.
        by apply hodef in hc as [].
      }
      assert (hbc: bounded_constraint (length σ0) c).
      { apply wf_constraints_bounded in hodef.
        rewrite /wf_cdef_constraints_bounded Forall_lookup in hodef.
        rewrite hl0.
        by apply hodef in hc.
      }
      destruct hbc as [].
      rewrite interp_type_subst; last done.
      rewrite interp_type_subst; last done.
      by iApply "hh".
    }
    assert (hwf_lty: wf_lty
      {| type_of_this := (orig, gen_targs (length odef.(generics)));
         ctxt := to_dyn <$> methodargs omdef
      |}).
    { split => /=.
      - rewrite /this_type /=.
        econstructor => //; last by apply gen_targs_wf.
        by rewrite length_gen_targs.
      - rewrite map_Forall_lookup => k tk.
        rewrite lookup_fmap_Some.
        by case => ty [<- ] hk.
    }
    assert (hlty_bounded: bounded_lty (length odef.(generics))
         {| type_of_this := (orig, gen_targs (length odef.(generics)));
            ctxt := to_dyn <$> methodargs omdef
         |}).
    { split => /=.
      - rewrite /this_type /=.
        constructor.
        by apply bounded_gen_targs.
      - rewrite map_Forall_lookup => k tk.
        rewrite /to_dyn lookup_fmap_Some => [[ty [<- hk]]].
        by constructor.
    }
    assert (hwfoΔsdt: Forall wf_constraint (odef.(constraints) ++ Δsdt_m orig name)).
    { apply Forall_app; split; first by apply wf_constraints_wf in hodef.
      apply Forall_lookup => k ty.
      by apply Δsdt_m_wf.
    }
    assert (hwfΔ0: Forall wf_constraint def0.(constraints)).
    { by apply wf_constraints_wf in hdef0. }
    assert (hwf0Δsdt: Forall wf_constraint (constraints def0 ++ Δsdt t0)).
    { apply Forall_app; split => //.
      apply Forall_lookup => k ty.
      by apply Δsdt_wf.
    }
    assert (hΔ_bounded: Forall (bounded_constraint (length odef.(generics)))
              (odef.(constraints) ++ Δsdt_m orig name)).
    { apply Forall_app; split; first by apply wf_constraints_bounded in hodef.
      rewrite Forall_lookup => ??.
      by apply Δsdt_m_bounded.
    }
    iAssert (interp_env_as_mixed (interp_list Σt σ0)) as "hmixed0".
    { iIntros (k phi hk w) "hphi".
      apply list_lookup_fmap_inv in hk as [ty0 [-> hty0]].
      rewrite -(interp_type_unfold Σt MixedT w).
      iApply (submixed_is_inclusion_aux Σt ty0 w) => //.
      rewrite Forall_lookup in hwfσ0.
      by apply hwfσ0 in hty0.
    }
    iAssert (□ Σinterp (interp_list Σt σ0) (constraints odef ++ Δsdt_m orig name))%I as "hΣt_".
    { iModIntro.
      iApply Σinterp_app; first done.
      (* Get relation between Δsdt *)
      assert (h0 := hdef0).
      apply wf_methods_dyn in h0.
      assert (h1 := hhasm0).
      apply h0 in h1.
      destruct h1 as (σo & hσo & hΔsdt_m).
      clear h0.
      replace σo with σ0 in *; last first.
      { by eapply inherits_using_fun. }
      clear σo hσo.
      iIntros (i c hc w) "#hc".
      assert (hsub: subst_constraints σ0 (Δsdt_m orig name) !! i = Some (subst_constraint σ0 c)).
      { by rewrite /subst_constraints list_lookup_fmap hc. }
      apply hΔsdt_m in hsub.
      rewrite /subst_constraint /= in hsub.
      assert (hbc : bounded_constraint (length σ0) c).
      { rewrite hl0.
        by eapply Δsdt_m_bounded.
      }
      destruct hbc as [].
      assert (hwf_sdt: Forall wf_constraint (Δsdt_m orig name)).
      { apply Forall_lookup => k ty.
        by apply Δsdt_m_wf.
      }
      assert (wf_ty (subst_ty σ0 c.1)).
      { apply wf_ty_subst => //.
        rewrite Forall_lookup in hwf_sdt.
        by apply hwf_sdt in hc as [].
      }
      rewrite -!interp_type_subst //.
      iAssert (□ Σinterp Σt (constraints def0 ++ Δsdt t0))%I as "#hconstr_".
      { iModIntro.
        by iApply Σinterp_app.
      }
      by iApply (subtype_is_inclusion with "hmixed hconstr_").
    }
    assert (hl: length (interp_list Σt σ0) = length odef.(generics)).
    { by rewrite /interp_list map_length. }
    assert (hokthis_ : ok_ty (constraints odef ++ Δsdt_m orig name)
            (this_type {|
              type_of_this := (orig, gen_targs (length (generics odef)));
              ctxt := to_dyn <$> methodargs omdef
            |})).
    { rewrite /this_type /=.
      econstructor => //.
      - move => k ty hty.
        apply lookup_gen_targs in hty as ->.
        by constructor.
      - move => k [c0 c1] hc /=.
        apply wf_constraints_bounded in hodef.
        rewrite /wf_cdef_constraints_bounded Forall_lookup in hodef.
        rewrite !subst_ty_id.
        + apply SubConstraint.
          apply elem_of_list_lookup_2 in hc.
          by set_solver.
        + by apply hodef in hc as [].
        + by apply hodef in hc as [].
    }
    (* Use the Löb induction hypothesis *)
    iSpecialize ("IH" $! _ _ Aware _ _ _ _ hwf_lty hlty_bounded
      hokthis_ hwfoΔsdt hΔ_bounded hbody (interp_list Σt σ0) _ _ _ hl heval_body with
      "hmixed0 hΣt_").
    iDestruct ("IH" with "[Hh Hle H●]") as "Hstep".
    { iClear "IH"; iSplit.
      - iExists _; iFrame.
        iSplit; last done.
        by rewrite Hdom.
      - iSplit => /=.
        + rewrite /interp_this_type interp_this_unseal /interp_this_def /=.
          iExists l, t0, def0, σ0, Σt, fields, ifields.
          iSplit; first done.
          iSplit; first done.
          iSplit; first done.
          iSplit; last by iSplit.
          iPureIntro.
          rewrite /interp_list.
          apply equiv_Forall2.
          rewrite Forall2_lookup => k.
          rewrite !list_lookup_fmap.
          destruct (σ0 !! k) as [ty | ] eqn:hty; last first.
          { rewrite lookup_seq_ge; first done.
            apply lookup_ge_None_1 in hty.
            by rewrite -hl0.
          }
          rewrite lookup_seq_lt /=; last first.
          { apply mk_is_Some in hty.
            apply lookup_lt_is_Some_1 in hty.
            by rewrite -hl0.
          }
          constructor => w.
          by rewrite interp_generic_unfold /interp_generic /= list_lookup_fmap hty.
        + iIntros (v ty hv).
          rewrite lookup_fmap_Some in hv.
          destruct hv as [tv [<- hv]].
          rewrite /to_dyn.
          (* From the runtime enforcement *)
          assert (ha: ∃ arg, args !! v = Some arg).
          { apply elem_of_dom.
            rewrite /subst_mdef /= !dom_fmap_L in hmdom.
            rewrite -hmdom.
            by apply elem_of_dom.
          }
          destruct ha as [arg ha].
          assert (hvarg: ∃ varg, vargs !! v = Some varg).
          { apply elem_of_dom.
            apply dom_map_args in hmap.
            rewrite hmap.
            apply elem_of_dom.
            now rewrite ha.
          }
          destruct hvarg as [varg hvarg].
          iExists varg; rewrite hvarg; iSplitR; first done.
          rewrite (map_args_lookup _ _ _ args vargs hmap v) ha /= in hvarg.
          move: (hi v _ ha) => haty.
          iDestruct (expr_soundness with "hΣ hΣΔ Hle") as "he" => //.
          by rewrite !interp_dynamic_unfold.
    }
    iRevert "Hstep".
    iApply updN_mono_I.
    iIntros "[Hmodels Hle2]"; iFrame.
    iApply interp_local_tys_update; first by done.
    rewrite /to_dyn in hret.
    iDestruct (expr_soundness (odef.(constraints) ++ Δsdt_m orig name) _ (interp_list Σt σ0) _ _ rty) as "hh" => //.
    rewrite !interp_dynamic_unfold.
    by iApply "hh".
  Qed.
End proofs.
