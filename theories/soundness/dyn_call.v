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

  Lemma dyn_call_soundness C cdef Δ kd rigid Γ lhs recv name args:
    wf_cdefs pdefs →
    wf_lty Γ →
    Forall wf_constraint Δ →
    Forall (bounded_constraint rigid) Δ →
    pdefs !! C = Some cdef →
    expr_has_ty Δ Γ rigid kd recv DynamicT →
    (∀ (x : string) (arg : expr),
       args !! x = Some arg →
       expr_has_ty Δ Γ rigid kd arg DynamicT) →
    match recv with
    | ThisE => False
    | _ => True
    end →
    ∀ t0 t0def Σt0 σ0,
    pdefs !! t0 = Some t0def →
    length Σt0 = length t0def.(generics) →
    inherits_using t0 C σ0 →
    ∀ Σ st st' n,
    length Σ = rigid →
    rigid ≥ length cdef.(generics) →
    cmd_eval C st (CallC lhs recv name args) st' n →
    let Σthis := interp_exact_tag interp_type t0 Σt0 in
    ⌜interp_list interp_nothing Σt0 σ0 ≡ take (length cdef.(generics)) Σ⌝ -∗
    □ interp_env_as_mixed Σt0 -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis Σ Δ -∗

    □ (▷ ∀ C cdef Δ kd rigid Γ cmd Γ'
         (_: wf_lty Γ)
         (_: bounded_lty rigid Γ)
         (_: Forall wf_constraint Δ)
         (_: Forall (bounded_constraint rigid) Δ)
         (_: pdefs !! C = Some cdef)
         t tdef Σt σ
         (_: pdefs !! t = Some tdef)
         (_: length Σt = length tdef.(generics))
         (_: inherits_using t C σ)
         (_: cmd_has_ty C Δ kd rigid Γ cmd Γ')
         Σ st st' n
         (_: length Σ = rigid)
         (_: rigid ≥ length cdef.(generics))
         (_: cmd_eval C st cmd st' n),
         ⌜interp_list interp_nothing Σt σ ≡ take (length cdef.(generics)) Σ⌝ -∗
         □ interp_env_as_mixed Σt -∗
         □ interp_env_as_mixed Σ -∗
         □ Σinterp (interp_exact_tag interp_type t Σt) Σ Δ -∗
         heap_models st.2 ∗
         interp_local_tys (interp_exact_tag interp_type t Σt) Σ Γ st.1 -∗
         |=▷^n heap_models st'.2 ∗
               interp_local_tys (interp_exact_tag interp_type t Σt) Σ Γ' st'.1) -∗

    heap_models st.2 ∗ interp_local_tys Σthis Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗
          interp_local_tys Σthis Σ (<[lhs:=DynamicT]> Γ) st'.1.
  Proof.
    move => wfpdefs wflty hΔ hΔb hcdef hrecv hty_args hnotthis.
    move => t0 t0def Σt0 σt0 ht0def hlenΣt0 hin_t0_C.
    move => Σ st st' n hrigid hge hc Σthis.
    iIntros "%hΣeq #hΣt0 #hΣ #hΣΔ #IH".
    elim/cmd_eval_callI : hc.
    move => {n}.
    move => Ω h h' l t vs vargs orig mdef run_env run_env' ret n.
    move => heval_recv hmap hheap hhasm0 hvis hmdom <- heval_body heval_ret /=.
    assert (wfpdefs0 := wfpdefs).
    destruct wfpdefs0.
    iIntros "[Hh #Hle]".
    (* TODO *)
    iAssert (□ interp_as_mixed Σthis)%I as "#hΣthis".
    { rewrite /Σthis.
      iModIntro; iIntros (w) "hw".
      iLeft; iRight; iRight.
      iExists t0, Σt0, t0def; iSplit; first done.
      by iApply (exact_subtype_is_inclusion_aux with "hΣt0 hw").
    }
    iDestruct (expr_soundness Δ _ _ Σ _ recv with "hΣthis hΣ hΣΔ Hle") as "#Hl" => //.
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
    iDestruct "He" as (? tdyn def deftdyn ? Σt ??) "(%H & #hmixed & #hconstr & #hf0 & #hdyn & H◯)".
    destruct H as ([= <-] & hdef & hdeftdyn & hlenΣt & htdyn_dyn_σ & hfields & hidom).
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
    destruct h0 as (odef & omdef & hodef & homdef & _ & [σ0 [htdyn_orig_σ0 ->]]).
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
    assert (hok0 : (ok_ty deftdyn.(constraints)) (ClassT true orig σ0)).
    { apply inherits_using_ok in htdyn_orig_σ0 => //.
      by destruct htdyn_orig_σ0 as (? & ? & hok); simplify_eq.
    }
    assert (hh: length σ0 = length (generics odef) ∧
      wf_ty (ClassT true orig σ0) ∧
      Forall no_this σ0).
    { apply inherits_using_wf in htdyn_orig_σ0 => //.
      destruct htdyn_orig_σ0 as (? & ? & ? & hwf & ?); split => //.
      apply wf_tyI in hwf as (? & ? & ? & ?); by simplify_eq.
    }
    destruct hh as (hl0 & hwf0 & hnothisσ0).
    assert (hwfσ0: Forall wf_ty σ0) by by apply wf_ty_classI in hwf0.
    iModIntro; iNext.
    (* Show that Σt |= Δt ∧ Δsdt^t *)
    iAssert (□ interp_as_mixed interp_nothing)%I as "#hnothing".
    { iModIntro; by iIntros (w) "hw". }
    iAssert (□ Σinterp interp_nothing Σt (Δsdt tdyn))%I as "#hΣt_Δt_sdt_t".
    { by iApply (Σt_models_sdt with "hnothing hf0 hmixed1 hΣ1 HΣdyn hmixed hconstr"). }
    (* Build premises of "IH" *)
    assert (hl: length (interp_list interp_nothing Σt σ0) = length odef.(generics)).
    { by rewrite /interp_list map_length. }
    pose (Σthis1 := interp_exact_tag interp_type tdyn Σt).
    (* TODO *)
    iAssert (□ interp_as_mixed Σthis1)%I as "#hΣthis1".
    { rewrite /Σthis1.
      iModIntro; iIntros (w) "hw".
      iLeft; iRight; iRight.
      iExists tdyn, Σt, deftdyn; iSplit; first done.
      by iApply (exact_subtype_is_inclusion_aux with "hmixed hw").
    }
    iAssert (interp_env_as_mixed (interp_list interp_nothing Σt σ0)) as "hmixed0".
    { iIntros (k phi hk w) "hphi".
      apply list_lookup_fmap_inv in hk as [ty0 [-> hty0]].
      rewrite -(interp_type_unfold _ Σt MixedT w).
      iApply (submixed_is_inclusion_aux _ Σt ty0 w) => //.
      - rewrite Forall_lookup in hwfσ0.
        by apply hwfσ0 in hty0.
      - rewrite (interp_type_no_this _ _ _ interp_nothing Σthis1); first done.
        rewrite Forall_lookup in hnothisσ0.
        by eauto.
    }
    pose (TC := (ThisT, ClassT false orig (gen_targs (length (generics odef))))).
    pose (ΔC := TC :: (odef.(constraints) ++ Δsdt_m orig name)).
    iAssert (□ Σinterp Σthis1 (interp_list interp_nothing Σt σ0) odef.(constraints))%I as "#hΣtΔo".
    { iModIntro; iIntros (k c hc v) "hv".
      apply ok_tyI in hok0 as (? & ? & ? & hok0); simplify_eq.
      assert (hc' := hc).
      apply hok0 in hc'.
      iDestruct (subtype_is_inclusion with "hnothing hmixed hconstr") as "hh"; try assumption.
      { by apply wf_constraints_wf in hdeftdyn. }
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
      assert (hnoc: no_this_constraint c).
      { apply wf_constraints_no_this in hodef.
        rewrite /wf_cdef_constraints_no_this Forall_lookup in hodef.
        by apply hodef in hc.
      }
      destruct hnoc as [].
      rewrite (interp_type_no_this _ _ _ Σthis1 interp_nothing); last done.
      rewrite (interp_type_no_this _ _ _ Σthis1 interp_nothing); last done.
      by iApply "hh".
    }
    assert (hwf_lty: wf_lty (to_dyn <$> omdef.(methodargs))).
    { rewrite /wf_lty map_Forall_lookup => k tk.
      rewrite lookup_fmap_Some.
      by case => ty [<- ] hk.
    }
    assert (hlty_bounded:
      bounded_lty (length odef.(generics)) (to_dyn <$> omdef.(methodargs))).
    { rewrite /bounded_lty map_Forall_lookup => k tk.
      rewrite /to_dyn lookup_fmap_Some => [[ty [<- hk]]].
      by constructor.
    }
    assert (hwfoΔsdt: Forall wf_constraint ΔC).
    { apply Forall_cons; split.
      - split; first done.
        econstructor => //; last by apply gen_targs_wf_2.
        by rewrite length_gen_targs.
      - apply Forall_app; split; first by apply wf_constraints_wf in hodef.
        apply Forall_lookup => k ty.
        by apply Δsdt_m_wf.
    }
    assert (hwfΔ0: Forall wf_constraint deftdyn.(constraints)).
    { by apply wf_constraints_wf in hdeftdyn. }
    assert (hwf0Δsdt: Forall wf_constraint (constraints deftdyn ++ Δsdt tdyn)).
    { apply Forall_app; split => //.
      apply Forall_lookup => k ty.
      by apply Δsdt_wf.
    }
    assert (hΔ_bounded: Forall (bounded_constraint (length odef.(generics))) ΔC).
    { apply Forall_cons; split.
      - split; first done.
        constructor; by apply bounded_gen_targs.
      - apply Forall_app; split; first by apply wf_constraints_bounded in hodef.
        rewrite Forall_lookup => ??.
        by apply Δsdt_m_bounded.
    }
    iAssert (□ Σinterp Σthis1 (interp_list interp_nothing Σt σ0) ΔC)%I as "hΣt_".
    { iModIntro.
      iApply Σinterp_cons.
      { rewrite /=.
        iIntros (w) "#hw".
        rewrite interp_this_unfold interp_tag_unfold.
        assert (heq_:
        interp_list Σthis1 (interp_list interp_nothing Σt σ0)
        (gen_targs (length (generics odef))) ≡
        (interp_list interp_nothing Σt σ0)).
        { apply interp_list_gen_targs.
          by rewrite /interp_list fmap_length.
        }
        rewrite (interp_tag_equivI _ _ heq_ orig w).
        rewrite /Σthis1.
        iDestruct ((exact_subtype_is_inclusion_aux _ _ _ _ hdeftdyn hlenΣt)
          with "hmixed hw") as "hw2".
        by iApply (tag_inherits_using_is_inclusion wf_parent wf_mono
          wf_fields_wf wf_constraints_wf _ _ _ _ _ _ _ hdeftdyn htdyn_orig_σ0).
      }
      iApply Σinterp_app; first done.
      (* Get relation between Δsdt *)
      assert (h0 := hdeftdyn).
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
      assert (hno: no_this_constraint c).
      { by apply Δsdt_m_no_this in hc. }
      destruct hno as [].
      rewrite (interp_type_no_this _ _ _ Σthis1 interp_nothing); last done.
      rewrite (interp_type_no_this _ _ _ Σthis1 interp_nothing); last done.
      rewrite -!interp_type_subst //.
      iAssert (□ Σinterp interp_nothing Σt (constraints deftdyn ++ Δsdt tdyn))%I as "#hconstr_".
      { iModIntro.
        by iApply Σinterp_app.
      }
      by iApply (subtype_is_inclusion with "hnothing hmixed hconstr_").
    }
    (* Use the Löb induction hypothesis *)
    assert (hge2: length (generics odef) ≥ length (generics odef)) by constructor.
    iSpecialize ("IH" $! _ _ _ Aware _ _ _ _ hwf_lty hlty_bounded).
    iSpecialize ("IH" $!  hwfoΔsdt hΔ_bounded hodef tdyn deftdyn Σt σ0).
    iSpecialize ("IH" $! hdeftdyn hlenΣt htdyn_orig_σ0 hbody).
    iSpecialize ("IH" $! (interp_list interp_nothing Σt σ0) _ _ _ hl hge2 heval_body).
    assert (hΣeq2:
      interp_list interp_nothing Σt σ0 ≡
      take (length (generics odef)) (interp_list interp_nothing Σt σ0)).
    { replace (length odef.(generics)) with
        (length (interp_list interp_nothing Σt σ0)).
      by rewrite firstn_all.
    }
    iSpecialize ("IH" $! hΣeq2 with "hmixed hmixed0 hΣt_").
    iDestruct ("IH" with "[Hh Hle H●]") as "Hstep".
    { iClear "IH"; iSplit.
      - iExists _; iFrame.
        iSplit; last done.
        by rewrite Hdom.
      - iSplit => /=.
        + rewrite interp_exact_tag_unseal /interp_exact_tag_def /=.
          iExists l, deftdyn, fields, ifields.
          iSplit; first done.
          iSplit; first done.
          by iSplit.
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
          move: (hty_args v _ ha) => haty.
          iDestruct (expr_soundness with "hΣthis hΣ hΣΔ Hle") as "he" => //.
          by rewrite !interp_dynamic_unfold.
    }
    iRevert "Hstep".
    iApply updN_mono_I.
    iIntros "[Hmodels Hle2]"; iFrame.
    iApply interp_local_tys_update; first by done.
    rewrite /to_dyn in hret.
    iDestruct (expr_soundness ΔC _ Σthis1 (interp_list interp_nothing Σt σ0)
      _ _ rty with "hΣthis1 hmixed0 hΣt_") as "hh" => //.
    rewrite !interp_dynamic_unfold.
    by iApply "hh".
  Qed.
End proofs.
