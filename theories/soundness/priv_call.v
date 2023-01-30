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

  (* TODO: keep in sync with call_soundness. Ideally, factor as much as
   * possible and refactor.
   *)
  Lemma priv_call_soundness C cdef Δ kd rigid Γ lhs name mdef args:
    wf_cdefs pdefs →
    wf_lty Γ →
    Forall wf_constraint Δ →
    Forall (bounded_constraint rigid) Δ →
    pdefs !! C = Some cdef →
    cdef.(classmethods) !! name = Some mdef →
    mdef.(methodvisibility) = Private →
    dom (methodargs mdef) = dom args →
    (∀ (x : string) (ty : lang_ty) (arg : expr),
       methodargs mdef !! x = Some ty →
       args !! x = Some arg →
       expr_has_ty Δ Γ rigid kd arg ty) →
    ∀ t tdef Σt σ,
    pdefs !! t = Some tdef →
    length Σt = length tdef.(generics) →
    inherits_using t C σ →
    ∀ Σ st st' n,
    length Σ = rigid →
    rigid ≥ length cdef.(generics) →
    cmd_eval C st (CallC lhs ThisE name args) st' n →
    let Σthis := interp_exact_tag interp_type t Σt in
    ⌜interp_list interp_nothing Σt σ ≡ Σ⌝ -∗
    □ interp_env_as_mixed Σt -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis Σ Δ -∗

    □ (▷ ∀ C cdef Δ kd rigid Γ cmd Γ',
         ⌜wf_lty Γ⌝ →
         ⌜bounded_lty rigid Γ⌝ →
         ⌜Forall wf_constraint Δ⌝ →
         ⌜Forall (bounded_constraint rigid) Δ⌝ →
         ⌜pdefs !! C = Some cdef⌝ →
         ∀ t tdef Σt σ,
         ⌜pdefs !! t = Some tdef⌝ →
         ⌜length Σt = length tdef.(generics)⌝ →
         ⌜inherits_using t C σ⌝ →
         ⌜cmd_has_ty C Δ kd rigid Γ cmd Γ'⌝ →
         ∀ Σ st st' n,
         ⌜length Σ = rigid⌝ →
         ⌜rigid ≥ length cdef.(generics)⌝ →
         ⌜cmd_eval C st cmd st' n⌝ →
         ⌜interp_list interp_nothing Σt σ ≡ Σ⌝ -∗
         □ interp_env_as_mixed Σt -∗
         □ interp_env_as_mixed Σ -∗
         □ Σinterp (interp_exact_tag interp_type t Σt) Σ Δ -∗
         heap_models st.2 ∗
         interp_local_tys (interp_exact_tag interp_type t Σt) Σ Γ st.1 -∗
         |=▷^n heap_models st'.2 ∗
               interp_local_tys (interp_exact_tag interp_type t Σt) Σ Γ' st'.1) -∗

    heap_models st.2 ∗ interp_local_tys Σthis Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗
          interp_local_tys Σthis Σ (<[lhs:= mdef.(methodrettype)]> Γ) st'.1.
  Proof.
    move => wfpdefs.
    assert (wfpdefs0 := wfpdefs).
    destruct wfpdefs0.
    move => wflty hΔ hΔb hcdef hmdef hpriv hdom hty_args.
    move => t tdef Σt σ htdef hlenΣt hin_t_C_σ.
    move => Σ st st' n hrigid hge hc Σthis.
    iIntros "%heq #hΣt #hΣ #hΣΔ #IH".
    elim/cmd_eval_callI : hc => {n}.
    move => Ω h h' l t0 vs vargs orig mdef0 run_env run_env' ret n.
    move => heval_recv hmap hheap hhasm0 hvis hmdom <- heval_body heval_ret.
    simpl.
    iIntros "[Hh #Hle]".
    iAssert (□ interp_local_tys Σthis Σ Γ Ω)%I as "#Hle_"; first by done.
    destruct Ω as [vthis Ω].
    case: heval_recv => hvthis; subst.
    iAssert (□ interp_as_mixed interp_nothing)%I as "#hnothing".
    { iModIntro; by iIntros (w) "hw". }
    iAssert (□ interp_as_mixed Σthis)%I as "#hΣthis".
    { rewrite /Σthis.
      iModIntro; iIntros (w) "hw".
      iLeft; iRight; iRight.
      iExists t, Σt, tdef; iSplit; first done.
      by iApply (exact_subtype_is_inclusion_aux with "hΣt hw").
    }
    iDestruct "Hle_" as "[#Hthis #Hle_]" => /=.
    iAssert (Σthis (LocV l)) as "#Hl"; first by done.
    rewrite {3}/Σthis.
    rewrite interp_exact_tag_unseal /interp_exact_tag_def /=.
    iDestruct "Hthis" as (l0 ? fields ifields H) "(#hconstr & #hf0 & #H◯)".
    destruct H as ([= <-] & ? & hfields & hidom); simplify_eq.
    assert (hh: Forall wf_ty σ ∧ length σ = length cdef.(generics) ∧
      Forall (λ ty : lang_ty, no_this ty) σ).
    { apply inherits_using_wf in hin_t_C_σ => //.
      destruct hin_t_C_σ as (? & ?& ? & hh & ?).
      apply wf_tyI in hh as (? & ? & hlenC & ?); simplify_eq.
      by eauto.
    }
    destruct hh as (hwfσ & hlen & hnothis).
    assert (hmdefb : mdef_bounded (length cdef.(generics)) mdef).
    { apply wf_methods_bounded in hcdef.
      by apply hcdef in hmdef.
    }
    iDestruct "Hh" as (sh) "(H● & %Hdom & #Hh)".
    iDestruct (sem_heap_own_valid_2 with "H● H◯") as "#HΦ".
    iDestruct ("Hh" with "[//]") as (?) "[H H▷]".
    iRewrite "H" in "HΦ".
    rewrite option_equivI prod_equivI /=.
    iDestruct "HΦ" as "[%Ht HΦ]".
    fold_leibniz; subst.
    assert (hhasm : has_method name C C mdef) by by econstructor.
    destruct (has_method_ordered _ _ _ _ _ _ _ _ wf_override wf_parent
      wf_constraints_bounded wf_methods_bounded hin_t_C_σ hhasm0 hhasm)
    as (odef0 & odef & σt1_o0 & σt_o & omdef0 & omdef & hodef0 & hodef & homdef0 & homdef & hin_t1_o0
        & hin_t_o & -> & -> & (*hpub0 &*) hincl0 & [hh | hh]); last first.
    (* TODO: update this when proper private methods are implemented *)
    { destruct hh as (σ_ & hin_ & _).
      assert (hin__: inherits_using orig C (subst_ty σ_ <$> σt_o)).
      { by eapply inherits_using_trans. }
      move: (wf_override _ _ _ _ _ _ _ _ hodef0 hodef hin__  homdef0 homdef).
      rewrite hpriv.
      by intro hf; elim hf.
    }
    destruct hh as (_ & -> & -> & <-).
    assert (h0 : subst_mdef σt_o omdef = omdef).
    { apply inherits_using_refl in hin_t_o => //.
      destruct hin_t_o as (? & ? & ->); simplify_eq.
      apply subst_mdef_gen_targs.
      by rewrite H.
    }
    rewrite !h0 in hty_args, hdom, hpriv, hmdef hmdefb.
    assert (h1: mdef_bounded (length σt_o) omdef).
    { apply inherits_using_wf in hin_t_o => //.
      destruct hin_t_o as (? & ? & ? & hwf & ?); simplify_eq.
      apply wf_tyI in hwf as (? & ? & hlen0 & ?); simplify_eq.
      by rewrite hlen0.
    }
    rewrite -subst_mdef_mdef in hhasm0; last done.
    rewrite -!subst_mdef_mdef in heval_ret => //.
    rewrite h0 in heval_ret.
    rewrite -subst_mdef_mdef in heval_body; last done.
    rewrite h0 in heval_body.
    rewrite -subst_mdef_mdef in hvis; last done.
    rewrite h0 in hvis.
    rewrite -subst_mdef_mdef in hmdom; last done.
    rewrite h0 in hmdom.
    rewrite h0.
    clear hin_t1_o0 hin_t_o hincl0 hhasm hhasm0 h0 h1 σt_o.
    simplify_eq.
    (* END TODO *)
    pose (CT := ClassT false C (gen_targs (length cdef.(generics)))).
    pose (ΔC := (ThisT, CT) :: cdef.(constraints)).
    assert (hh: wf_mdef_ty C ΔC (length cdef.(generics)) omdef).
    { apply wf_mdefs in hcdef.
      by apply hcdef in homdef0.
    }
    destruct hh as (Γ' & hwfΓ' & hbody & hret).
    assert (hwf_lty0 : wf_lty omdef.(methodargs)).
    { apply wf_methods_wf in hcdef.
      apply hcdef in homdef0.
      by apply homdef0.
    }
    assert (hbounded : bounded_lty (length cdef.(generics)) omdef.(methodargs)).
    { apply wf_methods_bounded in hcdef.
      apply hcdef in homdef0.
      by apply homdef0.
    }
    assert (hΔt : Forall wf_constraint tdef.(constraints)).
    { by apply wf_constraints_wf in htdef.  }
    apply cmd_eval_subst in heval_body.
    rewrite expr_eval_subst in heval_ret.
    iModIntro; iNext.
    assert (heq2: interp_list interp_nothing Σt σ ≡ interp_list interp_nothing Σt σ) by done.
    iAssert (□ interp_env_as_mixed (interp_list interp_nothing Σt σ))%I as "#hΣc".
    { iModIntro; iIntros (k phi hk w) "hw".
      apply list_lookup_fmap_inv in hk as [ty [-> hk]].
      iDestruct (submixed_is_inclusion_aux with "hnothing hΣt hw") as "hh".
      - rewrite Forall_lookup in hwfσ; by apply hwfσ in hk.
      - by rewrite interp_mixed_unfold.
    }
    iAssert (□ Σinterp Σthis Σt tdef.(constraints))%I as "#hΣtc".
    { iModIntro; iIntros (k0 c0 hc0 w) "h0".
      assert (hc0' := hc0).
      apply wf_constraints_no_this in htdef.
      rewrite /wf_cdef_constraints_no_this Forall_lookup in htdef.
      apply htdef in hc0' as [].
      rewrite (interp_type_no_this _ _ _ Σthis interp_nothing); last done.
      rewrite (interp_type_no_this _ _ _ Σthis interp_nothing); last done.
      by iApply "hconstr".
    }
    iAssert (□ Σinterp Σthis (interp_list interp_nothing Σt σ) ΔC)%I as "#hΣΔc".
    { iModIntro.
      iIntros (k c hc v) "hv".
      destruct k as [ | k]; simpl in hc.
      { assert (heq_:
          interp_list Σthis
            (interp_list interp_nothing Σt σ) (gen_targs (length (generics cdef))) ≡
            (interp_list interp_nothing Σt σ)).
        { apply interp_list_gen_targs.
          by rewrite /interp_list fmap_length.
        }
        case : hc => <- /=.
        rewrite /ΔC /CT interp_this_unfold interp_tag_unfold.
        rewrite (interp_tag_equivI _ _ heq_ C v).
        iDestruct ((exact_subtype_is_inclusion_aux _ _ _ _ htdef hlenΣt) with "hΣt hv") as "hv".
        by iApply tag_inherits_using_is_inclusion.
      }
      apply inherits_using_ok in hin_t_C_σ => //.
      destruct hin_t_C_σ as (? & ? & hokC); simplify_eq.
      apply ok_tyI in hokC as(? & ? & ? & hok); simplify_eq.
      assert (hc' := hc).
      apply hok in hc'.
      iDestruct ((subtype_is_inclusion _ hΔt wf_parent wf_mono wf_constraints_wf
        wf_constraints_no_this wf_constraints_bounded wf_fields_wf _ _ _ _ _ hc' v) with "hΣthis hΣt hΣtc") as "hh".
      { apply wf_ty_subst; first done.
        apply wf_constraints_wf in hcdef.
        rewrite /wf_cdef_constraints_wf Forall_lookup in hcdef.
        by apply hcdef in hc as [].
      }
      assert (hbc: bounded_constraint (length σ) c).
      { apply wf_constraints_bounded in hcdef.
        rewrite /wf_cdef_constraints_bounded Forall_lookup in hcdef.
        rewrite hlen.
        by apply hcdef in hc.
      }
      destruct hbc as [].
      rewrite interp_type_subst; last done.
      rewrite interp_type_subst; last done.
      assert (heq_: interp_list Σthis Σt σ ≡ interp_list interp_nothing Σt σ).
      { by apply interp_list_no_this. }
      rewrite (interp_type_equivI _ _ _ heq_).
      rewrite (interp_type_equivI _ _ _ heq_).
      by iApply "hh".
    }
    assert (hlc: length (interp_list interp_nothing Σt σ) = length cdef.(generics)).
    { by rewrite /interp_list !fmap_length. }
    assert (hwfΔc: Forall wf_constraint ((ThisT, CT) :: cdef.(constraints))).
    { apply Forall_cons; split.
      - split => //=.
        econstructor => //; first by rewrite length_gen_targs.
        by apply gen_targs_wf_2.
      - by apply wf_constraints_wf in hcdef.
    }
    assert (hbΔc: Forall (bounded_constraint (length cdef.(generics))) ((ThisT, CT) :: cdef.(constraints))).
    { apply Forall_cons; split.
      - split => //=.
        constructor.
        by apply bounded_gen_targs.
      - by apply wf_constraints_bounded in hcdef.
    }
    assert (hgec: length (generics cdef) ≥ length (generics cdef)) by constructor.
    iSpecialize ("IH" $! C _ _ Plain (length cdef.(generics)) _ _ _ hwf_lty0 hbounded hwfΔc hbΔc hcdef).
    iSpecialize ("IH" $! t tdef Σt σ htdef hlenΣt hin_t_C_σ hbody (interp_list interp_nothing Σt σ)).
    iSpecialize ("IH" $! _ _ _ hlc hgec heval_body heq2 with "hΣt hΣc hΣΔc"); simpl.
    iDestruct ("IH" with "[Hh Hle_ H●]") as "Hstep".
    { iClear "IH"; iSplit.
      - iExists _; iFrame.
        iSplit; last done.
        by rewrite Hdom.
      - iSplit => /=; first done.
        + iIntros (v ty hv).
          assert (ha: ∃ arg, args !! v = Some arg).
          { apply elem_of_dom.
            rewrite /subst_mdef /= !dom_fmap_L in hmdom.
            rewrite -hdom.
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
          move: (hty_args v _ _ hv ha) => haty.
          iDestruct (expr_soundness with "hΣthis hΣ hΣΔ Hle") as "he" => //.
          by rewrite (interp_type_equivI _ _ _ heq).
    }
    iRevert "Hstep".
    iApply updN_mono_I.
    iIntros "[Hmodels Hle2]"; iFrame.
    iApply interp_local_tys_update; first by done.
    iDestruct ((expr_soundness ΔC _ Σthis (interp_list interp_nothing Σt σ)  _ _ Γ' run_env') with "hΣthis hΣc hΣΔc") as "hr" => //.
    rewrite (interp_type_equivI _ _ _ heq).
    by iApply "hr".
  Qed.
End proofs.
