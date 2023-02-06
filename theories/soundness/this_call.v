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

  Lemma this_call_soundness C cdef Δ kd rigid Γ lhs recv name orig mdef args:
    wf_cdefs pdefs →
    wf_lty Γ →
    Forall wf_constraint Δ →
    Forall (bounded_constraint rigid) Δ →
    pdefs !! C = Some cdef →
    expr_has_ty Δ Γ rigid kd recv ThisT →
    has_method name C orig mdef →
    methodvisibility mdef = Public →
    dom (methodargs mdef) = dom args →
    (∀ (x : string) (ty : lang_ty) (arg : expr),
       methodargs mdef !! x = Some ty →
       args !! x = Some arg →
       expr_has_ty Δ Γ rigid kd arg ty) →
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
          interp_local_tys Σthis Σ (<[lhs:=mdef.(methodrettype)]> Γ) st'.1.
  Proof.
    move => wfpdefs.
    assert (wfpdefs0 := wfpdefs).
    destruct wfpdefs0.
    move => wflty hΔ hΔb hcdef hrecv hhasm hpub hdom hty_args.
    move => t0 t0def Σt0 σ0 ht0def hlenΣt0 hin_t0_C_σ0.
    move => Σ st st' n hrigid hge hc Σthis.
    iIntros "%heq #hΣt0 #hΣ #hΣΔ #IH".
    elim/cmd_eval_callI : hc => {n}.
    move => Ω h h' l t1 vs vargs orig0 mdef0 run_env run_env' ret n.
    move => heval_recv hmap hheap hhasm0 hvis hmdom <- heval_body heval_ret.
    simpl.
    iIntros "[Hh #Hle]".
    iAssert (□ interp_as_mixed interp_nothing)%I as "#hnothing".
    { iModIntro; by iIntros (w) "hw". }
    iAssert (□ interp_as_mixed Σthis)%I as "#hΣthis".
    { rewrite /Σthis.
      iModIntro; iIntros (w) "hw".
      iLeft; iRight; iRight.
      iExists t0, Σt0, t0def; iSplit; first done.
      by iApply (exact_subtype_is_inclusion_aux with "hΣt0 hw").
    }
    (* Get inherits relation between dynamic tag and static tag *)
    iDestruct (expr_soundness Δ rigid Σthis Σ _ recv with "hΣthis hΣ hΣΔ Hle") as "#Hrecv" => //.
    clear hrecv heval_recv.
    iAssert (Σthis (LocV l)) as "#Hrecv0".
    { by rewrite interp_this_unfold {4}/Σthis. }
    rewrite interp_this_unfold {4}/Σthis.
    rewrite interp_exact_tag_unseal /interp_exact_tag_def /=.
    iDestruct "Hrecv" as (l0 _t0def fields ifields H) "(#hconstr & #hf0 & #H◯)".
    destruct H as ([= <-] & _htdef & hfields & hidom); simplify_eq.
    iDestruct "Hh" as (sh) "(H● & %Hdom & #Hh)".
    iDestruct (sem_heap_own_valid_2 with "H● H◯") as "#HΦ".
    iDestruct ("Hh" with "[//]") as (?) "[H H▷]".
    iRewrite "H" in "HΦ".
    rewrite option_equivI prod_equivI /=.
    iDestruct "HΦ" as "[%Ht HΦ]".
    fold_leibniz; subst.
    destruct (has_method_ordered _ _ _ _ _ _ _ _ wf_override wf_parent
      wf_constraints_bounded wf_methods_bounded hin_t0_C_σ0 hhasm0 hhasm (*hpub*))
      as (odef0 & odef & σt0_o0 & σt_o & omdef0 & omdef & hodef0 & hodef & homdef0 & homdef & hin_t0_o0
          & hin_t_o & -> & -> & (*hpub0 &*) hincl0 & _).
    destruct hincl0 as [hdom0 [hmargs0 hmret0_]].
    pose (CT := ClassT false orig0 (gen_targs (length odef0.(generics)))).
    pose (ΔC := (ThisT, CT) :: odef0.(constraints)).
    assert (hh: wf_mdef_ty orig0 ΔC (length odef0.(generics)) omdef0).
    { apply wf_mdefs in hodef0.
      by apply hodef0 in homdef0.
    }
    destruct hh as (Γ' & hwfΓ' & hbody & hret).
    assert (hwf_lty0 : wf_lty omdef0.(methodargs)).
    { apply wf_methods_wf in hodef0.
      apply hodef0 in homdef0.
      by apply homdef0.
    }
    assert (hbounded : bounded_lty (length odef0.(generics)) omdef0.(methodargs)).
    { apply wf_methods_bounded in hodef0.
      apply hodef0 in homdef0.
      by apply homdef0.
    }
    assert (hΔt0 : Forall wf_constraint t0def.(constraints)).
    { by apply wf_constraints_wf in ht0def. }
    apply cmd_eval_subst in heval_body.
    rewrite expr_eval_subst in heval_ret.
    iModIntro; iNext.
    assert (h0 := hin_t0_o0).
    apply inherits_using_wf in h0 => //.
    destruct h0 as (? & ? &? & hwf0 & hnothis0 ); simplify_eq.
    apply wf_tyI in hwf0.
    destruct hwf0 as (? & ? & hlen0 & hwf0); simplify_eq.
    iAssert (□ interp_env_as_mixed (interp_list interp_nothing Σt0 σt0_o0))%I as "#hΣ0".
    { iModIntro; iIntros (k phi hk w) "hw".
      apply list_lookup_fmap_inv in hk as [ty [-> hk]].
      iDestruct (submixed_is_inclusion_aux with "hnothing hΣt0 hw") as "hh".
      - rewrite Forall_lookup in hwf0; by apply hwf0 in hk.
      - by rewrite interp_mixed_unfold.
    }
    iAssert (□ Σinterp Σthis Σt0 t0def.(constraints))%I as "#hΣto".
    { iModIntro; iIntros (k0 c0 hc0 w) "h0".
      assert (hc0' := hc0).
      apply wf_constraints_no_this in ht0def.
      rewrite /wf_cdef_constraints_no_this Forall_lookup in ht0def.
      apply ht0def in hc0' as [].
      rewrite (interp_type_no_this _ _ _ Σthis interp_nothing); last done.
      rewrite (interp_type_no_this _ _ _ Σthis interp_nothing); last done.
      by iApply "hconstr".
    }
    iAssert (□ Σinterp Σthis (interp_list interp_nothing Σt0 σt0_o0) ΔC)%I as "#hΣΔ0".
    { iModIntro.
      iIntros (k c hc v) "hv".
      destruct k as [ | k]; simpl in hc.
      { assert (heq_:
          interp_list Σthis
          (interp_list interp_nothing Σt0 σt0_o0) (gen_targs (length (generics odef0))) ≡
            (interp_list interp_nothing Σt0 σt0_o0)).
        { apply interp_list_gen_targs.
          by rewrite /interp_list fmap_length.
        }
        case : hc => <- /=.
        rewrite /ΔC /CT interp_this_unfold interp_tag_unfold.
        rewrite (interp_tag_equivI _ _ heq_ orig0 v).
        iDestruct ((exact_subtype_is_inclusion_aux _ _ _ _ ht0def hlenΣt0) with "hΣt0 hv") as "hv".
        by iApply (tag_inherits_using_is_inclusion with "hv").
      }
      apply inherits_using_ok in hin_t0_o0 => //.
      destruct hin_t0_o0 as (? & ? & hok0); simplify_eq.
      apply ok_tyI in hok0 as(? & ? & ? & hok); simplify_eq.
      assert (hc' := hc).
      apply hok in hc'.
      iDestruct ((subtype_is_inclusion _ hΔt0 wf_parent wf_mono wf_constraints_wf
        wf_constraints_no_this wf_constraints_bounded wf_fields_wf _ _ _ _ _ hc' v) with "hΣthis hΣt0 hΣto") as "hh".
      { apply wf_ty_subst; first done.
        apply wf_constraints_wf in hodef0.
        rewrite /wf_cdef_constraints_wf Forall_lookup in hodef0.
        by apply hodef0 in hc as [].
      }
      assert (hbc: bounded_constraint (length σt0_o0) c).
      { apply wf_constraints_bounded in hodef0.
        rewrite /wf_cdef_constraints_bounded Forall_lookup in hodef0.
        rewrite hlen0.
        by apply hodef0 in hc.
      }
      destruct hbc as [].
      rewrite interp_type_subst; last done.
      rewrite interp_type_subst; last done.
      assert (heq_: interp_list Σthis Σt0 σt0_o0 ≡ interp_list interp_nothing Σt0 σt0_o0).
      { by apply interp_list_no_this. }
      rewrite (interp_type_equivI _ _ _ heq_).
      rewrite (interp_type_equivI _ _ _ heq_).
      by iApply "hh".
    }
    assert (hlo: length (interp_list interp_nothing Σt0 σt0_o0) =
                 length (generics odef0)).
    { by rewrite /interp_list !fmap_length hlen0. }
    assert (heq2: interp_list interp_nothing Σt0 σt0_o0 ≡
                  take (length (generics odef0)) (interp_list interp_nothing Σt0 σt0_o0)).
    { by rewrite -hlo firstn_all. }
    assert (hwfΔo: Forall wf_constraint ((ThisT, CT) :: odef0.(constraints))).
    { apply Forall_cons; split.
      - split => //=.
        econstructor => //; first by rewrite length_gen_targs.
        by apply gen_targs_wf_2.
      - by apply wf_constraints_wf in hodef0.
    }
    assert (hbΔo: Forall (bounded_constraint (length odef0.(generics))) ((ThisT, CT) :: odef0.(constraints))).
    { apply Forall_cons; split.
      - split => //=.
        constructor.
        by apply bounded_gen_targs.
      - by apply wf_constraints_bounded in hodef0.
    }
    assert (hgeo: length (generics odef0) ≥ length (generics odef0)) by constructor.
    assert (hok0: ok_ty (constraints t0def) (ClassT true orig0 σt0_o0)).
    { apply inherits_using_ok in hin_t0_o0 => //.
      destruct hin_t0_o0 as (? & ? & ?).
      by simplify_eq.
    }
    assert (hconstraints: ∀ i c,
      subst_constraints σt0_o0 (constraints odef0) !! i = Some c →
      constraints t0def ⊢ c.1 <D: c.2
    ).
    { move => i ? hc.
      apply list_lookup_fmap_inv in hc as [c [-> hc]].
      rewrite /subst_constraint /=.
      apply ok_tyI in hok0 as (? & ? & ? & ?); simplify_eq.
      by eauto.
    }
    assert (h_ := hin_t_o).
    apply inherits_using_wf in h_ => //.
    destruct h_ as (? & ? &? & hwf & hnoo).
    apply wf_tyI in hwf as (? & ? & hleno & hwfo); simplify_eq.
    assert (h_ := hin_t0_C_σ0).
    apply inherits_using_wf in h_ => //.
    destruct h_ as (? & ? &? & hwfo0 & hno0).
    apply wf_tyI in hwfo0 as (? & ? & hleno0 & hwfo0); simplify_eq.
    iSpecialize ("IH" $! orig0 _ _ Plain (length odef0.(generics)) _ _ _ hwf_lty0 hbounded hwfΔo hbΔo hodef0).
    iSpecialize ("IH" $! t0 t0def Σt0 σt0_o0 ht0def hlenΣt0 hin_t0_o0 hbody).
    iSpecialize ("IH" $! (interp_list interp_nothing Σt0 σt0_o0)).
    iSpecialize ("IH" $! _ _ _ hlo hgeo heval_body heq2 with "hΣt0 hΣ0 hΣΔ0"); simpl.
    assert (heq_0 : interp_list interp_nothing Σt0 σt0_o0 ≡
                    interp_list Σthis Σt0 σt0_o0).
    { by apply interp_list_no_this. }
    iDestruct ("IH" with "[Hh Hle H●]") as "Hstep".
    { iClear "IH"; iSplit.
      - iExists _; iFrame.
        iSplit; last done.
        by rewrite Hdom.
      - iSplit => /=; first done.
        iIntros (v ty hv).
        rewrite !dom_fmap_L in hdom, hmdom, hdom0.
        assert (ha: ∃ arg, args !! v = Some arg).
        { apply elem_of_dom.
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
        destruct (methodargs omdef !! v) as [tw | ] eqn:htw; last first.
        { apply mk_is_Some in hv.
          apply elem_of_dom in hv.
          rewrite hdom0 in hv.
          apply elem_of_dom in hv.
          rewrite htw in hv.
          by elim: hv.
        }
        assert (h0: methodargs (subst_mdef σt_o omdef) !! v = Some (subst_ty σt_o tw)).
        { by rewrite /subst_mdef /= !lookup_fmap htw. }
        assert (h1 : methodargs (subst_mdef σ0 (subst_mdef σt_o omdef)) !! v = Some (subst_ty σ0 (subst_ty σt_o tw))).
        { by rewrite /subst_mdef /= !lookup_fmap htw. }
        assert (h2 : methodargs (subst_mdef σt0_o0 omdef0) !! v = Some (subst_ty σt0_o0 ty)).
        { by rewrite /subst_mdef /= lookup_fmap hv. }
        assert (hsub: t0def.(constraints) ⊢ subst_ty σ0 (subst_ty σt_o tw) <D: subst_ty σt0_o0 ty).
        { move: (hmargs0 v _ _ h2 h1) => hsub_.
          apply subtype_constraint_elim with (Δ' := subst_constraints σt0_o0 odef0.(constraints)) => //.
          apply subtype_weaken with (Δ := subst_constraints σt0_o0 odef0.(constraints)) => //.
          by set_solver.
        }
        assert (hwf_tw: wf_ty (subst_ty σt_o tw)).
        { apply wf_ty_subst => //.
          apply wf_methods_wf in hodef.
          apply hodef in homdef.
          by apply homdef in htw.
        }
        move: (hty_args v _ _ h0 ha) => haty.
        iAssert (□ interp_type (subst_ty σt_o tw) Σthis Σ varg)%I as "#he".
        { iModIntro.
          by iDestruct (expr_soundness with "hΣthis hΣ hΣΔ Hle") as "he".
        }
        assert (hb: bounded (length (generics odef)) tw).
        { apply wf_methods_bounded in hodef => //.
          apply hodef in homdef.
          destruct homdef as [hargs _].
          by apply hargs in htw.
        }
        rewrite -/Σthis.
        rewrite (interp_type_equivI _ _ _ heq_0).
        rewrite -interp_type_subst; last first.
        { apply wf_methods_bounded in hodef0.
          apply hodef0 in homdef0.
          apply homdef0 in hv.
          by rewrite hlen0.
        }
        iAssert (
          interp_type (subst_ty σ0 (subst_ty σt_o tw)) Σthis Σt0 varg-∗
          interp_type (subst_ty σt0_o0 ty) Σthis Σt0 varg)%I as "hh" .
        { iApply (subtype_is_inclusion _ hΔt0
          wf_parent wf_mono wf_constraints_wf wf_constraints_no_this
          wf_constraints_bounded wf_fields_wf _ _ _ _ _ hsub) => //.
          by apply wf_ty_subst.
        }
        iApply "hh"; iClear "hh".
        rewrite (interp_type_subst _ Σt0); last first.
        { apply bounded_subst with (length odef.(generics)) => //.
          by rewrite hleno0.
        }
        assert (heq__: interp_list Σthis Σt0 σ0 ≡
                       interp_list interp_nothing Σt0 σ0).
        { by apply interp_list_no_this. }
        rewrite (interp_type_equivI _ _ _ heq__).
        rewrite (interp_type_equivI _ _ _ heq).
        rewrite interp_type_take => //.
        { by apply bounded_subst with (length odef.(generics)). }
    }
    iRevert "Hstep".
    iApply updN_mono_I.
    iIntros "[Hmodels Hle2]"; iFrame.
    iApply interp_local_tys_update; first by done.
    assert (hmret0 :
      t0def.(constraints) ⊢ methodrettype (subst_mdef σt0_o0 omdef0) <D:
      methodrettype (subst_mdef σ0 (subst_mdef σt_o omdef))).
    { apply subtype_constraint_elim with (Δ' := subst_constraints σt0_o0 odef0.(constraints)) => //.
      apply subtype_weaken with (Δ := subst_constraints σt0_o0 odef0.(constraints)) => //.
      by set_solver.
    }
    rewrite -(interp_type_take _ _ Σ (length cdef.(generics))) //; first last.
    { apply bounded_subst with (length odef.(generics)) => //.
      apply wf_methods_bounded in hodef.
      apply hodef in homdef.
      by apply homdef.
    }
    rewrite (interp_type_equivI _ (take (length (generics cdef)) Σ)
      (interp_list interp_nothing Σt0 σ0)); last done.
    assert (heq_: interp_list interp_nothing Σt0 σ0 ≡
                   interp_list Σthis Σt0 σ0).
    { by apply interp_list_no_this. }
    rewrite (interp_type_equivI _ _ _ heq_).
    rewrite -interp_type_subst; last first.
    { apply bounded_subst with (length odef.(generics)) => //.
      + apply wf_methods_bounded in hodef.
        apply hodef in homdef.
        by apply homdef.
      + by rewrite hleno0.
    }
    iApply (subtype_is_inclusion _ hΔt0
      wf_parent wf_mono wf_constraints_wf wf_constraints_no_this
      wf_constraints_bounded wf_fields_wf _ _ _ _ _ hmret0 ) => //.
    { rewrite /subst_mdef /=.
      apply wf_ty_subst => //.
      apply wf_methods_wf in hodef0.
      apply hodef0 in homdef0.
      by apply homdef0.
    }
    rewrite interp_type_subst; last first.
    { apply wf_methods_bounded in hodef0.
      apply hodef0 in homdef0.
      rewrite hlen0.
      by apply homdef0.
    }
    iDestruct (expr_soundness ΔC _ _ _ _ _ Γ' _ omdef0.(methodrettype) ret
      wf_parent wf_mono wf_constraints_wf wf_constraints_no_this
      wf_constraints_bounded wf_fields_wf hwfΔo hwfΓ' heval_ret hret
      with "hΣthis hΣ0 hΣΔ0 Hle2") as "hr".
    assert (heq__:
      interp_list interp_nothing Σt0 σt0_o0 ≡ interp_list Σthis Σt0 σt0_o0).
    { by apply interp_list_no_this. }
    by rewrite (interp_type_equivI _ _ _ heq__).
  Qed.
End proofs.
