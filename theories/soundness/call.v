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

  Lemma call_soundness C cdef Δ kd rigid Γ lhs recv exact_ t σ name orig mdef args:
    wf_cdefs →
    wf_lty Γ →
    Forall wf_constraint Δ →
    Forall (bounded_constraint rigid) Δ →
    pdefs !! C = Some cdef →
    expr_has_ty Δ Γ rigid kd recv (ClassT exact_ t σ) →
    has_method name t orig mdef →
    (is_true exact_ ∨ no_this_mdef mdef) →
    mdef.(methodvisibility) = Public →
    dom (methodargs mdef) = dom args →
    (∀ (x : string) (ty : lang_ty) (arg : expr),
       methodargs mdef !! x = Some ty →
       args !! x = Some arg →
       expr_has_ty Δ Γ rigid kd arg (subst_fty  exact_ t σ ty)) →
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
          interp_local_tys Σthis Σ (<[lhs:=subst_fty exact_ t σ (methodrettype mdef)]> Γ) st'.1.
  Proof.
    move => wfpdefs.
    assert (wfpdefs0 := wfpdefs).
    destruct wfpdefs0.
    move => wflty hΔ hΔb hcdef hrecv hhasm hex hpub hdom hty_args.
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
    assert (hwfr : wf_ty (ClassT true t σ)).
    { apply expr_has_ty_wf in hrecv => //.
      by eapply wf_ty_exact.
    }
    assert (hh : ∃ tdef, pdefs !! t = Some tdef ∧ length σ = length tdef.(generics)).
    { apply wf_tyI in hwfr => //.
      destruct hwfr as (tdef & ? & ? & ?).
      by exists tdef; split.
    }
    destruct hh as (tdef & htdef & hlenσ).
    (* Get inherits relation between dynamic tag and static tag *)
    iDestruct (expr_soundness Δ rigid Σthis Σ _ recv with "hΣthis hΣ hΣΔ Hle") as "#Hrecv" => //.
    (* TODO: think of a way to share more of this proof along the two paths
     * since it's a long one. Still working on it so we'll keep it separated
     * for now.
     *)
    destruct exact_.
    - (* receiver is an exact type *)
      rewrite interp_exact_tag_unfold.
      rewrite (interp_exact_tag_unseal _ t (interp_list Σthis Σ σ)).
      iDestruct "Hrecv" as (l0 tdef' fields ifields H) "(#hconstr & #hf0 & #H◯)".
      destruct H as ([= <-] & htdef' & hfields & hidom); simplify_eq.
      iDestruct "Hh" as (sh) "(H● & %Hdom & #Hh)".
      iDestruct (sem_heap_own_valid_2 with "H● H◯") as "#HΦ".
      iDestruct ("Hh" with "[//]") as (?) "[H H▷]".
      iRewrite "H" in "HΦ".
      rewrite option_equivI prod_equivI /=.
      iDestruct "HΦ" as "[%Ht HΦ]".
      fold_leibniz; subst.
      destruct (has_method_fun _ _ _ _ _ _ hhasm hhasm0) as [<- <-].
      assert (h0 := hhasm).
      apply has_method_from_def in h0 => //.
      destruct h0 as (odef & omdef & hodef & homdef & hmdef0 & [σin [hin_t_orig ->]]).
      pose (CT := ClassT false orig (gen_targs (length odef.(generics)))).
      pose (ΔC := (ThisT, CT) :: odef.(constraints)).
      assert (hh: wf_mdef_ty orig ΔC (length odef.(generics)) omdef).
      { apply wf_mdefs in hodef.
        by apply hodef in homdef.
      }
      destruct hh as (Γ' & hwfΓ' & hbody & hret).
      assert (hwf_lty0 : wf_lty omdef.(methodargs)).
      { apply wf_methods_wf in hodef.
        apply hodef in homdef.
        by apply homdef.
      }
      assert (hbounded : bounded_lty (length odef.(generics)) omdef.(methodargs)).
      { apply wf_methods_bounded in hodef.
        apply hodef in homdef.
        by apply homdef.
      }
      assert (hwfΔc: Forall wf_constraint ΔC).
      { apply Forall_cons; split.
        - split => //=.
          econstructor => //; first by rewrite length_gen_targs.
          by apply gen_targs_wf_2.
        - by apply wf_constraints_wf in hodef.
      }
      assert (hbΔc: Forall (bounded_constraint (length odef.(generics))) ΔC).
      { apply Forall_cons; split.
        - split => //=.
          constructor.
          by apply bounded_gen_targs.
        - by apply wf_constraints_bounded in hodef.
      }
      assert (hΔt : Forall wf_constraint tdef.(constraints)).
      { by apply wf_constraints_wf in htdef.  }
      apply cmd_eval_subst in heval_body.
      rewrite expr_eval_subst in heval_ret.
      assert (hh: Forall wf_ty σin ∧
        Forall (bounded (length tdef.(generics))) σin ∧
        length odef.(generics) = length σin ∧
        Forall (λ ty : lang_ty, no_this ty) σin).
      { apply inherits_using_wf in hin_t_orig => //.
        destruct hin_t_orig as (?&?&?&hh&?); simplify_eq.
        split; first by apply wf_ty_classI in hh.
        split; first done.
        split; last done.
        apply wf_tyI in hh as (? & ? & ? & ?); by simplify_eq.
      }
      destruct hh as (hFσin & hBσin & heq2 & hNTσin).
      iModIntro; iNext.
      iAssert (□ interp_env_as_mixed (interp_list Σthis Σ σ))%I as "#hmixed0".
      { iModIntro; iIntros (k ϕi hk v) "#hv".
        rewrite /interp_list in hk.
        apply list_lookup_fmap_inv in hk as [ty [-> hty]].
        iDestruct (submixed_is_inclusion_aux with "hΣthis hΣ hv") as "hh".
        - apply wf_ty_classI in hwfr.
          rewrite Forall_lookup in hwfr.
          by apply hwfr in hty.
        - by rewrite interp_mixed_unfold.
      }
      iAssert(□ interp_env_as_mixed
           (interp_list interp_nothing (interp_list Σthis Σ σ) σin))%I as "#hmixed1".
      { iModIntro; iIntros (k ϕi hk v) "#hv".
        rewrite /interp_list in hk.
        apply list_lookup_fmap_inv in hk as [ty [-> hty]].
        iDestruct (submixed_is_inclusion_aux with "hnothing hmixed0 hv") as "hh".
        - rewrite Forall_lookup in hFσin.
          by apply hFσin in hty.
        - by rewrite interp_mixed_unfold.
      }
      assert (hlt : length (interp_list Σthis Σ σ) = length (generics tdef)).
      { by rewrite /interp_list fmap_length. }
      iAssert (□ Σinterp (interp_exact_tag interp_type t (interp_list Σthis Σ σ))
           (interp_list interp_nothing (interp_list Σthis Σ σ) σin) ΔC)%I as "#hΣΔc".
      { iModIntro.
        iIntros (k c hc v) "hv".
        destruct k as [ | k]; simpl in hc.
        { assert (heq_:
            interp_list (interp_exact_tag interp_type t (interp_list Σthis Σ σ))
              (interp_list interp_nothing (interp_list Σthis Σ σ) σin)
              (gen_targs (length (generics odef))) ≡
            (interp_list interp_nothing (interp_list Σthis Σ σ) σin)).
          { apply interp_list_gen_targs.
            by rewrite /interp_list fmap_length.
          }
          case : hc => <- /=.
          rewrite /ΔC /CT interp_this_unfold interp_tag_unfold.
          rewrite (interp_tag_equivI _ _ heq_ orig v).
          iDestruct ((exact_subtype_is_inclusion_aux _ _ _ _ htdef hlt) with "hmixed0 hv") as "hv".
          by iApply (tag_inherits_using_is_inclusion wf_parent wf_mono
            wf_fields_wf wf_constraints_wf _ _ _ _ _ _ _ htdef hin_t_orig).
        }
        apply inherits_using_ok in hin_t_orig => //.
        destruct hin_t_orig as (? & ? & hokC); simplify_eq.
        apply ok_tyI in hokC as(? & ? & ? & hok); simplify_eq.
        assert (hc' := hc).
        apply hok in hc'.
        iDestruct ((subtype_is_inclusion _ hΔt wf_parent wf_mono wf_constraints_wf
          wf_constraints_no_this wf_constraints_bounded wf_fields_wf
          _ _ _ _ _ hc' v) with "hnothing hmixed0 hconstr") as "hh".
        { apply wf_ty_subst; first done.
          apply wf_constraints_wf in hodef.
          rewrite /wf_cdef_constraints_wf Forall_lookup in hodef.
          by apply hodef in hc as [].
        }
        assert (hbc: bounded_constraint (length σin) c).
        { apply wf_constraints_bounded in hodef.
          rewrite /wf_cdef_constraints_bounded Forall_lookup in hodef.
          rewrite -heq2.
          by apply hodef in hc.
        }
        destruct hbc as [].
        rewrite interp_type_subst; last done.
        rewrite interp_type_subst; last done.
        apply wf_constraints_no_this in hodef.
        rewrite /wf_cdef_constraints_no_this Forall_lookup in hodef.
        apply hodef in hc as [].
        rewrite (interp_type_no_this _ _ _ (interp_exact_tag interp_type t (interp_list Σthis Σ σ)) interp_nothing); last done.
        rewrite (interp_type_no_this _ _ _ (interp_exact_tag interp_type t (interp_list Σthis Σ σ)) interp_nothing); last done.
        by iApply "hh".
      }
      assert (hl0 : length (interp_list interp_nothing (interp_list Σthis Σ σ) σin) = length (generics odef)).
      { by rewrite /interp_list fmap_length heq2. }
      assert (hge0 : length (generics odef) ≥ length (generics odef)) by constructor.
      assert (heqΣ :
        interp_list interp_nothing (interp_list Σthis Σ σ) σin ≡
        take (length odef.(generics)) (interp_list interp_nothing (interp_list Σthis Σ σ) σin)).
      { by rewrite -hl0 firstn_all. }
      iSpecialize ("IH" $! _ odef _ Plain _ _ _ _ hwf_lty0 hbounded hwfΔc hbΔc hodef).
      iSpecialize ("IH" $! t tdef (interp_list Σthis Σ σ) σin htdef hlt).
      iSpecialize ("IH" $! hin_t_orig hbody _ _ _ _ hl0 hge0 heval_body heqΣ).
      iSpecialize ("IH" with "hmixed0 hmixed1 hΣΔc").
      assert (heq_:
        interp_list (interp_exact_tag interp_type t (interp_list Σthis Σ σ))
          (interp_list Σthis Σ σ) σin ≡
          interp_list interp_nothing (interp_list Σthis Σ σ) σin).
      { by apply interp_list_no_this. }
      iDestruct ("IH" with "[Hh Hle H●]") as "Hstep".
      { iClear "IH"; iSplit.
        - iExists _; iFrame.
          iSplit; last done.
          by rewrite Hdom.
        - iSplit => /=.
          + rewrite {2}(interp_exact_tag_unseal _ t (interp_list Σthis Σ σ)).
            rewrite /interp_exact_tag_def /=.
            iExists l, tdef, fields, ifields.
            iSplit; first done.
            iSplit; first done.
            by iSplit.
          + iIntros (v ty hv).
            assert (ha: ∃ arg, args !! v = Some arg).
            { apply elem_of_dom.
              rewrite /subst_mdef /= !dom_fmap_L in hdom.
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
            assert (h0: methodargs (subst_mdef σin omdef) !! v = Some (subst_ty σin ty)).
            { by rewrite /subst_mdef /= !lookup_fmap hv. }
            move: (hty_args v _ _ h0 ha) => haty.
            iDestruct (expr_soundness with "hΣthis hΣ hΣΔ Hle") as "he" => //.
            rewrite /subst_fty interp_type_subst; last first.
            { apply bounded_subst_this; last by (constructor; by apply bounded_gen_targs).
              eapply bounded_subst => //.
              - apply wf_methods_bounded in hodef.
                apply hodef in homdef.
                by apply homdef in hv.
              - by rewrite hlenσ.
            }
            rewrite hlenσ -hlt.
            rewrite interp_type_subst_this => //.
            rewrite interp_type_subst; last first.
            { apply wf_methods_bounded in hodef.
              apply hodef in homdef.
              apply homdef in hv.
              by rewrite -heq2.
            }
            by rewrite (interp_type_equivI _ _ _ heq_).
      }
      iRevert "Hstep".
      iApply updN_mono_I.
      iIntros "[Hmodels Hle2]"; iFrame.
      iApply interp_local_tys_update; first by done.
      rewrite /subst_fty interp_type_subst; last first.
      { apply bounded_subst_this; last by (constructor; apply bounded_gen_targs).
        eapply bounded_subst => //.
        - apply wf_methods_bounded in hodef.
          apply hodef in homdef.
          by apply homdef.
        - by rewrite hlenσ.
      }
      rewrite hlenσ -hlt.
      rewrite interp_type_subst_this => //.
      rewrite /subst_mdef /= interp_type_subst; last first.
      { apply wf_methods_bounded in hodef.
        apply hodef in homdef.
        rewrite -heq2.
        by apply homdef.
      }
      pose (Σthis_ := interp_exact_tag interp_type t (interp_list Σthis Σ σ)).
      pose (Σ_ :=
        interp_list interp_nothing (interp_list Σthis Σ σ) σin).
      iAssert (□ interp_as_mixed Σthis_)%I as "#HHH0".
      { rewrite /Σthis_.
        iModIntro; iIntros (w) "hw".
        iLeft; iRight; iRight.
        iExists t, (interp_list Σthis Σ σ), tdef; iSplit; first done.
        by iApply exact_subtype_is_inclusion_aux.
      }
      iDestruct ((expr_soundness ΔC _ Σthis_ Σ_ _ omdef.(methodret) Γ')
        with "HHH0 hmixed1 hΣΔc Hle2") as "hr" => //.
      by rewrite (interp_type_equivI _ _ _ heq_).
    - (* method signature doesn't mention `this` *)
      case : hex => //= hnothis.
      rewrite interp_tag_unfold interp_tag_equiv //; last first.
      { by rewrite /interp_list fmap_length. }
      iDestruct "Hrecv" as (? t1_ tdef' def1 σin Σt fields ifields) "(%Hpure & #hΣt & #hΣtΔ1 & #hf & #hdyn & Hl)".
      destruct Hpure as ([= <-] & htdef' & hdef1 & hlen1 & hin_t1_t & hfields & hidom).
      pose (Σthis1 := interp_exact_tag interp_type t1_ Σt).
      iAssert (□ ▷ interp_as_mixed Σthis1)%I as "#hmixed1".
      { rewrite /Σthis1; iModIntro; iNext; iIntros (w) "hw".
        iLeft; iRight; iRight.
        iExists t1_, Σt, def1; iSplit; first done.
        by iApply (exact_subtype_is_inclusion_aux with "hΣt hw").
      }
      iAssert (□ ▷ Σinterp Σthis1 Σt (constraints def1))%I as "#hΣtΔ1_".
      { iModIntro; iNext; iIntros (k c hc w) "hw".
        apply wf_constraints_no_this in hdef1.
        assert (hc0 := hc).
        rewrite /wf_cdef_constraints_no_this Forall_lookup in hdef1.
        apply hdef1 in hc as [].
        rewrite (interp_type_no_this _ _ _ Σthis1 interp_nothing); last done.
        rewrite (interp_type_no_this _ _ _ Σthis1 interp_nothing); last done.
        by iApply "hΣtΔ1".
      }
      iDestruct "Hh" as (sh) "(H● & %Hdom & #Hh)".
      iDestruct (sem_heap_own_valid_2 with "H● Hl") as "#HΦ".
      iDestruct ("Hh" with "[//]") as (?) "[H H▷]".
      iRewrite "H" in "HΦ".
      rewrite option_equivI prod_equivI /=.
      iDestruct "HΦ" as "[%Ht HΦ]".
      fold_leibniz; subst.
      simplify_eq.
      destruct (has_method_ordered _ _ _ _ _ _ _ _ wf_override wf_parent
        wf_constraints_bounded wf_methods_bounded hin_t1_t hhasm0 hhasm (*hpub*))
      as (odef0 & odef & σt1_o0 & σt_o & omdef0 & omdef & hodef0 & hodef & homdef0 & homdef & hin_t1_o0
          & hin_t_o & -> & -> & (*hpub0 &*) hincl0 & _).
      assert (hwf0: wf_ty (ClassT false orig0 (gen_targs (length odef0.(generics))))).
      { econstructor => //; last by apply gen_targs_wf_2.
        by rewrite length_gen_targs.
      }
      assert (hh: Forall wf_ty σt_o ∧ length odef.(generics) = length σt_o).
      { apply inherits_using_wf in hin_t_o => //.
        destruct hin_t_o as (?&?&?&hh&?).
        split; first by apply wf_ty_classI in hh.
        apply wf_tyI in hh as (? & ? & ? & ?); by simplify_eq.
      }
      destruct hh as [hFσt_o heq1].
      assert (hok0: ok_ty (constraints def1) (ClassT true orig0 σt1_o0)).
      { apply inherits_using_ok in hin_t1_o0 => //.
        destruct hin_t1_o0 as (? & ? & ?).
        by simplify_eq.
      }
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
      assert (hΔ1 : Forall wf_constraint def1.(constraints)).
      { by apply wf_constraints_wf in hdef1.  }
      assert (hΔ0 : Forall wf_constraint ΔC).
      { apply Forall_cons; by apply wf_constraints_wf in hodef0. }
      assert (hΔb0 : Forall (bounded_constraint (length odef0.(generics))) ΔC).
      { apply Forall_cons; split; last by apply wf_constraints_bounded in hodef0.
        split => //=.
        constructor; by apply bounded_gen_targs.
      }
      apply cmd_eval_subst in heval_body.
      rewrite expr_eval_subst in heval_ret.
      assert (hh: Forall wf_ty σt1_o0 ∧
        length odef0.(generics) = length σt1_o0 ∧
        Forall no_this σt1_o0).
      { apply inherits_using_wf in hin_t1_o0 => //.
        destruct hin_t1_o0 as (?&?&?&hh&?).
        split; first by apply wf_ty_classI in hh.
        split; last done.
        apply wf_tyI in hh as (? & ? & ? & ?); by simplify_eq.
      }
      destruct hh as (hFσt1_o0 & heq0 & hNσt1_o0).
      assert (hh: Forall wf_ty σin ∧
        Forall (bounded (length def1.(generics))) σin ∧
        length tdef.(generics) = length σin ∧
        Forall (λ ty : lang_ty, no_this ty) σin).
      { apply inherits_using_wf in hin_t1_t => //.
        destruct hin_t1_t as (?&?&?&hh&?); simplify_eq.
        split; first by apply wf_ty_classI in hh.
        split; first done.
        split; last done.
        apply wf_tyI in hh as (? & ? & ? & ?); by simplify_eq.
      }
      destruct hh as (hFσin & hBσin & heq2 & hNTσin).
      assert (heq3: length tdef.(generics) = length σ).
      { apply wf_tyI in hwfr as (? & ? & ? & ?); by simplify_eq. }
      iModIntro; iNext.
      iAssert (interp_env_as_mixed (interp_list interp_nothing Σt σt1_o0)) as "hmixed0".
      { iIntros (k ϕi hk v) "#hv".
        rewrite /interp_list in hk.
        apply list_lookup_fmap_inv in hk as [ty [-> hty]].
        iDestruct (submixed_is_inclusion_aux with "hnothing hΣt hv") as "hh".
        - rewrite Forall_lookup in hFσt1_o0.
          by apply hFσt1_o0 in hty.
        - by rewrite interp_mixed_unfold.
      }
      iAssert (Σinterp Σthis1 (interp_list interp_nothing Σt σt1_o0) ΔC)%I as "hΣtΔ0".
      { iIntros (k c hc v) "hv".
        destruct k as [ | k]; simpl in hc.
        { assert (heq_:
            interp_list Σthis1 (interp_list interp_nothing Σt σt1_o0)
              (gen_targs (length (generics odef0))) ≡
            interp_list interp_nothing Σt σt1_o0).
          { apply interp_list_gen_targs.
            by rewrite /interp_list fmap_length.
          }
          case : hc => <- /=.
          rewrite /ΔC /CT interp_this_unfold interp_tag_unfold.
          rewrite (interp_tag_equivI _ _ heq_ orig0 v).
          iDestruct ((exact_subtype_is_inclusion_aux _ _ _ _ hdef1) with "hΣt hv") as "hv".
          { done. }
          by iApply (tag_inherits_using_is_inclusion wf_parent wf_mono
            wf_fields_wf wf_constraints_wf _ _ _ _ _ _ _ hdef1).
        }
        apply ok_tyI in hok0 as (? & ? & ? & hok0); simplify_eq.
        assert (hc' := hc).
        apply hok0 in hc'.
        iDestruct ((subtype_is_inclusion _ hΔ1 wf_parent wf_mono wf_constraints_wf
          wf_constraints_no_this wf_constraints_bounded wf_fields_wf
          _ _ _ _ _ hc' v) with "hnothing hΣt hΣtΔ1") as "hh".
        { apply wf_ty_subst; first done.
          apply wf_constraints_wf in hodef0.
          rewrite /wf_cdef_constraints_wf Forall_lookup in hodef0.
          by apply hodef0 in hc as [].
        }
        assert (hbc: bounded_constraint (length σt1_o0) c).
        { apply wf_constraints_bounded in hodef0.
          rewrite /wf_cdef_constraints_bounded Forall_lookup in hodef0.
          rewrite -heq0.
          by apply hodef0 in hc.
        }
        destruct hbc as [].
        rewrite interp_type_subst; last done.
        rewrite interp_type_subst; last done.
        apply wf_constraints_no_this in hodef0.
        rewrite /wf_cdef_constraints_no_this Forall_lookup in hodef0.
        apply hodef0 in hc as [].
        rewrite (interp_type_no_this _ _ _ Σthis1 interp_nothing); last done.
        rewrite (interp_type_no_this _ _ _ Σthis1 interp_nothing); last done.
        by iApply "hh".
      }
      assert (hconstraints:
        ∀ (i : nat) (c : lang_ty * lang_ty),
        subst_constraints σt1_o0 (constraints odef0) !! i = Some c →
        constraints def1 ⊢ c.1 <D: c.2
      ).
      { move => i ? hc.
        apply list_lookup_fmap_inv in hc as [c [-> hc]].
        rewrite /subst_constraint /=.
        apply ok_tyI in hok0 as (? & ? & ? & ?); simplify_eq.
        by eauto.
      }
      destruct hincl0 as [hdom0 [hmargs0 hmret0_]].
      iDestruct (neg_interp_variance with "hf") as "hf2".
      assert (hl0 : length (interp_list interp_nothing Σt σt1_o0) = length (generics odef0)).
      { by rewrite /interp_list fmap_length -heq0. }
      assert (hge0: length (generics odef0) ≥ length (generics odef0)) by constructor.
      assert (heqΣ: interp_list interp_nothing Σt σt1_o0 ≡
                    take (length odef0.(generics)) (interp_list interp_nothing Σt σt1_o0)).
      { by rewrite -hl0 firstn_all. }
      iSpecialize ("IH" $! orig0 _ _ Plain _ _ _ _ hwf_lty0 hbounded hΔ0 hΔb0 hodef0).
      iSpecialize ("IH" $! t1_ def1 Σt _ hdef1 hlen1 hin_t1_o0 hbody).
      iSpecialize ("IH" $! _ _ _ _ hl0 hge0 heval_body heqΣ with "hΣt hmixed0 hΣtΔ0"); simpl.
      assert (heq_: interp_list interp_nothing Σt σin ≡ interp_list Σthis Σt σin).
      { by apply interp_list_no_this. }
      assert (heq_1: interp_list interp_nothing Σt σin ≡ interp_list Σthis1 Σt σin).
      { by apply interp_list_no_this. }
      iAssert (□ Σinterp Σthis Σt (constraints def1))%I as "#hΣthisΔ".
      { iModIntro; iIntros (k c hc w) "hw".
        apply wf_constraints_no_this in hdef1.
        rewrite /wf_cdef_constraints_no_this Forall_lookup in hdef1.
        assert (hc0 := hc).
        apply hdef1 in hc as [].
        rewrite (interp_type_no_this _ c.1 _ Σthis interp_nothing); last done.
        rewrite (interp_type_no_this _ c.2 _ Σthis interp_nothing); last done.
        iSpecialize ("hΣtΔ1" $! k c hc0 w).
        by iApply ("hΣtΔ1" with "hw").
      }
      iDestruct ("IH" with "[Hh Hle H●]") as "Hstep".
      { iClear "IH"; iSplit.
        - iExists _; iFrame.
          iSplit; last done.
          by rewrite Hdom.
        - iSplit => /=.
          + rewrite (interp_exact_tag_unseal _ t1_ Σt) /interp_exact_tag_def /=.
            iExists l, def1, fields, ifields.
            iSplit; first done.
            iSplit; first done.
            by iSplit.
          + iIntros (v ty hv).
            assert (ha: ∃ arg, args !! v = Some arg).
            { apply elem_of_dom.
              rewrite /subst_mdef /= !dom_fmap_L in hdom0, hmdom.
              rewrite -hdom /subst_mdef /= dom_fmap -hdom0.
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
              rewrite /subst_mdef /= !dom_fmap_L in hdom0.
              rewrite hdom0 in hv.
              apply elem_of_dom in hv.
              rewrite htw in hv.
              by elim: hv.
            }
            assert (h0: methodargs (subst_mdef σt_o omdef) !! v = Some (subst_ty σt_o tw)).
            { by rewrite /subst_mdef /= !lookup_fmap htw. }
            assert (h1 : methodargs (subst_mdef σin (subst_mdef σt_o omdef)) !! v = Some (subst_ty σin (subst_ty σt_o tw))).
            { by rewrite /subst_mdef /= !lookup_fmap htw. }
            assert (h2 : methodargs (subst_mdef σt1_o0 omdef0) !! v = Some (subst_ty σt1_o0 ty)).
            { by rewrite /subst_mdef /= lookup_fmap hv. }
            assert (hsub: def1.(constraints) ⊢ subst_ty σin (subst_ty σt_o tw) <D: subst_ty σt1_o0 ty).
            { move: (hmargs0 v _ _ h2 h1) => hsub_.
              apply subtype_constraint_elim with (Δ' := subst_constraints σt1_o0 odef0.(constraints)) => //.
              apply subtype_weaken with (Δ := subst_constraints σt1_o0 odef0.(constraints)) => //.
              by set_solver.
            }
            assert (hwf_tw: wf_ty (subst_ty σt_o tw)).
            { apply wf_ty_subst => //.
              apply wf_methods_wf in hodef.
              apply hodef in homdef.
              by apply homdef in htw.
            }
            move: (hty_args v _ _ h0 ha) => haty.
            assert (hno : no_this (subst_ty σt_o tw)).
            { case: hnothis => hnothis _.
              by apply hnothis in h0.
            }
            rewrite /subst_fty subst_this_no_this_id in haty; last done.
            iAssert (□ interp_type (subst_ty σ (subst_ty σt_o tw)) Σthis Σ varg)%I as "#he".
            { iModIntro.
              by iDestruct (expr_soundness with "hΣthis hΣ hΣΔ Hle") as "he".
            }
            assert (hmono: mono (neg_variance <$> tdef.(generics)) (subst_ty σt_o tw)).
            { apply mono_subst with (neg_variance <$> odef.(generics)) => //.
              + apply wf_methods_mono in hodef.
                apply hodef in homdef.
                rewrite /wf_mdef_mono hpub in homdef.
                by apply homdef in htw.
              + rewrite map_length.
                apply wf_methods_bounded in hodef.
                apply hodef in homdef.
                by apply homdef in htw.
              + by rewrite map_length heq1.
              + rewrite neg_variance_fmap_idem => i vi ti hvi.
                apply list_lookup_fmap_inv in hvi.
                destruct hvi as [wi [-> hwi]].
                move => hti hc.
                apply inherits_using_mono with (def := tdef) in hin_t_o => //.
                elim/mono_classI : hin_t_o => ????; simplify_eq.
                destruct wi; by eauto.
              + move => i vi ti hvi.
                apply list_lookup_fmap_inv in hvi.
                destruct hvi as [wi [-> hwi]].
                move => hti hc.
                apply inherits_using_mono with (def := tdef) in hin_t_o => //.
                elim/mono_classI : hin_t_o => ????; simplify_eq.
                destruct wi; by eauto.
            }
            assert (hb: bounded (length (generics odef)) tw).
            { apply wf_methods_bounded in hodef => //.
              apply hodef in homdef.
              destruct homdef as [hargs _].
              by apply hargs in htw.
            }
            iAssert (interp_type (subst_ty σt_o tw) Σthis (interp_list interp_nothing Σt σin) varg)%I as "he2".
            { iApply (interp_with_mono with "hf2") => //.
              rewrite interp_type_subst; first done.
              apply bounded_subst with (length odef.(generics)) => //.
              apply inherits_using_wf in hin_t_o => //.
              destruct hin_t_o as (? & ? & hF & hL); simplify_eq.
              by rewrite -heq3.
            }
            iClear "he hf hf2".
            rewrite -/Σthis1.
            rewrite (interp_type_no_this _ _ _ Σthis Σthis1); last done.
            rewrite (interp_type_equivI _ _ _ heq_1).
            rewrite -interp_type_subst; last first.
            { apply bounded_subst with (length odef.(generics)) => //.
              apply inherits_using_wf in hin_t_o => //.
              destruct hin_t_o as (? & ? & hF & hL); simplify_eq.
              by rewrite -heq2.
            }
            iAssert (
              interp_type (subst_ty σin (subst_ty σt_o tw)) Σthis1 Σt varg-∗
              interp_type (subst_ty σt1_o0 ty) Σthis1 Σt varg)%I as "hh" .
            { iApply (subtype_is_inclusion _ hΔ1
              wf_parent wf_mono wf_constraints_wf wf_constraints_no_this
              wf_constraints_bounded wf_fields_wf _ _ _ _ _ hsub) => //.
              by apply wf_ty_subst.
            }
            iDestruct ("hh" with "he2") as "hh2".
            iClear "he2 hh".
            assert (heq__: interp_list interp_nothing Σt σt1_o0 ≡
                           interp_list Σthis1 Σt σt1_o0).
            { by apply interp_list_no_this. }
            rewrite (interp_type_equivI _ _ _ heq__).
            rewrite interp_type_subst; first done.
            apply wf_methods_bounded in hodef0.
            apply hodef0 in homdef0.
            apply homdef0 in hv.
            by rewrite -heq0.
      }
      iRevert "Hstep".
      iApply updN_mono_I.
      iIntros "[Hmodels Hle2]"; iFrame.
      iApply interp_local_tys_update; first by done.
      rewrite -/Σthis -/Σthis1.
      assert (hno : no_this (subst_ty σt_o omdef.(methodrettype))).
      { case: hnothis => _.
        by apply.
      }
      rewrite /subst_fty subst_this_no_this_id; last done.
      rewrite interp_type_subst; last first.
      { apply bounded_subst with (length odef.(generics)) => //.
        + apply wf_methods_bounded in hodef.
          apply hodef in homdef.
          by apply homdef.
        + apply inherits_using_wf in hin_t_o => //.
          destruct hin_t_o as (?& ? & hF & hL); simplify_eq.
          by rewrite -heq3.
      }
      rewrite (interp_type_no_this _ _ _ Σthis Σthis1); last done.
      assert (hmono:
        mono (generics tdef) (subst_ty σt_o (methodrettype omdef))).
      { apply mono_subst with odef.(generics) => //.
        + apply wf_methods_mono in hodef.
          apply hodef in homdef.
          rewrite /wf_mdef_mono hpub in homdef.
          by apply homdef.
        + apply wf_methods_bounded in hodef.
          apply hodef in homdef.
          by apply homdef.
        + move => i vi ti hvi hti hc.
          apply inherits_using_mono with (def := tdef) in hin_t_o => //.
          elim/mono_classI : hin_t_o => ????; simplify_eq.
          destruct vi; by eauto.
        + move => i vi ti hvi hti hc.
          apply inherits_using_mono with (def := tdef) in hin_t_o => //.
          elim/mono_classI : hin_t_o => ????; simplify_eq.
          destruct vi; by eauto.
      }
      iApply (interp_with_mono with "hf") => //.
      { apply wf_ty_subst => //.
        apply wf_methods_wf in hodef.
        apply hodef in homdef.
        by apply homdef.
      }
      rewrite (interp_type_equivI _ _ _ heq_1).
      rewrite -interp_type_subst; last first.
      { apply bounded_subst with (length odef.(generics)) => //.
        + apply wf_methods_bounded in hodef.
          apply hodef in homdef.
          by apply homdef.
        + apply inherits_using_wf in hin_t_o => //.
          destruct hin_t_o as (?&?&hF&?); simplify_eq.
          by rewrite -heq2.
      }
      assert (hmret0 :
        def1.(constraints) ⊢ methodrettype (subst_mdef σt1_o0 omdef0) <D:
        methodrettype (subst_mdef σin (subst_mdef σt_o omdef))).
      { apply subtype_constraint_elim with (Δ' := subst_constraints σt1_o0 odef0.(constraints)) => //.
        apply subtype_weaken with (Δ := subst_constraints σt1_o0 odef0.(constraints)) => //.
        by set_solver.
      }
      iApply (subtype_is_inclusion _ hΔ1 wf_parent wf_mono wf_constraints_wf
        wf_constraints_no_this wf_constraints_bounded wf_fields_wf
        _ _ _ _ _ hmret0) => //.
      { apply wf_ty_subst => //.
        apply wf_methods_wf in hodef0.
        apply hodef0 in homdef0.
        by apply homdef0.
      }
      rewrite interp_type_subst; last first.
      { apply wf_methods_bounded in hodef0.
        apply hodef0 in homdef0.
        rewrite -heq0.
        by apply homdef0.
      }
      iDestruct (expr_soundness ΔC _ _ _ _ _ Γ' _ omdef0.(methodrettype) ret
        wf_parent wf_mono wf_constraints_wf wf_constraints_no_this
        wf_constraints_bounded wf_fields_wf hΔ0 hwfΓ' heval_ret hret
        with "hmixed1 hmixed0 hΣtΔ0 Hle2") as "hr".
      assert (heq__:
        interp_list interp_nothing Σt σt1_o0 ≡ interp_list Σthis1 Σt σt1_o0).
      { by apply interp_list_no_this. }
      by rewrite (interp_type_equivI _ _ _ heq__).
  Qed.
End proofs.
