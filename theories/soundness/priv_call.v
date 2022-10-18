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

  (* TODO: keep in sync with call_soundness. Ideally, factor as much as
   * possible and refactor.
   *)
  Lemma priv_call_soundness C Δ kd rigid Γ lhs t σ name mdef args:
    wf_cdefs pdefs →
    wf_lty Γ →
    Forall wf_constraint Δ →
    Forall (bounded_constraint rigid) Δ →
    ok_ty Δ (this_type Γ) →
    type_of_this Γ = (t, σ) →
    has_method name t C mdef →
    mdef.(methodvisibility) = Private →
    dom (methodargs mdef) = dom args →
    (∀ (x : string) (ty : lang_ty) (arg : expr),
       methodargs mdef !! x = Some ty →
       args !! x = Some arg →
       expr_has_ty Δ Γ rigid kd arg (subst_ty σ ty)) →
    ∀ Σ st st' n,
    length Σ = rigid →
    cmd_eval C st (CallC lhs ThisE name args) st' n →
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
          interp_local_tys Σ (<[lhs:=subst_ty σ (methodrettype mdef)]> Γ) st'.1.
  Proof.
    move => wfpdefs wflty hΔ hΔb hokthis ht hhasm hpriv hdom hi Σ st st' n hrigid hc.
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
    assert (ht0: this_type Γ = ClassT t σ).
    { destruct Γ as [[] Γ].
      rewrite /this_type /type_of_this /= in ht.
      rewrite /this_type /type_of_this /=.
      by injection ht; intros; subst; clear ht.
    }
    assert (hwfthis : wf_ty (ClassT t σ)).
    { rewrite -ht0.
      by apply wflty.
    }
    assert (hwfσ : Forall wf_ty σ) by by apply wf_ty_class_inv in hwfthis.
    assert (hcdef : ∃ cdef, pdefs !! C = Some cdef).
    { apply has_method_from_def in hhasm => //.
      destruct hhasm as (cdef & _ & hcdef & _).
      by exists cdef.
    }
    destruct hcdef as [cdef hcdef].
    assert (hrecv: expr_has_ty Δ Γ (length Σ) kd ThisE (ClassT t σ)).
    { rewrite -ht0.
      by apply ThisTy.
    }
    (* Get inherits relation between dynamic tag and static tag *)
    iDestruct (expr_soundness Δ (length Σ) Σ _ ThisE with "hΣ hΣΔ Hle") as "#Hrecv" => //.
    rewrite interp_class_unfold //.
    iDestruct "Hrecv" as (? t1 def def1 σin Σt fields ifields) "[%Hpure [_ [_ [_ [_ Hl]]]]]".
    destruct Hpure as ([= <-] & hdef & hdef1 & hlen & ? & hin_t1_t & hfields & hidom).
    iDestruct "Hh" as (sh) "(H● & %Hdom & #Hh)".
    iDestruct (sem_heap_own_valid_2 with "H● Hl") as "#HΦ".
    iDestruct ("Hh" with "[//]") as (?) "[H H▷]".
    iRewrite "H" in "HΦ".
    rewrite option_equivI prod_equivI /=.
    iDestruct "HΦ" as "[%Ht HΦ]".
    fold_leibniz; subst.
    destruct (has_method_ordered _ _ _ _ _ _ _ _ wf_override wf_parent
      wf_constraints_bounded wf_methods_bounded hin_t1_t hhasm0 hhasm)
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
    destruct hh as (_ & -> & -> & <-); simplify_eq.
    (* END TODO *)
    assert (hh: Forall wf_ty σt_o ∧ length cdef.(generics) = length σt_o).
    { apply inherits_using_wf in hin_t_o => //.
      destruct hin_t_o as (?&?&?&hh).
      split; first by apply wf_ty_class_inv in hh.
      inv hh; by simplify_eq.
    }
    destruct hh as [hFσt_o heq1].
    assert (hokc: ok_ty cdef.(constraints) (ClassT C (gen_targs (length cdef.(generics))))).
    { econstructor => //.
      - move => k ty hty.
        apply lookup_gen_targs in hty as ->.
        by constructor.
      - move => k [c0 c1] hc /=.
        rewrite !subst_ty_id.
        + apply SubConstraint.
          by apply elem_of_list_lookup_2 in hc.
        + apply wf_constraints_bounded in hcdef.
          rewrite /wf_cdef_constraints_bounded Forall_lookup in hcdef.
          by apply hcdef in hc as [].
        + apply wf_constraints_bounded in hcdef.
          rewrite /wf_cdef_constraints_bounded Forall_lookup in hcdef.
          by apply hcdef in hc as [].
    }
    assert (hF: Forall (bounded (length σ)) σt_o).
    { apply inherits_using_wf in hin_t_o => //.
      destruct hin_t_o as (? & ? & ? & ?); simplify_eq.
      inv hwfthis; simplify_eq.
      by rewrite H5.
    }
    assert (hh: wf_mdef_ty C cdef.(constraints) (length cdef.(generics)) (gen_targs (length cdef.(generics))) omdef).
    { apply wf_mdefs in hcdef.
      by apply hcdef in homdef0.
    }
    destruct hh as (Γ' & hwfΓ' & hbody & hret).
    assert (hwf_lty0 : wf_lty
    {|
      type_of_this := (C, gen_targs (length cdef.(generics)));
      ctxt := methodargs omdef
    |}).
    { split.
      - rewrite /this_type /=.
        eapply wf_ty_class => //; first by rewrite length_gen_targs.
        by apply gen_targs_wf_2.
      - rewrite map_Forall_lookup => k tk hk.
        apply wf_methods_wf in hcdef.
        apply hcdef in homdef0.
        by apply homdef0 in hk.
    }
    assert (hbounded : bounded_lty (length cdef.(generics))
    {|
      type_of_this := (C, gen_targs (length cdef.(generics)));
      ctxt := methodargs omdef
    |}).
    { split => /=.
      - rewrite /this_type /=.
        constructor.
        by apply bounded_gen_targs.
      - rewrite map_Forall_lookup => k tk hk.
        apply wf_methods_bounded in hcdef.
        apply hcdef in homdef0.
        by apply homdef0 in hk.
    }
    assert (hΔ1 : Forall wf_constraint def1.(constraints)).
    { by apply wf_constraints_wf in hdef1.  }
    apply cmd_eval_subst in heval_body.
    rewrite expr_eval_subst in heval_ret.
    iModIntro; iNext.
    iAssert (□ interp_env_as_mixed (interp_list Σ (subst_ty σ <$> σt_o)))%I as "#hΣc".
    { iModIntro.
      iIntros (k ϕ hk v) "hv".
      apply list_lookup_fmap_inv in hk as [ty0 [-> h0]].
      apply list_lookup_fmap_inv in h0 as [ty1 [-> h1]].
      iDestruct (submixed_is_inclusion_aux with "hΣ hv") as "hh".
      - apply wf_ty_subst => //.
        rewrite Forall_lookup in hFσt_o; by eapply hFσt_o.
      - by rewrite interp_mixed_unfold.
    }
    assert (hokt: ok_ty Δ (ClassT t σ)).
    { destruct Γ as [[] ?].
      rewrite /this_type /= in ht, hokthis.
      injection ht; intros; subst; clear ht.
      done.
    }
    assert (hok0: ok_ty (Δ ++ subst_constraints σ (constraints def)) (ClassT C (subst_ty σ <$> σt_o))).
    { econstructor => //.
      - move => k ty hk.
        apply list_lookup_fmap_inv in hk as [ty0 [-> h0]].
        eapply ok_ty_subst => //.
        + apply inherits_using_ok in hin_t_o => //.
          destruct hin_t_o as (tdef & htdef & hokC); simplify_eq.
          inv hokC.
          by apply H2 in h0.
        + rewrite Forall_lookup in hFσt_o; by eapply hFσt_o.
        + inv hokt.
          apply Forall_lookup => ? ty hl.
          by apply H2 in hl.
      - move => k [c0 c1] hc /=.
        assert (h0 := hcdef).
        apply wf_constraints_bounded in h0.
        rewrite /wf_cdef_constraints_bounded Forall_lookup in h0.
        rewrite -!subst_ty_subst.
        + apply subtype_weaken with (Δ := subst_constraints σ def.(constraints)); last by set_solver.
          apply subtype_subst => //.
          apply inherits_using_ok in hin_t_o => //.
          destruct hin_t_o as (tdef & htdef & hokC); simplify_eq.
          inv hokC; simplify_eq.
          by apply H4 in hc.
        + rewrite -heq1; by apply h0 in hc as [].
        + rewrite -heq1; by apply h0 in hc as [].
    }
    assert (hok0_: ok_ty Δ (ClassT C (subst_ty σ <$> σt_o))).
    { eapply ok_ty_constraint_trans with (kd := Aware); first by apply hok0.
      move => k c hc /=.
      rewrite lookup_app in hc.
      destruct (Δ !! k) as [c0 | ] eqn:hc0.
      - case : hc => <-.
        apply SubConstraint.
        apply elem_of_list_lookup_2 in hc0.
        by destruct c0.
      - apply list_lookup_fmap_inv in hc as [c1 [-> hc1]].
        rewrite /subst_constraint /=.
        inv hokt; simplify_eq.
        by apply H4 in hc1.
    }
    iAssert (□ Σinterp (interp_list Σ (subst_ty σ <$> σt_o)) (constraints cdef))%I as "#hΣΔc".
    { iModIntro.
      iIntros (k c hc v) "hv".
      inv hok0_; simplify_eq.
      assert (hc' := hc).
      apply H4 in hc'.
      iDestruct ((subtype_is_inclusion _ hΔ wf_parent wf_mono wf_constraints_wf
        wf_constraints_bounded _ _ _ _ hc') with "hΣ hΣΔ") as "hh"; try assumption.
      { apply wf_ty_subst; first by apply wf_ty_subst_map.
        apply wf_constraints_wf in hcdef.
        rewrite /wf_cdef_constraints_wf Forall_lookup in hcdef.
        by apply hcdef in hc as [].
      }
      assert (hbc: bounded_constraint (length (subst_ty σ <$> σt_o)) c).
      { apply wf_constraints_bounded in hcdef.
        rewrite /wf_cdef_constraints_bounded Forall_lookup in hcdef.
        rewrite map_length -heq1.
        by apply hcdef in hc.
      }
      destruct hbc as [].
      rewrite interp_type_subst; last done.
      rewrite interp_type_subst; last done.
      by iApply "hh".
    }
    assert (hlc:
      length (interp_list Σ (subst_ty σ <$> σt_o)) = length cdef.(generics)).
    { by rewrite /interp_list !fmap_length heq1. }
    assert (hentails_cdef: ∀ k s t,
      cdef.(constraints) !! k = Some (s, t) → cdef.(constraints) ⊢ s <: t).
    { move => ??? hc.
      eapply SubConstraint.
      by apply elem_of_list_lookup_2 in hc.
    }
    assert (hwfΔc: Forall wf_constraint cdef.(constraints)).
    { by apply wf_constraints_wf in hcdef. }
    assert (hbΔc: Forall (bounded_constraint (length cdef.(generics))) cdef.(constraints)).
    { by apply wf_constraints_bounded in hcdef. }
    iSpecialize ("IH" $! C _ Plain (length cdef.(generics)) _ _ _ hwf_lty0 hbounded hokc hwfΔc hbΔc
    hbody (interp_list Σ (subst_ty σ <$> σt_o))  _ _ _ hlc heval_body with "hΣc hΣΔc"); simpl.
    iDestruct ("IH" with "[Hh Hle H●]") as "Hstep".
    { iClear "IH"; iSplit.
      - iExists _; iFrame.
        iSplit; last done.
        by rewrite Hdom.
      - iSplit => /=.
        + iDestruct ((this_inherits_using_is_inclusion wf_parent Σ _ _ σ _ (LocV l) hin_t_o)) as "hh" => //.
          destruct Γ as [[? ?] Γ].
          destruct Ω as [vthis Ω].
          rewrite /type_of_this in ht.
          injection ht; intros; subst; clear ht.
          iDestruct "Hle" as "[hthis _]".
          simpl in heval_recv.
          case: heval_recv => ->.
          simpl.
          iDestruct ("hh" with "hthis") as "hh2".
          iClear "hΣ hΣΔ hthis Hl Hh HΦ H H▷ hh H●".
          rewrite /interp_this_type.
          rewrite interp_this_equivI; first done.
          rewrite list_equiv_lookup => k.
          rewrite !list_lookup_fmap.
          destruct (decide (k < length cdef.(generics))) as [hlt | hge].
          * assert (hh: is_Some (σt_o !! k)).
            { rewrite heq1 in hlt.
              by apply lookup_lt_is_Some_2 in hlt.
            }
            destruct hh as [ty hty]; rewrite hty /=.
            rewrite lookup_seq_lt //=.
            f_equiv => w.
            by rewrite interp_generic_unfold /interp_generic /=
              !list_lookup_fmap hty.
          * assert (hle: length cdef.(generics) ≤ k) by lia.
            rewrite lookup_seq_ge //=.
            rewrite heq1 in hle.
            by apply lookup_ge_None_2 in hle as ->.
        + iIntros (v ty hv).
          assert (ha: ∃ arg, args !! v = Some arg).
          { apply elem_of_dom.
            rewrite /subst_mdef /= !dom_fmap_L in hmdom.
            rewrite -hdom /subst_mdef /= dom_fmap.
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
          destruct (methodargs omdef !! v) as [tw | ] eqn:htw => //.
          case: hv => <-; clear ty.
          assert (h0: methodargs (subst_mdef σt_o omdef) !! v = Some (subst_ty σt_o tw)).
          { by rewrite /subst_mdef /= !lookup_fmap htw. }
          move: (hi v _ _ h0 ha) => haty.
          iDestruct (expr_soundness with "hΣ hΣΔ Hle") as "he" => //.
          assert (hb: bounded (length σt_o) tw).
          { apply wf_methods_bounded in hcdef.
            apply hcdef in homdef0.
            apply homdef0 in htw.
            by rewrite -heq1.
          }
          rewrite interp_type_subst; last by eapply bounded_subst.
          rewrite interp_type_subst; last done.
          rewrite interp_type_equivI; first done.
          rewrite /interp_list -list_fmap_compose.
          apply list_fmap_equiv_ext => k ty hty w /=.
          rewrite interp_type_subst; first done.
          apply inherits_using_wf in hin_t_o => //.
          destruct hin_t_o as (? & ? & hB & ?); simplify_eq.
          rewrite Forall_lookup in hB.
          apply hB in hty.
          inv hwfthis; simplify_eq.
          by rewrite H4.
    }
    iRevert "Hstep".
    iApply updN_mono_I.
    iIntros "[Hmodels Hle2]"; iFrame.
    iApply interp_local_tys_update; first by done.
    assert (hb : bounded (length σt_o) (methodrettype omdef)).
    { apply wf_methods_bounded in hcdef.
      apply hcdef in homdef0.
      rewrite -heq1.
      by apply homdef0.
    }
    rewrite subst_ty_subst; last done.
    rewrite interp_type_subst; last by rewrite map_length.
    by iApply (expr_soundness _ _ (interp_list Σ (subst_ty σ <$> σt_o)) _ _ Γ').
  Qed.
End proofs.
