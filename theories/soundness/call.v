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
  Context `{SDTCP: SDTClassSpec}.

  (* Helping the inference with this notation that hides pdefs *)
  Local Notation "Δ ⊢ s <: t" := (@subtype _ _ Δ Plain s t) (at level 70, s at next level, no associativity).
  Local Notation "Δ ⊢ s <D: t" := (@subtype _ _ Δ Aware s t) (at level 70, s at next level, no associativity).

  (* Iris semantic context *)
  Context `{!sem_heapGS Θ}.

  Lemma call_soundness C Δ kd rigid Γ lhs recv t σ name orig mdef args:
    wf_cdefs pdefs →
    wf_lty Γ →
    Forall wf_constraint Δ →
    expr_has_ty Δ Γ rigid kd recv (ClassT t σ) →
    has_method name t orig mdef →
    dom (methodargs mdef) = dom args →
    (∀ (x : string) (ty : lang_ty) (arg : expr),
       methodargs mdef !! x = Some ty →
       args !! x = Some arg →
       expr_has_ty Δ Γ rigid kd arg (subst_ty σ ty)) →
    ∀ Σ st st' n,
    length Σ = rigid →
    cmd_eval C st (CallC lhs recv name args) st' n →
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σ Δ -∗
    □ (▷ (∀ (a : tag) (a0 : list (lang_ty * lang_ty)) 
            (a1 : subtype_kind) (a2 : nat) (a3 : local_tys) 
            (a4 : cmd) (a5 : local_tys),
            ⌜wf_lty a3⌝ -∗
            ⌜bounded_lty a2 a3⌝ -∗
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
    move => wfpdefs wflty hΔ hrecv hhasm hdom hi Σ st st' n hrigid hc.
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
    assert (hwfr : wf_ty (ClassT t σ)) by by apply expr_has_ty_wf in hrecv.
    (* Get inherits relation between dynamic tag and static tag *)
    iDestruct (expr_soundness Δ (length Σ) Σ _ recv with "hΣ hΣΔ Hle") as "#Hrecv" => //.
    rewrite interp_class_unfold //.
    iDestruct "Hrecv" as (? t1 def def1 σin Σt fields ifields) "[%Hpure [#hΣt [#hΣtΔ1 [#hf [#hdyn Hl]]]]]".
    destruct Hpure as ([= <-] & hdef & hdef1 & hlen & ? & hin_t1_t & hfields & hidom).
    iDestruct "Hh" as (sh) "(H● & %Hdom & #Hh)".
    iDestruct (sem_heap_own_valid_2 with "H● Hl") as "#HΦ".
    iDestruct ("Hh" with "[//]") as (?) "[H H▷]".
    iRewrite "H" in "HΦ".
    rewrite option_equivI prod_equivI /=.
    iDestruct "HΦ" as "[%Ht HΦ]".
    fold_leibniz; subst.
    destruct (has_method_ordered _ _ _ _ _ _ _ _ wf_extends_wf wf_override wf_parent wf_constraints_bounded wf_methods_bounded hin_t1_t hhasm0 hhasm)
    as (odef0 & odef & σt1_o0 & σt_o & omdef0 & omdef & hodef0 & hodef & homdef0 & homdef & hin_t1_o0
    & hin_t_o & -> & -> & hincl0 & _).
    assert (hwf0: wf_ty (ClassT orig0 (gen_targs (length odef0.(generics))))).
    { econstructor => //; last by apply gen_targs_wf.
      by rewrite length_gen_targs.
    }
    assert (hh: Forall wf_ty σt_o ∧ length odef.(generics) = length σt_o).
    { apply inherits_using_wf in hin_t_o => //.
      destruct hin_t_o as (?&?&?&hh).
      split; first by apply wf_ty_class_inv in hh.
      inv hh; by simplify_eq.
    }
    destruct hh as [hFσt_o heq1].
    assert (hok0: ok_ty (constraints def1) (ClassT orig0 σt1_o0)).
    { apply inherits_using_ok in hin_t1_o0 => //.
      destruct hin_t1_o0 as (? & ? & ?).
      by simplify_eq.
    }
    assert (hh: wf_mdef_ty orig0 odef0.(constraints) (length odef0.(generics)) (gen_targs (length odef0.(generics))) omdef0).
    { apply wf_mdefs in hodef0.
      by apply hodef0 in homdef0.
    }
    destruct hh as (Γ' & hwfΓ' & hbody & hret).
    assert (hwf_lty0 : wf_lty
    {|
      type_of_this := (orig0, gen_targs (length odef0.(generics)));
      ctxt := methodargs omdef0
    |}).
    { split => //=.
      rewrite map_Forall_lookup => k tk hk.
      apply wf_methods_wf in hodef0.
      apply hodef0 in homdef0.
      by apply homdef0 in hk.
    }
    assert (hbounded : bounded_lty (length odef0.(generics))
    {|
      type_of_this := (orig0, gen_targs (length odef0.(generics)));
      ctxt := methodargs omdef0
    |}).
    { split => /=.
      - rewrite /this_type /=.
        constructor.
        by apply bounded_gen_targs.
      - rewrite map_Forall_lookup => k tk hk.
        apply wf_methods_bounded in hodef0.
        apply hodef0 in homdef0.
        by apply homdef0 in hk.
    }
    assert (hΔ1 : Forall wf_constraint def1.(constraints)).
    { by apply wf_constraints_wf in hdef1.  }
    assert (hΔ0 : Forall wf_constraint odef0.(constraints)).
    { by apply wf_constraints_wf in hodef0. }
    assert (hΔb0 : Forall (bounded_constraint (length odef0.(generics))) odef0.(constraints)).
    { by apply wf_constraints_bounded in hodef0. }
    apply cmd_eval_subst in heval_body.
    rewrite expr_eval_subst in heval_ret.
    assert (hh: Forall wf_ty σt1_o0 ∧ length odef0.(generics) = length σt1_o0).
    { apply inherits_using_wf in hin_t1_o0 => //.
      destruct hin_t1_o0 as (?&?&?&hh).
      split; first by apply wf_ty_class_inv in hh.
      inv hh; by simplify_eq.
    }
    destruct hh as [hFσt1_o0 heq0].
    assert (hh: Forall wf_ty σin ∧ length def.(generics) = length σin).
    { apply inherits_using_wf in hin_t1_t => //.
      destruct hin_t1_t as (?&?&?&hh).
      split; first by apply wf_ty_class_inv in hh.
      inv hh; by simplify_eq.
    }
    destruct hh as [hFσin heq2].
    assert (heq3: length def.(generics) = length σ).
    { inv hwfr; by simplify_eq. }
    iModIntro; iNext.
    iAssert (interp_env_as_mixed (interp_list Σt σt1_o0)) as "hΣt0".
    { iIntros (k ϕi hk v) "#hv".
      rewrite /interp_list in hk.
      apply list_lookup_fmap_inv in hk as [ty [-> hty]].
      iDestruct (submixed_is_inclusion_aux with "hΣt hv") as "hh".
      - rewrite Forall_lookup in hFσt1_o0.
        by apply hFσt1_o0 in hty.
      - by rewrite interp_mixed_unfold.
    }
    iAssert (Σinterp (interp_list Σt σt1_o0) (constraints odef0))%I as "hΣtΔ0".
    { iIntros (k c hc v) "hv".
      inv hok0; simplify_eq.
      assert (hc' := hc).
      apply H4 in hc'.
      iDestruct (subtype_is_inclusion with "hΣt hΣtΔ1") as "hh"; try assumption.
      { by exact hc'. }
      { apply wf_ty_subst => //.
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
      inv hok0; simplify_eq.
      by eauto.
    }
    destruct hincl0 as [hdom0 [hmargs0 hmret0_]].
    iDestruct (neg_interp_variance with "hf") as "hf2".
    assert (hl0 : length (interp_list Σt σt1_o0) = length (generics odef0)).
    { by rewrite /interp_list fmap_length -heq0. }
    iSpecialize ("IH" $! _ _ Plain _ _ _ _ hwf_lty0 hbounded hΔ0 hΔb0 hbody
    (interp_list Σt σt1_o0) _ _ _ hl0 heval_body with "hΣt0 hΣtΔ0"); simpl.
    iDestruct ("IH" with "[Hh Hle H●]") as "Hstep".
    { iClear "IH"; iSplit.
      - iExists _; iFrame.
        iSplit; last done.
        by rewrite Hdom.
      - iSplit => /=.
        + rewrite /interp_this_type interp_this_unseal /interp_this_def /=.
          iExists l, t1, odef0, def1, σt1_o0, Σt, fields, ifields.
          iSplit.
          { iPureIntro; repeat split => //.
            by rewrite /interp_list fmap_length length_gen_targs.
          }
          iSplit; first done.
          iSplit; first done.
          iSplit; last by iSplit.
          iPureIntro.
          rewrite /interp_list.
          apply equiv_Forall2.
          rewrite Forall2_lookup => k.
          rewrite !list_lookup_fmap.
          destruct (σt1_o0 !! k) as [ty | ] eqn:hty; last first.
          { rewrite lookup_seq_ge; first done.
            apply lookup_ge_None_1 in hty.
            by rewrite heq0.
          }
          rewrite lookup_seq_lt /=; last first.
          { apply mk_is_Some in hty.
            apply lookup_lt_is_Some_1 in hty.
            by rewrite heq0.
          }
          constructor => w.
          by rewrite interp_generic_unfold /interp_generic /= list_lookup_fmap hty /=.
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
          move: (hi v _ _ h0 ha) => haty.
          iDestruct (expr_soundness with "hΣ hΣΔ Hle") as "he" => //.
          assert (hmono: mono (neg_variance <$> def.(generics)) (subst_ty σt_o tw)).
          { apply mono_subst with (neg_variance <$> odef.(generics)) => //.
            + apply wf_methods_mono in hodef.
              apply hodef in homdef.
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
              apply inherits_using_mono with (def := def) in hin_t_o => //.
              inv hin_t_o; simplify_eq.
              destruct wi; by eauto.
            + move => i vi ti hvi.
              apply list_lookup_fmap_inv in hvi.
              destruct hvi as [wi [-> hwi]].
              move => hti hc.
              apply inherits_using_mono with (def := def) in hin_t_o => //.
              inv hin_t_o; simplify_eq.
              destruct wi; by eauto.
          }
          assert (hb: bounded (length (generics odef)) tw).
          { apply wf_methods_bounded in hodef => //.
            apply hodef in homdef.
            destruct homdef as [hargs _].
            by apply hargs in htw.
          }
          iAssert (interp_type (subst_ty σt_o tw) (interp_list Σt σin) varg)%I as "he2".
          { iApply (interp_with_mono with "hf2") => //.
            rewrite interp_type_subst //.
            apply bounded_subst with (length odef.(generics)) => //.
            apply inherits_using_wf in hin_t_o => //.
            destruct hin_t_o as (? & ? & hF & hL); simplify_eq.
            by rewrite -heq3.
          }
          iClear "he hf hf2".
          rewrite -interp_type_subst; last first.
          { apply bounded_subst with (length odef.(generics)) => //.
            apply inherits_using_wf in hin_t_o => //.
            destruct hin_t_o as (? & ? & hF & hL); simplify_eq.
            by rewrite -heq2.
          }
          iAssert (
          interp_type (subst_ty σin (subst_ty σt_o tw)) Σt varg-∗
          interp_type (subst_ty σt1_o0 ty) Σt varg)%I as "hh" .
          { iApply (subtype_is_inclusion _ hΔ1 wf_parent wf_mono wf_constraints_wf wf_constraints_bounded _ _ _ _ hsub) => //.
            by apply wf_ty_subst.
          }
          rewrite -interp_type_subst; last first.
          { apply wf_methods_bounded in hodef0.
            apply hodef0 in homdef0.
            rewrite -heq0.
            by apply homdef0 in hv.
          }
          by iApply "hh".
    }
    iRevert "Hstep".
    iApply updN_mono_I.
    iIntros "[Hmodels Hle2]"; iFrame.
    iApply interp_local_tys_update; first by done.
    assert (hmono: mono def.(generics) (subst_ty σt_o omdef.(methodrettype))).
    { apply mono_subst with odef.(generics) => //.
      + apply wf_methods_mono in hodef.
        apply hodef in homdef.
        by apply homdef.
      + apply wf_methods_bounded in hodef.
        apply hodef in homdef.
        by apply homdef.
      + move => i vi ti hvi hti hc.
        apply inherits_using_mono with (def := def) in hin_t_o => //.
        inv hin_t_o; simplify_eq.
        destruct vi; by eauto.
      + move => i vi ti hvi hti hc.
        apply inherits_using_mono with (def := def) in hin_t_o => //.
        inv hin_t_o; simplify_eq.
        destruct vi; by eauto.
    }
    rewrite interp_type_subst; last first.
    { apply bounded_subst with (length odef.(generics)) => //.
      + apply wf_methods_bounded in hodef.
        apply hodef in homdef.
        by apply homdef.
      + apply inherits_using_wf in hin_t_o => //.
        destruct hin_t_o as (?& ? & hF & hL); simplify_eq.
        by rewrite -heq3.
    }
    iApply (interp_with_mono with "hf") => //.
    { apply wf_ty_subst => //.
      apply wf_methods_wf in hodef.
      apply hodef in homdef.
      by apply homdef.
    }
    rewrite -interp_type_subst; last first.
    { apply bounded_subst with (length odef.(generics)) => //.
      + apply wf_methods_bounded in hodef.
        apply hodef in homdef.
        by apply homdef.
      + apply inherits_using_wf in hin_t_o => //.
        destruct hin_t_o as (?&?&hF&?); simplify_eq.
        by rewrite -heq2.
    }
    assert (
    hmret0 : def1.(constraints) ⊢ methodrettype (subst_mdef σt1_o0 omdef0) <D:
    methodrettype (subst_mdef σin (subst_mdef σt_o omdef))).
    { apply subtype_constraint_elim with (Δ' := subst_constraints σt1_o0 odef0.(constraints)) => //.
      apply subtype_weaken with (Δ := subst_constraints σt1_o0 odef0.(constraints)) => //.
      by set_solver.
    }
    iApply (subtype_is_inclusion _ hΔ1 wf_parent wf_mono wf_constraints_wf wf_constraints_bounded _ _ _ _ hmret0) => //.
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
    by iApply (expr_soundness _ _ _ _ _ Γ').
  Qed.
End proofs.
