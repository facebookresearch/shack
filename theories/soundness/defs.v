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

Section proofs.
  (* assume a given set of class definitions and their SDT annotations. *)
  Context `{SDTCVS: SDTClassVarianceSpec}.

  (* Iris semantic context *)
  Context `{!sem_heapGS Θ}.
  Notation γ := sem_heap_name.

  Lemma interp_local_tys_update Σ v Γ Ω ty val :
    interp_local_tys Σ Γ Ω -∗
    interp_type ty Σ val -∗
    interp_local_tys Σ (<[v:=ty]>Γ) (<[v:=val]>Ω).
  Proof.
    iIntros "#[Hthis Hi] #?".
    iSplit; first done.
    iIntros (v' ty') "H".
    rewrite lookup_insert_Some.
    iDestruct "H" as %[[<- <-]|[??]].
    - iExists _. rewrite lookup_insert. by iSplit.
    - rewrite lookup_insert_ne; last done. by iApply "Hi".
  Qed.

  (* heap models relation; the semantic heap does
     not appear because it is hidden in iProp  *)
  (* Helper defintion to state that fields are correctly modeled *)
  Definition heap_models_fields
    (iFs: gmapO string (sem_typeO Θ)) (vs: stringmap value) : iProp Θ :=
    ⌜dom vs ≡ dom iFs⌝  ∗
    ∀ f (iF: sem_typeO Θ),
    iFs !! f ≡ Some iF -∗ ∃ v, (⌜vs !! f = Some v⌝ ∗ iF v).

  Definition heap_models (h : heap) : iProp Θ :=
    ∃ (sh: gmap loc (prodO tagO (laterO (gmapO string (sem_typeO Θ))))),
    own γ (gmap_view_auth (DfracOwn 1) sh) ∗ ⌜dom sh = dom h⌝ ∗
    □ ∀ (ℓ : loc) (t : tag) (vs : stringmap value),
    ⌜h !! ℓ = Some (t, vs)⌝ -∗
    ∃ (iFs : gmapO string (sem_typeO Θ)),
    sh !! ℓ ≡ Some (t, Next iFs) ∗ ▷ heap_models_fields iFs vs.

  Lemma heap_models_update Δ Σ h l rt vs exact_ t σt f vis fty orig v:
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _cname, wf_cdef_fields) pdefs →
    map_Forall (λ _cname, wf_cdef_fields_bounded) pdefs →
    map_Forall (λ _ : string, wf_cdef_fields_wf) pdefs →
    map_Forall (λ _cname, wf_field_mono) pdefs →
    map_Forall (λ _ : string, wf_cdef_mono) pdefs →
    Forall wf_constraint Δ →
    h !! l = Some (rt, vs) →
    has_field f t vis fty orig →
    wf_ty (ClassT true t σt) →
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σ Δ -∗
    match vis with
    | Public => interp_type (ClassT exact_ t σt) Σ (LocV l)
    | Private => interp_this_type t σt Σ (LocV l)
    end -∗
    interp_type (subst_ty σt fty) Σ v -∗
    heap_models h -∗
    heap_models (<[l:=(rt, <[f:=v]> vs)]> h).
  Proof.
    move => ??????? hheap hfield hwf.
    iIntros "#wfΣ #Σcoherency hrecv".
    iAssert (∃ t' σ' Σt fields (ifields: gmapO string (sem_typeO Θ)),
      ⌜inherits_using t' t σ' ∧ has_fields t' fields ∧ dom fields = dom ifields⌝ ∗
       (□ ▷ ∀ w,
           interp_type fty (interp_list Σ σt) w ∗-∗
           interp_type (subst_ty σ' fty) Σt w)
       ∗
       (▷ ∀ f vis ty orig, ⌜has_field f t' vis ty orig⌝ -∗ (ifields !! f ≡ Some (interp_car (interp_type ty Σt)))) ∗
      l↦(t',ifields))%I with "[hrecv]" as "hrecv".
    { destruct vis.
      - iDestruct (exact_subtype_is_inclusion with "hrecv") as "hrecv".
        rewrite interp_class_unfold //.
        iDestruct "hrecv" as (l' t' def tdef' σ' Σt fields ifields) "(%H & #hmixed & #? & #hf0 & hdyn & hl)".
        destruct H as ([= <-] & hdef & htdef' & ? & hinherits & hfields & hdom).
        iExists t', σ', Σt, fields, ifields.
        iSplitR; first done.
        iSplitR; last by iSplit.
        iModIntro; iNext; iIntros (w).
        assert (hl0: length def.(generics) = length σ').
        { apply inherits_using_wf in hinherits => //.
          destruct hinherits as (? & ? & ? & hhh).
          apply wf_tyI in hhh as (? & ? & ? & ?).
          by simplify_eq.
        }
        assert (hl1: length σ' = length σt).
        { apply wf_tyI in hwf as (? & ? & ? & ?); simplify_eq.
          by rewrite -hl0.
        }
        assert (hwf_fty: wf_ty fty).
        { by apply has_field_wf in hfield. }
        assert (hb: bounded (length σ') fty).
        { apply has_field_bounded in hfield => //.
          destruct hfield as (? & ? & hf); simplify_eq.
          by rewrite -hl0.
        }
        apply has_field_mono in hfield => //.
        destruct hfield as (def' & hdef' & [hco hcontra]); simplify_eq.
        iDestruct (neg_interp_variance with "hf0") as "hf1".
        iSplit; iIntros "#?".
        + iAssert (interp_type (subst_ty σ' fty) Σt w) as "h"; last done.
          rewrite interp_type_subst //.
          by iApply (interp_with_mono with "hf1").
        + iApply (interp_with_mono with "hf0") => //.
          by rewrite -interp_type_subst.
      - rewrite /interp_this_type interp_this_unseal /interp_this_def /=.
        iDestruct "hrecv" as (l' t' tdef' σ' Σt fields ifields) "(%H & #hmixed & #? & %hinst & hdyn & hl)".
        destruct H as ([= <-] & htdef' & ? & hinherits & hfields & hdom).
        assert (hl1: length σ' = length σt).
        { apply inherits_using_wf in hinherits => //.
          destruct hinherits as (? & ? & ? & hhh).
          apply wf_tyI in hhh as (? & ? & hl0 & ?).
          apply wf_tyI in hwf as (? & ? & hl1 & ?).
          simplify_eq.
          by rewrite hl0 hl1.
        }
        assert (hb: bounded (length σ') fty).
        { apply has_field_bounded in hfield => //.
          destruct hfield as (? & ? & hf); simplify_eq.
          apply inherits_using_wf in hinherits => //.
          destruct hinherits as (? & ? & ? & hh).
          apply wf_tyI in hh as (? & ? & hlen & ?); simplify_eq.
          by rewrite hlen.
        }
        iExists t', σ', Σt, fields, ifields.
        iSplitR; first done.
        iSplitR; last by iSplit.
        iModIntro; iNext; iIntros (w).
        rewrite interp_type_subst // -hinst.
        by iSplit; iIntros.
    }
    iDestruct "hrecv" as (t' σ' Σt fields ifields) "(%hpure & #hstatic & #hdyn & hl)".
    destruct hpure as (hinherits' & hfields & hdomfields).
    iIntros "#hv hmodels".
    iDestruct "hmodels" as (sh) "(hown & %hdom & #h)".
    iExists sh.
    iDestruct (sem_heap_own_valid_2 with "hown hl") as "#Hv".
    iSplitL "hown"; first by iFrame.
    iSplitR.
    { iPureIntro.
      by rewrite hdom dom_insert_lookup_L.
    }
    iModIntro.
    iIntros (l'' t'' vs'') "%Heq".
    rewrite lookup_insert_Some in Heq.
    destruct Heq as [[<- [= <- <-]] | [hne hl]]; last first.
    { iApply "h".
      by iPureIntro.
    }
    iSpecialize ("h" $! l rt vs with "[//]").
    iDestruct "h" as (iFs) "[#hsh hmodels]".
    iExists iFs; iSplit; first done.
    iRewrite "Hv" in "hsh".
    rewrite !option_equivI prod_equivI /=.
    iDestruct "hsh" as "[%ht #hifs]".
    fold_leibniz; subst.
    assert (hfield2 : has_field f rt vis (subst_ty σ' fty) orig) by (by eapply has_field_inherits_using).
    iSpecialize ("hdyn" $! f vis (subst_ty σ' fty) orig hfield2).
    rewrite later_equivI. iNext.
    iAssert (⌜is_Some (iFs !! f)⌝)%I as "%hiFs".
    { iRewrite -"hifs".
      by iRewrite "hdyn".
    }
    rewrite /heap_models_fields.
    iDestruct "hmodels" as "[%hdomv #hmodfs]".
    iSplit.
    { iPureIntro.
      by rewrite -hdomv dom_insert_lookup // -elem_of_dom hdomv elem_of_dom.
    }
    iIntros (f' iF') "#hf'".
    destruct (decide (f = f')) as [-> | hne]; last first.
    { rewrite lookup_insert_ne //.
      by iApply "hmodfs".
    }
    rewrite lookup_insert.
    iExists v; iSplitR; first done.
    iRewrite -"hifs" in "hf'".
    iRewrite "hdyn" in "hf'".
    rewrite !option_equivI discrete_fun_equivI.
    iSpecialize ("hf'" $! v).
    iRewrite -"hf'".
    rewrite interp_type_subst; last first.
    { apply has_field_bounded in hfield => //.
      destruct hfield as (def' & hdef' & hfty).
      apply wf_tyI in hwf as (? & ? & hlen & ?); simplify_eq.
      by rewrite hlen.
    }
    by iApply "hstatic".
  Qed.

  (* This is dynamic related. Once a [| dynamic |] is open,
   * we want to use facts about the Σt and Σdyn to show that
   * Σt models the SDT constraints of the runtime type.
   *)
  (* Show that Σt |= Δt ∧ Δsdt^t *)
  Lemma Σt_models_sdt t A tdef adef σ (Σt ΣA: list (interp Θ)):
    wf_cdefs pdefs →
    pdefs !! t = Some tdef →
    pdefs !! A = Some adef →
    length Σt = length tdef.(generics) →
    length ΣA = length adef.(generics) →
    inherits_using t A σ →
    □iForall3 interp_variance adef.(generics) (interp_list Σt σ) ΣA -∗
    □ interp_env_as_mixed ΣA -∗
    □ Σinterp ΣA adef.(constraints) -∗
    □ Σinterp ΣA (Δsdt A) -∗
    □ interp_env_as_mixed Σt -∗
    □ Σinterp Σt tdef.(constraints) -∗
    □ Σinterp Σt (Δsdt t).
  Proof.
    move => wfpdefs htdef hadef hlt htA hin.
    iIntros "#hF #hmA #hΣΔA #hΣΔsdtA #hmt #ΣΔt".
    assert (hh: Forall wf_ty σ ∧ length adef.(generics) = length σ).
    { apply inherits_using_wf in hin; try (by apply wfpdefs).
      destruct hin as (?&?&?&hh).
      split; first by apply wf_ty_classI in hh.
      apply wf_tyI in hh as (? & ? & ? & ?); by simplify_eq.
    }
    destruct hh as [hwfσ hl].
    assert (hwfc: Forall wf_constraint tdef.(constraints)) by by apply wf_constraints_wf in htdef.
    pose (Δsdt_A := subst_constraints σ (Δsdt A)).
    iAssert (□ Σinterp Σt Δsdt_A)%I as "#hΣt_sdt_A".
    { iAssert (interp_env_as_mixed (interp_list Σt σ)) as "hmixed0".
      { iIntros (k phi hk w) "hphi".
        apply list_lookup_fmap_inv in hk as [ty0 [-> hty0]].
        rewrite -(interp_type_unfold Σt MixedT w).
        iApply (submixed_is_inclusion_aux Σt ty0 w) => //.
        rewrite Forall_lookup in hwfσ.
        by apply hwfσ in hty0.
      }
      iAssert (□ Σinterp (interp_list Σt σ) adef.(constraints))%I as "#hΣ0".
      { iModIntro.
        apply inherits_using_ok in hin => //; try by apply wfpdefs.
        destruct hin as (? & ? & hok); simplify_eq.
        apply ok_tyI in hok as (? & ? & ? & hok); simplify_eq.
        iIntros (i c hc w) "#h".
        assert (hb : bounded_constraint (length σ) c).
        { apply wf_constraints_bounded in hadef => //.
          rewrite /wf_cdef_constraints_bounded Forall_lookup in hadef.
          apply hadef in hc.
          by rewrite -hl.
        }
        destruct hb as [].
        assert (hwf: wf_ty (subst_ty σ c.1)).
        { apply wf_ty_subst => //.
          apply wf_constraints_wf in hadef => //.
          rewrite /wf_cdef_constraints_wf Forall_lookup in hadef.
          apply hadef in hc.
          by destruct hc.
        }
        apply hok in hc.
        rewrite -!interp_type_subst //.
        iApply (subtype_is_inclusion tdef.(constraints)) => //; by apply wfpdefs.
      }
      iModIntro; iIntros (i c0 hc w) "#h".
      apply list_lookup_fmap_inv in hc as [c [-> hc]] => /=.
      assert (hbc : bounded_constraint (length σ) c).
      { rewrite -hl.
        by eapply Δsdt_bounded in hc.
      }
      destruct hbc as [].
      rewrite !interp_type_subst //.
      destruct wfpdefs.
      by iApply ((Δsdt_variance_interp _ _ _ _
      wf_mono wf_parent wf_constraints_bounded wf_constraints_wf hadef)
      with "hmixed0 hmA hF hΣ0 hΣΔA hΣΔsdtA").
    }
    iAssert (□ Σinterp Σt (constraints tdef ++ Δsdt_A))%I as "#hconstr_".
    { iModIntro.
      by iApply Σinterp_app.
    }
    iModIntro.
    assert (hnewcond: Δentails Aware (tdef.(constraints) ++ Δsdt_A) (Δsdt t)).
    { apply inherits_using_extends_dyn in hin => //; try by apply wfpdefs.
      destruct hin as (? & ? & hwf); simplify_eq.
      move => k c hc.
      by apply hwf with k.
    }
    assert (Forall wf_constraint Δsdt_A).
    { rewrite Forall_lookup => k c hc.
      apply list_lookup_fmap_inv in hc as [c0 [-> hc]].
      apply Δsdt_wf in hc as [].
      split; by apply wf_ty_subst.
    }
    assert (hwf_ : Forall wf_constraint (tdef.(constraints) ++ Δsdt_A)).
    { apply Forall_app; by split.  }
    assert (hwfΔ0: Forall wf_constraint (Δsdt t)).
    { rewrite Forall_lookup; by apply Δsdt_wf. }
    iIntros (i c hc w) "#h".
    assert (h0 := hc).
    apply hnewcond in h0.
    assert (wf_ty c.1).
    { rewrite Forall_lookup in hwfΔ0.
      by apply hwfΔ0 in hc as [].
    }
    iApply (subtype_is_inclusion with "hmt hconstr_ h") => //; by apply wfpdefs.
  Qed.
End proofs.
