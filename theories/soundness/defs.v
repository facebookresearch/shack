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

Section proofs.
  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.
  (* assume some SDT constraints *)
  Context `{SDTCC: SDTClassConstraints}.
  (* assume the good properties of SDT constraints *)
  Context `{SDTCP: SDTClassSpec}.

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

  Lemma heap_models_update Δ Σ h l rt vs t σt f vis fty orig v:
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _cname, wf_cdef_fields) pdefs →
    map_Forall (λ _cname, wf_cdef_fields_bounded) pdefs →
    map_Forall (λ _ : string, wf_cdef_fields_wf) pdefs →
    map_Forall (λ _cname, wf_field_mono) pdefs →
    map_Forall (λ _ : string, wf_cdef_mono) pdefs →
    Forall wf_constraint Δ →
    h !! l = Some (rt, vs) →
    has_field f t vis fty orig →
    wf_ty (ClassT t σt) →
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σ Δ -∗
    match vis with
    | Public => interp_type (ClassT t σt) Σ (LocV l)
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
      - rewrite interp_class_unfold //.
        iDestruct "hrecv" as (l' t' def tdef' σ' Σt fields ifields) "[%H [#hmixed [#? [#hf0 [hdyn hl]]]]]".
        destruct H as ([= <-] & hdef & htdef' & hlen & ? & hinherits & hfields & hdom).
        iExists t', σ', Σt, fields, ifields.
        iSplitR; first done.
        iSplitR; last by iSplit.
        iModIntro; iNext; iIntros (w).
        assert (hl0: length def.(generics) = length σ').
        { apply inherits_using_wf in hinherits => //.
          destruct hinherits as (? & ? & ? & hhh).
          inv hhh; by simplify_eq.
        }
        assert (hl1: length σ' = length σt).
        { rewrite /interp_list fmap_length in hlen.
          by rewrite hlen.
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
        iDestruct "hrecv" as (l' t' tdef tdef' σ' Σt fields ifields) "[%H [#hmixed [#? [#hinst [hdyn hl]]]]]".
        destruct H as ([= <-] & htdef & htdef' & hlen & ? & hinherits & hfields & hdom).
        assert (hl1: length σ' = length σt).
        { apply inherits_using_wf in hinherits => //.
          destruct hinherits as (? & ? & ? & hhh).
          inv hhh; inv hwf; simplify_eq.
          by rewrite H5 H8.
        }
        assert (hb: bounded (length σ') fty).
        { apply has_field_bounded in hfield => //.
          destruct hfield as (? & ? & hf); simplify_eq.
          apply inherits_using_wf in hinherits => //.
          destruct hinherits as (? & ? & ? & hh).
          inv hh; simplify_eq.
          by rewrite H6.
        }
        iExists t', σ', Σt, fields, ifields.
        iSplitR; first done.
        iSplitR; last by iSplit.
        iModIntro; iNext; iIntros (w).
        rewrite interp_type_subst //.
        iRewrite -"hinst".
        by iSplit; iIntros.
    }
    iDestruct "hrecv" as (t' σ' Σt fields ifields) "[%hpure [#hstatic [#hdyn hl]]]".
    destruct hpure as (hinherits' & hfields & hdomfields).
    iIntros "#hv hmodels".
    iDestruct "hmodels" as (sh) "[hown [%hdom #h]]".
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
      inv hwf; simplify_eq.
      by rewrite H2.
    }
    by iApply "hstatic".
  Qed.
End proofs.
