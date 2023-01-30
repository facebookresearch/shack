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

  Notation "X ≡≡ Y" := (∀ (w: value), X w ∗-∗ Y w)%I (at level 50, no associativity).

  Lemma interp_local_tys_update Σthis Σ v Γ Ω ty val :
    interp_local_tys Σthis Σ Γ Ω -∗
    interp_type ty Σthis Σ val -∗
    interp_local_tys Σthis Σ (<[v:=ty]>Γ) (<[v:=val]>Ω).
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

  (* TODO: try to refactor them up like before *)
  Lemma heap_models_update_pub Δ Σ h l t1 vs exact_ t σ  f fty orig v:
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _cname, wf_cdef_fields) pdefs →
    map_Forall (λ _cname, wf_cdef_fields_bounded) pdefs →
    map_Forall (λ _ : string, wf_cdef_fields_wf) pdefs →
    map_Forall (λ _cname, wf_field_mono) pdefs →
    map_Forall (λ _ : string, wf_cdef_mono) pdefs →
    map_Forall (λ _ : string, wf_cdef_constraints_wf) pdefs →
    Forall wf_constraint Δ →
    wf_ty (ClassT exact_ t σ) →
    h !! l = Some (t1, vs) →
    has_field f t Public fty orig →
    is_true exact_ ∨ no_this fty →
    ∀ t0 Σt0,
    let Σthis0 := interp_exact_tag interp_type t0 Σt0 in
    □ interp_env_as_mixed Σt0 -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis0 Σ Δ -∗
    interp_type (ClassT exact_ t σ) Σthis0 Σ (LocV l) -∗
    interp_type (subst_fty exact_ t σ fty) Σthis0 Σ v -∗
    heap_models h -∗
    heap_models (<[l:=(t1, <[f:=v]> vs)]> h).
  Proof.
    move => ???????? hwf hheap hf hex.
    move => t0 Σt0 Σthis0.
    iIntros "#hΣt0 #hΣ #hΣΔ #hrecv #hv Hh".
    assert (hh : ∃ tdef, pdefs !! t = Some tdef ∧
      length σ = length tdef.(generics)).
    { apply wf_tyI in hwf as (? & ? & ? & ?).
      by eauto.
    }
    destruct hh as (tdef & htdef & hlenσ).
    destruct exact_.
    - (* Public access on exact type *)
      rewrite interp_exact_tag_unfold interp_exact_tag_unseal /interp_exact_tag_def /=.
      iDestruct "hrecv" as (? tdef' fields ifields hpure) "(#hconstr & #hfields & hl)".
      destruct hpure as ([= <-] & htdef' & hfields & hdomfields); simplify_eq.
      iDestruct "Hh" as (sh) "(hown & %hdom & #h)".
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
      iSpecialize ("h" $! l t1 vs with "[//]").
      iDestruct "h" as (iFs) "[#hsh hmodels]".
      iExists iFs; iSplit; first done.
      iRewrite "Hv" in "hsh".
      rewrite !option_equivI prod_equivI /=.
      iDestruct "hsh" as "[%ht #hifs]".
      fold_leibniz; subst.
      iSpecialize ("hfields" $! f Public fty orig hf).
      rewrite later_equivI.
      iNext.
      iDestruct "hfields" as (iF) "(#hiF & #hiff)".
      iAssert (⌜is_Some (iFs !! f)⌝)%I as "%hiFs".
      { iRewrite -"hifs".
        by iRewrite "hiF".
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
      iRewrite "hiF" in "hf'".
      rewrite !option_equivI discrete_fun_equivI.
      iSpecialize ("hf'" $! v).
      iRewrite -"hf'".
      iApply "hiff".
      rewrite interp_type_subst; last first.
      { apply bounded_subst_this; last by (constructor; by apply bounded_gen_targs).
        apply has_field_bounded in hf => //.
        destruct hf as (def' & hdef' & hfty).
        apply wf_tyI in hwf as (? & ? & hlen & ?); simplify_eq.
        by rewrite hlen.
      }
      iClear "hconstr hiF hiff hl hifs hmodfs hf' Hv".
      rewrite /subst_gen hlenσ.
      rewrite (interp_type_no_this _ _ _ Σthis0 interp_nothing); first done.
      apply subst_this_has_no_this => /=.
      apply forallb_True.
      by apply gen_targs_has_no_this.
    - (* property doesn't have `this` *)
      case: hex => // hnothis.
      rewrite interp_tag_unfold interp_tag_equiv //; last first.
      { by rewrite /interp_list fmap_length. }
      rewrite /interp_tag_alt /=.
      iDestruct "hrecv" as (? t2 tdef' t2def σin Σt2 fields ifields hpure)
        "(#hΣt2 & #hconstr & #hinst & #hfields & hl)".
      destruct hpure as ([= <-] & htdef' & ht2def & hlenΣt2 & hin & hfields & hdomfields); simplify_eq.
      iDestruct "Hh" as (sh) "(hown & %hdom & #h)".
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
      iSpecialize ("h" $! l t1 vs with "[//]").
      iDestruct "h" as (iFs) "[#hsh hmodels]".
      iExists iFs; iSplit; first done.
      iRewrite "Hv" in "hsh".
      rewrite !option_equivI prod_equivI /=.
      iDestruct "hsh" as "[%ht #hifs]".
      fold_leibniz; subst.
      (* NEW *)
      assert (hfield2 : has_field f t1 Public (subst_ty σin fty) orig)
      by (by eapply has_field_inherits_using).
      iSpecialize ("hfields" $! f Public (subst_ty σin fty) orig hfield2).
      (* NEW *)
      rewrite later_equivI.
      iNext.
      iDestruct "hfields" as (iF) "(#hiF & #hiff)".
      iAssert (⌜is_Some (iFs !! f)⌝)%I as "%hiFs".
      { iRewrite -"hifs".
        by iRewrite "hiF".
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
      iRewrite "hiF" in "hf'".
      rewrite !option_equivI discrete_fun_equivI.
      iSpecialize ("hf'" $! v).
      iRewrite -"hf'".
      rewrite interp_type_subst; last first.
      { apply bounded_subst_this; last by (constructor; by apply bounded_gen_targs).
        apply has_field_bounded in hf => //.
        destruct hf as (def' & hdef' & hfty).
        apply wf_tyI in hwf as (? & ? & hlen & ?); simplify_eq.
        by rewrite hlen.
      }
      iApply "hiff".
      iClear "hconstr hiF hiff hl hifs hmodfs hf' Hv".
      (* NEW *)
      rewrite /subst_gen -hlenΣt2.
      iAssert (
        interp_type (subst_ty σin fty) (interp_exact_tag interp_type t1 Σt2) Σt2 v -∗
        interp_type
          (subst_this (ClassT true t1 (gen_targs (length Σt2))) (subst_ty σin fty)) interp_nothing Σt2 v)%I as "HH".
      { iIntros "HH".
        by rewrite -(interp_type_subst_this _ _ interp_nothing).
      }
      iApply "HH"; iClear "HH".
      rewrite subst_this_no_this_id; last done.
      rewrite (interp_type_no_this _ _ _ Σthis0 (interp_exact_tag interp_type t1 Σt2)); last done.
      iDestruct (neg_interp_variance with "hinst") as "hinst2".
      iDestruct (interp_with_mono with "hinst2 hv") as "hv2" => //.
      { apply has_field_mono in hf => //.
        destruct hf as (? & ? & []); by simplify_eq.
      }
      { by apply has_field_wf in hf. }
      assert (heq:
        interp_list interp_nothing Σt2 σin ≡
        interp_list (interp_exact_tag interp_type t1 Σt2) Σt2 σin).
      { apply interp_list_no_this.
        apply inherits_using_wf in hin => //.
        by destruct hin as (? & ? & ? & ? & ?).
      }
      rewrite (interp_type_equivI _ _ _ heq).
      rewrite interp_type_subst; first done.
      apply has_field_bounded in hf => //.
      destruct hf as (? & ? & hf); simplify_eq.
      apply inherits_using_wf in hin => //.
      destruct hin as (? & ? & ? & hwfσin & ?); simplify_eq.
      apply wf_tyI in hwfσin as (? & ? & hlen & ?); simplify_eq.
      by rewrite hlen.
  Qed.

  Lemma heap_models_update_priv Δ Σ h l t1 C σ0 cdef vs f fty v:
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _cname, wf_cdef_fields) pdefs →
    map_Forall (λ _cname, wf_cdef_fields_bounded) pdefs →
    map_Forall (λ _ : string, wf_cdef_fields_wf) pdefs →
    map_Forall (λ _cname, wf_field_mono) pdefs →
    map_Forall (λ _ : string, wf_cdef_mono) pdefs →
    map_Forall (λ _ : string, wf_cdef_constraints_wf) pdefs →
    Forall wf_constraint Δ →
    h !! l = Some (t1, vs) →
    (* TODO: maybe turn this one into a has_field to share more proof ? *)
    pdefs !! C = Some cdef →
    cdef.(classfields) !! f = Some (Private, fty) →
    ∀ t0 Σt0 tdef0,
    pdefs !! t0 = Some tdef0 →
    inherits_using t0 C σ0 →
    length Σt0 = length tdef0.(generics) →
    let Σthis0 := interp_exact_tag interp_type t0 Σt0 in
    ⌜interp_list interp_nothing Σt0 σ0 ≡ Σ⌝ -∗
    □ interp_env_as_mixed Σt0 -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis0 Σ Δ -∗
    Σthis0 (LocV l) -∗
    interp_type fty Σthis0 Σ v -∗
    heap_models h -∗
    heap_models (<[l:=(t1, <[f:=v]> vs)]> h).
  Proof.
    move => ?? hwfb ????? hheap hcdef hf.
    move => t0 Σt0 tdef0 hdef0 hin hlenΣt0 Σthis0.
    iIntros "%heqΣ #hΣt0 #hΣ #hΣΔ #hrecv #hv Hh".
    rewrite {2}/Σthis0 interp_exact_tag_unseal /interp_exact_tag_def /=.
    iDestruct "hrecv" as (? tdef' fields ifields hpure) "(#hconstr & #hfields & hl)".
    destruct hpure as ([= <-] & htdef' & hfields & hdomfields); simplify_eq.
    iDestruct "Hh" as (sh) "(hown & %hdom & #h)".
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
    iSpecialize ("h" $! l t1 vs with "[//]").
    iDestruct "h" as (iFs) "[#hsh hmodels]".
    iExists iFs; iSplit; first done.
    iRewrite "Hv" in "hsh".
    rewrite !option_equivI prod_equivI /=.
    iDestruct "hsh" as "[%ht #hifs]".
    fold_leibniz; subst.
    assert (hf0: has_field f t1 Private (subst_ty σ0 fty) C).
    { eapply has_field_inherits_using => //.
      change Private with (Private, fty).1.
      by eapply HasField.
    }
    iSpecialize ("hfields" $! f Private _ C hf0).
    rewrite later_equivI.
    iNext.
    iDestruct "hfields" as (iF) "(#hiF & #hiff)".
    iAssert (⌜is_Some (iFs !! f)⌝)%I as "%hiFs".
    { iRewrite -"hifs".
      by iRewrite "hiF".
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
    iRewrite "hiF" in "hf'".
    rewrite !option_equivI discrete_fun_equivI.
    iSpecialize ("hf'" $! v).
    iRewrite -"hf'".
    iApply "hiff".
    (* NEW *)
    rewrite /subst_gen -hlenΣt0.
    iAssert (
      interp_type (subst_ty σ0 fty) (interp_exact_tag interp_type t1 Σt0) Σt0 v -∗
      interp_type
        (subst_this (ClassT true t1 (gen_targs (length Σt0))) (subst_ty σ0 fty)) interp_nothing Σt0 v)%I as "HH".
    { iIntros "HH".
      by rewrite -(interp_type_subst_this _ _ interp_nothing).
    }
    iApply "HH"; iClear "HH".
    iClear "hconstr hiF hiff hl hifs hmodfs hf' Hv".
    apply inherits_using_wf in hin => //.
    destruct hin as (? & ? & ? & hwf & ?); simplify_eq.
    rewrite (interp_type_equivI _ Σ (interp_list interp_nothing Σt0 σ0)); last done.
    rewrite interp_type_subst; last first.
    { assert (h0 := hcdef).
      apply hwfb in h0.
      apply h0 in hf.
      apply wf_tyI in hwf as (? & ? & hlen & ?); simplify_eq.
      by rewrite hlen.
    }
    assert (heq_ : interp_list interp_nothing Σt0 σ0 ≡ interp_list Σthis0 Σt0 σ0).
    { by apply interp_list_no_this. }
    by rewrite (interp_type_equivI _ _ _ heq_).
  Qed.

  (*
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
  *)
End proofs.
