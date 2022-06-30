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

  (* Iris semantic context *)
  Context `{!sem_heapGS Θ}.
  Notation γ := sem_heap_name.

  (* Helping the inference with this notation that hides pdefs *)
  Local Notation "Δ ⊢ s <: t" := (@subtype _ Δ Plain s t) (at level 70, s at next level, no associativity).
  Local Notation "Δ ⊢ s <D: t" := (@subtype _ Δ Aware s t) (at level 70, s at next level, no associativity).

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

  Lemma expr_soundness (Δ: list constraint) rigid (Σ: list (interp Θ)) kd e Γ Ω ty val :
    map_Forall (λ _, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _, wf_cdef_mono) pdefs →
    Forall wf_constraint Δ →
    wf_lty Γ →
    expr_eval Ω e = Some val →
    expr_has_ty Δ Γ rigid kd e ty →
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σ Δ -∗
    interp_local_tys Σ Γ Ω -∗
    interp_type ty Σ val.
  Proof.
    move => ??? wflty he h; move: Ω val he.
    induction h as [| | | kd op e1 e2 hop he1 hi1 he2 hi2 |
        kd op e1 e2 hop he1 hi1 he2 hi2 | kd e1 e2 h1 hi1 h2 hi2 | kd e0 h hi |
        kd v vty hv | | kd exp S T hS hi hwf hok hsub | kd exp S T hS hi hwf hok hsub]
        => Ω val he; iIntros "#wfΣ #Σcoherency #Hlty".
    - inv he; rewrite interp_type_unfold /=; by eauto.
    - inv he; rewrite interp_type_unfold /=; by eauto.
    - inv he; rewrite interp_type_unfold /=; by eauto.
    - inv he.
      case heq1 : (expr_eval Ω e1) => [v1 | ]; rewrite heq1 in H0; last by done.
      apply hi1 in heq1.
      iDestruct (heq1 with "wfΣ Σcoherency Hlty") as "hv1".
      rewrite interp_type_unfold /=.
      iDestruct "hv1" as (z1) "%hz1".
      rewrite hz1 in H0.
      case heq2 : (expr_eval Ω e2) => [v2 | ]; rewrite heq2 in H0; last by done.
      apply hi2 in heq2.
      iDestruct (heq2 with "wfΣ Σcoherency Hlty") as "hv2".
      rewrite interp_type_unfold /=.
      iDestruct "hv2" as (z2) "%hz2".
      rewrite hz2 in H0.
      case: H0 => <-.
      rewrite interp_type_unfold /= /interp_int.
      move: hop; rewrite /is_bool_op; destruct op => //= _; by iExists _.
    - inv he.
      case heq1 : (expr_eval Ω e1) => [v1 | ]; rewrite heq1 in H0; last by done.
      apply hi1 in heq1.
      iDestruct (heq1 with "wfΣ Σcoherency Hlty") as "hv1".
      rewrite interp_type_unfold /=.
      iDestruct "hv1" as (z1) "%hz1".
      rewrite hz1 in H0.
      case heq2 : (expr_eval Ω e2) => [v2 | ]; rewrite heq2 in H0; last by done.
      apply hi2 in heq2.
      iDestruct (heq2 with "wfΣ Σcoherency Hlty") as "hv2".
      rewrite interp_type_unfold /=.
      iDestruct "hv2" as (z2) "%hz2".
      rewrite hz2 in H0.
      case: H0 => <-.
      rewrite interp_type_unfold /= /interp_bool.
      move: hop; rewrite /is_bool_op; destruct op => //= _; by iExists _.
    - inv he.
      case heq1 : (expr_eval Ω e1) => [v1 | ]; rewrite heq1 in H0; last by done.
      apply hi1 in heq1.
      iDestruct (heq1 with "wfΣ Σcoherency Hlty") as "hv1".
      rewrite interp_type_unfold /=.
      iDestruct "hv1" as (b1) "%hb1".
      rewrite hb1 in H0.
      case heq2 : (expr_eval Ω e2) => [v2 | ]; rewrite heq2 in H0; last by done.
      apply hi2 in heq2.
      iDestruct (heq2 with "wfΣ Σcoherency Hlty") as "hv2".
      rewrite interp_type_unfold /=.
      iDestruct "hv2" as (b2) "%hb2".
      rewrite hb2 in H0.
      case: H0 => <-.
      rewrite interp_type_unfold /= /interp_bool.
      by iExists _.
    - inv he.
      case heq : (expr_eval Ω e0) => [v0 | ]; rewrite heq in H0; last by done.
      apply hi in heq.
      iDestruct (heq with "wfΣ Σcoherency Hlty") as "hv".
      rewrite interp_type_unfold /=.
      iDestruct "hv" as (b) "%hb".
      rewrite hb in H0.
      case: H0 => <-.
      rewrite interp_type_unfold /= /interp_bool.
      by iExists _.
    - inv he.
      iDestruct "Hlty" as "[? Hlty]".
      iDestruct ("Hlty" with "[//]") as (?) "[% H]".
      rewrite H0 in H; by case: H => ->.
    - inv he.
      iDestruct "Hlty" as "[Hthis Hv]".
      rewrite /interp_this_type interp_this_unseal /interp_this_def /=.
      iDestruct "Hthis" as (?? thisdef tdef ????) "[%H [#hmixed [#hconstr [#hinst [hdyn hloc]]]]]".
      destruct H as ([= <-] & hthisdef & htdef & hl & ? & hin & hfields & hdom).
      rewrite /this_type interp_class_unfold //=; last first.
      { by apply wflty. }
      destruct Γ as [[this σthis] Γ]; simpl in *.
      iExists _,t,thisdef,tdef,_, _, _, _.
      iSplit; first done.
      iSplit; first by iApply "hmixed".
      iSplit; first by iApply "hconstr".
      iSplit; last by iSplit.
      iModIntro; iNext.
      iClear "wfΣ Σcoherency hmixed hdyn hloc Hv".
      assert (hl0 : length thisdef.(generics) = length σ).
      { apply inherits_using_wf in hin => //.
        destruct hin as (?&?&?&h).
        by inv h; simplify_eq.
      }
      assert (hl1: length σ = length σthis).
      { rewrite /interp_list !fmap_length in hl.
        by rewrite hl.
      }
      move : hl0 hl1.
      generalize thisdef.(generics); clear.
      move => l hl0 hl1.
      iInduction l as [ | hd tl hi] "IH" forall (σ σthis hl0 hl1) "hinst".
      { by destruct σ; destruct σthis. }
      destruct σ as [ | ty0 σ] => //=.
      destruct σthis as [ | ty1 σthis] => //=.
      case: hl0 => hl0.
      case: hl1 => hl1.
      rewrite list_equivI.
      iSplitL.
      + iSpecialize ("hinst" $! 0).
        rewrite /= option_equivI.
        destruct hd; iIntros (w).
        * iSplit; iIntros "h"; first by iRewrite -"hinst".
          by iRewrite "hinst".
        * iIntros "h"; by iRewrite -"hinst".
        * iIntros "h"; by iRewrite "hinst".
      + iApply "IH" => //.
        iModIntro; rewrite /interp_list list_equivI; iIntros (k).
        by iSpecialize ("hinst" $! (S k)).
    - apply hi in he.
      iApply subtype_is_inclusion => //.
      + by apply expr_has_ty_wf in hS.
      + by iApply he.
    - apply hi in he.
      iApply subtype_is_inclusion => //.
      + by apply expr_has_ty_wf in hS.
      + by iApply he.
  Qed.

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

  (* virtual calls using Dynamic all verify cdef_wf_mdef_dyn_ty *)
  Lemma wf_mdef_dyn_ty_wf Σ Δ C kd st st' rigid Γ lhs recv name args l n:
    wf_cdefs pdefs →
    wf_lty Γ →
    Forall wf_constraint Δ →
    expr_has_ty Δ Γ rigid kd recv DynamicT →
    expr_eval st.1 recv = Some (LocV l) →
    cmd_eval C st (CallC lhs recv name args) st' n →
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σ Γ st.1 -∗
    ⌜∃ t vs orig σ def mdef,
    has_method name t orig (subst_mdef σ mdef) ∧
    st.2 !! l = Some (t, vs) ∧
    inherits_using t orig σ ∧
    pdefs !! orig = Some def ∧
    def.(classmethods) !! name = Some mdef ∧
    wf_mdef_dyn_ty def.(constraints) orig (length def.(generics)) (gen_targs (length def.(generics))) mdef⌝%I.
  Proof.
    move => wfpdefs ?? hrty heval hceval.
    iIntros "#hΣ #hΣΔ [Hh #Hle]".
    inv hceval; simpl in *.
    rewrite heval in H3; simplify_eq.
    iDestruct (expr_soundness with "hΣ hΣΔ Hle") as "#He" => //; try (by apply wfpdefs).
    rewrite interp_dynamic_unfold.
    iDestruct "He" as "[H | He]".
    { iDestruct "H" as (z) "%H".
      discriminate H.
    }
    iDestruct "He" as "[H | He]".
    { iDestruct "H" as (b) "%H".
      discriminate H.
    }
    iDestruct "He" as "[H | He]".
    { iDestruct "H" as "%H".
      discriminate H.
    }
    iDestruct "He" as (dyntag Σdyn dyndef hpure) "He".
    destruct hpure as [hdyndef hsupdyn].
    rewrite interp_tag_equiv; last by apply wfpdefs.
    iDestruct "He" as (?? def def0 ????) "[%H [#hmixed [#hconstr [#hf0 [#hdyn H◯]]]]]".
    destruct H as ([= <-] & hdef & hdef0 & hlen & ? & hinherits & hfields & hidom).
    simplify_eq.
    iAssert (⌜t0 = t⌝)%I as "%Ht".
    { iDestruct "Hh" as (sh) "(H● & %hdom & #Hh)".
      iDestruct (sem_heap_own_valid_2 with "H● H◯") as "#HΦ".
      iDestruct ("Hh" with "[//]") as (iFs) "[H H▷]".
      iRewrite "H" in "HΦ".
      rewrite option_equivI prod_equivI /=.
      iDestruct "HΦ" as "[%Ht HΦ]".
      by fold_leibniz; subst.
    }
    subst.
    iPureIntro.
    assert (h0 := H6).
    apply has_method_from_def in h0 => //; try by apply wfpdefs.
    destruct h0 as (odef & omdef & hodef & homdef & _ & [σ0 [hin0 ->]]).
    exists t, vs, orig, σ0, odef, omdef.
    split; first done.
    split; first done.
    split; first done.
    split; first done.
    split; first done.
    destruct wfpdefs.
    assert (hsupdyn0: def0.(support_dynamic) = true).
    { apply inherits_using_dyn_parent in hinherits => //.
      destruct hinherits as (tdef & ddef & ? & ? & hh); simplify_eq.
      by apply hh.
    }
    apply wf_methods_dyn in hdef0.
    rewrite /wf_cdef_methods_dyn_wf hsupdyn0 in hdef0.
    apply hdef0 in H6.
    rewrite /subst_mdef /= in H6.
    apply wf_mdefs_dyn in hodef.
    apply hodef in homdef.
    by rewrite /cdef_wf_mdef_dyn_ty H6 in homdef.
  Qed.
  
  Lemma cmd_soundness_ Δ C kd rigid Γ cmd Γ' :
    wf_cdefs pdefs →
    wf_lty Γ →
    bounded_lty rigid Γ →
    Forall wf_constraint Δ →
    Forall (bounded_constraint rigid) Δ →
    cmd_has_ty Δ C kd rigid Γ cmd Γ' →
    ∀ Σ st st' n,
    length Σ = rigid →
    cmd_eval C st cmd st' n →
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σ Γ st.1 -∗ |=▷^n
        heap_models st'.2 ∗ interp_local_tys Σ Γ' st'.1.
  Proof.
    move => wfpdefs wflty blty hΔ hΔb.
    iLöb as "IH" forall (Δ C kd rigid Γ cmd Γ' wflty blty hΔ hΔb).
    iIntros "%hty" (Σ st st' n hrigid hc) "#hΣ #hΣΔ".
    iInduction hty as [ kd rigid Γ |
        kd rigid Γ rty hwf |
        kd rigid Γ1 Γ2 Γ3 fstc sndc hfst hi1 hsnd hi2 |
        kd rigid Γ lhs e ty he |
        kd rigid Γ1 Γ2 cond thn els hcond hthn hi1 hels hi2 |
        kd rigid Γ lhs t targs name fty hrecv hf |
        kd rigid Γ lhs recv t targs name fty orig hrecv hf |
        kd rigid Γ fld rhs fty t σ hrecv hrhs hf |
        kd rigid Γ recv fld rhs fty orig t σ hrecv hrhs hf |
        kd rigid Γ lhs t targs args fields hwf hb hok hf hdom harg |
        kd rigid Γ lhs recv t targs name orig mdef args hrecv hhasm hdom hi |
        kd rigid Γ c rty' rty hsub hb h hi |
        kd rigid Γ0 Γ1 v tv t def thn els hv hdef hΓ1 hthn hi0 hels hi1 |
        kd rigid Γ rty v tv thn els hv hthn hi0 hels hi1 |
        kd rigid Γ rty v tv thn els hv hthn hi0 hels hi1 |
        kd rigid Γ rty v tv thn els hv hthn hi0 hels hi1 |
        kd rigid Γ rty v tv thn els hv hthn hi0 hels hi1 |
        kd rigid Γ1 Γ2 cond thn els hcond hthn hi1 hels hi2 |
        kd rigid Γ lhs recv name he hnotthis |
        kd rigid Γ recv fld rhs hrecv hrhs hnotthis |
        kd rigid Γ lhs recv name args hrecv hi hnotthis
      ] "IHty" forall (Σ st st' n hrigid hc) "hΣ hΣΔ".
    - (* SkipC *) inv hc.
      rewrite updN_zero.
      by iIntros "?".
    - (* Error *)
      by inv hc.
    - (* SeqC *) inv hc. iIntros "H".
      iSpecialize ("IHty" $! wflty blty hΔb Σ _ _ _ refl_equal with "[//] hΣ hΣΔ H").
      rewrite Nat_iter_add.
      iApply (updN_mono_I with "[] IHty").
      destruct wfpdefs.
      iApply "IHty1" => //.
      + by apply cmd_has_ty_wf in hfst.
      + by apply cmd_has_ty_bounded in hfst.
    - (* LetC *)
      inv hc.
      iClear "IH".
      iIntros "[? #Hle]".
      rewrite updN_zero /=.
      iFrame.
      iDestruct (expr_soundness with "hΣ hΣΔ Hle") as "#?" => //; try (by apply wfpdefs).
      by iApply interp_local_tys_update.
    - (* IfC *) inv hc
      + iIntros "H". by iApply "IHty".
      + iIntros "H". by iApply "IHty1".
    - (* GetPriv *) inv hc.
      iClear "IH".
      iIntros "[Hh #Hle]".
      iModIntro. (* keep the later *)
      destruct Γ as [[this σ] Γ].
      destruct Ω as [vthis Ω].
      destruct wflty as [wfthis wflty].
      rewrite /this_type /= in wfthis, hrecv.
      injection hrecv; intros; subst; clear hrecv.
      inv H2.
      simpl in *.
      iDestruct "Hle" as "[Hthis Hle]".
      rewrite /this_type /=.
      rewrite /interp_this_type interp_this_unseal /interp_this_def /=.
      iDestruct "Hthis" as (????????) "[%H [#hmixed [#? [#hinst [#hdyn H◯]]]]]".
      destruct H as ([= <-] & hdef & hdef1 & hlen & ? & hinherits & hidom & hfields).
      iAssert (⌜t0 = t1⌝ ∗ heap_models h ∗ ▷ interp_type (subst_ty targs fty) Σ v)%I with "[Hh]" as "[%Ht [Hh Hv]]".
      { iDestruct "Hh" as (sh) "(H● & %hdom & #Hh)".
        iDestruct (sem_heap_own_valid_2 with "H● H◯") as "#HΦ".
        iDestruct ("Hh" with "[//]") as (iFs) "[H H▷]".
        iRewrite "H" in "HΦ".
        rewrite option_equivI prod_equivI /=.
        iDestruct "HΦ" as "[%Ht HΦ]".
        fold_leibniz; subst.
        iSplitR; first done.
        iSplitL. { iExists _. iFrame. by iSplit. }
        assert (hfC: has_field name t1 Private (subst_ty σ fty) C) by (destruct wfpdefs; by eapply has_field_inherits_using).
        iSpecialize ("hdyn" $! name Private (subst_ty σ fty) C hfC).
        iDestruct "H▷" as "[hdf h]".
        rewrite later_equivI. iNext.
        iRewrite -"HΦ" in "hdyn".
        iSpecialize ("h" $! name _ with "[hdyn]"); first done.
        iDestruct "h" as (w) "[%hw hiw]".
        simplify_eq.
        rewrite interp_type_subst; last first.
        { destruct wfpdefs.
          apply has_field_bounded in hf => //.
          destruct hf as (? & ? & ?).
          apply inherits_using_wf in hinherits => //.
          destruct hinherits as (? & ?& ? & hh).
          inv wfthis; simplify_eq.
          by rewrite H10.
        }
        iRewrite -"hinst".
        rewrite -interp_type_subst //.
        destruct wfpdefs.
        apply has_field_bounded in hf => //.
        destruct hf as (? & ? & ?).
        apply inherits_using_wf in hinherits => //.
        destruct hinherits as (? & ?& ? & hh).
        inv hh; simplify_eq.
        by rewrite H10.
      }
      subst.
      iNext.
      iFrame.
      iApply interp_local_tys_update => //.
      iSplit; last done.
      rewrite /type_of_this /interp_this_type interp_this_unseal.
      iExists l, t1, cdef, tdef, σ, Σt, fields, ifields.
      by repeat iSplit.
    - (* GetC *) inv hc.
      iClear "IH".
      iIntros "[Hh #Hle]".
      iModIntro. (* keep the later *)
      iDestruct (expr_soundness with "hΣ hΣΔ Hle") as "#He" => //; try (by apply wfpdefs).
      rewrite interp_class_unfold //; first last.
      { by apply expr_has_ty_wf in hrecv. }
      { by apply wfpdefs. }
      iDestruct "He" as (?? def def0 ????) "[%H [#hmixed [#? [#hf0 [#hdyn H◯]]]]]".
      destruct H as ([= <-] & hdef & hdef0 & hlen & ? & hinherits & hfields & hidom).
      assert (hwf0: wf_ty (ClassT t targs)) by (by apply expr_has_ty_wf in hrecv).
      assert (hl0: length (generics def) = length σ).
      { apply inherits_using_wf in hinherits; try (by apply wfpdefs).
        destruct hinherits as (?&?&?&hh).
        inv hh; by simplify_eq.
      }
      assert (hl1: length σ = length targs).
      { rewrite -hl0.
        rewrite /interp_list fmap_length in hlen.
        by rewrite hlen.
      }
      assert (hff: has_field name t1 Public (subst_ty σ fty) orig).
      { by apply has_field_inherits_using with (A := t1) (σB := σ) in hf => //; try (by apply wfpdefs). }
      iAssert (⌜t0 = t1⌝ ∗ heap_models h ∗ ▷ interp_type (subst_ty σ fty) Σt v)%I with "[Hh]" as "[%Ht [Hh Hv]]".
      { iDestruct "Hh" as (sh) "(H● & %hdom & #Hh)".
        iDestruct (sem_heap_own_valid_2 with "H● H◯") as "#HΦ".
        iDestruct ("Hh" with "[//]") as (iFs) "[H H▷]".
        iRewrite "H" in "HΦ".
        rewrite option_equivI prod_equivI /=.
        iDestruct "HΦ" as "[%Ht HΦ]".
        fold_leibniz; subst.
        iSplitR; first done.
        iSplitL. { iExists _. iFrame. by iSplit. }
        iSpecialize ("hdyn" $! name Public (subst_ty σ fty) orig hff).
        iNext.
        iDestruct "H▷" as "[%hdf h]".
        iRewrite -"HΦ" in "hdyn".
        iSpecialize ("h" $! name _ with "[hdyn]"); first done.
        iDestruct "h" as (w) "[%hw hiw]".
        by simplify_eq.
      }
      subst; simpl.
      iNext.
      iFrame.
      destruct wfpdefs.
      iApply interp_local_tys_update => //.
      rewrite !interp_type_subst; first last.
      { apply has_field_bounded in hf => //.
        destruct hf as (?&?&hf); simplify_eq.
        by rewrite -hl0.
      }
      { apply has_field_bounded in hf => //.
        destruct hf as (?&?&hf); simplify_eq.
        by rewrite -hl1 -hl0.
      }
      iApply interp_with_mono => //.
      { apply has_field_mono in hf => //.
        destruct hf as (?&?&hh); simplify_eq.
        by destruct hh.
      }
      by apply has_field_wf in hf.
    - (* SetPriv *) inv hc.
      assert (wfpdefs' := wfpdefs).
      destruct wfpdefs'.
      iClear "IH".
      iIntros "[Hh #Hle]" => /=.
      iSplitL; last done.
      destruct Γ as [[tthis σthis]  Γ].
      destruct Ω as [vthis Ω].
      injection hrecv; intros; subst; clear hrecv.
      assert (ht: wf_ty (ClassT t σ)) by apply wflty.
      iApply (heap_models_update _ _ _ _ _ _ t σ) => //=.
      + iDestruct "Hle" as "[Hthis Hle]".
        rewrite /= /interp_this_type interp_this_unseal /interp_this_def /=.
        iDestruct "Hthis" as (l' t1 def def1 σ0 σt fields ifields) "[%H [#hmixed [#? [#hinst [#hdyn #Hl]]]]]".
        destruct H as ([= <-] & hdef & hdef1 & hlen & ? & hin & hfields & hidom).
        iExists l, t1, def, def1, σ0, σt, fields, ifields.
        repeat iSplit => //.
        by inv H2.
      + iApply expr_soundness => //; by apply wfpdefs.
    - (* SetPub *) inv hc.
      assert (wfpdefs' := wfpdefs).
      destruct wfpdefs'.
      iClear "IH".
      iIntros "[Hh #Hle]" => /=.
      iSplitL; last done.
      assert (ht: wf_ty (ClassT t σ)) by (by apply expr_has_ty_wf in hrecv).
      iApply (heap_models_update _ _ _ _ _ _ t σ) => //=.
      + iApply expr_soundness => //; by apply wfpdefs.
      + iApply expr_soundness => //; by apply wfpdefs.
    - (* NewC *) inv hc.
      iClear "IH".
      iIntros "[Hh #Hle]"; simpl.
      (* we need one modality to semantic heap *)
      iDestruct "Hh" as (sh) "(H● & %Hdom & #Hh)".
      assert (hnew: sh !! new = None).
      { apply (not_elem_of_dom (D:=gset loc)).
        by rewrite Hdom not_elem_of_dom.
      }
      set (iFs :=
         (λ(ty: lang_ty), (interp_car (interp_type ty Σ))) <$> ((λ x, subst_ty targs x.1.2) <$> fields)
      ).
      iMod ((sem_heap_own_update new) with "H●") as "[H● #H◯]" => //;
        first by apply (sem_heap_view_alloc _ new t iFs).
      iIntros "!> !>". (* kill the modalities *)
      iAssert (interp_type (ClassT t targs) Σ (LocV new)) with "[]" as "#Hl".
      { rewrite interp_class_unfold //; last by apply wfpdefs.
        assert (hwf' := hwf).
        inv hwf'.
        iExists new, t, def, def, (gen_targs (length def.(generics))), (interp_list Σ targs), fields, iFs.
        iSplit.
        { iPureIntro.
          repeat split => //.
          + by rewrite /interp_list fmap_length.
          + by rewrite /interp_list fmap_length.
          + by econstructor.
          + by rewrite /iFs /= !dom_fmap_L.
        }
        assert (wf_targs : Forall wf_ty targs) by by apply wf_ty_class_inv in hwf.
        iSplit.
        { iModIntro; iNext.
          iIntros (i ? heq v) "hphi".
          rewrite /interp_list in heq.
          apply list_lookup_fmap_inv in heq as [phi [-> heq]].
          assert (hsub: Δ ⊢ phi <: MixedT) by eauto.
          destruct wfpdefs.
          iDestruct (subtype_is_inclusion _ hΔ wf_parent wf_mono _ _ _ _ hsub v with "hΣ hΣΔ hphi") as "hsub".
          + by eauto.
          + by rewrite interp_mixed_unfold.
        }
        assert (hconstraints: ∀ i c,
          subst_constraints targs def.(constraints) !! i = Some c → Δ ⊢ c.1 <D: c.2
        ).
        { rewrite /subst_constraints => i ? hin.
          apply list_lookup_fmap_inv in hin as [c [-> hin]].
          rewrite /subst_constraint /=.
          inv hok; simplify_eq.
          apply H6 in hin.
          apply subtype_weaken with (Δ' := (Δ ++ subst_constraints targs def.(constraints))) in hin => //;
            last by set_solver.
          apply subtype_constraint_elim in hin => //.
          move => j ? hj.
          rewrite /subst_constraints in hj.
          apply list_lookup_fmap_inv in hj as [cc [-> hj]].
          rewrite /subst_constraint /=.
          by eauto.
        }
        iSplit.
        { iModIntro; iNext.
          iIntros (i c heq v) "h".
          assert (hsub: Δ ⊢ (subst_ty targs c.1) <D: (subst_ty targs c.2)).
          { apply subtype_constraint_elim with (Δ' := subst_constraints targs def.(constraints)) => //.
            apply subtype_weaken with (Δ := subst_constraints targs def.(constraints)); last by set_solver.
            eapply subtype_subst => //.
            - by apply wfpdefs.
            - eapply SubConstraint.
              apply elem_of_list_lookup_2 in heq.
              by rewrite (surjective_pairing c) in heq.
          }
          destruct wfpdefs.
          rewrite -!interp_type_subst.
          { iApply (subtype_is_inclusion _ hΔ wf_parent wf_mono _ _ _ _ hsub v with "hΣ hΣΔ") => //.
            apply wf_ty_subst => //.
            apply wf_constraints_wf in H1.
            rewrite /wf_cdef_constraints_wf Forall_forall in H1.
            apply elem_of_list_lookup_2 in heq.
            apply H1 in heq.
            by apply heq.
          }
          { apply wf_constraints_bounded in H1.
            rewrite /wf_cdef_constraints_bounded Forall_forall -H2 in H1.
            apply elem_of_list_lookup_2 in heq.
            apply H1 in heq.
            by apply heq.
          }
          { apply wf_constraints_bounded in H1.
            rewrite /wf_cdef_constraints_bounded Forall_forall -H2 in H1.
            apply elem_of_list_lookup_2 in heq.
            apply H1 in heq.
            by apply heq.
          }
        }
        iSplit.
        { iModIntro; iNext.
          iApply iForall3_interp_gen_targs => //.
          by rewrite /interp_list fmap_length.
        }
        iSplit; last done.
        iIntros (f vis ty orig hff).
        rewrite /iFs /=.
        assert (hbtargs: bounded (length targs) ty).
        { apply has_field_bounded in hff; try (by apply wfpdefs).
          destruct hff as (?&?&hh); simplify_eq.
          by rewrite H2.
        }
        apply hf in hff.
        rewrite !lookup_fmap hff /= option_equivI.
        iPureIntro.
        move => x.
        by apply interp_type_subst.
      }
      iSplitL; last by iApply interp_local_tys_update.
      iExists _. iFrame. iSplit; first by rewrite !dom_insert_L Hdom.
      iModIntro. iIntros (???) "Hlook".
      rewrite lookup_insert_Some.
      iDestruct "Hlook" as %[[<- [= <- <-]]|[Hℓ Hlook]]; last first.
      { rewrite lookup_insert_ne; last done.
        by iApply "Hh".
      }
      iExists _. rewrite lookup_insert.
      iSplitR; first done.
      rewrite /heap_models_fields.
      iSplitR.
      {
        apply dom_map_args in H8.
        by rewrite /iFs !dom_fmap_L H8 -hdom.
      }
      iNext.
      iIntros (f iF) "hiF".
      iAssert (⌜f ∈ dom fields⌝)%I as "%hfield".
      {
        rewrite !lookup_fmap.
        rewrite elem_of_dom.
        destruct (fields !! f) => //=.
        by rewrite option_equivI.
      }
      assert (h0: is_Some (args !! f)).
      {
        apply elem_of_dom.
        by rewrite -hdom.
      }
      destruct h0 as [a0 ha0].
      assert (h1: is_Some (vargs !! f)).
      {
        apply elem_of_dom.
        apply dom_map_args in H8.
        by rewrite H8 -hdom.
      }
      destruct h1 as [v0 hv0].
      assert (h2: is_Some (fields !! f)) by (by apply elem_of_dom).
      destruct h2 as [fty hty].
      iExists v0; iSplitR; first done.
      rewrite lookup_fmap.
      assert (heval0: expr_eval Ω a0 = Some v0).
      { rewrite (map_args_lookup _ _ _ args vargs H8 f) in hv0.
        by rewrite ha0 in hv0.
      }
      assert (hty0: expr_has_ty Δ Γ (length Σ) kd a0 (subst_ty targs fty.1.2)) by (by apply harg with f).
      rewrite !lookup_fmap hty /= option_equivI.
      rewrite discrete_fun_equivI.
      iSpecialize ("hiF" $! v0).
      iRewrite -"hiF".
      iDestruct (expr_soundness Δ (length Σ) Σ kd a0 with "hΣ hΣΔ Hle") as "#Ha0" => //; by apply wfpdefs.
    - (* CallC *) inv hc; simpl.
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
      assert (hwfr : wf_ty (ClassT t targs)) by by apply expr_has_ty_wf in hrecv.
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
      destruct (has_method_ordered _ _ _ _ _ _ _ _ wf_extends_wf wf_override wf_parent wf_methods_bounded hin_t1_t hhasm0 hhasm)
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
      assert (hh: wf_mdef_ty odef0.(constraints) orig0 (length odef0.(generics)) (gen_targs (length odef0.(generics))) omdef0).
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
      assert (heq3: length def.(generics) = length targs).
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
            { iApply (subtype_is_inclusion _ hΔ1 wf_parent wf_mono _ _ _ _ hsub) => //.
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
      iApply (subtype_is_inclusion _ hΔ1 wf_parent wf_mono _ _ _ _ hmret0) => //.
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
    - (* Subtyping *)
      destruct wfpdefs.
      iIntros "H".
      iSpecialize ("IHty" $! wflty blty hΔb _ _ _ _ hrigid with "[//] hΣ hΣΔ H").
      iApply updN_mono_I; last done.
      iIntros "[Hh #Hrty]". iFrame.
      iDestruct (interp_local_tys_is_inclusion with "hΣ hΣΔ Hrty") as "Hrty'" => //.
      + by apply cmd_has_ty_wf in h.
      + rewrite Forall_forall => i hi v.
        by apply _.
    - (* RuntimeCheck tag *) inv hc; last first.
      { iIntros "[Hh H]".
        iApply "IHty1" => //.
        by iSplit.
      }
      iIntros "H".
      pose (rigid := length Σ).
      pose (tc := ClassT t (map GenT (seq rigid (length def.(generics))))).
      assert (hwf: wf_lty (<[v:=InterT tv tc]> Γ0)).
      { apply insert_wf_lty => //.
        constructor; first by apply wflty in hv.
        econstructor => //.
        - by rewrite map_length seq_length.
        - move => k ty hx.
          apply list_lookup_fmap_inv in hx.
          destruct hx as [ty' [ -> h]].
          by constructor.
      }
      assert (hbounded:
         bounded_lty (length Σ + length (generics def)) (<[v:=InterT tv tc]> Γ0)).
      { apply insert_bounded_lty.
        - constructor.
          + apply bounded_ge with (length Σ); last by lia.
            by apply blty in hv.
          + by apply bounded_rigid.
        - apply bounded_lty_ge with (length Σ); last by lia.
          by apply blty.
      }
      iClear "IH IHty1".
      destruct H7 as (l & hl & t' & fields & hlt & hinherits).
      iDestruct "H" as "[H #Hle]".
      iDestruct "Hle" as "[Hthis Hle]".
      iDestruct ("Hle" $! v with "[//]") as (?) "[%Hlev Hv]".
      rewrite Hlev in hl; simplify_eq.
      iAssert (heap_models st.2 ∗
        ∃ Σex, interp_tag interp_type Σex t (LocV l) ∗
        ⌜length Σex = length def.(generics)⌝ ∗
        □ ▷ interp_env_as_mixed Σex
      )%I with "[H]" as "[Hh #Hv2]".
      { iAssert (interp_type MixedT Σ (LocV l)) as "Hmixed".
        { destruct wfpdefs.
          assert (hsub : Δ ⊢ tv <: MixedT) by apply SubMixed.
          iApply subtype_is_inclusion => //.
          by apply wflty in hv.
        }
        rewrite interp_mixed_unfold /=.
        iDestruct "Hmixed" as "[Hnonnull | Hnull]"; last first.
        { iDestruct "Hnull" as "%Hnull"; discriminate. }
        iDestruct "Hnonnull" as "[Hint | Hl]".
        { iDestruct "Hint" as "%Hint"; by destruct Hint. }
        iDestruct "Hl" as "[Hbool | Hl]".
        { iDestruct "Hbool" as "%Hbool"; by destruct Hbool. }
        iDestruct "Hl" as (exTag exΣ) "Hl".
        rewrite interp_tag_equiv; last (by apply wfpdefs).
        iDestruct "Hl" as (k rt exdef rtdef σ Σt exfields ifields) "[%H [#hmixed [#hΣt [#hinst [#hdyn #Hl]]]]]".
        destruct H as ([= <-] & hexdef & hrtdef & hlexΣ & hlΣt & hinherits' & hfields' & hidom'); simplify_eq.
        iDestruct "H" as (sh) "(H● & %hdom & #Hh)".
        iDestruct (sem_heap_own_valid_2 with "H● Hl") as "#HΦ".
        iDestruct ("Hh" with "[//]") as (iFs) "[H H▷]".
        iRewrite "H" in "HΦ".
        rewrite option_equivI prod_equivI /=.
        iDestruct "HΦ" as "[%Ht HΦ]".
        fold_leibniz; subst.
        iSplitL. { iExists _. iFrame. by iSplit. }
        assert (hh: ∃ σ, inherits_using rt t σ ∧ length σ = length def.(generics)).
        { move: hdef hinherits.
          clear => hdef.
          induction 1 as [ t | s t u hst htu hi ].
          - exists (gen_targs (length def.(generics))).
            split; first by constructor.
            by rewrite length_gen_targs.
          - destruct (hi hdef) as (σ & h0 & h1).
            inv hst.
            exists (subst_ty σB <$> σ); split.
            + eapply InheritsTrans.
              * by econstructor.
              * done.
            + by rewrite map_length.
        }
        destruct hh as (σin & hσin & heq).
        assert (hwfσin : Forall wf_ty σin).
        { destruct wfpdefs.
          apply inherits_using_wf in hσin => //.
          destruct hσin as (? & ? & ? & h); simplify_eq.
          by apply wf_ty_class_inv in h.
        }
        iExists (interp_list Σt σin).
        iSplit.
        { rewrite interp_tag_equiv; last (by apply wfpdefs).
          iExists l, rt, def, rtdef, σin, Σt, exfields, ifields.
          iSplit.
          { iPureIntro; repeat split => //.
            by rewrite /interp_list map_length heq.
          }
          iSplit => //.
          iSplit => //.
          iSplit; last by iSplit.
          iModIntro; iNext.
          iApply iForall3_interp_reflexive.
          by rewrite /interp_list map_length heq.
        }
        iSplit.
        { iPureIntro.
          by rewrite /interp_list fmap_length.
        }
        { iModIntro; iNext.
          iIntros (k ϕ hϕ w) "#Hw".
          apply list_lookup_fmap_inv in hϕ as [ty [-> hty]].
          iAssert (interp_type MixedT Σt w) as "HH".
          { iApply (submixed_is_inclusion_aux _ ty) => //.
            rewrite Forall_lookup in hwfσin.
            by apply hwfσin in hty.
          }
          by rewrite interp_mixed_unfold.
        }
      }
      iDestruct "Hv2" as (Σex) "(Hv2 & %heq & #HΣex)".
      (* We need the extra +1 to get that the existiential Σ
       * is correctly ⊆ mixed
       *)
      rewrite updN_S.
      iModIntro; iNext.
      iAssert (interp_env_as_mixed (Σ ++ Σex)) as "hmixed".
      { iIntros (k ϕ hϕ w) "#hw".
        rewrite lookup_app in hϕ.
        destruct (Σ !! k) as [ty0 | ] eqn:h0.
        + case: hϕ => <-.
          by iApply "hΣ".
        + by iApply "HΣex".
      }
      iAssert (Σinterp (Σ ++ Σex) Δ) as "hΣ_Δ".
      { iIntros (k c hc w) "#hw".
        rewrite Forall_lookup in hΔb.
        rewrite -!interp_type_app.
        + by iApply "hΣΔ".
        + by apply hΔb in hc as [].
        + by apply hΔb in hc as [].
      }
      iAssert (|=▷^n0 heap_models st'.2 ∗ interp_local_tys (Σ ++ Σex) Γ1 st'.1)%I with "[Hh]" as "H".
      { iApply "IHty".
        - by iPureIntro.
        - by iPureIntro.
        - iPureIntro.
          apply bounded_constraints_ge with (length Σ); last by lia.
          done.
        - by rewrite app_length heq.
        - by iPureIntro.
        - by iModIntro.
        - by iModIntro.
        - iFrame.
          iSplit.
          + rewrite /= -interp_this_type_app; first done.
            by apply blty.
          + rewrite /=.
            iIntros (w tw).
            rewrite lookup_insert_Some.
            iIntros "%Hw".
            destruct Hw as [[<- <-] | [hne hw]].
            * iExists (LocV l); rewrite Hlev; iSplitR; first done.
              rewrite interp_inter_unfold; iSplit.
              { rewrite -interp_type_app; first done.
                by apply blty in hv.
              }
              rewrite (interp_type_rigid Σ Σex); first by rewrite heq.
              { by destruct wfpdefs. }
              econstructor => //.
              { by rewrite map_length seq_length heq. }
              move => k ty h.
              apply list_lookup_fmap_inv in h as [? [-> h]].
              by constructor.
            * iDestruct ("Hle" $! w tw hw) as (z hz) "#Hz".
              iExists z; iSplit; first done.
              rewrite -interp_type_app; first done.
              by apply blty in hw.
      }
      iRevert "H".
      iApply updN_mono_I.
      iIntros "[Hm H]"; iFrame.
      rewrite -interp_local_app; first done.
      destruct wfpdefs.
      by apply cmd_has_ty_bounded in hels.
    - (* RuntimeCheck Int *) inv hc; last first.
      { iIntros "[Hh H]".
        iApply "IHty1" => //.
        by iSplit.
      }
      iIntros "H".
      assert (hwf: wf_lty (<[v:=InterT tv IntT]> Γ)).
      { apply insert_wf_lty => //.
        constructor; first by apply wflty in hv.
        by constructor.
      }
      assert (hbounded: bounded_lty (length Σ) (<[v:=InterT tv IntT]> Γ)).
      { apply insert_bounded_lty => //.
        constructor; last by constructor.
        by apply blty in hv.
      }
      iModIntro; iNext.
      iApply ("IHty" $! hwf hbounded hΔb with "[//]") => //; iClear "IH IHty".
      clear H8.
      destruct H7 as (z & hz).
      iDestruct "H" as "[H #Hle]".
      iDestruct "Hle" as "[Hthis Hle]".
      iDestruct ("Hle" $! v with "[//]") as (?) "[%Hlev Hv]".
      rewrite Hlev in hz; simplify_eq.
      iFrame.
      iSplit => /=; first done.
      iIntros (w tw).
      rewrite lookup_insert_Some.
      iIntros "%Hw".
      destruct Hw as [[<- <-] | [hne hw]]; last by iApply "Hle".
      iExists (IntV z); rewrite Hlev; iSplitR; first done.
      rewrite interp_inter_unfold /=; iSplit; first done.
      rewrite !interp_type_unfold /=.
      by iExists z.
    - (* RuntimeCheck Bool *) inv hc; last first.
      { iIntros "[Hh H]".
        iApply "IHty1" => //.
        by iSplit.
      }
      iIntros "H".
      assert (hwf: wf_lty (<[v:=InterT tv BoolT]> Γ)).
      { apply insert_wf_lty => //.
        constructor; first by apply wflty in hv.
        by constructor.
      }
      assert (hbounded: bounded_lty (length Σ) (<[v:=InterT tv BoolT]> Γ)).
      { apply insert_bounded_lty => //.
        constructor; last by constructor.
        by apply blty in hv.
      }
      iModIntro; iNext.
      iApply ("IHty" $! hwf hbounded hΔb with "[//]") => //; iClear "IH IHty".
      clear H8.
      destruct H7 as (b & hb).
      iDestruct "H" as "[H #Hle]".
      iDestruct "Hle" as "[Hthis Hle]".
      iDestruct ("Hle" $! v with "[//]") as (?) "[%Hlev Hv]".
      rewrite Hlev in hb; simplify_eq.
      iFrame.
      iSplit => /=; first done.
      iIntros (w tw).
      rewrite lookup_insert_Some.
      iIntros "%Hw".
      destruct Hw as [[<- <-] | [hne hw]]; last by iApply "Hle".
      iExists (BoolV b); rewrite Hlev; iSplitR; first done.
      rewrite interp_inter_unfold /=; iSplit; first done.
      rewrite !interp_type_unfold /=.
      by iExists b.
    - (* RuntimeCheck Null *) inv hc; last first.
      { iIntros "[Hh H]".
        iApply "IHty1" => //.
        by iSplit.
      }
      iIntros "H".
      assert (hwf: wf_lty (<[v:=InterT tv NullT]> Γ)).
      { apply insert_wf_lty => //.
        constructor; first by apply wflty in hv.
        by constructor.
      }
      assert (hbounded: bounded_lty (length Σ) (<[v:=InterT tv NullT]> Γ)).
      { apply insert_bounded_lty => //.
        constructor; last by constructor.
        by apply blty in hv.
      }
      iModIntro; iNext.
      iApply ("IHty" $! hwf hbounded hΔb with "[//]") => //; iClear "IH IHty".
      clear H8.
      simpl in H7.
      iDestruct "H" as "[H #Hle]".
      iDestruct "Hle" as "[Hthis Hle]".
      iDestruct ("Hle" $! v with "[//]") as (?) "[%Hlev Hv]".
      rewrite Hlev in H7; simplify_eq.
      iFrame.
      iSplit => /=; first done.
      iIntros (w tw).
      rewrite lookup_insert_Some.
      iIntros "%Hw".
      destruct Hw as [[<- <-] | [hne hw]]; last by iApply "Hle".
      iExists NullV; rewrite Hlev; iSplitR; first done.
      rewrite interp_inter_unfold /=; iSplit; first done.
      by rewrite !interp_type_unfold.
    - (* RuntimeCheck NonNull *) inv hc; last first.
      { iIntros "[Hh H]".
        iApply "IHty1" => //.
        by iSplit.
      }
      iIntros "H".
      assert (hwf: wf_lty (<[v:=InterT tv NonNullT]> Γ)).
      { apply insert_wf_lty => //.
        constructor; first by apply wflty in hv.
        by constructor.
      }
      assert (hbounded: bounded_lty (length Σ) (<[v:=InterT tv NonNullT]> Γ)).
      { apply insert_bounded_lty => //.
        constructor; last by constructor.
        by apply blty in hv.
      }
      iModIntro; iNext.
      iApply ("IHty" $! hwf hbounded hΔb with "[//]") => //; iClear "IH IHty".
      clear H8.
      simpl in H7.
      iDestruct "H" as "[H #Hle]".
      iFrame.
      iAssert (interp_local_tys Σ Γ st.1) as "#Hle_"; first done.
      iDestruct "Hle_" as "[Hthis Hle_]".
      iDestruct ("Hle_" $! v with "[//]") as (?) "[%Hlev Hv]".
      iAssert (interp_type MixedT Σ val) as "Hmixed".
      { destruct wfpdefs.
        assert (hsub : Δ ⊢ tv <: MixedT) by apply SubMixed.
        iApply subtype_is_inclusion => //.
        by apply wflty in hv.
      }
      replace (interp_local_tys Σ (<[v:=InterT tv NonNullT]> Γ) st.1) with
              (interp_local_tys Σ (<[v:=InterT tv NonNullT]> Γ) (<[v := val]>st.1)); last first.
      { f_equal.
        destruct st as [[? ll] ?]; simpl in *.
        move : Hlev.
        rewrite /insert /local_env_insert /=; clear => h.
        f_equal.
        induction ll as [| s w ws Hs IH] using map_ind => //=.
        rewrite lookup_insert_Some in h.
        destruct h as [[-> ->] | [hneq hv]].
        * by rewrite insert_insert.
        * by rewrite insert_commute // IH.
      }
      iApply interp_local_tys_update => //.
      rewrite interp_mixed_unfold interp_inter_unfold.
      iSplit; first done.
      iDestruct "Hmixed" as "[? | %hnull]".
      { by rewrite interp_nonnull_unfold. }
      rewrite hnull in Hlev.
      by rewrite Hlev in H7.
    - (* Dynamic ifC *) inv hc.
      + iIntros "H". by iApply "IHty".
      + iIntros "H". by iApply "IHty1".
    - (* Dynamic Get *) inv hc.
      iClear "IH".
      iIntros "[Hh #Hle]"; simpl.
      iModIntro. (* keep the later *)
      iDestruct (expr_soundness with "hΣ hΣΔ Hle") as "#He" => //; try (by apply wfpdefs).
      rewrite interp_dynamic_unfold.
      iDestruct "He" as "[H | He]".
      { iDestruct "H" as (z) "%H".
        discriminate H.
      }
      iDestruct "He" as "[H | He]".
      { iDestruct "H" as (b) "%H".
        discriminate H.
      }
      iDestruct "He" as "[H | He]".
      { iDestruct "H" as "%H".
        discriminate H.
      }
      iDestruct "He" as (dyntag Σdyn dyndef hpure) "He".
      destruct hpure as [hdyndef hsupdyn].
      rewrite interp_tag_equiv; last by apply wfpdefs.
      iDestruct "He" as (?? def def0 ????) "[%H [#hmixed [#hconstr [#hf0 [#hdyn H◯]]]]]".
      destruct H as ([= <-] & hdef & hdef0 & hlen & ? & hinherits & hfields & hidom).
      simplify_eq.
      assert (hl0: length (generics dyndef) = length σ).
      { apply inherits_using_wf in hinherits; try (by apply wfpdefs).
        destruct hinherits as (?&?&?&hh).
        inv hh; by simplify_eq.
      }
      iAssert (⌜t0 = t⌝ ∗ heap_models h ∗ ▷ interp_type DynamicT Σt v)%I with "[Hh]" as "[%Ht [Hh Hv]]".
      { iDestruct "Hh" as (sh) "(H● & %hdom & #Hh)".
        iDestruct (sem_heap_own_valid_2 with "H● H◯") as "#HΦ".
        iDestruct ("Hh" with "[//]") as (iFs) "[H H▷]".
        iRewrite "H" in "HΦ".
        rewrite option_equivI prod_equivI /=.
        iDestruct "HΦ" as "[%Ht HΦ]".
        fold_leibniz; subst.
        iSplitR; first done.
        iSplitL. { iExists _. iFrame. by iSplit. }
        (* the field must be public, since we can't access it from This *)
        destruct H9 as (vis & fty & orig & hf & hvc).
        destruct vis; last by destruct recv.
        assert (hsub: def0.(constraints) ⊢ fty <D: DynamicT).
        { destruct wfpdefs.
          assert (h0 := hinherits).
          apply inherits_using_dyn_parent in h0 => //.
          destruct h0 as (def0' & dyndef' & hdef0' & hdyndef' & hsd); simplify_eq.
          apply hsd in hsupdyn.
          apply wf_fields_dyn in hdef0.
          rewrite /wf_cdef_fields_dyn_wf hsupdyn in hdef0.
          assert (h1 := hfields).
          apply hdef0 in h1.
          apply hfields in hf.
          apply h1 in hf.
          by apply hf.
        }
        destruct wfpdefs.
        assert (hwfc: Forall wf_constraint def0.(constraints)) by by apply wf_constraints_wf in hdef0.
        iSpecialize ("hdyn" $! name Public fty orig hf).
        iNext.
        iDestruct "H▷" as "[%hdf h]".
        iRewrite -"HΦ" in "hdyn".
        iSpecialize ("h" $! name _ with "[hdyn]"); first done.
        iDestruct "h" as (w) "[%hw hiw]".
        simplify_eq.
        iDestruct (subtype_is_inclusion _ hwfc wf_parent wf_mono _ Σt _ _ hsub v) as "hsub".
        { by apply has_field_wf in hf. }
        by iApply "hsub".
      }
      subst.
      iNext.
      iFrame.
      iApply interp_local_tys_update => //.
      by rewrite !interp_dynamic_unfold.
    - (* Dynamic Set *) inv hc.
      assert (wfpdefs' := wfpdefs).
      destruct wfpdefs'.
      iClear "IH".
      iIntros "[Hh #Hle]" => /=.
      iSplitL; last done.
      iAssert (interp_type DynamicT Σ (LocV l)) as "#Hl".
      { by iApply expr_soundness. }
      rewrite interp_dynamic_unfold.
      iDestruct "Hl" as "[H | Hl]".
      { iDestruct "H" as (z) "%H".
        discriminate H.
      }
      iDestruct "Hl" as "[H | Hl]".
      { iDestruct "H" as (b) "%H".
        discriminate H.
      }
      iDestruct "Hl" as "[H | Hl]".
      { iDestruct "H" as "%H".
        discriminate H.
      }
      iDestruct "Hl" as (dyntag Σdyn dyndef hpure) "Hl".
      destruct hpure as [hdyndef hsupdyn].
      rewrite interp_tag_equiv //.
      iDestruct "Hl" as (?? def def0 ????) "[%H [#hmixed [#hconstr [#hf0 [#hdyn H◯]]]]]".
      destruct H as ([= <-] & hdef & hdef0 & hlen & ? & hinherits & hfields & hidom).
      simplify_eq.
      assert (hwf : wf_ty (ClassT dyntag σ)).
      { apply inherits_using_wf in hinherits => //.
        by destruct hinherits as (?&?&?&?).
      }
      (* This is based on heap_models_update, but specialized for Dynamic *)
      destruct H10 as (vis & fty & orig & hf & hv).
      destruct vis; last by destruct recv.
      iDestruct "Hh" as (sh) "[hown [%hdom #h]]".
      iExists sh.
      iDestruct (sem_heap_own_valid_2 with "hown H◯") as "#Hv".
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
      iSpecialize ("h" $! l t vs with "[//]").
      iDestruct "h" as (iFs) "[#hsh hmodels]".
      iExists iFs; iSplit; first done.
      iRewrite "Hv" in "hsh".
      rewrite !option_equivI prod_equivI /=.
      iDestruct "hsh" as "[%ht #hifs]".
      fold_leibniz; subst.
      iSpecialize ("hdyn" $! fld Public fty orig hf).
      rewrite later_equivI. iNext.
      iAssert (⌜is_Some (iFs !! fld)⌝)%I as "%hiFs".
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
      destruct (decide (fld = f')) as [-> | hne]; last first.
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
      iAssert (interp_type DynamicT Σ v) as "#Hve".
      { by iApply expr_soundness. }
      assert (hsub: def0.(constraints) ⊢ DynamicT <D: fty).
      { destruct wfpdefs.
        assert (h0 := hinherits).
        apply inherits_using_dyn_parent in h0 => //.
        destruct h0 as (def0' & dyndef' & hdef0' & hdyndef' & hsd); simplify_eq.
        apply hsd in hsupdyn.
        apply wf_fields_dyn in hdef0.
        rewrite /wf_cdef_fields_dyn_wf hsupdyn in hdef0.
        assert (h1 := hfields).
        apply hdef0 in h1.
        apply hfields in hf.
        apply h1 in hf.
        by apply hf.
      }
      assert (hwfc: Forall wf_constraint def0.(constraints)) by by apply wf_constraints_wf in hdef0.
      iDestruct (subtype_is_inclusion _ hwfc wf_parent wf_mono _ Σt _ _ hsub v) as "hsub".
      { by apply has_field_wf in hf. }
      iApply "hsub" => //.
      by rewrite !interp_dynamic_unfold.
    - (* DynCall *) inv hc; simpl.
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
      iDestruct "Hl" as "[H | Hl]".
      { iDestruct "H" as "%Hn".
        discriminate Hn.
      }
      iDestruct "Hl" as (dyntag Σdyn dyndef hpure) "Hl".
      destruct hpure as [hdyndef hsupdyn].
      rewrite interp_tag_equiv //.
      iDestruct "Hl" as (?? def def0 ????) "[%Hpure [#hΣt [#hconstr [#hf0 [#hdyn H◯]]]]]".
      destruct Hpure as ([= <-] & hdef & hdef0 & hlen & ? & hinherits & hfields & hidom).
      simplify_eq.
      iDestruct "Hh" as (sh) "(H● & %Hdom & #Hh)".
      iDestruct (sem_heap_own_valid_2 with "H● H◯") as "#HΦ".
      iDestruct ("Hh" with "[//]") as (?) "[H H▷]".
      iRewrite "H" in "HΦ".
      rewrite option_equivI prod_equivI /=.
      iDestruct "HΦ" as "[%Ht HΦ]".
      fold_leibniz; subst.
      (* Inlining wf_mdef_dyn_ty_wf. TODO: maybe remove the former one,
       * or rewrite it in a more reusable way.
       *) 
      assert (h0 := hhasm0).
      apply has_method_from_def in h0 => //.
      destruct h0 as (odef & omdef & hodef & homdef & _ & [σ0 [hin0 ->]]).
      assert (hsupdyn0: def0.(support_dynamic) = true).
      { apply inherits_using_dyn_parent in hinherits => //.
        destruct hinherits as (tdef & ddef & ? & ? & hh); simplify_eq.
        by apply hh.
      }
      assert (h0 := hdef0).
      apply wf_methods_dyn in h0.
      rewrite /wf_cdef_methods_dyn_wf hsupdyn0 in h0.
      assert (h1 := hhasm0).
      apply h0 in h1.
      rewrite /subst_mdef /= in h1.
      clear h0; assert (h0 := hodef).
      apply wf_mdefs_dyn in h0.
      assert (hwfdyn := homdef).
      apply h0 in hwfdyn.
      rewrite /cdef_wf_mdef_dyn_ty h1 in hwfdyn.
      destruct hwfdyn as (rty & wfrty & hbody & hret).
      apply cmd_eval_subst in heval_body.
      rewrite expr_eval_subst in heval_ret.
      assert (hh: length σ0 = length (generics odef) ∧ wf_ty (ClassT orig σ0)).
      { apply inherits_using_wf in hin0 => //.
        destruct hin0 as (?&?&?&hh); split => //.
        inv hh; by simplify_eq.
      }
      destruct hh as [hl0 hwf0].
      assert (hwfσ0: Forall wf_ty σ0).
      { by apply wf_ty_class_inv in hwf0. }
      assert (hwf_lty0 : wf_lty
           {|
             type_of_this := (orig, gen_targs (length odef.(generics)));
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
      assert (hbounded : bounded_lty (length odef.(generics))
           {|
             type_of_this := (orig, gen_targs (length odef.(generics)));
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
      assert (hok0 : (ok_ty def0.(constraints)) (ClassT orig σ0)).
      { apply inherits_using_ok in hin0 => //.
        by destruct hin0 as (? & ? & hok); simplify_eq.
      }
      assert (hΔo: Forall wf_constraint (constraints odef)).
      { by apply wf_constraints_wf in hodef. }
      assert (hΔ0: Forall wf_constraint (constraints def0)).
      { by apply wf_constraints_wf in hdef0. }
      assert (hΔb0 : Forall (bounded_constraint (length odef.(generics))) odef.(constraints)).
      { by apply wf_constraints_bounded in hodef. }
      iModIntro; iNext.
      iAssert (interp_env_as_mixed (interp_list Σt σ0)) as "hΣt0".
      { iIntros (k ϕi hk v) "#hv".
        rewrite /interp_list in hk.
        apply list_lookup_fmap_inv in hk as [ty [-> hty]].
        iDestruct (submixed_is_inclusion_aux with "hΣt hv") as "hh".
        - rewrite Forall_lookup in hwfσ0.
          by apply hwfσ0 in hty.
        - by rewrite interp_mixed_unfold.
      }
      iAssert (Σinterp (interp_list Σt σ0) (constraints odef))%I as "hΣtΔo".
      { iIntros (k c hc v) "hv".
        inv hok0; simplify_eq.
        assert (hc' := hc).
        apply H4 in hc'.
        iDestruct (subtype_is_inclusion with "hΣt hconstr") as "hh"; try assumption.
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
      assert (hl1 : length (interp_list Σt σ0) = length (generics odef)) by
       (by rewrite /interp_list fmap_length hl0). 
      iSpecialize ("IH" $! _ _ Aware _ _ _ _ hwf_lty0 hbounded hΔo hΔb0 hbody
        (interp_list Σt σ0) _ _ _ hl1 heval_body with "hΣt0 hΣtΔo"); simpl.
      iDestruct ("IH" with "[Hh Hle H●]") as "Hstep".
      { iClear "IH"; iSplit.
        - iExists _; iFrame.
          iSplit; last done.
          by rewrite Hdom.
        - iSplit => /=.
          + rewrite /interp_this_type interp_this_unseal /interp_this_def /=.
            iExists l, t0, odef, def0, σ0, Σt, fields, ifields.
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
      iDestruct (expr_soundness odef.(constraints) _ (interp_list Σt σ0) _ _ rty) as "hh" => //.
      rewrite !interp_dynamic_unfold.
      by iApply "hh".
  Qed.

  Lemma cmd_soundness Δ C kd Σ Γ cmd Γ' :
    wf_cdefs pdefs →
    wf_lty Γ →
    bounded_lty (length Σ) Γ →
    Forall wf_constraint Δ →
    Forall (bounded_constraint (length Σ)) Δ →
    cmd_has_ty Δ C kd (length Σ) Γ cmd Γ' →
    ∀ st st' n, cmd_eval C st cmd st' n →
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σ Γ' st'.1.
  Proof.
    intros.
    by iApply cmd_soundness_.
  Qed.

End proofs.

Print Assumptions cmd_soundness.

Definition main_lty tag := {|
  type_of_this := (tag, []);
  ctxt := ∅
|}.

Definition main_le := {|
  vthis := 1%positive;
  lenv := ∅;
|}.

Definition main_cdef tag methods := {|
  classname := tag;
  generics := [];
  constraints := [];
  superclass := None;
  classfields := ∅;
  classmethods := methods;
  support_dynamic := false;
|}.

Definition main_heap tag : heap := {[1%positive := (tag, ∅)]}.

(* Critical lemma to generate the initial iris state and boot strap
 * all the reasoning.
 * We suppose the existence of an empty class, with a single allocated
 * value of this type.
 *)
Lemma sem_heap_init
  `{PDC: ProgDefContext}
  `{!sem_heapGpreS Θ}:
  ∀ MainTag methods, pdefs !! MainTag = Some (main_cdef MainTag methods) →
  ⊢@{iPropI Θ} |==> ∃ _: sem_heapGS Θ, (heap_models (main_heap MainTag) ∗ interp_local_tys [] (main_lty MainTag) main_le).
Proof.
  move => MainTag methods hpdefs.
  set (empty := ∅ : gmap loc (prodO tagO (laterO (gmapO string (sem_typeO Θ))))).
  assert (hl : empty !! 1%positive = None) by (by rewrite /empty lookup_empty).
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) empty)) as (γI) "HI";
    first by apply gmap_view_auth_valid.
  iMod (own_update with "HI") as "[? ?]";
    first by apply (gmap_view_alloc _ 1%positive DfracDiscarded (MainTag, Next ∅)).
  iExists (SemHeapGS _ _ γI).
  iModIntro; iSplit.
  - iExists _.
    iSplit; first done.
    iSplit; first by (iPureIntro; by set_solver).
    iModIntro; iIntros (k t vs) "%H".
    rewrite /main_heap lookup_singleton_Some in H.
    destruct H as [<- [= <- <-]].
    iExists ∅; iSplit.
    + by rewrite lookup_insert.
    + iSplit; first done.
      iIntros (v t); rewrite !lookup_empty option_equivI.
      iNext.
      by iIntros "?".
  - rewrite /main_lty /main_le; iSplit => /=.
    + rewrite /interp_this_type interp_this_unseal /interp_this_def /=.
      iExists 1%positive, MainTag, _, _, (gen_targs (length (main_cdef MainTag methods).(generics))), [] , ∅, ∅; iSplitR.
      { iPureIntro.
        repeat split => //.
        * by eapply InheritsRefl.
        * move => h.
          by inv h; simplify_eq.
        * by rewrite !dom_empty_L.
      }
      iSplit.
      { iModIntro; iNext; iIntros (n ? h).
        by rewrite lookup_nil in h.
      }
      iSplit.
      { iModIntro; iNext; iIntros (n ? h).
        by rewrite lookup_nil in h.
      }
      iSplit => //.
      iSplit.
      { iIntros (f vis ty orig hf).
        rewrite /main_cdef in hpdefs.
        inv hf.
        { by rewrite hpdefs in H; injection H; intros; subst. }
        { by rewrite hpdefs in H; injection H; intros; subst. }
      }
      by rewrite mapsto_eq /mapsto_def /loc_mapsto_def.
    + iIntros (v t H).
      by rewrite !lookup_empty in H.
Qed.
