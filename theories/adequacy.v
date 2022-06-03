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
  Context `{!sem_heapGS Σ}.
  Notation γ := sem_heap_name.

  (* Helping the inference with this notation that hides Δ *)
  Local Notation "Γ ⊢ s <: t" := (@subtype _ Γ Plain s t) (at level 70, s at next level, no associativity).
  Local Notation "Γ ⊢ s <D: t" := (@subtype _ Γ Aware s t) (at level 70, s at next level, no associativity).

  (* heap models relation; the semantic heap does
     not appear because it is hidden in iProp  *)
  (* Helper defintion to state that fields are correctly modeled *)
  Definition heap_models_fields
    (iFs: gmapO string (laterO (sem_typeO Σ))) (vs: stringmap value) : iProp Σ :=
    ⌜dom vs ≡ dom iFs⌝  ∗
    ∀ f (iF: sem_typeO Σ),
    iFs !! f ≡ Some (Next iF) -∗ ∃ v, (⌜vs !! f = Some v⌝ ∗ ▷iF v).

  Definition heap_models (h : heap) : iProp Σ :=
    ∃ (sh: gmap loc (prodO tagO (gmapO string (laterO (sem_typeO Σ))))),
    own γ (gmap_view_auth (DfracOwn 1) sh) ∗ ⌜dom sh = dom h⌝ ∗
    □ ∀ (ℓ : loc) (t : tag) (vs : stringmap value),
    ⌜h !! ℓ = Some (t, vs)⌝ -∗
    ∃ (iFs : gmapO string (laterO (sem_typeO Σ))),
    sh !! ℓ ≡ Some (t, iFs) ∗ heap_models_fields iFs vs.

  Lemma expr_adequacy (Σc: list constraint) (Σi: list (interp Σ)) kd e lty le ty val :
    map_Forall (λ _, wf_cdef_parent Δ) Δ →
    map_Forall (λ _, wf_cdef_mono) Δ →
    Forall wf_constraint Σc →
    wf_lty lty →
    expr_eval le e = Some val →
    expr_has_ty Σc lty kd e ty →
    □ interp_env_as_mixed Σi -∗
    □ Σinterp Σi Σc -∗
    interp_local_tys Σi lty le -∗
    interp_type ty Σi val.
  Proof.
    move => ??? wflty he h; move: le val he.
    induction h as [| | | kd op e1 e2 hop he1 hi1 he2 hi2 |
        kd op e1 e2 hop he1 hi1 he2 hi2 | kd e1 e2 h1 hi1 h2 hi2 | kd e0 h hi |
        kd v vty hv | | kd exp S T hS hi hwf hok hsub | kd exp S T hS hi hwf hok hsub]
        => le val he; iIntros "#wfΣi #Σcoherency #Hlty".
    - inv he; rewrite interp_type_unfold /=; by eauto.
    - inv he; rewrite interp_type_unfold /=; by eauto.
    - inv he; rewrite interp_type_unfold /=; by eauto.
    - inv he.
      case heq1 : (expr_eval le e1) => [v1 | ]; rewrite heq1 in H0; last by done.
      apply hi1 in heq1.
      iDestruct (heq1 with "wfΣi Σcoherency Hlty") as "hv1".
      rewrite interp_type_unfold /=.
      iDestruct "hv1" as (z1) "%hz1".
      rewrite hz1 in H0.
      case heq2 : (expr_eval le e2) => [v2 | ]; rewrite heq2 in H0; last by done.
      apply hi2 in heq2.
      iDestruct (heq2 with "wfΣi Σcoherency Hlty") as "hv2".
      rewrite interp_type_unfold /=.
      iDestruct "hv2" as (z2) "%hz2".
      rewrite hz2 in H0.
      case: H0 => <-.
      rewrite interp_type_unfold /= /interp_int.
      move: hop; rewrite /is_bool_op; destruct op => //= _; by iExists _.
    - inv he.
      case heq1 : (expr_eval le e1) => [v1 | ]; rewrite heq1 in H0; last by done.
      apply hi1 in heq1.
      iDestruct (heq1 with "wfΣi Σcoherency Hlty") as "hv1".
      rewrite interp_type_unfold /=.
      iDestruct "hv1" as (z1) "%hz1".
      rewrite hz1 in H0.
      case heq2 : (expr_eval le e2) => [v2 | ]; rewrite heq2 in H0; last by done.
      apply hi2 in heq2.
      iDestruct (heq2 with "wfΣi Σcoherency Hlty") as "hv2".
      rewrite interp_type_unfold /=.
      iDestruct "hv2" as (z2) "%hz2".
      rewrite hz2 in H0.
      case: H0 => <-.
      rewrite interp_type_unfold /= /interp_bool.
      move: hop; rewrite /is_bool_op; destruct op => //= _; by iExists _.
    - inv he.
      case heq1 : (expr_eval le e1) => [v1 | ]; rewrite heq1 in H0; last by done.
      apply hi1 in heq1.
      iDestruct (heq1 with "wfΣi Σcoherency Hlty") as "hv1".
      rewrite interp_type_unfold /=.
      iDestruct "hv1" as (b1) "%hb1".
      rewrite hb1 in H0.
      case heq2 : (expr_eval le e2) => [v2 | ]; rewrite heq2 in H0; last by done.
      apply hi2 in heq2.
      iDestruct (heq2 with "wfΣi Σcoherency Hlty") as "hv2".
      rewrite interp_type_unfold /=.
      iDestruct "hv2" as (b2) "%hb2".
      rewrite hb2 in H0.
      case: H0 => <-.
      rewrite interp_type_unfold /= /interp_bool.
      by iExists _.
    - inv he.
      case heq : (expr_eval le e0) => [v0 | ]; rewrite heq in H0; last by done.
      apply hi in heq.
      iDestruct (heq with "wfΣi Σcoherency Hlty") as "hv".
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
      destruct lty as [[this σthis] lty]; simpl in *.
      iExists _,t,thisdef,tdef,_, _, _, _.
      iSplit; first done.
      iSplit; first by iApply "hmixed".
      iSplit; first by iApply "hconstr".
      iSplit; last by iSplit.
      iModIntro; iNext.
      iClear "wfΣi Σcoherency hmixed hdyn hloc Hv".
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
      + iSpecialize ("hinst" $! 0); rewrite /= !option_equivI.
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

  Lemma interp_local_tys_update Σi v lty le ty val :
    interp_local_tys Σi lty le -∗
    interp_type ty Σi val -∗
    interp_local_tys Σi (<[v:=ty]>lty) (<[v:=val]>le).
  Proof.
    iIntros "#[Hthis Hi] #?".
    iSplit; first done.
    iIntros (v' ty') "H".
    rewrite lookup_insert_Some.
    iDestruct "H" as %[[<- <-]|[??]].
    - iExists _. rewrite lookup_insert. by iSplit.
    - rewrite lookup_insert_ne; last done. by iApply "Hi".
  Qed.

  Lemma heap_models_update Σc Σi h l rt vs t σt f vis fty orig v:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
    map_Forall (λ _ : string, wf_cdef_fields_wf) Δ →
    map_Forall (λ _cname, wf_field_mono) Δ →
    map_Forall (λ _ : string, wf_cdef_mono) Δ →
    Forall wf_constraint Σc →
    h !! l = Some (rt, vs) →
    has_field f t vis fty orig →
    wf_ty (ClassT t σt) →
    □ interp_env_as_mixed Σi -∗
    □ Σinterp Σi Σc -∗
    match vis with
    | Public => interp_type (ClassT t σt) Σi (LocV l)
    | Private => interp_this_type t σt Σi (LocV l)
    end -∗
    interp_type (subst_ty σt fty) Σi v -∗
    heap_models h -∗
    heap_models (<[l:=(rt, <[f:=v]> vs)]> h).
  Proof.
    move => ??????? hheap hfield hwf.
    iIntros "#wfΣi #Σcoherency hrecv".
    iAssert (∃ t' σ' Σt fields (ifields: gmapO string (laterO (sem_typeO Σ))),
      ⌜inherits_using t' t σ' ∧ has_fields t' fields ∧ dom fields = dom ifields⌝ ∗
       (□ ▷ ∀ w,
           interp_type fty (interp_list Σi σt) w ∗-∗
           interp_type (subst_ty σ' fty) Σt w)
       ∗
       (∀ f vis ty orig, ⌜has_field f t' vis ty orig⌝ -∗ ifields !! f ≡ Some (Next (interp_car (interp_type ty Σt)))) ∗
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
    rewrite !option_equivI later_equivI discrete_fun_equivI.
    iNext.
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
  Lemma wf_mdef_dyn_ty_wf Σi Σc C kd st st' lty lhs recv name args l n:
    wf_cdefs Δ →
    wf_lty lty →
    Forall wf_constraint Σc →
    expr_has_ty Σc lty kd recv DynamicT →
    expr_eval st.1 recv = Some (LocV l) →
    cmd_eval C st (CallC lhs recv name args) st' n →
    □ interp_env_as_mixed Σi -∗
    □ Σinterp Σi Σc -∗
    heap_models st.2 ∗ interp_local_tys Σi lty st.1 -∗
    ⌜∃ t vs orig σ def mdef,
    has_method name t orig (subst_mdef σ mdef) ∧
    st.2 !! l = Some (t, vs) ∧
    inherits_using t orig σ ∧
    Δ !! orig = Some def ∧
    def.(classmethods) !! name = Some mdef ∧
    wf_mdef_dyn_ty def.(constraints) orig (gen_targs (length def.(generics))) mdef⌝%I.
  Proof.
    move => wfΔ ?? hrty heval hceval.
    iIntros "#hΣi #hΣiΣc [Hh #Hle]".
    inv hceval; simpl in *.
    rewrite heval in H3; simplify_eq.
    iDestruct (expr_adequacy with "hΣi hΣiΣc Hle") as "#He" => //; try (by apply wfΔ).
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
    iDestruct "He" as (dyntag dyndef hpure Σdyn) "He".
    destruct hpure as [hdyndef hsupdyn].
    rewrite interp_tag_equiv; last by apply wfΔ.
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
    apply has_method_from_def in h0 => //; try by apply wfΔ.
    destruct h0 as (odef & omdef & hodef & homdef & _ & [σ0 [hin0 ->]]).
    exists t, vs, orig, σ0, odef, omdef.
    split; first done.
    split; first done.
    split; first done.
    split; first done.
    split; first done.
    destruct wfΔ.
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
    
  Lemma cmd_adequacy_ Σc C kd lty cmd lty' :
    wf_cdefs Δ →
    wf_lty lty →
    Forall wf_constraint Σc →
    cmd_has_ty Σc C kd lty cmd lty' →
    ∀ Σi st st' n,
    cmd_eval C st cmd st' n →
    □ interp_env_as_mixed Σi -∗
    □ Σinterp Σi Σc -∗
    heap_models st.2 ∗ interp_local_tys Σi lty st.1 -∗ |=▷^n
        heap_models st'.2 ∗ interp_local_tys Σi lty' st'.1.
  Proof.
    move => wfΔ wflty hΣc .
    iLöb as "IH" forall (Σc C kd lty cmd lty' wflty hΣc).
    iIntros "%hty" (Σi st st' n hc) "#hΣi #hΣiΣc".
    iInduction hty as [ kd lty | kd lty1 lty2 lty3 fstc sndc hfst hi1 hsnd hi2 |
        kd lty lhs e ty he | kd lty1 lty2 cond thn els hcond hthn hi1 hels hi2 |
        kd lty lhs t targs name fty hrecv hf |
        kd lty lhs recv t targs name fty orig hrecv hf |
        kd lty fld rhs fty t σ hrecv hrhs hf |
        kd lty recv fld rhs fty orig t σ hrecv hrhs hf |
        kd lty lhs t targs args fields hwf hok hf hdom harg |
        kd lty lhs recv t targs name orig mdef args hrecv hhasm hdom hi |
        kd lty c rty' rty hsub h hi |
        kd lty rty v tv t cmd hv hr h hi |
        kd lty rty v tv cmd hv hr h hi |
        kd lty rty v tv cmd hv hr h hi |
        kd lty rty v tv cmd hv hr h hi |
        kd lty rty v tv cmd hv hr h hi |
        kd lty1 lty2 cond thn els hcond htn hi1 hels hi2 |
        kd lty lhs recv name he hnotthis |
        kd lty recv fld rhs hrecv hrhs hnotthis |
        kd lty lhs recv name args hrecv hi hnotthis
      ] "IHty" forall (st st' n hc).
    - (* SkipC *) inv hc.
      rewrite updN_zero.
      by iIntros "?".
    - (* SeqC *) inv hc. iIntros "H".
      iSpecialize ("IHty" $! wflty with "[//] H").
      rewrite Nat_iter_add.
      iApply (updN_mono_I with "[] IHty").
      iApply "IHty1" => //.
      destruct wfΔ.
      by apply cmd_has_ty_wf in hfst.
    - (* LetC *)
      inv hc.
      iClear "IH".
      iIntros "[? #Hle]".
      rewrite updN_zero /=.
      iFrame.
      iDestruct (expr_adequacy with "hΣi hΣiΣc Hle") as "#?" => //; try (by apply wfΔ).
      by iApply interp_local_tys_update.
    - (* IfC *) inv hc
      + iIntros "H". by iApply "IHty".
      + iIntros "H". by iApply "IHty1".
    - (* GetPriv *) inv hc.
      iClear "IH".
      iIntros "[Hh #Hle]".
      iModIntro. (* keep the later *)
      destruct lty as [[this σ] lty].
      destruct le as [vthis lenv].
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
      iAssert (⌜t0 = t1⌝ ∗ heap_models h ∗ ▷ interp_type (subst_ty targs fty) Σi v)%I with "[Hh]" as "[%Ht [Hh Hv]]".
      { iDestruct "Hh" as (sh) "(H● & %hdom & #Hh)".
        iDestruct (sem_heap_own_valid_2 with "H● H◯") as "#HΦ".
        iDestruct ("Hh" with "[//]") as (iFs) "[H H▷]".
        iRewrite "H" in "HΦ".
        rewrite option_equivI prod_equivI /=.
        iDestruct "HΦ" as "[%Ht HΦ]".
        fold_leibniz; subst.
        iSplitR; first done.
        iSplitL. { iExists _. iFrame. by iSplit. }
        assert (hfC: has_field name t1 Private (subst_ty σ fty) C) by (destruct wfΔ; by eapply has_field_inherits_using).
        iSpecialize ("hdyn" $! name Private (subst_ty σ fty) C hfC).
        iDestruct "H▷" as "[%hdf h]".
        iRewrite -"HΦ" in "hdyn".
        iSpecialize ("h" $! name _ with "[hdyn]"); first done.
        iDestruct "h" as (w) "[%hw hiw]".
        simplify_eq.
        iNext.
        rewrite interp_type_subst; last first.
        { destruct wfΔ.
          apply has_field_bounded in hf => //.
          destruct hf as (? & ? & ?).
          apply inherits_using_wf in hinherits => //.
          destruct hinherits as (? & ?& ? & hh).
          inv wfthis; simplify_eq.
          by rewrite H10.
        }
        iRewrite -"hinst".
        rewrite -interp_type_subst //.
        destruct wfΔ.
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
      iDestruct (expr_adequacy with "hΣi hΣiΣc Hle") as "#He" => //; try (by apply wfΔ).
      rewrite interp_class_unfold //; first last.
      { by apply expr_has_ty_wf in hrecv. }
      { by apply wfΔ. }
      iDestruct "He" as (?? def def0 ????) "[%H [#hmixed [#? [#hf0 [#hdyn H◯]]]]]".
      destruct H as ([= <-] & hdef & hdef0 & hlen & ? & hinherits & hfields & hidom).
      assert (hwf0: wf_ty (ClassT t targs)) by (by apply expr_has_ty_wf in hrecv).
      assert (hl0: length (generics def) = length σ).
      { apply inherits_using_wf in hinherits; try (by apply wfΔ).
        destruct hinherits as (?&?&?&hh).
        inv hh; by simplify_eq.
      }
      assert (hl1: length σ = length targs).
      { rewrite -hl0.
        rewrite /interp_list fmap_length in hlen.
        by rewrite hlen.
      }
      assert (hff: has_field name t1 Public (subst_ty σ fty) orig).
      { by apply has_field_inherits_using with (A := t1) (σB := σ) in hf => //; try (by apply wfΔ). }
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
        iDestruct "H▷" as "[%hdf h]".
        iRewrite -"HΦ" in "hdyn".
        iSpecialize ("h" $! name _ with "[hdyn]"); first done.
        iDestruct "h" as (w) "[%hw hiw]".
        by simplify_eq.
      }
      subst; simpl.
      iNext.
      iFrame.
      destruct wfΔ.
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
      assert (wfΔ' := wfΔ).
      destruct wfΔ'.
      iClear "IH".
      iIntros "[Hh #Hle]" => /=.
      iSplitL; last done.
      destruct lty as [[tthis σthis]  lty].
      destruct le as [vthis le].
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
      + iApply expr_adequacy => //; by apply wfΔ.
    - (* SetPub *) inv hc.
      assert (wfΔ' := wfΔ).
      destruct wfΔ'.
      iClear "IH".
      iIntros "[Hh #Hle]" => /=.
      iSplitL; last done.
      assert (ht: wf_ty (ClassT t σ)) by (by apply expr_has_ty_wf in hrecv).
      iApply (heap_models_update _ _ _ _ _ _ t σ) => //=.
      + iApply expr_adequacy => //; by apply wfΔ.
      + iApply expr_adequacy => //; by apply wfΔ.
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
         (λ(ty: lang_ty), Next (interp_car (interp_type ty Σi))) <$> ((λ x, subst_ty targs x.1.2) <$> fields)
      ).
      iMod ((sem_heap_own_update new) with "H●") as "[H● #H◯]" => //;
        first by apply (sem_heap_view_alloc _ new t iFs).
      iIntros "!> !>". (* kill the modalities *)
      iAssert (interp_type (ClassT t targs) Σi (LocV new)) with "[]" as "#Hl".
      { rewrite interp_class_unfold //; last by apply wfΔ.
        assert (hwf' := hwf).
        inv hwf'.
        iExists new, t, def, def, (gen_targs (length def.(generics))), (interp_list Σi targs), fields, iFs.
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
          assert (hsub: Σc ⊢ phi <: MixedT) by eauto.
          destruct wfΔ.
          iDestruct (subtype_is_inclusion _ hΣc wf_parent wf_mono _ _ _ _ hsub v with "hΣi hΣiΣc hphi") as "hsub".
          + by eauto.
          + by rewrite interp_mixed_unfold.
        }
        assert (hconstraints: ∀ i c,
          subst_constraints targs def.(constraints) !! i = Some c → Σc ⊢ c.1 <D: c.2
        ).
        { rewrite /subst_constraints => i ? hin.
          apply list_lookup_fmap_inv in hin as [c [-> hin]].
          rewrite /subst_constraint /=.
          inv hok; simplify_eq.
          apply H6 in hin.
          apply subtype_weaken with (Γ' := (Σc ++ subst_constraints targs def.(constraints))) in hin => //;
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
          assert (hsub: Σc ⊢ (subst_ty targs c.1) <D: (subst_ty targs c.2)).
          { apply subtype_constraint_elim with (Γ' := subst_constraints targs def.(constraints)) => //.
            apply subtype_weaken with (Γ := subst_constraints targs def.(constraints)); last by set_solver.
            eapply subtype_subst => //.
            - by apply wfΔ.
            - eapply SubConstraint.
              apply elem_of_list_lookup_2 in heq.
              by rewrite (surjective_pairing c) in heq.
          }
          destruct wfΔ.
          rewrite -!interp_type_subst.
          { iApply (subtype_is_inclusion _ hΣc wf_parent wf_mono _ _ _ _ hsub v with "hΣi hΣiΣc") => //.
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
        assert (hb: bounded (length targs) ty).
        { apply has_field_bounded in hff; try (by apply wfΔ).
          destruct hff as (?&?&hh); simplify_eq.
          by rewrite H2.
        }
        apply hf in hff.
        rewrite !lookup_fmap hff /= option_equivI later_equivI.
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
      assert (heval0: expr_eval le a0 = Some v0).
      { rewrite (map_args_lookup _ _ _ args vargs H8 f) in hv0.
        by rewrite ha0 in hv0.
      }
      assert (hty0: expr_has_ty Σc lty kd a0 (subst_ty targs fty.1.2)) by (by apply harg with f).
      rewrite !lookup_fmap hty /= option_equivI later_equivI.
      iNext.
      rewrite discrete_fun_equivI.
      iSpecialize ("hiF" $! v0).
      iRewrite -"hiF".
      iDestruct (expr_adequacy Σc Σi kd a0 with "hΣi hΣiΣc Hle") as "#Ha0" => //; by apply wfΔ.
    - (* CallC *) inv hc; simpl.
      assert (wfΔ0 := wfΔ).
      destruct wfΔ0.
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
      iDestruct (expr_adequacy Σc Σi _ recv with "hΣi hΣiΣc Hle") as "#Hrecv" => //.
      rewrite interp_class_unfold //.
      iDestruct "Hrecv" as (? t1 def def1 σin Σt fields ifields) "[%Hpure [#hΣt [#hΣtΣ1 [#hf [#hdyn Hl]]]]]".
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
      assert (hwf0: wf_ty (ClassT orig0 σt1_o0)).
      { apply inherits_using_wf in hin_t1_o0 => //.
        destruct hin_t1_o0 as (? & ? & ? & ?).
        by simplify_eq.
      }
      assert (hok0: ok_ty (constraints def1) (ClassT orig0 σt1_o0)).
      { apply inherits_using_ok in hin_t1_o0 => //.
        destruct hin_t1_o0 as (? & ? & ?).
        by simplify_eq.
      }
      destruct (wf_mdef_ty_gen def1.(constraints) orig0 name σt1_o0 odef0 omdef0)
        as (rty & hwf_rty & hbody0 & hret0) => //.
      assert (hwf_lty0 : wf_lty
           {|
             type_of_this := (orig0, σt1_o0);
             ctxt := subst_ty σt1_o0 <$> methodargs omdef0
           |}).
      { split => //=.
        rewrite map_Forall_lookup => k tk.
        rewrite lookup_fmap_Some.
        case => ty [<- ] hk.
        apply wf_ty_subst => //; first by apply wf_ty_class_inv in hwf0.
        apply wf_methods_wf in hodef0.
        apply hodef0 in homdef0.
        by apply homdef0 in hk.
      }
      assert (hΣ1 : Forall wf_constraint def1.(constraints)).
      { by apply wf_constraints_wf in hdef1.  }
      rewrite /subst_mdef /= in heval_body.
      rewrite /subst_mdef /= in heval_ret.
      assert (hh: Forall wf_ty σt1_o0 ∧ length odef0.(generics) = length σt1_o0).
      { apply inherits_using_wf in hin_t1_o0 => //.
        destruct hin_t1_o0 as (?&?&?&hh).
        split; first by apply wf_ty_class_inv in hh.
        inv hh; by simplify_eq.
      }
      destruct hh as [hFσt1_o0 heq0].
      assert (hh: Forall wf_ty σt_o ∧ length odef.(generics) = length σt_o).
      { apply inherits_using_wf in hin_t_o => //.
        destruct hin_t_o as (?&?&?&hh).
        split; first by apply wf_ty_class_inv in hh.
        inv hh; by simplify_eq.
      }
      destruct hh as [hFσt_o heq1].
      assert (hh: Forall wf_ty σin ∧ length def.(generics) = length σin).
      { apply inherits_using_wf in hin_t1_t => //.
        destruct hin_t1_t as (?&?&?&hh).
        split; first by apply wf_ty_class_inv in hh.
        inv hh; by simplify_eq.
      }
      destruct hh as [hFσin heq2].
      assert (heq3: length def.(generics) = length targs).
      { inv hwfr; by simplify_eq. }
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
      assert (
        hmret0 : def1.(constraints) ⊢ methodrettype (subst_mdef σt1_o0 omdef0) <D:
                                      methodrettype (subst_mdef σin (subst_mdef σt_o omdef))).
      { apply subtype_constraint_elim with (Γ' := subst_constraints σt1_o0 odef0.(constraints)) => //.
        apply subtype_weaken with (Γ := subst_constraints σt1_o0 odef0.(constraints)) => //.
        by set_solver.
      }
      iModIntro; iNext.
      iDestruct (neg_interp_variance with "hf") as "hf2".
      iSpecialize ("IH" $! _ _ Plain _ _ _ hwf_lty0 hΣ1 hbody0 Σt _ _ _ heval_body with "hΣt hΣtΣ1"); simpl.
      iDestruct ("IH" with "[Hh Hle H●]") as "Hstep".
      { iClear "IH"; iSplit.
        - iExists _; iFrame.
          iSplit; last done.
          by rewrite Hdom.
        - iSplit => /=.
          + rewrite /interp_this_type interp_this_unseal /interp_this_def /=.
            iExists l, t1, odef0, def1, σt1_o0, Σt, fields, ifields.
            repeat iSplit => //.
            iPureIntro.
            by rewrite /interp_list fmap_length.
          + iIntros (v ty hv).
            rewrite lookup_fmap_Some in hv.
            destruct hv as [tv [<- hv]].
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
            assert (h2 : methodargs (subst_mdef σt1_o0 omdef0) !! v = Some (subst_ty σt1_o0 tv)).
            { by rewrite /subst_mdef /= lookup_fmap hv. }
            assert (hsub: def1.(constraints) ⊢ subst_ty σin (subst_ty σt_o tw) <D: subst_ty σt1_o0 tv).
            { move: (hmargs0 v _ _ h2 h1) => hsub_.
              apply subtype_constraint_elim with (Γ' := subst_constraints σt1_o0 odef0.(constraints)) => //.
              apply subtype_weaken with (Γ := subst_constraints σt1_o0 odef0.(constraints)) => //.
              by set_solver.
            }
            assert (hwf_tw: wf_ty (subst_ty σt_o tw)).
            { apply wf_ty_subst => //.
              apply wf_methods_wf in hodef.
              apply hodef in homdef.
              by apply homdef in htw.
            }
            move: (hi v _ _ h0 ha) => haty.
            iDestruct (expr_adequacy with "hΣi hΣiΣc Hle") as "he" => //.
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
            iApply (subtype_is_inclusion _ hΣ1 wf_parent wf_mono _ _ _ _ hsub) => //.
            by apply wf_ty_subst.
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
      iApply (subtype_is_inclusion _ hΣ1 wf_parent wf_mono _ _ _ _ hmret0) => //.
      { apply wf_ty_subst => //.
        apply wf_methods_wf in hodef0.
        apply hodef0 in homdef0.
        by apply homdef0.
      }
      by iDestruct (expr_adequacy with "hΣt hΣtΣ1 Hle2") as "hret0".
    - (* Subtyping *)
      destruct wfΔ.
      iIntros "H".
      iSpecialize ("IHty" $! wflty with "[//] H").
      iApply updN_mono_I; last done.
      iIntros "[Hh #Hrty]". iFrame.
      iDestruct (interp_local_tys_is_inclusion with "hΣi hΣiΣc Hrty") as "Hrty'" => //.
      + by apply cmd_has_ty_wf in h.
      + rewrite Forall_forall => i hi v.
        by apply _.
    - (* RuntimeCheck tag *) inv hc; last first.
      { iIntros "[Hh H]".
        iAssert (heap_models st'.2 ∗ interp_local_tys Σi rty st'.1)%I with "[Hh H]" as "H".
        + iFrame.
          destruct wfΔ.
          iApply interp_local_tys_is_inclusion => //.
          rewrite Forall_forall => ???.
          by apply _.
        + iRevert "H".
          by iApply updN_intro.
      }
      iIntros "H".
      assert (hwf: wf_lty (<[v:=InterT tv (ExT t)]> lty)).
      { apply insert_wf_lty => //.
        constructor; first by apply wflty in hv.
        by constructor.
      }
      iApply ("IHty" $! hwf with "[//]"); iClear "IH IHty".
      clear H7 h.
      destruct H6 as (l & hl & t' & fields & hlt & hinherits).
      iDestruct "H" as "[H #Hle]".
      iDestruct "Hle" as "[Hthis Hle]".
      iDestruct ("Hle" $! v with "[//]") as (?) "[%Hlev Hv]".
      rewrite Hlev in hl; simplify_eq.
      iAssert (interp_type MixedT Σi (LocV l)) as "Hmixed".
      { destruct wfΔ.
        assert (hsub : Σc ⊢ tv <: MixedT) by apply SubMixed.
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
      rewrite interp_tag_equiv; last (by apply wfΔ).
      iDestruct "Hl" as (k rt def rtdef σ Σt exfields ifields) "[%H [#hmixed [#hΣt [#hinst [#hdyn #Hl]]]]]".
      destruct H as ([= <-] & hdef & hrtdef & hlexΣ & hlΣt & hinherits' & hfields' & hidom'); simplify_eq.
      iAssert (⌜t' = rt⌝ ∗ heap_models st.2 ∗ interp_type (ExT rt) Σi (LocV l))%I with "[H]" as "[%heq [Hh #Hv2]]".
      { iDestruct "H" as (sh) "(H● & %hdom & #Hh)".
        iDestruct (sem_heap_own_valid_2 with "H● Hl") as "#HΦ".
        iDestruct ("Hh" with "[//]") as (iFs) "[H H▷]".
        iRewrite "H" in "HΦ".
        rewrite option_equivI prod_equivI /=.
        iDestruct "HΦ" as "[%Ht HΦ]".
        fold_leibniz; subst.
        iSplitR; first by iPureIntro.
        iSplitL. { iExists _. iFrame. by iSplit. }
        rewrite interp_ex_unfold /=.
        iExists Σt.
        rewrite interp_tag_equiv //; last by apply wfΔ.
        iExists l, rt, rtdef, rtdef, (gen_targs (length rtdef.(generics))), Σt, exfields, ifields.
        iSplit.
        { iPureIntro; repeat split => //.
          by constructor.
        }
        iSplit => //.
        iSplit => //.
        iSplit.
        { iModIntro; iNext.
          by iApply iForall3_interp_gen_targs.
        }
        by iSplit.
      }
      subst.
      iFrame.
      iSplit => /=; first done.
      iIntros (w tw).
      rewrite lookup_insert_Some.
      iIntros "%Hw".
      destruct Hw as [[<- <-] | [hne hw]]; last by iApply "Hle".
      iExists (LocV l); rewrite Hlev; iSplitR; first done.
      rewrite interp_inter_unfold /=; iSplit; first done.
      destruct wfΔ.
      by iApply inherits_is_ex_inclusion.
    - (* RuntimeCheck Int *) inv hc; last first.
      { iIntros "[Hh H]".
        iAssert (heap_models st'.2 ∗ interp_local_tys Σi rty st'.1)%I with "[Hh H]" as "H".
        + iFrame.
          destruct wfΔ.
          iApply interp_local_tys_is_inclusion => //.
          rewrite Forall_forall => ???.
          by apply _.
        + iRevert "H".
          by iApply updN_intro.
      }
      iIntros "H".
      assert (hwf: wf_lty (<[v:=InterT tv IntT]> lty)).
      { apply insert_wf_lty => //.
        constructor; first by apply wflty in hv.
        by constructor.
      }
      iApply ("IHty" $! hwf with "[//]"); iClear "IH IHty".
      clear H7 h.
      destruct H6 as (z & hz).
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
        iAssert (heap_models st'.2 ∗ interp_local_tys Σi rty st'.1)%I with "[Hh H]" as "H".
        + iFrame.
          destruct wfΔ.
          iApply interp_local_tys_is_inclusion => //.
          rewrite Forall_forall => ???.
          by apply _.
        + iRevert "H".
          by iApply updN_intro.
      }
      iIntros "H".
      assert (hwf: wf_lty (<[v:=InterT tv BoolT]> lty)).
      { apply insert_wf_lty => //.
        constructor; first by apply wflty in hv.
        by constructor.
      }
      iApply ("IHty" $! hwf with "[//]"); iClear "IH IHty".
      clear H7 h.
      destruct H6 as (b & hb).
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
        iAssert (heap_models st'.2 ∗ interp_local_tys Σi rty st'.1)%I with "[Hh H]" as "H".
        + iFrame.
          destruct wfΔ.
          iApply interp_local_tys_is_inclusion => //.
          rewrite Forall_forall => ???.
          by apply _.
        + iRevert "H".
          by iApply updN_intro.
      }
      iIntros "H".
      assert (hwf: wf_lty (<[v:=InterT tv NullT]> lty)).
      { apply insert_wf_lty => //.
        constructor; first by apply wflty in hv.
        by constructor.
      }
      iApply ("IHty" $! hwf with "[//]"); iClear "IH IHty".
      clear H7 h.
      simpl in H6.
      iDestruct "H" as "[H #Hle]".
      iDestruct "Hle" as "[Hthis Hle]".
      iDestruct ("Hle" $! v with "[//]") as (?) "[%Hlev Hv]".
      rewrite Hlev in H6; simplify_eq.
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
        iAssert (heap_models st'.2 ∗ interp_local_tys Σi rty st'.1)%I with "[Hh H]" as "H".
        + iFrame.
          destruct wfΔ.
          iApply interp_local_tys_is_inclusion => //.
          rewrite Forall_forall => ???.
          by apply _.
        + iRevert "H".
          by iApply updN_intro.
      }
      iIntros "H".
      assert (hwf: wf_lty (<[v:=InterT tv NonNullT]> lty)).
      { apply insert_wf_lty => //.
        constructor; first by apply wflty in hv.
        by constructor.
      }
      iApply ("IHty" $! hwf with "[//]"); iClear "IH IHty".
      clear H7 h.
      simpl in H6.
      iDestruct "H" as "[H #Hle]".
      iFrame.
      iAssert (interp_local_tys Σi lty st.1) as "#Hle_"; first done.
      iDestruct "Hle_" as "[Hthis Hle_]".
      iDestruct ("Hle_" $! v with "[//]") as (?) "[%Hlev Hv]".
      iAssert (interp_type MixedT Σi val) as "Hmixed".
      { destruct wfΔ.
        assert (hsub : Σc ⊢ tv <: MixedT) by apply SubMixed.
        iApply subtype_is_inclusion => //.
        by apply wflty in hv.
      }
      replace (interp_local_tys Σi (<[v:=InterT tv NonNullT]> lty) st.1) with
              (interp_local_tys Σi (<[v:=InterT tv NonNullT]> lty) (<[v := val]>st.1)); last first.
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
      by rewrite Hlev in H6.
    - (* Dynamic ifC *) inv hc.
      + iIntros "H". by iApply "IHty".
      + iIntros "H". by iApply "IHty1".
    - (* Dynamic Get *) inv hc.
      iClear "IH".
      iIntros "[Hh #Hle]"; simpl.
      iModIntro. (* keep the later *)
      iDestruct (expr_adequacy with "hΣi hΣiΣc Hle") as "#He" => //; try (by apply wfΔ).
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
      iDestruct "He" as (dyntag dyndef hpure Σdyn) "He".
      destruct hpure as [hdyndef hsupdyn].
      rewrite interp_tag_equiv; last by apply wfΔ.
      iDestruct "He" as (?? def def0 ????) "[%H [#hmixed [#hconstr [#hf0 [#hdyn H◯]]]]]".
      destruct H as ([= <-] & hdef & hdef0 & hlen & ? & hinherits & hfields & hidom).
      simplify_eq.
      assert (hl0: length (generics dyndef) = length σ).
      { apply inherits_using_wf in hinherits; try (by apply wfΔ).
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
        { destruct wfΔ.
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
        destruct wfΔ.
        assert (hwfc: Forall wf_constraint def0.(constraints)) by by apply wf_constraints_wf in hdef0.
        iSpecialize ("hdyn" $! name Public fty orig hf).
        iDestruct "H▷" as "[%hdf h]".
        iRewrite -"HΦ" in "hdyn".
        iSpecialize ("h" $! name _ with "[hdyn]"); first done.
        iDestruct "h" as (w) "[%hw hiw]".
        simplify_eq.
        iNext.
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
      assert (wfΔ' := wfΔ).
      destruct wfΔ'.
      iClear "IH".
      iIntros "[Hh #Hle]" => /=.
      iSplitL; last done.
      iAssert (interp_type DynamicT Σi (LocV l)) as "#Hl".
      { by iApply expr_adequacy. }
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
      iDestruct "Hl" as (dyntag dyndef hpure Σdyn) "Hl".
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
      rewrite !option_equivI later_equivI discrete_fun_equivI.
      iNext.
      iSpecialize ("hf'" $! v).
      iRewrite -"hf'".
      iAssert (interp_type DynamicT Σi v) as "#Hve".
      { by iApply expr_adequacy. }
      assert (hsub: def0.(constraints) ⊢ DynamicT <D: fty).
      { destruct wfΔ.
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
      assert (wfΔ0 := wfΔ).
      destruct wfΔ0.
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
      iDestruct (expr_adequacy Σc Σi _ recv with "hΣi hΣiΣc Hle") as "#Hl" => //.
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
      iDestruct "Hl" as (dyntag dyndef hpure Σdyn) "Hl".
      destruct hpure as [hdyndef hsupdyn].
      rewrite interp_tag_equiv //.
      iDestruct "Hl" as (?? def def0 ????) "[%Hpure [#hmixed [#hconstr [#hf0 [#hdyn H◯]]]]]".
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
             type_of_this := (orig, σ0);
             ctxt := to_dyn <$> methodargs omdef
           |}).
      { split => //=.
        rewrite map_Forall_lookup => k tk.
        rewrite lookup_fmap_Some.
        by case => ty [<- ] hk.
      }
      assert (hok0 : (ok_ty def0.(constraints)) (ClassT orig σ0)).
      { apply inherits_using_ok in hin0 => //.
        by destruct hin0 as (? & ? & hok); simplify_eq.
      }
      assert (hΣ0: Forall wf_constraint (constraints def0)).
      { by apply wf_constraints_wf in hdef0. }
      assert (hbody0 : cmd_has_ty def0.(constraints) orig Aware
          {|
            type_of_this := (orig, σ0);
            ctxt := to_dyn <$> methodargs omdef
          |} (subst_cmd σ0 (methodbody omdef)) (subst_lty σ0 rty)).
      { apply cmd_has_ty_subst with (Γ' := def0.(constraints)) (σ := σ0) in hbody => //; first last.
        - by apply ok_ty_class_inv in hok0.
        - split => /=.
          + rewrite /this_type /=.
            econstructor => //.
            { by rewrite length_gen_targs. }
            { by apply gen_targs_wf. }
          + rewrite map_Forall_lookup => k ?.
            by rewrite lookup_fmap_Some => [[ty [<- hk]]].
        - by apply wf_constraints_wf in hodef.
        - rewrite {1}/subst_lty subst_ty_gen_targs //= in hbody.
          replace (subst_ty σ0 <$> (to_dyn <$> methodargs omdef)) with
                  (to_dyn <$> methodargs omdef) in hbody; last first.
          { apply map_eq => k.
            rewrite !lookup_fmap.
            by destruct (omdef.(methodargs) !! k).
          }
          eapply cmd_has_ty_constraint_elim => //.
          move => i ? hc.
          apply list_lookup_fmap_inv in hc as [c [-> hc]].
          rewrite /subst_constraint /=.
          inv hok0; simplify_eq.
          by eauto.
      }
      (* iDestruct (neg_interp_variance with "hf0") as "hf2". *)
      iModIntro; iNext.
      iSpecialize ("IH" $! _ _ Aware _ _ _ hwf_lty0 hΣ0 hbody0 Σt _ _ _ heval_body with "hmixed hconstr"); simpl.
      iDestruct ("IH" with "[Hh Hle H●]") as "Hstep".
      { iClear "IH"; iSplit.
        - iExists _; iFrame.
          iSplit; last done.
          by rewrite Hdom.
        - iSplit => /=.
          + rewrite /interp_this_type interp_this_unseal /interp_this_def /=.
            iExists l, t0, odef, def0, σ0, Σt, fields, ifields.
            repeat iSplit => //.
            iPureIntro.
            by rewrite /interp_list fmap_length.
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
            iDestruct (expr_adequacy with "hΣi hΣiΣc Hle") as "he" => //.
            by rewrite !interp_dynamic_unfold.
      }
      iRevert "Hstep".
      iApply updN_mono_I.
      iIntros "[Hmodels Hle2]"; iFrame.
      iApply interp_local_tys_update; first by done.
      rewrite /to_dyn in hret.
      assert (hwfrty : wf_lty (subst_lty σ0 rty)).
      { by apply subst_wf_lty => //. }
      assert (hret0:
        expr_has_ty (constraints def0) (subst_lty σ0 rty) Aware (subst_expr σ0 omdef.(methodret)) DynamicT).
      { apply expr_has_ty_subst with (Γ' := def0.(constraints)) (σ := σ0) in hret => //; first last.
        + by apply ok_ty_class_inv in hok0.
        + eapply expr_has_ty_constraint_elim in hret => //.
          rewrite /subst_constraints => i ? hc.
          apply list_lookup_fmap_inv in hc as [c [-> hc]].
          rewrite /subst_constraint /=.
          inv hok0; simplify_eq.
          by eauto.
      }
      iDestruct (expr_adequacy with "hmixed hconstr Hle2") as "hret0" => //.
      by rewrite !interp_dynamic_unfold.
  Qed.

  Lemma cmd_adequacy Σc C kd Σi lty cmd lty' :
    wf_cdefs Δ →
    wf_lty lty →
    Forall wf_constraint Σc →
    cmd_has_ty Σc C kd lty cmd lty' →
    ∀ st st' n, cmd_eval C st cmd st' n →
    □ interp_env_as_mixed Σi -∗
    □ Σinterp Σi Σc -∗
    heap_models st.2 ∗ interp_local_tys Σi lty st.1 -∗ |=▷^n
        heap_models st'.2 ∗ interp_local_tys Σi lty' st'.1.
  Proof.
    intros.
    by iApply cmd_adequacy_.
  Qed.

End proofs.

Print Assumptions cmd_adequacy.

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
  `{!sem_heapGpreS Σ}:
  ∀ MainTag methods, Δ !! MainTag = Some (main_cdef MainTag methods) →
  ⊢@{iPropI Σ} |==> ∃ _: sem_heapGS Σ, (heap_models (main_heap MainTag) ∗ interp_local_tys [] (main_lty MainTag) main_le).
Proof.
  move => MainTag methods hΔ.
  set (empty := ∅ : gmap loc (prodO tagO (gmapO string (laterO (sem_typeO Σ))))).
  assert (hl : empty !! 1%positive = None) by (by rewrite /empty lookup_empty).
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) empty)) as (γI) "HI";
    first by apply gmap_view_auth_valid.
  iMod (own_update with "HI") as "[? ?]";
    first by apply (gmap_view_alloc _ 1%positive DfracDiscarded (MainTag, ∅)).
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
        rewrite /main_cdef in hΔ.
        inv hf.
        { by rewrite hΔ in H; injection H; intros; subst. }
        { by rewrite hΔ in H; injection H; intros; subst. }
      }
      by rewrite mapsto_eq /mapsto_def /loc_mapsto_def.
    + iIntros (v t H).
      by rewrite !lookup_empty in H.
Qed.
