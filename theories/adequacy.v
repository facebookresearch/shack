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

From shack Require Import lang heap modality interp.

Section proofs.
  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.

  (* Iris semantic context *)
  Context `{!sem_heapGS Σ}.
  Notation γ := sem_heap_name.

  (* Helping the inference with this notation that hides Δ *)
  Local Notation "s <: t" := (@subtype _ s t) (at level 70, no associativity).
  Local Notation "lty <:< rty" := (@lty_sub _ lty rty) (at level 70, no associativity).
  Local Notation "lts <: vs :> rts" := (@subtype_targs _ vs lts rts) (at level 70, vs at next level).

  (* heap models relation; the semantic heap does
     not appear because it is hidden in iProp  *)
  (* Helper defintion to state that fields are correctly modeled *)
  Definition heap_models_fields
    (iFs: gmapO string (laterO (sem_typeO Σ))) (vs: stringmap value) : iProp Σ :=
    ⌜dom (gset string) vs ≡ dom _ iFs⌝  ∗
    ∀ f (iF: sem_typeO Σ),
    iFs !! f ≡ Some (Next iF) -∗ ∃ v, (⌜vs !! f = Some v⌝ ∗ ▷iF v).

  Definition heap_models (h : heap) : iProp Σ :=
    ∃ (sh: gmap loc (prodO tagO (gmapO string (laterO (sem_typeO Σ))))),
    own γ (gmap_view_auth (DfracOwn 1) sh) ∗ ⌜dom (gset loc) sh = dom _ h⌝ ∗
    □ ∀ (ℓ : loc) (t : tag) (vs : stringmap value),
    ⌜h !! ℓ = Some (t, vs)⌝ -∗
    ∃ (iFs : gmapO string (laterO (sem_typeO Σ))),
    sh !! ℓ ≡ Some (t, iFs) ∗ heap_models_fields iFs vs.

  Lemma expr_adequacy (σi:interp_env) e lty le ty val :
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _ : string, wf_cdef_mono) Δ →
    wf_lty lty →
    expr_eval le e = Some val →
    expr_has_ty lty e ty →
    interp_local_tys σi lty le -∗
    interp_type ty σi val.
  Proof.
    move => ????? he h; move: le val he.
    elim: h => [z | b | | op e1 e2 hop he1 hi1 he2 hi2 |
        op e1 e2 hop he1 hi1 he2 hi2 |
        v vty hv | | exp S T hS hi hwf hsub ] => le val he; iIntros "#Hlty".
    - inv he; rewrite interp_type_unfold /=; by eauto.
    - inv he; rewrite interp_type_unfold /=; by eauto.
    - inv he; rewrite interp_type_unfold /=; by eauto.
    - inv he.
      case heq1 : (expr_eval le e1) => [v1 | ]; rewrite heq1 in H0; last by done.
      apply hi1 in heq1.
      iDestruct (heq1 with "Hlty") as "hv1".
      rewrite interp_type_unfold /=.
      iDestruct "hv1" as (z1) "%hz1".
      rewrite hz1 in H0.
      case heq2 : (expr_eval le e2) => [v2 | ]; rewrite heq2 in H0; last by done.
      apply hi2 in heq2.
      iDestruct (heq2 with "Hlty") as "hv2".
      rewrite interp_type_unfold /=.
      iDestruct "hv2" as (z2) "%hz2".
      rewrite hz2 in H0.
      case: H0 => <-.
      rewrite interp_type_unfold /= /interp_int.
      move: hop; rewrite /is_bool_op; destruct op => //= _; by iExists _.
    - inv he.
      case heq1 : (expr_eval le e1) => [v1 | ]; rewrite heq1 in H0; last by done.
      apply hi1 in heq1.
      iDestruct (heq1 with "Hlty") as "hv1".
      rewrite interp_type_unfold /=.
      iDestruct "hv1" as (z1) "%hz1".
      rewrite hz1 in H0.
      case heq2 : (expr_eval le e2) => [v2 | ]; rewrite heq2 in H0; last by done.
      apply hi2 in heq2.
      iDestruct (heq2 with "Hlty") as "hv2".
      rewrite interp_type_unfold /=.
      iDestruct "hv2" as (z2) "%hz2".
      rewrite hz2 in H0.
      case: H0 => <-.
      rewrite interp_type_unfold /= /interp_bool.
      move: hop; rewrite /is_bool_op; destruct op => //= _; by iExists _.
    - inv he.
      iDestruct "Hlty" as "[? Hlty]".
      iDestruct ("Hlty" with "[//]") as (?) "[% H]".
      rewrite H0 in H; by case: H => ->.
    - inv he.
      iDestruct "Hlty" as "[Hthis ?]".
      by rewrite /this_type interp_class_unfold.
    - apply hi in he.
      iApply subtype_is_inclusion => //.
      + by apply expr_has_ty_wf in hS.
      + by iApply he.
  Qed.

  Lemma interp_local_tys_update σi v lty le ty val :
    interp_local_tys σi lty le -∗
    interp_type ty σi val -∗
    interp_local_tys σi (<[v:=ty]>lty) (<[v:=val]>le).
  Proof.
    iIntros "#[Hthis Hi] #?".
    iSplit; first done.
    iIntros (v' ty') "H".
    rewrite lookup_insert_Some.
    iDestruct "H" as %[[<- <-]|[??]].
    - iExists _. rewrite lookup_insert. by iSplit.
    - rewrite lookup_insert_ne; last done. by iApply "Hi".
  Qed.

  Lemma interp_local_tys_list (σi:interp_env) lty le targs args vargs l t σ:
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _ : string, wf_cdef_mono) Δ →
    wf_lty lty →
    dom stringset targs = dom stringset args →
    map_args (expr_eval le) args = Some vargs →
    (∀ (x : string) (ty : lang_ty) (arg : expr),
    targs !! x = Some ty →
    args !! x = Some arg →
    expr_has_ty lty arg ty) →
    interp_type (ClassT t σ) σi (LocV l) -∗
    interp_local_tys σi lty le -∗
    interp_local_tys σi {| type_of_this := (t, σ); ctxt := targs |}
                        {| vthis := l; lenv := vargs |}.
  Proof.
    move => ????? hdom hargs helt.
    iIntros "#Hl #[Hthis Hle]".
    iSplit; first by rewrite interp_class_unfold.
    iIntros (v ty) "%hin".
    assert (ha: ∃ arg, args !! v = Some arg).
    { apply elem_of_dom.
      rewrite -hdom.
      apply elem_of_dom.
      now rewrite hin.
    }
    destruct ha as [arg harg].
    apply helt with v ty arg in hin; last done.
    assert (hv: ∃ varg, vargs !! v = Some varg).
    { apply elem_of_dom.
      apply dom_map_args in hargs.
      rewrite hargs.
      apply elem_of_dom.
      now rewrite harg.
    }
    destruct hv as [varg hvarg].
    iExists varg; rewrite hvarg; iSplitR; first done.
    rewrite (map_args_lookup _ _ _ args vargs hargs v) harg /= in hvarg.
    iApply expr_adequacy => //.
    by iSplit.
  Qed.

  Lemma heap_models_update h l rt vs (σi: interp_env) t σt f fty v:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
    map_Forall (λ _ : string, wf_cdef_fields_wf) Δ →
    (* Note: overkill, contra is enough for fields in this proof *)
    map_Forall (λ _cname, wf_field_mono) Δ →
    map_Forall (λ _ : string, wf_cdef_mono) Δ →
    h !! l = Some (rt, vs) →
    has_field f t fty →
    wf_ty (ClassT t σt) →
    interp_type (ClassT t σt) σi (LocV l) -∗
    interp_type (subst_ty σt fty) σi v -∗
    heap_models h -∗
    heap_models (<[l:=(rt, <[f:=v]> vs)]> h).
  Proof.
    move => ?? hfb ??? hheap hfield hwf.
    iIntros "#hrecv #hv hmodels".
    iDestruct "hmodels" as (sh) "[hown [%hdom #h]]".
    iExists sh.
    rewrite interp_class_unfold.
    iDestruct "hrecv" as (l' t' def σ' σt' fields ifields) "[%H [hsem hl]]".
    iDestruct "hsem" as "[%hdomf #hifields]".
    destruct H as [[= <-] [ hinherits' [hwfσ' [hdef [hσ' hfields]]]]].
    iDestruct (sem_heap_own_valid_2 with "hown hl") as "#Hv".
    iSplitL; first by iFrame.
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
    assert (hfield2 : has_field f rt (subst_ty σ' fty)) by (by eapply has_field_inherits_using).
    iSpecialize ("hifields" $! f (subst_ty σ' fty) hfield2).
    iAssert (⌜is_Some (iFs !! f)⌝)%I as "%hsome".
    { iRewrite -"hifs".
      by iRewrite "hifields".
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
    iRewrite "hifields" in "hf'".
    rewrite !option_equivI later_equivI discrete_fun_equivI.
    iNext.
    iSpecialize ("hf'" $! v).
    iRewrite -"hf'".
    rewrite subst_ty_subst; last first.
    { apply has_field_bounded in hfield => //.
      destruct hfield as (def' & hdef' & hfty).
      apply inherits_using_wf in hinherits' => //.
      destruct hinherits' as (? & ? & ? & ? & _ & hL & _).
      simplify_eq.
      by rewrite hL.
    }
    assert (hsub : subst_ty σt fty <: subst_ty (subst_ty σt' <$> σ') fty).
    { clear hdom hdomf hdomv.
      assert (hfwf := hfield).
      apply has_field_wf in hfwf => //.
      apply has_field_mono in hfield => //.
      destruct hfield as (tdef & ? & [_ hcontra]); simplify_eq.
      apply subtype_lift with (neg_variance <$> generics tdef) => //.
      - by apply wf_ty_class_inv in hwf.
      - apply wf_ty_subst_map.
        + by apply wf_ty_class_inv in hwfσ'.
        + apply inherits_using_wf in hinherits' => //.
          by repeat destruct hinherits' as [? hinherits'].
      - by apply neg_subtype_targs.

    }
    iApply subtype_is_inclusion => //.
    apply has_field_wf in hfield => //.
    apply wf_ty_subst => //.
    by apply wf_ty_class_inv in hwf.
  Qed.

  Lemma cmd_adequacy_ lty cmd lty' :
    wf_cdefs Δ →
    wf_lty lty →
    ⌜cmd_has_ty lty cmd lty'⌝ -∗
    ∀ (σi: interp_env) st st' n, ⌜cmd_eval st cmd st' n⌝ -∗
    heap_models st.2 ∗ interp_local_tys σi lty st.1 -∗ |=▷^n
        heap_models st'.2 ∗ interp_local_tys σi lty' st'.1.
  Proof.
    move => wfΔ wflty.
    iLöb as "IH" forall (lty cmd lty' wflty).
    iIntros "%hty" (σi st st' n) "%hc".
    iInduction hty as [ lty | lty1 lty2 lty3 fstc sndc hfst hi1 hsnd hi2 |
        lty lhs e ty he | lty1 lty2 cond thn els hcond hthn hi1 hels hi2 |
        lty lhs recv t targs name fty hrecv hf |
        lty recv fld rhs fty t σ hrecv hrhs hf |
        lty lhs t targs args fields hwf hf hdom harg |
        lty lhs recv t targs name orig mdef args hrecv hhasm hdom hi |
        lty c rty' rty hsub h hi |
        lty rty v tv t cmd hv hr h hi
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
      iDestruct (expr_adequacy with "Hle") as "#?" => //; try (by apply wfΔ).
      by iApply interp_local_tys_update.
    - (* IfC *) inv hc
      + iIntros "H". by iApply "IHty".
      + iIntros "H". by iApply "IHty1".
    - (* GetC *) inv hc.
      iClear "IH".
      iIntros "[Hh #Hle]".
      iModIntro. (* keep the later *)
      iDestruct (expr_adequacy with "Hle") as "#He" => //; try (by apply wfΔ).
      rewrite interp_class_unfold /=.
      iDestruct "He" as (???????) "[%H [#Hifields H◯]]".
      destruct H as [[= <-] [hinherits [hwfσt [hdef [htargs hfields]]]]].
      iAssert (⌜t0 = t1⌝ ∗ heap_models h ∗ ▷ interp_type (subst_ty (subst_ty σt <$> σ)  fty) σi v)%I with "[Hh]" as "[%Ht [Hh Hv]]".
      { iDestruct "Hh" as (sh) "(H● & %hdom & #Hh)".
        iDestruct (sem_heap_own_valid_2 with "H● H◯") as "#HΦ".
        iDestruct ("Hh" with "[//]") as (iFs) "[H H▷]".
        iRewrite "H" in "HΦ".
        rewrite option_equivI prod_equivI /=.
        iDestruct "HΦ" as "[%Ht HΦ]".
        fold_leibniz; subst.
        iSplitR; first done.
        iSplitL. { iExists _. iFrame. by iSplit. }
        iAssert (interp_fields σi t (subst_ty σt <$> σ) fields ifields interp_type) with "[Hifields]" as "Hifields_t".
        { destruct wfΔ.
          by iApply interp_fields_inclusion.
        }
        rewrite /interp_fields.
        iDestruct "Hifields_t" as "[%hdiom Hifields_t]".
        iSpecialize ("Hifields_t" $! name fty hf).
        iDestruct "H▷" as "[%hdf h]".
        iRewrite -"HΦ" in "Hifields_t".
        iSpecialize ("h" $! name _ with "[Hifields_t]"); first done.
        iDestruct "h" as (w) "[%hw hiw]".
        iNext.
        by simplify_eq.
      }
      subst.
      destruct wfΔ.
      assert (hsub: subst_ty (subst_ty σt <$> σ) fty <: subst_ty targs fty).
      {
        assert (hfwf := hf).
        apply has_field_wf in hfwf => //.
        apply has_field_mono in hf => //.
        destruct hf as (tdef & ? & [hcov _]); simplify_eq.
        apply subtype_lift with (generics tdef) => //.
        - apply wf_ty_subst_map; first by apply wf_ty_class_inv in hwfσt.
          apply inherits_using_wf in hinherits => //.
          by repeat destruct hinherits as [? hinherits].
        - apply expr_has_ty_wf in hrecv => //.
          by apply wf_ty_class_inv in hrecv.
      }
      iNext.
      iFrame.
      iApply interp_local_tys_update => //.
      iApply subtype_is_inclusion => //.
      apply wf_ty_subst.
      * apply wf_ty_subst_map; first by apply wf_ty_class_inv in hwfσt.
        apply inherits_using_wf in hinherits => //.
        by repeat destruct hinherits as [? hinherits].
      * by apply has_field_wf in hf.
    - (* SetC *) inv hc.
      assert (wfΔ' := wfΔ).
      destruct wfΔ'.
      iClear "IH".
      iIntros "[Hh #Hle]" => /=.
      iSplitL; last done.
      assert (ht: wf_ty (ClassT t σ)) by (by apply expr_has_ty_wf in hrecv).
      iApply heap_models_update => //.
      + iApply expr_adequacy => //; by apply wfΔ.
      + iApply expr_adequacy => //; by apply wfΔ.
    - (* NewC *) inv hc.
      iIntros "[Hh #Hle]"; simpl.
      (* we need one modality to semantic heap *)
      iDestruct "Hh" as (sh) "(H● & %Hdom & #Hh)".
      assert (hnew: sh !! new = None).
      { apply (not_elem_of_dom (D:=gset loc)).
        by rewrite Hdom not_elem_of_dom.
      }
      set (iFs :=
         (λ(ty: lang_ty), Next (interp_car (interp_type ty σi))) <$> (subst_ty targs <$> fields)
      ).
      iMod ((sem_heap_own_update new) with "H●") as "[H● #H◯]" => //;
        first by apply (sem_heap_view_alloc _ new t iFs).
      iIntros "!> !>". (* kill the modalities *)
      iAssert (interp_type (ClassT t targs) σi (LocV new)) with "[]" as "#Hl".
      {
        iAssert (interp_fields σi t targs fields iFs interp_type) as "HiFs".
        { rewrite /interp_fields; iSplit; first by rewrite /iFs !dom_fmap_L.
          iIntros (f fty) "%hfty".
          apply hf in hfty.
          rewrite /iFs !lookup_fmap.
          by rewrite hfty /=.
        }
        rewrite interp_type_unfold /=.
        assert (hwf' := hwf).
        inv hwf'.
        iExists new, t, def, (gen_targs (length def.(generics))), targs, fields, iFs.
        iSplit; last by (repeat iSplit => //).
        iPureIntro.
        repeat split => //.
        + by econstructor.
        + rewrite subst_ty_gen_targs => //.
          by apply subtype_targs_refl.
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
        apply dom_map_args in H6.
        by rewrite /iFs !dom_fmap_L H6 -hdom.
      }
      iIntros (f iF) "hiF".
      iAssert (⌜f ∈ dom stringset fields⌝)%I as "%hfield".
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
        apply dom_map_args in H6.
        by rewrite H6 -hdom.
      }
      destruct h1 as [v0 hv0].
      assert (h2: is_Some (fields !! f)) by (by apply elem_of_dom).
      destruct h2 as [fty hty].
      iExists v0; iSplitR; first done.
      rewrite /interp_fields lookup_fmap.
      assert (heval0: expr_eval le a0 = Some v0).
      { rewrite (map_args_lookup _ _ _ args vargs H6 f) in hv0.
        by rewrite ha0 in hv0.
      }
      assert (hty0: expr_has_ty lty a0 (subst_ty targs fty)) by (by apply harg with f).
      rewrite !lookup_fmap hty /=  option_equivI later_equivI.
      iNext.
      rewrite discrete_fun_equivI.
      iSpecialize ("hiF" $! v0).
      iRewrite -"hiF".
      iDestruct (expr_adequacy _ a0 with "Hle") as "#Ha0" => //; by apply wfΔ.
    - (* CallC *) inv hc; simpl.
      destruct wfΔ.
      (* Get inherits relation between dynamic tag and static tag *)
      iIntros "[Hh #Hle]".
      (* make the script more resilient. Should provide a proper inversion
       * lemma but this is the next best thing.
       *)
      rename H3 into heval_recv.
      rename H4 into hmap.
      rename H5 into hheap.
      rename H7 into hhasm0.
      rename H11 into heval_body.
      rename H12 into heval_ret.
      iDestruct (expr_adequacy _ recv with "Hle") as "#Hrecv" => //.
      rewrite interp_class_unfold /=.
      iDestruct "Hrecv" as (? t1 def σin σt fields ifields) "[%Hpure [hifields Hl]]".
      destruct Hpure as [[= <-] [hin_t1_t [hwf_t1_σt [hdef [htargs hfields]]]]].
      iDestruct "Hh" as (sh) "(H● & %Hdom & #Hh)".
      iDestruct (sem_heap_own_valid_2 with "H● Hl") as "#HΦ".
      iDestruct ("Hh" with "[//]") as (?) "[H H▷]".
      iRewrite "H" in "HΦ".
      rewrite option_equivI prod_equivI /=.
      iDestruct "HΦ" as "[%Ht HΦ]".
      fold_leibniz; subst.
      (* both static and dynamic classes actually exists in Δ *)
      assert (ht1: is_Some (Δ !! t1)).
      { apply has_method_from_def in hhasm0 as (? & ? & ? & ? & _ & [? [hin ?]]) => //.
        by apply inherits_using_wf in hin as (? & ? & ht1 & _).
      }
      destruct ht1 as [ def1 hdef1 ].
      (* Get method inclusion information between mdef0 and mdef *)
      destruct (has_method_ordered _ _ _ _ _ _ _ _
        wf_extends_wf wf_override wf_parent wf_methods_bounded
        hin_t1_t hhasm0 hhasm)
      as (σoin & σot1 & σot & odef0 & odef & omdef0 & omdef &
         hσeq & hodef0 & hodef & homdef0 & homdef & hin_o_o0 & hin_t1_o0 & hin_t_o &
         -> & -> & hincl0 & hincl1).
      (* Get location of the definition of the dynamic method mdef0 *)
      destruct (has_method_from_def _ _ _ _  wf_parent wf_methods_bounded hhasm0) as
        (odef0' & mdef0_orig & hodef0' & hmdef0_orig & hhasm_morig0 & [σ0 [hin_t1_o0' heqmdef]]).
      rewrite hodef0 in hodef0'; injection hodef0'; intros <-; clear hodef0'.
      rewrite homdef0 in hmdef0_orig; injection hmdef0_orig; intros <-; clear hmdef0_orig.
      replace σot1 with σ0 in *; last by eapply inherits_using_fun.
      clear σot1 hin_t1_o0' heqmdef.
      rewrite subst_mdef_body in heval_body.
      rewrite subst_mdef_ret in heval_ret.
      assert (wf0: wf_ty (ClassT orig0 σ0)).
      { apply inherits_using_wf in hin_t1_o0 => //.
        destruct hin_t1_o0 as (? & ? & ? & ? & hF & hL & hwf); simplify_eq.
        by eapply wf_ty_class.
      }
      assert (hwf_targs: Forall wf_ty targs).
      { apply expr_has_ty_wf in hrecv => //.
        by apply wf_ty_class_inv in hrecv.
      }
      assert (hwf_σin: Forall wf_ty σin).
      { apply inherits_using_wf in hin_t1_t => //.
        by repeat destruct hin_t1_t as [? hin_t1_t].
      }
      assert (hwf_σt: Forall wf_ty σt) by (by apply wf_ty_class_inv in hwf_t1_σt).
      assert (hwf_σt_σin: Forall wf_ty (subst_ty σt <$> σin)) by (by apply wf_ty_subst_map).
      assert (hb_σin_σot : Forall (bounded (length σin)) σot).
      { apply inherits_using_wf in hin_t1_t => //.
        destruct hin_t1_t as (? & ? & ? & ? & hF & hL & hwf).
        apply inherits_using_wf in hin_t_o => //.
        destruct hin_t_o as (? & ? & ? & ? & hF' & hL' & hwf').
        simplify_eq.
        by rewrite hL.
      }
      assert (hb_ret0: bounded (length σ0) (methodrettype omdef0)).
      { assert (h0 := hodef0).
        apply wf_methods_bounded in h0.
        apply h0 in homdef0.
        destruct homdef0 as [_ hret].
        apply inherits_using_wf in hin_t1_o0 => //.
        destruct hin_t1_o0 as (? & ? & ? & ? & ? & hL &?); simplify_eq.
        by rewrite hL.
      }
      (* Get typing information about mdef0 *)
      assert (mdef0_wt:
        ∃ rty, wf_lty rty ∧
        cmd_has_ty (subst_lty σt {| type_of_this := (orig0, σ0);
                                 ctxt := subst_ty σ0 <$> methodargs omdef0 |})
                   (methodbody omdef0) rty ∧
        expr_has_ty rty (methodret omdef0) (subst_ty σt (subst_ty σ0 (methodrettype omdef0)))).
      { assert (h0 := hodef0).
        assert (h1 := homdef0).
        apply wf_mdefs in h0.
        apply h0 in h1 as [rty [wfryt [hbody0 hret0]]].
        apply inherits_using_wf in hin_t1_o0 => //.
        destruct hin_t1_o0 as (? & ? & ? & ? & hF & hL & hwf); simplify_eq.
        exists (subst_lty σt (subst_lty σ0 rty)); split; last split.
        - apply subst_wf_lty => //.
          by apply subst_wf_lty.
        - apply cmd_has_ty_subst => //.
          { split => /=; first by rewrite /this_type.
            rewrite map_Forall_lookup => k tk.
            rewrite lookup_fmap_Some.
            case => ty [<- hk].
            apply wf_ty_subst => //.
            assert (h2 := hodef0).
            assert (h1 := homdef0).
            apply wf_methods_wf in h2.
            apply h2 in h1.
            by apply h1 in hk.
          } 
          replace 
            {| type_of_this := (orig0, σ0); ctxt := subst_ty σ0 <$> methodargs omdef0 |}
          with
           (subst_lty σ0
             {| type_of_this := (orig0, gen_targs (length (generics odef0)));
               ctxt := subst_ty (gen_targs (length (generics odef0))) <$> methodargs omdef0
             |}); last first.
          { rewrite /subst_lty subst_ty_gen_targs //= fmap_subst_tys_id //.
            assert (h2 := hodef0).
            assert (h1 := homdef0).
            apply wf_methods_bounded in h2.
            apply h2 in h1.
            by apply h1.
          }
          apply cmd_has_ty_subst => //.
          split => /=.
          { rewrite /this_type /=.
            econstructor => //.
            - by rewrite length_gen_targs.
            - by apply gen_targs_wf.
          }
          rewrite map_Forall_lookup => k tk.
          rewrite lookup_fmap_Some.
          case => ty [<- hk].
          rewrite subst_ty_id //.
          + assert (h2 := hodef0).
            assert (h1 := homdef0).
            apply wf_methods_wf in h2.
            apply h2 in h1.
            by apply h1 in hk.
          + assert (h2 := hodef0).
            assert (h1 := homdef0).
            apply wf_methods_bounded in h2.
            apply h2 in h1.
            by apply h1 in hk.
        - apply expr_has_ty_subst => //.
          rewrite subst_ty_id // in hret0 => //; last by rewrite -hL.
          by apply expr_has_ty_subst => //.
      }
      destruct mdef0_wt as (rty & wfrty & hbody & hret).
      assert (wfbody:
        wf_lty (subst_lty σt {| type_of_this := (orig0, σ0); ctxt := subst_ty σ0 <$> methodargs omdef0 |})
      ).
      { split => /=.
        - rewrite /this_type /=.
          eapply wf_ty_class => //.
          + apply inherits_using_wf in hin_t1_o0 => //.
            destruct hin_t1_o0 as (? & ? & ? & ? & hF & hL & hwf); simplify_eq.
            by rewrite map_length hL.
          + apply wf_ty_subst_map => //.
            apply inherits_using_wf in hin_t1_o0 => //.
            by repeat destruct hin_t1_o0 as [? hin_t1_o0].
        - rewrite map_Forall_lookup => k tk.
          rewrite lookup_fmap_Some.
          case => ty [<- ].
          rewrite lookup_fmap_Some.
          case => ty' [<- hk].
          apply wf_ty_subst => //.
          apply wf_ty_subst; first by (by apply wf_ty_class_inv in wf0).
          assert (h2 := hodef0).
          assert (h1 := homdef0).
          apply wf_methods_wf in h2.
          apply h2 in h1.
          by apply h1 in hk.
      }
      iModIntro; iNext.
      iSpecialize ("IH" $! _ _ _ wfbody hbody σi _ _ _ heval_body); simpl.
      iDestruct ("IH" with "[Hh Hle H●]") as "Hstep".
      { iSplit.
        - iExists _; iFrame.
          iSplit; last done.
          by rewrite Hdom.
        - iApply (interp_local_tys_list _ lty le) => //.
          + destruct hincl0 as [hdomincl _].
            rewrite !dom_fmap_L in hdomincl.
            rewrite !dom_fmap_L in hdom.
            by rewrite !dom_fmap_L hdomincl hdom.
          + move => x ty arg.
            rewrite lookup_fmap_Some /=.
            case => [tx [<- ]].
            rewrite lookup_fmap_Some.
            case => [tx' [<- hx]] harg.
            destruct hincl1 as [hdom1 [hincl1 _]].
            destruct (methodargs omdef !! x) as [ty' | ] eqn:hty'.
            { assert (bounded (length σot) ty').
              { assert (ho := hodef).
                apply wf_methods_bounded in ho.
                apply ho in homdef.
                apply homdef in hty'.
                apply inherits_using_wf in hin_t_o => //.
                destruct hin_t_o as ( ? & ? & ? & ? & _ & hL & _); simplify_eq.
                by rewrite hL.
              }
              eapply ESubTy.
              - apply hi with x => //.
                by rewrite /subst_mdef /= lookup_fmap hty'.
              - apply wf_ty_subst => //.
                apply wf_ty_subst; first by (by apply wf_ty_class_inv in wf0).
                apply has_method_wf in hhasm_morig0 as [hargs _] => //.
                by apply hargs in hx.
              - (* step by step, using variance info *)
                assert (hsub: subst_ty targs (subst_ty σot ty') <: subst_ty (subst_ty σt <$> σin) (subst_ty σot ty')).
                { apply subtype_lift with (neg_variance <$> generics def) => //.
                  - assert (hmono := hodef).
                    apply wf_methods_mono in hmono.
                    assert (ho := homdef).
                    apply hmono in ho as [hmonoa _].
                    assert (ha := hty').
                    apply hmonoa in ha.
                    apply mono_subst with (neg_variance <$> generics odef) => //.
                    + rewrite map_length.
                      apply wf_methods_bounded in hodef.
                      apply hodef in homdef.
                      by apply homdef in hty'.
                    + rewrite map_length.
                      apply inherits_using_wf in hin_t_o => //.
                      repeat destruct hin_t_o as [? hin_t_o]; by simplify_eq.
                    + rewrite neg_variance_fmap_idem => i vi ti hvi.
                      apply list_lookup_fmap_inv in hvi.
                      destruct hvi as [wi [-> hwi]].
                      move => hti hc.
                      apply inherits_using_mono with (def0 := def) in hin_t_o => //.
                      inv hin_t_o; simplify_eq.
                      destruct wi; by eauto.
                    + move => i vi ti hvi.
                      apply list_lookup_fmap_inv in hvi.
                      destruct hvi as [wi [-> hwi]].
                      move => hti hc.
                      apply inherits_using_mono with (def0 := def) in hin_t_o => //.
                      inv hin_t_o; simplify_eq.
                      destruct wi; by eauto.
                  - apply wf_ty_subst => //.
                    * apply inherits_using_wf in hin_t_o => //.
                      by repeat destruct hin_t_o as [? hin_t_o].
                    * apply wf_methods_wf in hodef.
                      apply hodef in homdef.
                      by apply homdef in hty'.
                  - by apply neg_subtype_targs.
                }
                eapply SubTrans; first by exact hsub.
                rewrite -subst_ty_subst; last first.
                { by apply bounded_subst with (length σot). }
                apply subtype_subst => //.
                eapply hincl1 with x.
                * by rewrite /subst_mdef /= lookup_fmap hx /=.
                * by rewrite /subst_mdef /= !lookup_fmap hty' /=.
            }
            rewrite /subst_mdef /= !dom_fmap_L in hdom1.
            apply mk_is_Some in hx.
            apply elem_of_dom in hx.
            rewrite hdom1 in hx.
            apply elem_of_dom in hx.
            rewrite hty' in hx.
            by elim hx.
          + rewrite interp_class_unfold /=.
            iExists l, t1, odef0, σ0, σt, fields, ifields; iSplitR.
            { iPureIntro; repeat split => //.
              apply subtype_targs_refl.
              apply inherits_using_wf in hin_t1_o0 => //.
              destruct hin_t1_o0 as ( ? & ? & ? & ? & _ & hL & _); simplify_eq.
              by rewrite map_length hL.
            }
            by iSplit.
      }
      iRevert "Hstep".
      iApply updN_mono_I.
      iIntros "[Hmodels Hle2]"; iFrame.
      iApply interp_local_tys_update; first by done.
      destruct hincl1 as [? [? hret1]].
      assert (hsub: subst_ty (subst_ty σt <$> σ0) (methodrettype omdef0) <:
                    subst_ty targs (subst_ty σot (methodrettype omdef))).
      { eapply SubTrans; last first.
        - apply subtype_lift with (σ1 := subst_ty σt <$> σin) (vs0 := generics def) => //.
          + assert (hmono := hodef).
            apply wf_methods_mono in hmono.
            assert (hm := homdef).
            apply hmono in hm as [_ hmonoret].
            apply mono_subst with (generics odef) => //.
            * apply wf_methods_bounded in hodef.
              apply hodef in homdef.
              by apply homdef.
            * apply inherits_using_wf in hin_t_o => //.
              repeat destruct hin_t_o as [? hin_t_o]; by simplify_eq.
            * move => i vi ti hvi hti hc.
              apply inherits_using_mono with (def0 := def) in hin_t_o => //.
              inv hin_t_o; simplify_eq.
              by eauto.
            * move => i vi ti hvi hti hc.
              apply inherits_using_mono with (def0 := def) in hin_t_o => //.
              inv hin_t_o; simplify_eq.
              by eauto.
          + apply wf_ty_subst => //.
            * apply inherits_using_wf in hin_t_o => //.
              by repeat destruct hin_t_o as [? hin_t_o].
            * apply wf_methods_wf in hodef.
              apply hodef in homdef.
              by apply homdef.
        - rewrite -!subst_ty_subst //; first by apply subtype_subst.
          apply bounded_subst with (length σot) => //.
          apply inherits_using_wf in hin_t_o => //.
          destruct hin_t_o as (? & ? & ? & ? & ? & hL & _).
          simplify_eq.
          assert (ho := hodef).
          apply wf_methods_bounded in ho.
          apply ho in homdef.
          rewrite hL.
          by apply homdef.
      }
      iDestruct (expr_adequacy _ (methodret omdef0) with "Hle2") as "#Hret" => //.
      iApply subtype_is_inclusion => //.
      + apply wf_ty_subst.
       * apply wf_ty_subst_map => //.
         by apply wf_ty_class_inv in wf0.
       * apply wf_methods_wf in hodef0.
         apply hodef0 in homdef0.
         by apply homdef0.
      + by rewrite -subst_ty_subst.
    - (* Subtyping *) 
      destruct wfΔ.
      iIntros "H".
      iSpecialize ("IHty" $! wflty with "[//] H").
      iApply updN_mono_I; last done.
      iIntros "[Hh #Hrty]". iFrame.
      iDestruct (interp_local_tys_is_inclusion with "Hrty") as "Hrty'" => //.
      + by apply cmd_has_ty_wf in h.
      + rewrite Forall_forall => i hi v.
        by apply _.
    - (* CondTagC *) inv hc; last first.
      { iIntros "[Hh H]".
        iAssert (heap_models st'.2 ∗ interp_local_tys σi rty st'.1)%I with "[Hh H]" as "H".
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
      clear H6 h.
      destruct H5 as (l & hl & t' & fields & hlt & hinherits).
      iDestruct "H" as "[H #Hle]".
      iDestruct "Hle" as "[Hthis Hle]".
      iDestruct ("Hle" $! v with "[//]") as (?) "[%Hlev Hv]".
      rewrite Hlev in hl; simplify_eq.
      iAssert (interp_type MixedT σi (LocV l)) as "Hmixed".
      { destruct wfΔ.
        assert (hsub : tv <: MixedT) by apply SubMixed.
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
      iDestruct "Hl" as (exTag exσ) "[wfex Hl]".
      iDestruct "Hl" as (k rt def σ σt exfields ifields) "[%H [#Hfields #Hl]]".
      destruct H as [[= <-] [hinherits' [hwf' [hdef [ heq' hfields']]]]].
      iAssert (⌜t' = rt⌝ ∗ heap_models st.2 ∗ interp_type (ExT rt) σi (LocV l))%I with "[H]" as "[%heq [Hh #Hv2]]".
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
        assert (hrt: is_Some(Δ !! rt)).
        { inv hwf'.
          by rewrite H1.
        }
        destruct hrt as [rdef hrt].
        iExists σt.
        iSplitR.
        { iPureIntro.
          by apply wf_ty_class_inv in hwf'.
        }
        iExists l, rt, rdef, (gen_targs (length rdef.(generics))), σt, exfields, ifields.
        iSplit.
        + iPureIntro; repeat split => //.
          * by constructor.
          * inv hwf'; simplify_eq.
            rewrite subst_ty_gen_targs //.
            by apply subtype_targs_refl.
        + by iSplit.
      }
      subst.
      iFrame.
      iSplit => /=; first done.
      iIntros (w tw).
      rewrite lookup_insert_Some.
      iIntros "%Hw".
      destruct Hw as [[<- <-] | [hne hw]].
      { iExists (LocV l); rewrite Hlev; iSplitR; first done.
        rewrite interp_inter_unfold /=; iSplit; first done.
        destruct wfΔ.
        by iApply inherits_is_ex_inclusion.
      }
      by iApply "Hle".
  Qed.

  Lemma cmd_adequacy (env: interp_env) lty cmd lty' :
    wf_cdefs Δ →
    wf_lty lty →
    cmd_has_ty lty cmd lty' →
    ∀ st st' n, cmd_eval st cmd st' n →
    heap_models st.2 ∗ interp_local_tys env lty st.1 -∗ |=▷^n
        heap_models st'.2 ∗ interp_local_tys env lty' st'.1.
  Proof.
    move => ?? hty ??? hc.
    by iApply cmd_adequacy_.
  Qed.

End proofs.

Print Assumptions cmd_adequacy.

Definition empty_lty tag := {|
  type_of_this := (tag, []);
  ctxt := ∅
|}.

Definition empty_le l := {|
  vthis := l;
  lenv := ∅;
|}.

Definition empty_cdef tag := {|
  classname := tag;
  generics := [];
  superclass := None;
  classfields := ∅;
  classmethods := ∅;
|}.

Definition init_heap l tag : heap := {[l := (tag, ∅)]}.

(* Critical lemma to generate the initial iris state and boot strap
 * all the reasoning.
 * We suppose the existence of an empty class, with a single allocated
 * value of this type.
 *)
Lemma sem_heap_init
  `{PDC: ProgDefContext}
  `{!sem_heapGpreS Σ}:
  ∀ MainTag l, Δ !! MainTag = Some (empty_cdef MainTag) →
  ⊢@{iPropI Σ} |==> ∃ _: sem_heapGS Σ, (heap_models (init_heap l MainTag) ∗ interp_local_tys [] (empty_lty MainTag) (empty_le l)).
Proof.
  move => MainTag l hΔ.
  set (empty := ∅ : gmap loc (prodO tagO (gmapO string (laterO (sem_typeO Σ))))).
  assert (hl : empty !! l = None) by (by rewrite /empty lookup_empty).
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) empty)) as (γI) "HI";
    first by apply gmap_view_auth_valid.
  iMod (own_update with "HI") as "[? ?]";
    first by apply (gmap_view_alloc _ l DfracDiscarded (MainTag, ∅)).
  iExists (SemHeapGS _ _ γI).
  iModIntro; iSplit.
  - iExists _. 
    iSplit; first done.
    iSplit; first by (iPureIntro; by set_solver).
    iModIntro; iIntros (k t vs) "%H".
    rewrite /init_heap lookup_singleton_Some in H.
    destruct H as [<- [= <- <-]].
    iExists ∅; iSplit.
    + by rewrite lookup_insert.
    + iSplit; first done.
      iIntros (v t); rewrite !lookup_empty option_equivI.
      by iIntros "?".
  - rewrite /empty_lty /empty_le; iSplit => /=.
    + iExists l, MainTag, (empty_cdef MainTag), (gen_targs (length (empty_cdef MainTag).(generics))), [] , ∅, ∅; iSplitR.
      { iPureIntro.
        split => //.
        split; first by eapply InheritsRefl.
        split; first by econstructor.
        split => //.
        split => //.
        rewrite /empty_cdef in hΔ.
        move => f fty; split; last by rewrite lookup_empty.
        move => h.
        inv h.
        - by rewrite hΔ in H; injection H; intros; subst.
        - by rewrite hΔ in H; injection H; intros; subst.
      }
      iSplit.
      * iSplit.
        { iPureIntro. 
          by rewrite !dom_empty_L.
        }
        iIntros (f ty hf).
        rewrite /empty_cdef in hΔ.
        inv hf.
        { by rewrite hΔ in H; injection H; intros; subst. }
        { by rewrite hΔ in H; injection H; intros; subst. }
      * by rewrite mapsto_eq /mapsto_def /loc_mapsto_def.
    + iIntros (v t H).
      by rewrite !lookup_empty in H.
Qed.
