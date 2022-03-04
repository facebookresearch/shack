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
    map_Forall (λ _, wf_ty) lty →
    expr_eval le e = Some val →
    expr_has_ty lty e ty →
    interp_local_tys σi lty le -∗
    interp_type ty σi val.
  Proof.
    move => ????? he h; move: le val he.
    elim: h => [z | b | | op e1 e2 hop he1 hi1 he2 hi2 |
        op e1 e2 hop he1 hi1 he2 hi2 |
        v vty hv | exp S T hS hi hwf hsub ] => le val he; iIntros "#Hlty".
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
      iDestruct ("Hlty" with "[//]") as (?) "[% H]".
      rewrite H0 in H; by case: H => ->.
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
    iIntros "#Hi #?". iIntros (v' ty') "H".
    rewrite lookup_insert_Some.
    iDestruct "H" as %[[<- <-]|[??]].
    - iExists _. rewrite lookup_insert. by iSplit.
    - rewrite lookup_insert_ne; last done. by iApply "Hi".
  Qed.

  Lemma interp_local_tys_list (σi:interp_env) lty le targs args vargs:
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _ : string, wf_cdef_mono) Δ →
    map_Forall (λ _, wf_ty) lty →
    dom stringset targs = dom stringset args →
    map_args (expr_eval le) args = Some vargs →
    (∀ (x : string) (ty : lang_ty) (arg : expr),
    targs !! x = Some ty →
    args !! x = Some arg →
    expr_has_ty lty arg ty) →
    interp_local_tys σi lty le -∗
    interp_local_tys σi targs vargs.
  Proof.
    move => ????? hdom hargs helt.
    iIntros "#Hle" (v ty) "%hin".
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
    by iApply expr_adequacy.
  Qed.

  Lemma heap_models_update h l rt vs (σi: interp_env) t σt f fty v:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
    map_Forall (λ _ : string, wf_cdef_fields_wf) Δ →
    (* overkill, contra is enough for fields in this proof *)
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
    destruct Heq as [[<- [= <- <-]] | [hne hl]].
    - iSpecialize ("h" $! l rt vs with "[//]").
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
      + iPureIntro.
        by rewrite -hdomv dom_insert_lookup // -elem_of_dom hdomv elem_of_dom.
      + iIntros (f' iF') "#hf'".
        destruct (decide (f = f')) as [-> | hne].
        * rewrite lookup_insert.
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
        * rewrite lookup_insert_ne //.
          by iApply "hmodfs".
    - iApply "h".
      by iPureIntro.
  Qed.

  Lemma cmd_adequacy_ lty cmd lty' :
    wf_cdefs Δ →
    map_Forall (λ _, wf_ty) lty →
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
        lty lhs recv t targs name orig mdef args hrecv hfrom hdom hi |
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
      iAssert (heap_models h ∗ ▷ interp_type (subst_ty targs fty) σi v)%I with "[Hh]" as "[Hh Hv]".
      { iDestruct "Hh" as (sh) "(H● & %hdom & #Hh)".
        iDestruct (sem_heap_own_valid_2 with "H● H◯") as "#HΦ".
        iDestruct ("Hh" with "[//]") as (iFs) "[H H▷]".
        iRewrite "H" in "HΦ".
        rewrite option_equivI prod_equivI /=.
        iDestruct "HΦ" as "[%Ht HΦ]".
        fold_leibniz; subst.
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
        destruct wfΔ.
        assert (hsub: subst_ty (subst_ty σt <$> σ) fty <: subst_ty targs fty).
        { clear hdom hdiom hdf.
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
        simplify_eq.
        iApply subtype_is_inclusion => //.
        apply wf_ty_subst.
        * apply wf_ty_subst_map; first by apply wf_ty_class_inv in hwfσt.
          apply inherits_using_wf in hinherits => //.
          by repeat destruct hinherits as [? hinherits].
        * by apply has_field_wf in hf.
      }
      iNext.
      iFrame.
      by iApply interp_local_tys_update.
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
      iDestruct (expr_adequacy _ recv with "Hle") as "#Hrecv" => //.
      rewrite interp_class_unfold /=.
      iDestruct "Hrecv" as (? ? def σin σt fields ifields) "[%Hpure [hifields Hl]]".
      destruct Hpure as [[= <-] [hσin [hwfσt [hdef [htargs hfields]]]]].
      iDestruct "Hh" as (sh) "(H● & %Hdom & #Hh)".
      iDestruct (sem_heap_own_valid_2 with "H● Hl") as "#HΦ".
      iDestruct ("Hh" with "[//]") as (?) "[H H▷]".
      iRewrite "H" in "HΦ".
      rewrite option_equivI prod_equivI /=.
      iDestruct "HΦ" as "[%Ht HΦ]".
      fold_leibniz; subst.
      (* both static and dynamic classes actually exists in Δ *)
      assert (ht1: is_Some (Δ !! t1)).
      { apply has_method_from_def in H7 as (? & ? & ? & ? & _ & [? [hin ?]]) => //.
        by apply inherits_using_wf in hin as (? & ? & ht1 & _).
      }
      destruct ht1 as [ def1 ht1 ].
      (* Get method inclusion information between mdef0 and mdef *)
      destruct (has_method_ordered _ _ _ _ _ _ _ _
        wf_extends_wf wf_override wf_parent wf_methods_bounded
        hσin H7 hfrom)
      as (σmin & σot1 & σot & odef0 & odef & omdef0 & omdef &
         hσeq & ho1 & ho & hom1 & hom & hino & hin1 & hin &
         _ & ? & heq0 & heq1 & hincl0 & hincl1).
      (* Get location of the definition of the dynamic method mdef0 *)
      destruct (has_method_from_def _ _ _ _  wf_parent wf_methods_bounded H7) as
        (odef0' & mdef0_orig & ho0 & hm0 & hmorig0 & [σ0 [hin0 ->]]).
      rewrite ho0 in ho1; injection ho1; intros; subst; clear ho1.
      rewrite subst_mdef_body in H11.
      rewrite subst_mdef_ret in H12.
      (* Get some type info about dynamic method mdef0 *)
      assert (hwf0 := hin0).
      eapply wf_mdef_ty_inherits in hwf0 => //; last first.
      { apply wf_mdefs in ho0.
        by apply ho0 in hm0.
      }
      (* Random helpers statements *)
      assert (bounded (length σ0) (methodrettype mdef0_orig)).
      { assert (ho0' := ho0).
        apply wf_methods_bounded in ho0'.
        apply ho0' in hm0.
        destruct hm0 as [_ hret].
        apply inherits_using_wf in hin0 => //.
        repeat destruct hin0 as [? hin0]; simplify_eq.
        by rewrite H6.
      }
      assert (hb0 : map_Forall (λ _ : string, bounded (length σ0)) (methodargs mdef0_orig)).
      { assert (ho0' := ho0).
        apply wf_methods_bounded in ho0'.
        apply ho0' in hm0.
        destruct hm0 as [hargs _].
        rewrite map_Forall_lookup => k tk hk.
        apply hargs in hk.
        apply inherits_using_wf in hin0 => //.
        repeat destruct hin0 as [? hin0]; simplify_eq.
        by rewrite H8.
      }
      assert (hbo: map_Forall (λ _ : string, bounded (length σot)) (methodargs omdef)).
      { assert (ho' := ho).
        apply wf_methods_bounded in ho'.
        apply ho' in hom.
        destruct hom as [hargs _].
        rewrite map_Forall_lookup => k tk hk.
        apply hargs in hk.
        apply inherits_using_wf in hin => //.
        repeat destruct hin as [? hin]; simplify_eq.
        by rewrite H8.
      }
      assert (length σt = length (generics def1)).
      { inv hwfσt.
        by simplify_eq.
      }
      assert (Forall wf_ty σt) by (by apply wf_ty_class_inv in hwfσt).
      assert (hwfot1: Forall wf_ty σot1).
      { apply inherits_using_wf in hin1 => //.
        by repeat destruct hin1 as [? hin1].
      }
      (* specialize the typing judgement of the method by adding the
       * runtime type substitution.
       *)
      assert (hwf1: wf_mdef_ty (ClassT t1 σt) (subst_ty σt <$> σ0) mdef0_orig).
      { destruct hwf0 as [rty0 [wf0 [hbody0 hret0]]].
        exists (subst_ty σt <$> rty0); split; last split.
        + rewrite map_Forall_lookup => k ty.
          rewrite lookup_fmap_Some.
          case => [ty' [<- hk]].
          apply wf_ty_subst => //.
          by apply wf0 in hk.
        + replace (ClassT t1 σt) with (subst_ty σt (ClassT t1 (gen_targs (length (generics def1))))); last first.
          { simpl.
            by rewrite subst_ty_gen_targs.
          }
          rewrite -fmap_subst_ty_subst // -fmap_insert.
          apply cmd_has_ty_subst => //.
          rewrite map_Forall_lookup => k tk.
          rewrite lookup_insert_Some.
          case => [[? <-]|[?]].
          * econstructor => //; first by rewrite length_gen_targs.
            by apply gen_targs_wf.
          * rewrite lookup_fmap_Some.
            case => [tx [<- hk]].
            apply wf_ty_subst.
            { apply inherits_using_wf in hin0 => //.
              by repeat destruct hin0 as [? hin0].
            }
            apply has_method_wf in hmorig0 as [hargs _] => //.
            by apply hargs in hk.
        + rewrite -subst_ty_subst //.
          by apply expr_has_ty_subst.
      }
      destruct hwf1 as [rty1 [wf1 [hbody1 hret1]]].
      (* manual clean up *)
      rewrite hm0 in hom1; injection hom1; intros; subst; clear hom1.
      replace σ0 with σot1 in *; last by eapply inherits_using_fun.
      clear hin0.
      assert (wfbody:
        map_Forall (λ _ : string, wf_ty)
          (<["$this":=ClassT t1 σt]> (subst_ty (subst_ty σt <$> σot1) <$> methodargs omdef0))
      ).
      { rewrite map_Forall_lookup => x tx.
        rewrite lookup_insert_Some.
        case => [[? <-]|[?]] => //.
        rewrite lookup_fmap_Some.
        case => [tx' [ <- hx]].
        apply wf_ty_subst.
        - apply Forall_forall => tk hk.
          apply elem_of_list_fmap_2 in hk as [tk2 [-> hk]].
          apply wf_ty_subst => //.
          rewrite Forall_forall in hwfot1.
          by apply hwfot1 in hk.
        - assert (ho0' := ho0).
          apply wf_methods_wf in ho0'.
          apply ho0' in hm0.
          by apply hm0 in hx.
      }
      assert (Forall wf_ty σin).
      { apply inherits_using_wf in hσin => //.
        by repeat destruct hσin as [? hσin].
      }
      assert (hbt: Forall wf_ty σt) by (by apply wf_ty_class_inv in hwfσt).
      assert (hwftin: Forall wf_ty (subst_ty σt <$> σin)) by (by apply wf_ty_subst_map).
      assert (hwftargs: Forall wf_ty targs).
      { apply expr_has_ty_wf in hrecv => //.
        by apply wf_ty_class_inv in hrecv.
      }
      assert (hbint : Forall (bounded (length σin)) σot).
      { apply inherits_using_wf in hin => //.
        destruct hin as (? & ? & ? & ? & hF & hL & hwf).
        apply inherits_using_wf in hσin => //.
        destruct hσin as (? & ? & ? & ? & hF' & hL' & hwf').
        simplify_eq.
        by rewrite hL'.
      }
      (* Time ot use the induction hypothesis *)
      iModIntro; iNext.
      iSpecialize ("IH" $! _ _ _ wfbody hbody1 σi _ _ _ H11); simpl.
      iDestruct ("IH" with "[Hh Hle H●]") as "Hstep".
      { iSplit.
        - iExists _; iFrame.
          iSplit; first by rewrite Hdom.
          done.
        - iApply interp_local_tys_update => //; last first.
            + rewrite interp_class_unfold /interp_class /=.
              iExists l, t1, def1, (gen_targs (length def1.(generics))), σt, fields, ifields; iSplitR.
              { iPureIntro; repeat split => //; first by econstructor.
                rewrite subst_ty_gen_targs //.
                by apply subtype_targs_refl.
              }
              by iSplit.
            + iApply (interp_local_tys_list _ lty le) => //.
              * destruct hincl0 as [hdomincl _].
                rewrite !dom_fmap_L in hdomincl.
                rewrite !dom_fmap_L in hdom.
                by rewrite !dom_fmap_L hdomincl hdom.
              * move => x ty arg.
                rewrite lookup_fmap_Some.
                case => [tx [<- hx]] harg.
                destruct hincl1 as [hdom1 [hincl1 _]].
                destruct (methodargs omdef !! x) as [ty' | ] eqn:hty'.
                { assert (bounded (length σot) ty').
                  { assert (ho' := ho).
                    apply wf_methods_bounded in ho'.
                    apply ho' in hom.
                    apply hom in hty'.
                    apply inherits_using_wf in hin => //.
                    destruct hin as ( ? & ? & ? & ? & _ & hL & _); simplify_eq.
                    by rewrite hL.
                  }
                  eapply ESubTy.
                  - apply hi with x => //.
                    by rewrite /subst_mdef /= lookup_fmap hty'.
                  - apply wf_ty_subst.
                    + rewrite Forall_forall => tk hk.
                      apply elem_of_list_fmap_2 in hk as [tk2 [-> hk]].
                      apply wf_ty_subst => //.
                      rewrite Forall_forall in hwfot1; by apply hwfot1.
                    + apply has_method_wf in hmorig0 as [hargs _] => //.
                      by apply hargs in hx.
                  - (* step by step, using variance info *)
                    assert (hsub: subst_ty targs (subst_ty σot ty') <: subst_ty (subst_ty σt <$> σin) (subst_ty σot ty')).
                    { apply subtype_lift with (neg_variance <$> generics def) => //.
                      - assert (hmono := ho).
                        apply wf_methods_mono in hmono.
                        assert (hom' := hom).
                        apply hmono in hom' as [hmonoa _].
                        assert (ha := hty').
                        apply hmonoa in ha.
                        apply mono_subst with (neg_variance <$> generics odef) => //.
                        + rewrite map_length.
                          apply wf_methods_bounded in ho.
                          apply ho in hom.
                          by apply hom in hty'.
                        + rewrite map_length.
                          apply inherits_using_wf in hin => //.
                          repeat destruct hin as [? hin]; by simplify_eq.
                        + rewrite neg_variance_fmap_idem => i vi ti hvi.
                          apply list_lookup_fmap_inv in hvi.
                          destruct hvi as [wi [-> hwi]].
                          move => hti hc.
                          apply inherits_using_mono with (def0 := def) in hin => //.
                          inv hin; simplify_eq.
                          eapply H15 => //.
                          by destruct wi.
                        + move => i vi ti hvi.
                          apply list_lookup_fmap_inv in hvi.
                          destruct hvi as [wi [-> hwi]].
                          move => hti hc.
                          apply inherits_using_mono with (def0 := def) in hin => //.
                          inv hin; simplify_eq.
                          eapply H16 => //.
                          by destruct wi.
                      - apply wf_ty_subst => //.
                        * apply inherits_using_wf in hin => //.
                          by repeat destruct hin as [? hin].
                        * apply wf_methods_wf in ho.
                          apply ho in hom.
                          by apply hom in hty'.
                      - by apply neg_subtype_targs.
                    }
                    eapply SubTrans; first by exact hsub.
                    rewrite -!subst_ty_subst; first last.
                    { by apply bounded_subst with (length σot). }
                    { assert (ho0' := ho0).
                      apply wf_methods_bounded in ho0.
                      apply ho0 in hm0.
                      apply hm0 in hx.
                      apply inherits_using_wf in hin1 => //.
                      destruct hin1 as (? & ? &? &? & ? &hL & ?).
                      simplify_eq.
                      by rewrite hL.
                    }
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
      }
      iRevert "Hstep".
      iApply updN_mono_I.
      iIntros "[Hmodels Hle2]"; iFrame.
      iApply interp_local_tys_update; first by done.
      destruct hincl1 as [? [? hret]].
      assert (hsub: subst_ty (subst_ty σt <$> σot1) (methodrettype omdef0) <:
                    subst_ty targs (subst_ty σot (methodrettype omdef))).
      { eapply SubTrans; last first.
        - apply subtype_lift with (σ1 := subst_ty σt <$> σin) (vs0 := generics def) => //.
          + assert (hmono := ho).
            apply wf_methods_mono in hmono.
            assert (hom' := hom).
            apply hmono in hom' as [_ hmonoret].
            apply mono_subst with (generics odef) => //.
            * apply wf_methods_bounded in ho.
              apply ho in hom.
              by apply hom.
            * apply inherits_using_wf in hin => //.
              repeat destruct hin as [? hin]; by simplify_eq.
            * move => i vi ti hvi hti hc.
              apply inherits_using_mono with (def0 := def) in hin => //.
              inv hin; simplify_eq.
              by eapply H17.
            * move => i vi ti hvi hti hc.
              apply inherits_using_mono with (def0 := def) in hin => //.
              inv hin; simplify_eq.
              by eapply H16.
          + apply wf_ty_subst => //.
            * apply inherits_using_wf in hin => //.
              by repeat destruct hin as [? hin].
            * apply wf_methods_wf in ho.
              apply ho in hom.
              by apply hom.
        - rewrite -!subst_ty_subst; last first.
          { by apply inherits_using_wf in hin1. }
          { apply bounded_subst with (length σot) => //.
            apply inherits_using_wf in hin => //.
            destruct hin as (? & ? & ? & ? & ? & hL & _).
            simplify_eq.
            assert (ho' := ho).
            apply wf_methods_bounded in ho'.
            apply ho' in hom.
            rewrite hL.
            by apply hom.
          }
          by apply subtype_subst.
      }
      iDestruct (expr_adequacy _ (methodret omdef0) with "Hle2") as "#Hret" => //.
      iApply subtype_is_inclusion => //.
      apply wf_ty_subst; first by apply wf_ty_subst_map.
      apply wf_methods_wf in ho0.
      apply ho0 in hm0.
      by apply hm0.
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
      assert (hwf: map_Forall (λ _ : string, wf_ty) (<[v:=InterT tv (ExT t)]> lty)).
      { rewrite map_Forall_lookup => k tk.
        rewrite lookup_insert_Some.
        case => [[? <-]|[? hk]].
        + constructor; first by apply wflty in hv.
          constructor.
        + by apply wflty in hk.
      }
      iApply ("IHty" $! hwf with "[//]"); iClear "IH IHty".
      clear H6 h.
      destruct H5 as (l & hl & t' & fields & hlt & hinherits).
      iDestruct "H" as "[H #Hle]".
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
    map_Forall (λ _ : string, wf_ty) lty →
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

(* Critical lemma to generate the initial iris state and boot strap
 * all the reasoning.
 *)
Lemma sem_heap_init
  `{PDC: ProgDefContext}
  `{!sem_heapGpreS Σ}:
  ⊢@{iPropI Σ} |==> ∃ _: sem_heapGS Σ, (heap_models ∅ ∗ interp_local_tys [] ∅ ∅).
Proof.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅)) as (γI) "HI";
    first by apply gmap_view_auth_valid.
  iExists (SemHeapGS _ _ γI).
  iModIntro; iSplit.
  { iExists ∅. 
    iSplit; first done.
    iSplit; first (iPureIntro; by set_solver).
    iModIntro; iIntros (l t vs) "%H".
    by rewrite !lookup_empty in H.
  }
  iIntros (v t H).
  by rewrite !lookup_empty in H.
Qed.
