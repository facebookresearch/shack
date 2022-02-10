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

Check fmap.

Section proofs.
  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.

  (* Iris semantic context *)
  Context `{!sem_heapGS Σ}.
  Notation γ := sem_heap_name.

  (* Helping the inference with this notation that hides Δ *)
  Local Notation "s <: t" := (@subtype _ s t) (at level 70, no associativity).
  Local Notation "lty <:< rty" := (@lty_sub _ lty rty) (at level 70, no associativity).

  (* heap models relation; the semantic heap does
     not appear because it is hidden in iProp  *)
  (* Helper defintion to state that fields are correctly modeled *)
  Definition heap_models_fields
    (iFs: gmapO string (laterO (sem_typeO Σ))) (vs: stringmap value) : iProp Σ :=
    ⌜dom (gset string) vs ≡ dom _ iFs⌝  ∗
    ∀ f (iF: sem_typeO Σ),
    iFs !! f ≡ Some (Next iF) -∗ ∃ v, (⌜vs !! f = Some v⌝ ∗ ▷iF v).

  Lemma heap_models_fields_ext_L: ∀ iFs iFs' vs,
    iFs ≡ iFs' -∗ heap_models_fields iFs vs -∗ heap_models_fields iFs' vs.
  Proof.
    move => iFs iFs' vs.
    iIntros "heq h".
    rewrite /heap_models_fields.
    iDestruct "h" as "[%hdom h]".
    iSplit.
    { rewrite gmap_equivI.
      fold_leibniz.
      rewrite set_eq hdom.
      iIntros (s).
      rewrite !elem_of_dom.
      by iRewrite ("heq" $! s).
    }
    iIntros (f iF) "hiF".
    iApply "h".
    by iRewrite "heq".
  Qed.

  Definition heap_models (h : heap) : iProp Σ :=
    ∃ (sh: gmap loc (prodO tagO (gmapO string (laterO (sem_typeO Σ))))),
    own γ (gmap_view_auth (DfracOwn 1) sh) ∗ ⌜dom (gset loc) sh = dom _ h⌝ ∗
    □ ∀ (ℓ : loc) (t : tag) (vs : stringmap value),
    ⌜h !! ℓ = Some (t, vs)⌝ -∗
    ∃ (iFs : gmapO string (laterO (sem_typeO Σ))),
    sh !! ℓ ≡ Some (t, iFs) ∗ heap_models_fields iFs vs.

  Lemma expr_adequacy (σi:interp_env) e lty le ty val :
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    expr_eval le e = Some val →
    expr_has_ty lty e ty →
    interp_local_tys σi lty le -∗
    interp_type ty σi val.
  Proof.
    move => hwf he h; move: le val he.
    elim: h => [z | b | | op e1 e2 hop he1 hi1 he2 hi2 |
        op e1 e2 hop he1 hi1 he2 hi2 |
        v vty hv | exp S T hS hi hsub ] le val he; iIntros "#Hlty".
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
      by iApply he.
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

  Lemma interp_local_tys_weaken_ty (σi: interp_env) v A B lty lty' le:
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    lty !! v = Some A →
    lty' !! v = Some B →
    (∀ w, v ≠ w → lty !! w = lty' !! w) →
    A <: B →
    interp_local_tys σi lty le -∗
    interp_local_tys σi lty' le.
  Proof.
    move => hwf hin1 hin2 hs hAB; iIntros "H".
    rewrite /interp_local_tys.
    iIntros (w ty) "%Hin".
    destruct (decide (v = w)) as [<- | hne].
    - rewrite hin2 in Hin; case: Hin => <-.
      iSpecialize ("H" $! v A).
      iDestruct ("H" with "[//]") as (val) "[%Hin #h]".
      iExists val; iSplitR; first done.
      by iApply subtype_is_inclusion.
    - iSpecialize ("H" $! w ty).
      rewrite -hs in Hin => //.
      iDestruct ("H" with "[//]") as (val) "[%Hin' #h]".
      iExists val; by iSplitR.
  Qed.

  Lemma interp_local_tys_subset_eq σi lty lty' le:
    lty' ⊆ lty →
    interp_local_tys σi lty le -∗
    interp_local_tys σi lty' le.
  Proof.
    move => hs; iIntros "H" (w ty) "%Hle".
    iSpecialize ("H" $! w ty).
    rewrite (lookup_weaken _ _ w ty Hle hs).
    iDestruct ("H" with "[//]") as (val) "[%hw H]".
    iExists val.
    by rewrite hw; iSplit.
  Qed.

  Lemma interp_local_tys_list (σi:interp_env) lty le targs args vargs:
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    dom stringset targs = dom stringset args →
    map_args (expr_eval le) args = Some vargs →
    (∀ (x : string) (ty : lang_ty) (arg : expr),
    targs !! x = Some ty →
    args !! x = Some arg →
    expr_has_ty lty arg ty) →
    interp_local_tys σi lty le -∗
    interp_local_tys σi targs vargs.
  Proof.
    move => hwf hdom hargs helt.
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

  Lemma heap_models_update h l rt vs σi t σt f fty v:
    h !! l = Some (rt, vs) →
    has_field f t fty →
    interp_type (ClassT t σt) σi (LocV l) -∗
    interp_type (subst_ty σt fty) σi v -∗
    heap_models h -∗
    heap_models (<[l:=(rt, <[f:=v]> vs)]> h).
  Proof.
    move => hheap hfield.
    iIntros "#hrecv #hv hmodels".
    iDestruct "hmodels" as (sh) "[hown [%hdom #h]]".
    iExists sh.
    rewrite interp_class_unfold.
    iDestruct "hrecv" as (l' t' fields ifields) "[%H [hsem hl]]".
    iDestruct "hsem" as "[%hdomf #hifields]".
    destruct H as [[= <-] [ hinherits' hfields]].
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
      iSpecialize ("hifields" $! f fty hfield).
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
          by iRewrite -"hf'".
        * rewrite lookup_insert_ne //.
          by iApply "hmodfs".
    - iApply "h".
      by iPureIntro.
  Qed.

  (* Lemma interp_mixed_spec σi v: *)
  (*   map_Forall (fun _ => wf_cdef_fields) Δ → *)
  (*   interp_type MixedT σi v -∗ *)
  (*   (interp_int v ∨ interp_bool v ∨ interp_null v ∨ *)
  (*   ∃ l t ifields, ⌜v = LocV l⌝ ∧ l ↦ (t, ifields) ∧ interp_ex σi t interp_type v)%I. *)
  (* Proof. *)
  (*   move => hwf. *)
  (*   rewrite interp_type_unfold /=. *)
  (*   iIntros "[H | H]"; last first. *)
  (*   { by iRight; iRight; iLeft. } *)
  (*   iDestruct "H" as "[? | H]". *)
  (*   { by iLeft. } *)
  (*   iDestruct "H" as "[? | H]". *)
  (*   { by iRight; iLeft. } *)
  (*   iDestruct "H" as (t σt l rt fields ifields) "[%Heq [#Hfields #hl]]". *)
  (*   destruct Heq as [-> [hinherits hrtf]]. *)
  (*   iRight; iRight; iRight. *)
  (*   iExists l, rt, ifields. *)
  (*   iSplit; first done. *)
  (*   iSplit; first done. *)
  (*   iDestruct "Hfields" as "[%hdom #Hfields]". *)
    
  (*   apply inherits_to_using in hinherits. *)
  (*   destruct hinherits as [-> | [σin hinherits]]; last first. *)
  (*   - iExists (subst_ty σin <$> σt), l, rt, fields, ifields. *)
  (*     iSplit; first done. *)
  (*     iSplit; last done. *)
  (*     iSplit; first done. *)
  (*     iIntros (f ty) "%hf". *)
  (*     assert (hf': has_field f t (subst_ty σin ty)). *)
  (*      eapply has_field_inherits => //. *)

  (* Lemma inherits_to_using A B: *)
  (*   inherits A B → (A = B) ∨ ∃ σ, inherits_using A B σ. *)

(* Lemma has_field_inherits : *)
  (* map_Forall (fun _ => wf_cdef_fields) Δ → *)
  (* ∀ A B σ, inherits_using A B σ → *) 
  (* ∀ f fty, has_field f B fty → has_field f A (subst_ty σ fty). *)
  (*
  Lemma interp_class_loc_inversion σi h l C σC t fields:
    h !! l = Some (t, fields) →
    heap_models h -∗
    interp_class C σC σi interp_type (LocV l) -∗
    heap_models h ∗ interp_type (ExT t) σi (LocV l).
  Proof.
    move => hl; iIntros "Hh H".
    iDestruct "H" as (????) "[%H [#Hifields H◯]]".
    destruct H as [[= <-] [hinherits hfields]].
    rewrite /interp_ex interp_type_unfold /=.
    iDestruct "Hh" as (sh) "[hown [%hdom #h]]".
    iDestruct (sem_heap_own_valid_2 with "hown H◯") as "#Hv".
    iSplitL "hown".
    { iExists _; iSplitL; first done.
      by iSplit.
    }
    iSpecialize ("h" $! l t fields hl).
    iDestruct "h" as (iFs) "[HiFs hmodfs]".
    iRewrite "HiFs" in "Hv".
    rewrite !option_equivI prod_equivI /=.
    iDestruct "Hv" as "[%ht #heq]".
    fold_leibniz; subst.
    iExists σC, l, t0, fields0, ifields.
    iSplitR; first done.
    iSplitR; last done.
    iDestruct "Hifields" as "[%hfdom #Hifields]".
    iSplit; first done.






    iDestruct ((heap_models_class _ _ cname _ _ hl) with "[Hh //]") as "Hv".
    iApply "Hv".
    by rewrite interp_type_unfold.
  Qed.

  Lemma interp_nonnull_loc_inversion σi h (v: string) l t fields:
    h !! l = Some (t, fields) →
    heap_models h -∗
    interp_nonnull σi interp_type (LocV l) -∗
    heap_models h ∗ interp_type (ExT t) σi (LocV l).
  Proof.
    move => hl; iIntros "Hh H".
    iDestruct "H" as "[H | H]".
    { iDestruct "H" as (z) "%H"; discriminate. }
    iDestruct "H" as "[H | H]".
    { iDestruct "H" as (b) "%H"; discriminate. }
    iDestruct "H" as (cname) "H".
    iFrame.
    rewrite interp_type_unfold.
    by iApply ((interp_class_loc_inversion _ v _ cname) with "[Hh]").
  Qed.

  Lemma interp_type_loc_inversion σi h le lty (v: string) l T t fields:
    h !! l = Some (t, fields) →
    le !! v = Some (LocV l) →
    interp_local_tys σi lty le -∗
    heap_models h -∗
    interp_type T σi (LocV l) -∗
    heap_models h ∗ interp_type (ExT t) σi (LocV l).
  Proof.
    rewrite interp_type_unfold => hl hv;  elim: T v hv => /=.
    - move => ??; iIntros "? ? H".
      iDestruct "H" as (z) "%H"; discriminate.
    - move => ??; iIntros "? ? H".
      iDestruct "H" as (b) "%H"; discriminate.
    - move => ??; iIntros "? ? H".
      iDestruct "H" as "%H"; by elim H.
    - move => v hv; iIntros "#Hs Hh H".
      iDestruct "H" as "[H | H]"; last first.
      { iDestruct "H" as "%H"; discriminate. }
      by iApply ((interp_nonnull_loc_inversion _ v) with "[Hh]").
    - move => cname v hv; iIntros "Hs Hh H".
      by iApply ((interp_class_loc_inversion _ v _ cname) with "[Hh]").
    - move => ??; iIntros "? ? H".
      iDestruct "H" as "%H"; discriminate.
    - move => v hv; iIntros "#Hs Hh H".
      by iApply ((interp_nonnull_loc_inversion _ v) with "[Hh]").
    - move => S hS T hT v hv; iIntros "#Hs Hh H".
      iDestruct "H" as "[H | H]".
      + apply hS in hv.
        by iApply (hv with "Hs Hh H").
      + apply hT in hv.
        by iApply (hv with "Hs Hh H").
    - move => S hS T hT v hv; iIntros "#Hs Hh H".
      iAssert (interp_type S (LocV l)) with "[H]" as "hs".
      { rewrite interp_type_unfold.
        by iDestruct "H" as "[HS HT]".
      }
      apply hS in hv.
      rewrite -!interp_type_unfold in hv.
      by iApply (hv with "Hs Hh hs").
  Qed.
   *)

  Lemma cmd_adequacy_ lty cmd lty' :
    wf_cdefs Δ →
    ⌜cmd_has_ty lty cmd lty'⌝ -∗
    ∀ (σi: interp_env) st st' n, ⌜cmd_eval st cmd st' n⌝ -∗
    heap_models st.2 ∗ interp_local_tys σi lty st.1 -∗ |=▷^n
        heap_models st'.2 ∗ interp_local_tys σi lty' st'.1.
  Proof.
    move => wfΔ.
    iLöb as "IH" forall (lty cmd lty').
    (* iIntros (wftys). *)
    iIntros "%hty" (σi st st' n) "%hc".
    iInduction hty as [ lty | lty1 lty2 lty3 fstc sndc hfst hi1 hsnd hi2 |
        lty lhs e ty he | lty1 lty2 cond thn els hcond hthn hi1 hels hi2 |
        lty lhs recv t targs name fty hrecv hf |
        lty recv fld rhs fty t σ hrecv hrhs hf |
        lty lhs t targs args fields (*cdef hΔ hconstraints*) hf hdom harg |
        (* lty lhs recv t targs name mdef args hrecv hm hdom hi | *)
        lty c rty' rty hsub h hi |
        lty v tv t cmd hv h hi
      ] "IHty" forall (st st' n hc).
    - (* SkipC *) inv hc.
      rewrite updN_zero.
      by iIntros "?".
    - (* SeqC *) inv hc. iIntros "H".
      iSpecialize ("IHty" with "[//] H").
      rewrite Nat_iter_add.
      iApply (updN_mono_I with "[] IHty").
      by iApply "IHty1".
    - (* LetC *)
      inv hc.
      iClear "IH".
      iIntros "[? #Hle]".
      rewrite updN_zero /=.
      iFrame.
      iDestruct (expr_adequacy with "Hle") as "#?" => //.
      { by apply wfΔ. }
      by iApply interp_local_tys_update.
    - (* IfC *) inv hc
      + iIntros "H". by iApply "IHty".
      + iIntros "H". by iApply "IHty1".
    - (* GetC *) inv hc.
      iClear "IH".
      iIntros "[Hh #Hle]".
      iModIntro. (* keep the later *)
      iDestruct (expr_adequacy with "Hle") as "#He" => //.
      { by apply wfΔ. }
      rewrite interp_class_unfold /=.
      iDestruct "He" as (????) "[%H [#Hifields H◯]]".
      destruct H as [[= <-] [hinherits hfields]].
      iAssert (heap_models h ∗ ▷ interp_type (subst_ty targs fty) σi v)%I with "[Hh]" as "[Hh Hv]".
      { iDestruct "Hh" as (sh) "(H● & %hdom & #Hh)".
        iDestruct (sem_heap_own_valid_2 with "H● H◯") as "#HΦ".
        iDestruct ("Hh" with "[//]") as (iFs) "[H H▷]".
        iRewrite "H" in "HΦ".
        rewrite option_equivI prod_equivI /=.
        iDestruct "HΦ" as "[%Ht HΦ]".
        fold_leibniz; subst.
        iSplitL. { iExists _. iFrame. by iSplit. }
        rewrite /interp_fields.
        iDestruct "Hifields" as "[%hdiom Hifields]".
        iSpecialize ("Hifields" $! name fty hf).
        iDestruct "H▷" as "[%hdf h]".
        iRewrite -"HΦ" in "Hifields".
        iSpecialize ("h" $! name _ with "[Hifields]"); first done.
        iDestruct "h" as (w) "[%hw hiw]".
        by rw_inj hw H7.
      }
      iNext.
      iFrame.
      by iApply interp_local_tys_update.
    - (* SetC *) inv hc.
      iClear "IH".
      iIntros "[Hh #Hle]" => /=.
      iSplitL; last done.
      iApply heap_models_update => //.
      + iApply expr_adequacy => //.
        by apply wfΔ.
      + iApply expr_adequacy => //.
        by apply wfΔ.
    - (* NewC *) inv hc.
      iIntros "[Hh #Hle]"; simpl.
      (* we need one modality to update the semantic heap *)
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
      { rewrite interp_type_unfold /=.
        iExists _, _, _, _.
        iSplit; first done.
        iSplit; last done.
        rewrite /interp_fields; iSplit; first by rewrite /iFs !dom_fmap_L.
        iIntros (f fty) "%hfty".
        rewrite /iFs !lookup_fmap.
        apply hf in hfty.
        by rewrite hfty /=.
      }
      iSplitL; last by iApply interp_local_tys_update.
      iExists _. iFrame. iSplit; first by rewrite !dom_insert_L Hdom.
      iModIntro. iIntros (???) "Hlook".
      rewrite lookup_insert_Some.
      iDestruct "Hlook" as %[[<- [= <- <-]]|[Hℓ Hlook]].
      + iExists _. rewrite lookup_insert.
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
        iDestruct (expr_adequacy _ a0 with "Hle") as "#Ha0" => //.
        by apply wfΔ.
      + rewrite lookup_insert_ne; last done.
        by iApply "Hh".
        (*
    - (* CallC *) inv hc. iIntros "[Hh #Hle]".
      assert (wfbody: ∃B cdef,
        Δ !! B = Some cdef ∧
        wf_mdef_ty B cdef.(generics) mdef0 ∧
        wf_mdef_bounded cdef.(generics) mdef0 ∧
        inherits t0 B).
      { destruct wfΔ as [_ _ _ hbounded hbodies].
        rewrite map_Forall_lookup in hbodies.
        rewrite map_Forall_lookup in hbounded.
        admit (*
        apply has_method_from in H7.
        destruct H7 as (B & cdef & hΔB & heq & hin).
        assert (hbody := hΔB).
        assert (hbound := hΔB).
        apply hbodies in hbody.
        apply hbounded in hbound.
        rewrite map_Forall_lookup in hbody.
        exists B; exists cdef; split; first done.
        split; last split; last done.
        + by apply hbody in heq.
        + by apply hbound in heq.
               *).
      }
      destruct wfbody as (B & cdef & hΔB & wfbody & wfbounded & hinherits).
      destruct wfbody  as (lty_body & hbody & hret).
      iAssert(⌜inherits t0 t⌝ ∗ interp_type (ClassT B targs) env (LocV l))%I as "#Hl".
      { iDestruct (expr_adequacy _ recv with "Hle") as "#Hrecv" => //.
        rewrite !interp_type_unfold /= /interp_class.
        iDestruct "Hrecv" as (? t1 ?) "[%hpure Hsem]".
        destruct hpure as [[= <-] [hinherits' ?]].
        iDestruct "Hh" as (sh) "(H● & % & #Hh)".
        iDestruct (sem_heap_own_valid_2 with "H● Hsem") as "#HΦ".
        iDestruct ("Hh" with "[//]") as (?) "[H H▷]".
        iRewrite "H" in "HΦ".
        rewrite option_equivI prod_equivI /=.
        iDestruct "HΦ" as "[%Ht HΦ]".
        fold_leibniz; rewrite Ht.
        iSplitR; first done.
        iExists l, t1, fields; iSplitR; last done.
        iPureIntro; split; first done.
        split => //.
        by rewrite -Ht.
      }
      iDestruct "Hl" as "[%Hinherits #Hl]".
      assert (hincl: mdef_incl mdef0 mdef).
      {
        eapply has_method_inherits in Hinherits; [ | by apply wfΔ | done ].
        destruct Hinherits as [? [? ?]].
        replace x with mdef0 in * by (by eapply has_method_fun).
        done.
      }
      (*
      assert (hbody':
        cmd_has_ty
          (<["$this":=ClassT B targs]> (subst_local_tys targs (methodargs mdef0)))
          (methodbody mdef0)
          (subst_local_tys targs lty_body)).
      { replace (ClassT B targs) with
         (subst_ty targs (ClassT B (gen_targs (generics cdef)))).
        + rewrite -insert_subst_local_tys.
          apply cmd_has_ty_subst.
          rewrite subst_local_tys_gen_targs_is_bounded // in hbody.
          by apply wfbounded.
        +
          rewrite /= -/fmap gen_targs_map_subst //.
          admit (* global invariant about targs' length *).
      }
      assert (hret' :
        expr_has_ty
          (subst_local_tys targs lty_body)
          (methodret mdef0)
          (subst_ty targs (methodrettype mdef0))).
      { destruct wfbounded as [_ retbounded].
        rewrite subst_gen_targs_is_bounded // in hret.
        by apply expr_has_ty_subst.
      }
       *)
      simpl.
      iModIntro; iNext.
      assert (hhh : ∃ env0: interp_env, interp_env_car env0 = (λ ty, interp_type ty env) <$> targs) by admit.
      destruct hhh as [env0 henv0].
      iSpecialize ("IH" $! _ _ _ hbody env0 _ _ _ H14); simpl.
      iDestruct ("IH" with "[Hh Hle]") as "H".
      { iFrame.
        iApply interp_local_tys_update => //.
        + iApply interp_local_tys_list => //.
          (* first by *)
          destruct hincl as [? _]; rewrite dom_subst_local_tys -H0 //.
          move => x ty arg hx harg.
          destruct hincl as [hdom' [hincl _]].
          destruct (methodargs mdef !! x) as [ty' | ] eqn:hty'.
          { apply lookup_subst_local_tys_Some in hx as [ z [ h0 ->]].
            apply (H1 _ _ _ hty') in harg.
            econstructor; first by apply harg.
            apply subtype_subst.
            by eapply hincl.
          }
        apply mk_is_Some in hx.
        apply elem_of_dom in hx.
        rewrite dom_subst_local_tys hdom' in hx.
        apply elem_of_dom in hx.
        rewrite hty' in hx.
        by elim: hx.
      }
      iRevert "H".
      iApply updN_mono_I.
      iIntros "[Hh Hle2]"; iFrame.
      iApply interp_local_tys_update; first by done.
      destruct hincl as [? [? hret'']].
      eapply subtype_subst in hret''.
      iApply subtype_is_inclusion; first by apply hret''.
      by iDestruct (expr_adequacy _ (methodret mdef0) with "Hle2") as "#Hret".
         *)
    - (* Subtyping *) 
      iIntros "H". iSpecialize ("IHty" with "[//] H").
      iApply updN_mono_I; last done.
      iIntros "[Hh #Hrty]". iFrame.
      iDestruct (interp_local_tys_is_inclusion with "Hrty") as "Hrty'" => //.
      { by apply wfΔ. }
      rewrite Forall_forall => i hi v.
      by apply _.
    - (* CondTagC *) inv hc; last first.
      { by iApply updN_intro. }
      iIntros "H".
      iApply ("IHty" with "[//]"); iClear "IH IHty".
      clear H6 h.
      destruct H5 as (l & hl & t' & fields & hlt & hinherits).
      iDestruct "H" as "[H #Hle]".
      iDestruct ("Hle" $! v with "[//]") as (?) "[%Hlev Hv]".
      rewrite Hlev in hl; simplify_eq.

      iAssert (interp_type MixedT σi (LocV l)) as "Hmixed".
      { iApply subtype_is_inclusion; last done.
        + by apply wfΔ.
        + by apply SubMixed.
      }
      rewrite interp_mixed_unfold /=.
      iDestruct "Hmixed" as "[Hnonnull | Hnull]"; last first.
      { iDestruct "Hnull" as "%Hnull"; discriminate. }
      iDestruct "Hnonnull" as "[Hint | Hl]".
      { iDestruct "Hint" as "%Hint"; by destruct Hint. }
      iDestruct "Hl" as "[Hbool | Hl]".
      { iDestruct "Hbool" as "%Hbool"; by destruct Hbool. }
      iDestruct "Hl" as (exTag exσ k rt exfields ifields) "[%H [#Hfields #Hl]]".
      destruct H as [[= <-] [hinherits' hfields']].
      iAssert (heap_models st.2 ∗ interp_type (ExT exTag) σi (LocV l))%I with "[H]" as "[Hh #Hv2]".
      { iDestruct "H" as (sh) "(H● & %hdom & #Hh)".
        iDestruct (sem_heap_own_valid_2 with "H● Hl") as "#HΦ".
        iDestruct ("Hh" with "[//]") as (iFs) "[H H▷]".
        iRewrite "H" in "HΦ".
        rewrite option_equivI prod_equivI /=.
        iDestruct "HΦ" as "[%Ht HΦ]".
        fold_leibniz; subst.
        iSplitL. { iExists _. iFrame. by iSplit. }
        rewrite interp_ex_unfold /=.
        iExists exσ, l, rt, exfields, ifields.
        iSplit; first done.
        by iSplit.
      }
      replace t' with rt in *; last by admit.
      iFrame.
      iIntros (w tw).
      rewrite lookup_insert_Some.
      iIntros "%Hw".
      destruct Hw as [[<- <-] | [hne hw]].
      { iExists (LocV l); rewrite Hlev; iSplitR; first done.
        rewrite interp_inter_unfold /=; iSplit; first done.
        by iApply inherits_is_inclusion.
      }
      by iApply "Hle".
  Qed.

  Lemma cmd_adequacy (env: interp_env) lty cmd lty' :
    wf_cdefs Δ →
    cmd_has_ty lty cmd lty' →
    ∀ st st' n, cmd_eval st cmd st' n →
    heap_models st.2 ∗ interp_local_tys env lty st.1 -∗ |=▷^n
        heap_models st'.2 ∗ interp_local_tys env lty' st'.1.
  Proof.
    move => ? hty ??? hc.
    iApply cmd_adequacy_; first done.
    by iPureIntro.
    by iPureIntro.
  Qed.

End proofs.

Print Assumptions cmd_adequacy.

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
