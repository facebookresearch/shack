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

From shack Require Import lang heap modality.

Section proofs.
  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.

  (* Iris semantic context *)
  Context `{!sem_heapGS Σ}.
  Notation iProp := (iProp Σ).
  Notation γ := sem_heap_name.

  (* Helping the inference with this notation that hides Δ *)
  Local Notation "s <: t" := (@subtype _ s t) (at level 70, no associativity).
  Local Notation "lty <:< rty" := (@lty_sub _ lty rty) (at level 70, no associativity).

  (* the interpretation of types is simply given by
     the carrier set of the sem_typeO ofe *)
  Notation interpO := (sem_typeO Σ).
  Definition interp := ofe_car interpO.
  Eval hnf in interp.
  (* = value → iPropO Σ *)
  (*      : Type *)

  (* now, let's interpret some types ! *)

  Definition interp_null : interp :=
    λ (v : value), ⌜v = NullV⌝%I.

  Definition interp_int : interp :=
    λ (v : value), (∃ z, ⌜v = IntV z⌝)%I.

  Definition interp_bool : interp :=
    λ (v : value), (∃ b, ⌜v = BoolV b⌝)%I.

  Definition interp_union (iA : interp) (iB : interp) : interp :=
    λ (v : value), (iA v ∨ iB v)%I.

  Definition interp_inter (iA : interp) (iB : interp) : interp :=
    λ (v : value), (iA v ∧ iB v)%I.

  Definition interp_nothing : interp :=
    λ (_: value), False%I.

  Notation ty_interpO := (lang_ty -d> interpO).

  Definition interp_fields (rec: ty_interpO) (ftys: stringmap lang_ty) :
    gmapO string (laterO interpO) :=
    let f := λ (typ: lang_ty), Next (rec typ) in
    @fmap _ _ _ (later interpO) f ftys
  .

  Lemma interp_fields_contractive ftys:
    Contractive (λ f, interp_fields f ftys).
  Proof.
    move => n i1 i2 hdist.
    rewrite /interp_fields.
    apply gmap_fmap_ne_ext => k ty hin.
    f_contractive.
    by destruct n.
  Qed.

  (* interpret a class type given the tag and the
     interpretation of their fields *)
  Definition interp_class (cname : tag) (rec : ty_interpO) : interp :=
    let f := λ (typ: lang_ty), Next (rec typ) in
    λ (w : value),
    (∃ ℓ t (fields:stringmap lang_ty),
    ⌜w = LocV ℓ ∧ inherits t cname ∧ has_fields t fields⌝ ∗
    (ℓ ↦ (t , interp_fields rec fields)))%I.

  Definition interp_nonnull (rec : ty_interpO) : interp :=
    λ (v : value),
    ((interp_int v) ∨
    (interp_bool v) ∨
    (∃ t, interp_class t rec v))%I.

  Definition interp_mixed (rec: ty_interpO) : interp :=
    λ (v: value), (interp_nonnull rec v ∨ interp_null v)%I.

  (* we use a blend of Coq/Iris recursion, the
     Coq recursion lets us handle simple structural
     cases, and we use Iris' recursion to deal with
     the more complicated case of class types *)
  Definition interp_type_pre (rec : ty_interpO) : ty_interpO :=
    λ (typ : lang_ty),
    (fix go (typ : lang_ty) : interp :=
    match typ with
    | IntT => interp_int
    | BoolT => interp_bool
    | NothingT => interp_nothing
    | MixedT => interp_mixed rec
    | ClassT t => interp_class t rec
    | NullT => interp_null
    | NonNullT => interp_nonnull rec
    | UnionT A B => interp_union (go A) (go B)
    | InterT A B => interp_inter (go A) (go B)
    end) typ.

  Lemma interp_class_contractive cname: Contractive (interp_class cname). 
  Proof.
    rewrite /interp_class => n i1 i2 hdist v.
    do 3 (f_equiv; intro).
    f_equiv.
    set (f := λ i, interp_fields i a1).
    assert (hf : Contractive f) by apply interp_fields_contractive.
    by apply (mapsto_contractive _ _ f).
  Qed.

  Lemma interp_nonnull_contractive: Contractive interp_nonnull.
  Proof.
    rewrite /interp_nonnull => n i1 i2 hdist v.
    do 4 f_equiv.
    revert v.
    by apply interp_class_contractive.
  Qed.

  (* we cannot use solve_contractive out of the box because of
   * the 'fix' combinator above
   *)
  Local Instance interp_type_pre_contractive:
  Contractive (interp_type_pre).
  Proof.
    move => n i1 i2 hdist.
    move => ty.
    elim : ty; intros => //=;
    [ (* mixed *)| (*class*) | (*nonnull*) 
 | solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv])
 | solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv])
     ].
     - move => v; rewrite /interp_mixed.
       f_equiv; revert v.
       by apply interp_nonnull_contractive.
     - by apply interp_class_contractive.
     - by apply interp_nonnull_contractive.
  Qed.

  (* the interpretation of types can now be
     defined as a fixpoint (because class types
     can be (mutually) recursive) *)
  Definition interp_type := fixpoint interp_type_pre.

  Lemma interp_type_unfold (ty : lang_ty) (v : value) :
    interp_type ty v ⊣⊢ interp_type_pre interp_type ty v.
  Proof.
    rewrite {1}/interp_type.
    apply (fixpoint_unfold interp_type_pre ty v).
  Qed.

  (* #hyp *)
  Global Instance interp_type_persistent : ∀ t v, Persistent (interp_type t v).
  Proof.
    elim => [ | | | | cname | | |s hs t ht | s hs t ht] v;
        rewrite interp_type_unfold //=; try by apply _.
    - rewrite /interp_union.
      by apply bi.or_persistent; rewrite -!interp_type_unfold.
    - rewrite /interp_union.
      by apply bi.and_persistent; rewrite -!interp_type_unfold.
  Qed.

  Lemma dom_interp_fields fields:
    dom stringset (interp_fields interp_type fields) ≡ dom _ fields.
  Proof. by rewrite /interp_fields dom_fmap. Qed.

  Lemma inherits_is_inclusion:
    ∀ A B, inherits A B →
    ∀ v, interp_class A interp_type v -∗ interp_class B interp_type v.
  Proof.
    move => A B hAB v.
    rewrite /interp_class.
    iIntros "h".
    iDestruct "h" as (ℓ t fields) "[%h hsem]".
    destruct h as [-> [hext2 hfields ]].
    iExists ℓ, t, fields.
    iSplit.
    { iPureIntro; split; first by done.
      split; last done.
      by eapply rtc_transitive.
    }
    by iFrame.
  Qed.

  (* A <: B → ΦA ⊂ ΦB *)
  Theorem subtype_is_inclusion_aux:
    ∀ (A B: lang_ty), A <: B →
    ∀ v,
    interp_type_pre interp_type A v -∗
    interp_type_pre interp_type B v.
  Proof.
    induction 1 as [A | A B hext | | | | A | A B| A B | A B C h0 hi0 h1 hi1
        | A B | A B | A B C h0 hi0 h1 hi1 | A | A B C h0 hi0 h1 hi1 ];
    move => v /=.
    - rewrite /interp_mixed.
      elim: A v => //=.
      + move => v; iIntros "h"; by repeat iLeft.
      + move => v; iIntros "h"; by iLeft; iRight; iLeft.
      + move => v; by rewrite /interp_nothing; iIntros "h".
      + move => cname v.
        iIntros "h".
        iLeft; iRight; iRight.
        iExists cname; by iApply inherits_is_inclusion. 
      + move => v; iIntros "h"; by iRight.
      + move => v; by iIntros "h"; iLeft.
      + move => s hs t ht v.
        rewrite /interp_union.
        iIntros "h".
        iDestruct "h" as "[ h | h ]"; first by iApply hs.
        by iApply ht.
      + move => s hs t ht v.
        rewrite /interp_inter.
        iIntros "h".
        iDestruct "h" as "[? _]"; by iApply hs.
    - by iApply inherits_is_inclusion.
    - by rewrite /= /interp_mixed.
    - iIntros "h"; by iLeft.
    - iIntros "h"; by iRight; iLeft.
    - iIntros "H".
      iRight; iRight.
      iExists A.
      by iApply inherits_is_inclusion.
    - rewrite /interp_union.
      by iIntros "h"; iLeft.
    - rewrite /interp_union.
      by iIntros "h"; iRight.
    - rewrite /interp_union.
      iIntros "[h | h]"; first by iApply hi0.
      by iApply hi1.
    - rewrite /interp_inter.
      by iIntros "[? _]".
    - rewrite /interp_inter.
      by iIntros "[_ ?]".
    - rewrite /interp_inter.
      iIntros "h".
      iSplit; first by iApply hi0.
      by iApply hi1.
    - done.
    - iIntros "h".
      iApply hi1.
  by iApply hi0.
  Qed.

  Theorem subtype_is_inclusion:
    ∀ A B, A <: B →
    ∀ v, interp_type A v -∗ interp_type B v.
  Proof.
    move => A B hAB v.
    rewrite !interp_type_unfold.
    by iApply subtype_is_inclusion_aux.
  Qed.

  (* heap models relation; the semantic heap does
     not appear because it is hidden in iProp  *)
  (* Helper defintion to state that fields are correctly modeled *)
  Definition heap_models_fields
    (iFs: gmapO string (laterO (sem_typeO Σ))) (vs: stringmap value) : iProp :=
    ⌜dom (gset string) vs ≡ dom _ iFs⌝ ∗
    ∀ f (iF: interp),
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

  Definition heap_models (h : heap) : iProp :=
    ∃ (sh: gmap loc (prodO tagO (gmapO string (laterO (sem_typeO Σ))))),
    own γ (gmap_view_auth (DfracOwn 1) sh) ∗ ⌜dom (gset loc) sh = dom _ h⌝ ∗
    □ ∀ (ℓ : loc) (t : tag) (vs : stringmap value),
    ⌜h !! ℓ = Some (t, vs)⌝ -∗
    ∃ (iFs : gmapO string (laterO (sem_typeO Σ))),
    sh !! ℓ ≡ Some (t, iFs) ∗ heap_models_fields iFs vs.

  Definition interp_local_tys
    (lty : local_tys) (le : local_env) : iProp :=
    (∀ v ty, ⌜lty !! v = Some ty⌝ -∗
    ∃ val, ⌜le !! v = Some val⌝ ∗ interp_type ty val)%I.

  Lemma interp_local_tys_is_inclusion lty rty le:
    lty <:< rty →
    interp_local_tys lty le -∗
    interp_local_tys rty le.
  Proof.
    move => hsub; iIntros "Hle" (v ty) "%Hv".
    apply hsub in Hv as (B & hB & hsubB).
    iDestruct ("Hle" $! v B hB) as (val) "[%Hv' #H]".
    iExists val; iSplitR; first done.
    by iApply subtype_is_inclusion.
  Qed.

  Lemma expr_adequacy e lty le ty val :
    expr_eval le e = Some val →
    expr_has_ty lty e ty →
    interp_local_tys lty le -∗
    interp_type ty val.
  Proof.
    move => he h; move: le val he.
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
      iApply subtype_is_inclusion; first by apply hsub.
      by iApply he.
  Qed.

  Lemma interp_local_tys_update v lty le ty val :
    interp_local_tys lty le -∗
    interp_type ty val -∗
    interp_local_tys (<[v:=ty]>lty) (<[v:=val]>le).
  Proof.
    iIntros "#Hi #?". iIntros (v' ty') "H".
    rewrite lookup_insert_Some.
    iDestruct "H" as %[[<- <-]|[??]].
    - iExists _. rewrite lookup_insert. by iSplit.
    - rewrite lookup_insert_ne; last done. by iApply "Hi".
  Qed.

  Lemma interp_local_tys_weaken_ty v A B lty lty' le:
    lty !! v = Some A →
    lty' !! v = Some B →
    (∀ w, v ≠ w → lty !! w = lty' !! w) →
    A <: B →
    interp_local_tys lty le -∗
    interp_local_tys lty' le.
  Proof.
    move => hin1 hin2 hs hAB; iIntros "H".
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

  Lemma interp_local_tys_subset_eq lty lty' le:
    lty' ⊆ lty →
    interp_local_tys lty le -∗
    interp_local_tys lty' le.
  Proof.
    move => hs; iIntros "H" (w ty) "%Hle".
    iSpecialize ("H" $! w ty).
    rewrite (lookup_weaken _ _ w ty Hle hs).
    iDestruct ("H" with "[//]") as (val) "[%hw H]".
    iExists val.
    by rewrite hw; iSplit.
  Qed.

  Lemma interp_local_tys_list lty le targs args vargs:
    dom stringset targs = dom stringset args →
    map_args (expr_eval le) args = Some vargs →
    (∀ (x : string) (ty : lang_ty) (arg : expr),
    targs !! x = Some ty →
    args !! x = Some arg →
    expr_has_ty lty arg ty) →
    interp_local_tys lty le -∗
    interp_local_tys targs vargs.
  Proof.
    move => hdom hargs helt.
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

  Lemma heap_models_lookup l h A vs t :
    h !! l = Some (t, vs) →
    heap_models h -∗
    interp_type (ClassT A) (LocV l) -∗
    ∃ fields, heap_models h ∗
    ⌜inherits t A ∧ has_fields t fields⌝ ∗
    ∀ f fty, ⌜fields !! f = Some fty⌝ → 
    ∃ v, ⌜vs !! f = Some v⌝ ∗
    ▷ interp_type fty v.
  Proof.
    move => hheap.
    iIntros "hmodels hl".
    rewrite interp_type_unfold /= /interp_class.
    iDestruct "hl" as (???) "[%H H◯]".
    destruct H as [[= <-] [hinherits hf]].
    iDestruct "hmodels" as (sh) "(H● & % & #Hh)".
    iDestruct (sem_heap_own_valid_2 with "H● H◯") as "#HΦ".
    iDestruct ("Hh" with "[//]") as (?) "[H H▷]".
    iRewrite "H" in "HΦ".
    rewrite option_equivI prod_equivI /=.
    iDestruct "HΦ" as "[%Ht HΦ]".
    fold_leibniz. rewrite Ht.
    iExists fields.
    iSplitL. { iExists _. iFrame. by iSplit. }
    iSplitR; first done.
    iIntros (f fty) "%hfield".
    iDestruct "H▷" as "[%hdf h]".
    rewrite gmap_equivI.
    iSpecialize ("HΦ" $! f).
    rewrite /interp_fields lookup_fmap hfield /=.
    iAssert (⌜is_Some (iFs !! f)⌝)%I as "%hiFs".
    { destruct (iFs !! f) eqn:hh; first done.
      by rewrite hh option_equivI.
    }
    destruct hiFs as [[iF] hIF].
    iDestruct ("h" $! f iF with "[]") as (v) "[%hv hl]"; first by rewrite hIF.
    iExists v; iSplitR; first done.
    rewrite hIF option_equivI later_equivI discrete_fun_equivI.
    iNext.
    iSpecialize ("HΦ" $! v).
    by iRewrite -"HΦ".
  Qed.

  Lemma heap_models_class l h A vs t :
    h !! l = Some (t, vs) →
    heap_models h -∗
    interp_type (ClassT A) (LocV l) -∗
    heap_models h ∗ interp_type (ClassT t) (LocV l).
  Proof.
    move => hheap.
    iIntros "hmodels hl".
    rewrite !interp_type_unfold /= /interp_class.
    iDestruct "hl" as (???) "[%H #H◯]".
    destruct H as [[= <-] [hinherits hf]].
    iDestruct "hmodels" as (sh) "(H● & % & #Hh)".
    iDestruct (sem_heap_own_valid_2 with "H● H◯") as "#HΦ".
    iDestruct ("Hh" with "[//]") as (?) "[H H▷]".
    iRewrite "H" in "HΦ".
    rewrite option_equivI prod_equivI /=.
    iDestruct "HΦ" as "[%Ht HΦ]".
    fold_leibniz; rewrite Ht.
    iSplitL.
    { iExists _; iFrame; by iSplit. }
    iExists l, t0, fields; by iSplitR.
  Qed.

  Lemma heap_models_fields_update iFs vs f v (Φ : interpO)
    `{∀ v, Persistent (Φ v)} :
    iFs !! f = Some (Next Φ) →
    heap_models_fields iFs vs -∗
    Φ v -∗
    heap_models_fields iFs (<[ f := v]>vs).
  Proof.
    move => hf.
    iIntros "hm hΦ".
    iDestruct "hm" as "[%hdom h]".
    rewrite /heap_models_fields.
    iSplitR.
    { iPureIntro.
      rewrite dom_insert_lookup //.
      by rewrite -elem_of_dom hdom elem_of_dom hf.
    }
    iIntros (f' iF) "hf".
    destruct (decide (f = f')) as [-> | hne].
    - rewrite lookup_insert.
      iExists v; iSplitR; first done.
      rewrite hf option_equivI later_equivI discrete_fun_equivI.
      iNext.
      iSpecialize ("hf" $! v).
      by iRewrite -"hf".
    - rewrite lookup_insert_ne //.
      by iApply "h".
  Qed.

  Lemma heap_models_update h l t t0 vs f v fty:
    wf_cdefs Δ →
    h !! l = Some (t, vs) →
    has_field f fty t0 →
    inherits t t0 →
    heap_models h -∗
    interp_type (ClassT t0) (LocV l) -∗
    interp_type fty v -∗
    heap_models (<[l:=(t, (<[f := v]>vs))]> h).
  Proof.
    move => wfΔ hheap hf hinherits.
    iIntros "hmodels #hl #hv".
    iDestruct "hmodels" as (sh) "[hown [%hdom #h]]".
    iExists sh.
    rewrite interp_type_unfold /= /interp_class.
    iDestruct "hl" as (?? fields) "[%H hsem]".
    destruct H as [[= <-] [ hinherits' hfields]].
    iDestruct (sem_heap_own_valid_2 with "hown hsem") as "#Hv".
    iSplitL; first by iFrame.
    iSplitR.
    { iPureIntro.
      by rewrite hdom dom_insert_lookup_L.
    }
    iModIntro.
    iIntros (ℓ t' vs') "%Heq".
    destruct (decide (l = ℓ)) as [-> | hne].
    - rewrite lookup_insert in Heq.
      injection Heq; intros <- <-; clear Heq.
      iAssert (t1 ≡ t)%I as "%Ht".
      { iSpecialize ("h" $! ℓ t vs with "[//]").
        iDestruct "h" as (iFs) "[hsh hmodels]".
        iRewrite "Hv" in "hsh".
        rewrite !option_equivI prod_equivI /=.
        by iDestruct "hsh" as "[? ?]".
      }
      iExists _; iSplitR.
      { replace t1 with t.
        by iRewrite "Hv".
      }
      iApply heap_models_fields_update; first by apply interp_type_persistent.
      + rewrite /interp_fields lookup_fmap.
        destruct (hfields f fty) as [h0 h1].
        rewrite h0; first by done.
        apply has_field_inherits with t0 => //.
        now apply wfΔ.
      + iSpecialize ("h" $! ℓ t vs with "[//]").
        iDestruct "h" as (iFs) "[hsh hmodels]".
        iRewrite "Hv" in "hsh".
        rewrite !option_equivI prod_equivI /=.
        iDestruct "hsh" as "[? h]".
        iApply heap_models_fields_ext_L; first by iRewrite "h".
        done.
      + done.
    - iApply "h".
      iPureIntro.
      by rewrite lookup_insert_ne // in Heq.
  Qed.

  Lemma interp_type_loc_inversion h le lty (v: string) l T t fields:
    h !! l = Some (t, fields) →
    le !! v = Some (LocV l) →
    interp_local_tys lty le -∗
    heap_models h -∗
    interp_type T (LocV l) -∗
    heap_models h ∗ interp_type (ClassT t) (LocV l).
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
      (* start of nonnull as part of mixed. TODO: factor outTODO: factor out class/nonnull *)
      iDestruct "H" as "[H | H]".
      { iDestruct "H" as (z) "%H"; discriminate. }
      iDestruct "H" as "[H | H]".
      { iDestruct "H" as (b) "%H"; discriminate. }
      iDestruct "H" as (cname) "H".
      iDestruct ((heap_models_class _ _ cname _ _ hl) with "[Hh //]") as "Hv".
      iApply "Hv".
      by rewrite interp_type_unfold.
    - move => cname v hv; iIntros "Hs Hh H".
      iDestruct ((heap_models_class _ _ cname _ _ hl) with "[Hh //]") as "Hv".
      iApply "Hv".
      by rewrite interp_type_unfold.
    - move => ??; iIntros "? ? H".
      iDestruct "H" as "%H"; discriminate.
    - move => v hv; iIntros "#Hs Hh H".
      iDestruct "H" as "[H | H]".
      { iDestruct "H" as (z) "%H"; discriminate. }
      iDestruct "H" as "[H | H]".
      { iDestruct "H" as (b) "%H"; discriminate. }
      iDestruct "H" as (cname) "H".
      iDestruct ((heap_models_class _ _ cname _ _ hl) with "[Hh //]") as "Hv".
      iApply "Hv".
      by rewrite interp_type_unfold.
    - move => S hS T hT v hv; iIntros "#Hs Hh H".
      iDestruct "H" as "[H | H]".
      + apply hS in hv.
        by iApply (hv with "Hs Hh H").
      + apply hT in hv.
        by iApply (hv with "Hs Hh H").
    - move => S hS T hT v hv; iIntros "#Hs Hh H".
      rewrite /interp_inter -!interp_type_unfold.
      iDestruct "H" as "[HS HT]".
      apply hS in hv.
      rewrite -!interp_type_unfold in hv.
      by iApply (hv with "Hs Hh HS").
  Qed.

  Lemma cmd_adequacy_ lty cmd lty' :
    wf_cdefs Δ →
    ⌜cmd_has_ty lty cmd lty'⌝ -∗
    ∀ st st' n, ⌜cmd_eval st cmd st' n⌝ -∗
    heap_models st.2 ∗ interp_local_tys lty st.1 -∗ |=▷^n
        heap_models st'.2 ∗ interp_local_tys lty' st'.1.
  Proof.
    move => wfΔ.
    iLöb as "IH" forall (lty cmd lty').
    iIntros "%hty" (st st' n) "%hc".
    move: st st' n hc.
    induction hty as [ lty | lty1 lty2 lty3 fstc sndc hfst hi1 hsnd hi2 |
        lty lhs e ty he | lty1 lty2 cond thn els hcond hthn hi1 hels hi2 |
        lty lhs recv t name fty hrecv hf |
        lty recv fld rhs fty t hrecv hrhs hf |
        lty lhs t args fields hf hdom harg |
        lty lhs recv t name mdef args hrecv hm hdom |
        lty c rty' rty hsub h hi |
        lty v tv t cmd hv h hi
        ] => st st' n hc.
    - inv hc.
      rewrite updN_zero.
      by iIntros "?".
    - inv hc.
      apply hi1 in H2; clear hi1.
      apply hi2 in H5; clear hi2.
      iIntros "H".
      iAssert(
        heap_models st.2 ∗ interp_local_tys lty1 st.1 -∗
        |=▷^n1 heap_models st2.2 ∗ interp_local_tys lty2 st2.1
      )%I as "H1"; first by apply H2.
      clear H2.
      iSpecialize ("H1" with "H").
      iAssert(
        heap_models st2.2 ∗ interp_local_tys lty2 st2.1 -∗
        |=▷^n2 heap_models st'.2 ∗ interp_local_tys lty3 st'.1
      )%I as "H2"; first by apply H5.
      clear H5.
      iAssert (
        (|=▷^n1 (heap_models st2.2 ∗ interp_local_tys lty2 st2.1)) -∗
        |=▷^n1 (|=▷^n2 heap_models st'.2 ∗ interp_local_tys lty3 st'.1)
      )%I as "H2'"; first by iApply updN_mono_I.
      rewrite Nat_iter_add.
      by iApply "H2'".
    - inv hc.
      iIntros "[? #Hle]".
      rewrite updN_zero. iFrame.
      iDestruct (expr_adequacy with "Hle") as "#?"; try done.
      by iApply interp_local_tys_update.
    - iIntros "H".
      inv hc.
      + apply hi1 in H6; clear hi1 hi2.
        iAssert (
          heap_models st.2 ∗ interp_local_tys lty1 st.1 -∗
          |=▷^n heap_models st'.2 ∗ interp_local_tys lty2 st'.1
        )%I as "H1"; first by apply H6.
        clear H6.
        by iApply "H1".
      + apply hi2 in H6; clear hi1 hi2.
        iAssert (
          heap_models st.2 ∗ interp_local_tys lty1 st.1 -∗
          |=▷^n heap_models st'.2 ∗ interp_local_tys lty2 st'.1
        )%I as "H1"; first by apply H6.
        clear H6.
        by iApply "H1".
    - inv hc.
      iIntros "[Hh #Hle]". simpl.
      iModIntro. (* keep the later *)
      iDestruct (expr_adequacy with "Hle") as "#He"; try done.
      iDestruct (heap_models_lookup with "Hh He") as (fields) "(Hh&Ht&Hv)"; first done.
      iDestruct "Ht" as %[? ?].
      rewrite bi.later_sep.
      iSplitL "Hh"; first done.
      assert (hfield: fields !! name = Some fty).
      { apply has_fields_inherits_lookup with t0 t => //.
        by apply wfΔ.
      }
      iDestruct ("Hv" $! name fty hfield) as (w) "[%hw hi]".
      rewrite H7 in hw; case: hw => ->.
      iNext. by iApply interp_local_tys_update.
    - inv hc.
      iIntros "[Hh #Hle]" => /=.
      iSplitL; last done.
      iDestruct (expr_adequacy recv with "Hle") as "#Hrecv" => //.
      iDestruct (expr_adequacy rhs with "Hle") as "#Hrhs" => //.
      iDestruct (heap_models_lookup with "Hh Hrecv") as (fields) "(Hh&Ht&?)"; first done.
      iDestruct "Ht" as %[? ?].
      by iApply (heap_models_update with "Hh").
    - inv hc; simpl.
      iIntros "[Hh #Hle]".
      (* we need one modality to update the
         semantic heap *)
      iDestruct "Hh" as (sh) "(H●&Hdom&#Hh)".
      iDestruct "Hdom" as %Hdom.
      assert (hnew: sh !! new = None).
      { apply (not_elem_of_dom (D:=gset loc)).
        by rewrite Hdom not_elem_of_dom.
      }
      iMod ((sem_heap_own_update new) with "H●") as "[H● H◯]" => //.
      {
        (* TODO *)
        rewrite loc_mapsto_eq /loc_mapsto_def.
        by apply (gmap_view_alloc _ new DfracDiscarded
          (t, interp_fields interp_type fields)).
      }
      iIntros "!> !>".
      (* TODO *)
      rewrite loc_mapsto_eq /loc_mapsto_def.
      iDestruct "H◯" as "#H◯".
      iAssert (interp_type (ClassT t) (LocV new))
      with "[]" as "#Hl".
      { rewrite interp_type_unfold /=.
        iExists _, _, _.
        iSplit; first done.
        (* TODO *)
        by rewrite mapsto_eq /mapsto_def.
      }
      iSplitL; last first.
      by iApply interp_local_tys_update.
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
          by rewrite dom_interp_fields H6 -hdom.
        }
        iIntros (f iF) "hiF".
        iAssert (⌜f ∈ dom stringset fields⌝)%I as "%hfield".
        {
          rewrite -dom_interp_fields elem_of_dom.
          rewrite /interp_fields.
          rewrite !lookup_fmap.
          by iRewrite "hiF".
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
        assert (hty0: expr_has_ty lty a0 fty) by (by apply harg with f).
        rewrite hty /= option_equivI later_equivI.
        iNext.
        rewrite discrete_fun_equivI.
        iSpecialize ("hiF" $! v0).
        iRewrite -"hiF".
        by iDestruct (expr_adequacy a0 with "Hle") as "#Ha0".
      + rewrite lookup_insert_ne; last done.
        by iApply "Hh".
    - iIntros "[Hh #Hle]".
      inv hc; simpl in *.
      assert (wfbody: ∃B, wf_mdef_ty B mdef0 ∧ inherits t0 B).
      { destruct wfΔ as [? ? hbodies].
        rewrite map_Forall_lookup in hbodies.
        apply has_method_from in H8.
        destruct H8 as (B & cdef & hB & heq & hin).
        apply hbodies in hB.
        rewrite map_Forall_lookup in hB.
        apply hB in heq.
        exists B; split; first done.
        by eapply rtc_transitive.
      }
      destruct wfbody as (B & wfbody & hinherits).
      destruct wfbody as (lty_body & hbody & hret).
      iAssert(⌜inherits t0 t⌝ ∗ interp_type (ClassT B) (LocV l))%I as "#Hl".
      { iDestruct (expr_adequacy recv with "Hle") as "#Hrecv" => //.
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
        split; first by rewrite -Ht.
        done.
      }
      iDestruct "Hl" as "[%Hinherits #Hl]".
      assert (hincl: mdef_incl mdef0 mdef).
      {
        eapply has_method_inherits in Hinherits; [ | by apply wfΔ | done ].
        destruct Hinherits as [? [? ?]].
        replace x with mdef0 in * by (by eapply has_method_fun).
        done.
      }
      iModIntro; iNext.
      iSpecialize ("IH" $! _ _ _ hbody  _ _ _ H12); simpl.
      iDestruct ("IH" with "[Hh Hle]") as "H".
      { iFrame.
        iApply interp_local_tys_update => //.
        iApply interp_local_tys_list => //;
        first by (destruct hincl as [? _]; by rewrite -hdom).
        move => x ty arg hx harg.
        destruct hincl as [hdom' [hincl _]].
        destruct (methodargs mdef !! x) as [ty' | ] eqn:hty'.
        { apply (H _ _ _ hty') in harg.
          econstructor; first by apply harg.
          by eapply hincl.
        }
        apply mk_is_Some in hx.
        apply elem_of_dom in hx.
        rewrite hdom' in hx.
        apply elem_of_dom in hx.
        rewrite hty' in hx.
        by elim: hx.
      }
      iRevert "H".
      iApply updN_mono_I.
      iIntros "[Hh Hle2]"; iFrame.
      iApply interp_local_tys_update; first by done.
      destruct hincl as [? [? hret']].
      iApply subtype_is_inclusion; first by apply hret'.
      by iDestruct (expr_adequacy (methodret mdef0) with "Hle2") as "#Hret".
    - apply hi in hc; clear hi.
      iAssert(
        heap_models st.2 ∗ interp_local_tys lty st.1 -∗
        |=▷^n heap_models st'.2 ∗ interp_local_tys rty st'.1
      )%I as "HC"; first by apply hc.
      iClear "IH".
      clear hc.
      iIntros "H".
      iSpecialize ("HC" with "H").
      iRevert "HC".
      iApply updN_mono_I.
      iIntros "[Hh #Hrty]".
      iFrame.
      iDestruct (interp_local_tys_is_inclusion with "Hrty") as "Hrty'"; first done.
      by iApply "Hrty'".
    - inv hc.
      + apply hi in H6; clear hi.
        iAssert (
          heap_models st.2 ∗
          interp_local_tys (<[v:=InterT tv (ClassT t)]> lty) st.1 -∗
          |=▷^n heap_models st'.2 ∗ interp_local_tys lty st'.1
        )%I as "HC"; first by apply H6.
        iClear "IH".
        clear H6.
        destruct H5 as (l & hl & t' & fields & hlt & hinherits).
        iIntros "[H #Hle]".
        iApply "HC"; iClear "HC".
        iDestruct ("Hle" $! v with "[//]") as (?) "[%Hlev Hv]".
        rewrite Hlev in hl; simplify_eq.
        iAssert(heap_models st.2 ∗ interp_type (ClassT t') (LocV l))%I with "[H]" as "[H #Hinv]";
        first by (iApply (interp_type_loc_inversion with "Hle H Hv")).
        iFrame.
        iIntros (w tw).
        rewrite lookup_insert_Some.
        iIntros "%Hw".
        destruct Hw as [[<- <-] | [hne hw]].
        { iExists (LocV l); rewrite Hlev; iSplitR; first done.
          rewrite !interp_type_unfold /= /interp_inter; iSplit; first done.
          by iApply inherits_is_inclusion.
        }
        by iApply "Hle".
      + by iApply updN_intro.
  Qed.

  Lemma cmd_adequacy lty cmd lty' :
    wf_cdefs Δ →
    cmd_has_ty lty cmd lty' →
    ∀ st st' n, cmd_eval st cmd st' n →
    heap_models st.2 ∗ interp_local_tys lty st.1 -∗ |=▷^n
        heap_models st'.2 ∗ interp_local_tys lty' st'.1.
  Proof.
    move => ? hty ??? hc.
    iApply cmd_adequacy_.
    done.
    by iPureIntro.
    by iPureIntro.
  Qed.

End proofs.

Print Assumptions cmd_adequacy.

Lemma sem_heap_init
  `{PDC: ProgDefContext}
  `{!sem_heapGpreS Σ}:
  ⊢@{iPropI Σ} |==> ∃ _: sem_heapGS Σ, (heap_models ∅ ∗ interp_local_tys ∅ ∅).
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
