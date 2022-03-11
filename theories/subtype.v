(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 * 
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
From stdpp Require Import base strings gmap stringmap fin_maps.
(* Not using iris but importing their ssreflect dependencies *)
From iris.proofmode Require Import tactics.
From shack Require Import lang progdef.

Section Subtype.
  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.

  (* Type well-formdness is mostly introduced to be able to define
   * subtyping rule correctly, like unions.
   *)
  Inductive subtype : lang_ty → lang_ty → Prop :=
    | SubMixed : ∀ ty, subtype ty MixedT
    | SubNothing : ∀ ty, wf_ty ty → subtype NothingT ty
    | SubClass : ∀ A σA B σB adef,
        Δ !! A = Some adef →
        length σA = length (adef.(generics)) →
        extends_using A B σB →
        subtype (ClassT A σA) (ClassT B (subst_ty σA <$> σB))
    | SubVariance : ∀ A adef σ0 σ1,
        Δ !! A = Some adef →
        Forall wf_ty σ1 →
        subtype_targs adef.(generics) σ0 σ1 →
        subtype (ClassT A σ0) (ClassT A σ1)
    | SubMixed2: subtype MixedT (UnionT NonNullT NullT)
    | SubIntNonNull: subtype IntT NonNullT
    | SubBoolNonNull: subtype BoolT NonNullT
    | SubClassNonNull: ∀ A targs, subtype (ClassT A targs) NonNullT
    | SubUnionUpper1 : ∀ s t, wf_ty t → subtype s (UnionT s t)
    | SubUnionUpper2 : ∀ s t, wf_ty s → subtype t (UnionT s t)
        (* TODO: Do we need this one ? *)
    | SubUnionLeast : ∀ s t u, subtype s u → subtype t u → subtype (UnionT s t) u
    | SubInterLower1 : ∀ s t, subtype (InterT s t) s
    | SubInterLower2 : ∀ s t, subtype (InterT s t) t
    | SubInterGreatest: ∀ s t u, subtype u s → subtype u t → subtype u (InterT s t)
    | SubRefl: ∀ s, subtype s s
    | SubTrans : ∀ s t u, subtype s t → subtype t u → subtype s u
 with subtype_targs : list variance → list lang_ty → list lang_ty → Prop :=
    | subtype_targs_nil : subtype_targs [] [] []
    | subtype_targs_invariant : ∀ ty0 ty1 vs ty0s ty1s,
        subtype ty0 ty1 →
        subtype ty1 ty0 →
        subtype_targs vs ty0s ty1s →
        subtype_targs (Invariant :: vs) (ty0 :: ty0s) ( ty1 :: ty1s)
    | subtype_targs_covariant : ∀ ty0 ty1 vs ty0s ty1s,
        subtype ty0 ty1 →
        subtype_targs vs ty0s ty1s →
        subtype_targs (Covariant :: vs) (ty0 :: ty0s) ( ty1 :: ty1s)
    | subtype_targs_contravariant : ∀ ty0 ty1 vs ty0s ty1s,
        subtype ty1 ty0 →
        subtype_targs vs ty0s ty1s →
        subtype_targs (Contravariant :: vs) (ty0 :: ty0s) ( ty1 :: ty1s)
  .
 
  Corollary length_subtype_targs_v0: ∀ vs ty0s ty1s,
    subtype_targs vs ty0s ty1s → length vs = length ty0s.
  Proof.
    induction 1 as [ | ??????? h hi | ?????? h hi | ?????? h hi] => //=; by rewrite hi.
  Qed.

  Corollary length_subtype_targs_v1: ∀ vs ty0s ty1s,
    subtype_targs vs ty0s ty1s → length vs = length ty1s.
  Proof.
    induction 1 as [ | ??????? h hi | ?????? h hi | ?????? h hi] => //=; by rewrite hi.
  Qed.

  Corollary length_subtype_targs_01: ∀ vs ty0s ty1s,
    subtype_targs vs ty0s ty1s → length ty0s = length ty1s.
  Proof.
    induction 1 as [ | ??????? h hi | ?????? h hi | ?????? h hi] => //=; by rewrite hi.
  Qed.

  Hint Constructors subtype : core.
  Hint Constructors subtype_targs : core.

  Notation "s <: t" := (subtype s t) (at level 70, no associativity).
  Notation "lts <: vs :> rts" := (subtype_targs vs lts rts) (at level 70, vs at next level).

  Lemma subtype_targs_refl vs: ∀ σ,
    length vs = length σ → σ <:vs:> σ.
  Proof.
    induction vs as [ | v vs hi] => σ hLen.
    - by rewrite (nil_length_inv σ).
    - destruct σ as [ | ty σ]; first by discriminate hLen.
      case : hLen => hLen.
      apply hi in hLen.
      destruct v; by constructor.
  Qed.

  Lemma neg_subtype_targs vs σ0 σ1 :
    σ0 <:vs:> σ1 → σ1 <:(neg_variance <$> vs):> σ0.
  Proof.
    induction 1 as [ | ??????? h hi | ?????? h hi | ?????? h hi] => //=.
    - by constructor.
    - by constructor.
    - by constructor.
  Qed.

  (* See Andrew Kennedy's paper:
     Variance and Generalized Constraints for C♯ Generics
  *)
  Inductive mono : list variance → lang_ty → Prop :=
    | MonoInt vs : mono vs IntT
    | MonoBool vs : mono vs BoolT
    | MonoNothing vs : mono vs NothingT
    | MonoMixed vs : mono vs MixedT
    | MonoNull vs : mono vs NullT
    | MonoNonNull vs : mono vs NonNullT
    | MonoUnion vs s t : mono vs s → mono vs t → mono vs (UnionT s t)
    | MonoInter vs s t : mono vs s → mono vs t → mono vs (InterT s t)
    | MonoVInvGen vs n: vs !! n = Some Invariant → mono vs (GenT n)
    | MonoVCoGen vs n: vs !! n = Some Covariant → mono vs (GenT n)
    | MonoGen vs n: vs !! n = None → mono vs (GenT n)
    | MonoEx vs cname: mono vs (ExT cname)
    | MonoClass vs cname cdef targs:
        Δ !! cname = Some cdef →
        (∀ i wi ti, cdef.(generics) !! i = Some wi →
                    targs !! i = Some ti →
                    not_contra wi →
                    mono vs ti) →
        (∀ i wi ti, cdef.(generics) !! i = Some wi →
                    targs !! i = Some ti →
                    not_cov wi →
                    mono (neg_variance <$> vs) ti) →
        mono vs (ClassT cname targs)
  .

  Definition wf_cdef_mono cdef : Prop :=
    match cdef.(superclass) with
    | None => True
    | Some (parent, σ) =>
        mono cdef.(generics) (ClassT parent σ)
    end
  .

  Definition wf_mdef_mono vs mdef : Prop :=
    map_Forall (λ _argname, mono (neg_variance <$> vs)) mdef.(methodargs) ∧
    mono vs mdef.(methodrettype).

  Definition wf_cdef_methods_mono cdef : Prop :=
    map_Forall (λ _mname, wf_mdef_mono cdef.(generics)) cdef.(classmethods)
  .

  Definition invariant vs ty :=
    mono vs ty ∧ mono (neg_variance <$> vs) ty.

  Definition field_mono vs (vfty: visibility * lang_ty) :=
    let (vis, fty) := vfty in
    match vis with
    | Public => invariant vs fty
    | Private => True
    end.

  Definition wf_field_mono cdef :=
    map_Forall (λ _fname, field_mono cdef.(generics)) cdef.(classfields).

  Lemma mono_subst vs ty:
    mono vs ty →
    bounded (length vs) ty →
    ∀ ws σ,
    length vs = length σ →
    (∀ i vi ti, vs !! i = Some vi → σ !! i = Some ti →
      not_cov vi → mono (neg_variance <$> ws) ti) →
    (∀ i vi ti, vs !! i = Some vi → σ !! i = Some ti →
      not_contra vi → mono ws ti) →
    mono ws (subst_ty σ ty).
  Proof.
    induction 1 as [ vs | vs | vs | vs | vs | vs | vs s t hs his ht hit
      | vs s t hs his ht hit | vs n hinv | vs n hco | vs n hnone
      | vs cname | vs cname cdef targs hΔ hcov hicov hcontra hicontra ]
      => hb ws σ hlen h0 h1 //=; try by constructor.
    - inv hb.
      constructor.
      + eapply his; by eauto.
      + eapply hit; by eauto.
    - inv hb.
      constructor.
      + eapply his; by eauto.
      + eapply hit; by eauto.
    - destruct (σ !! n) as [ty | ] eqn:hty => //=.
      + by eapply h1.
      + apply lookup_lt_Some in hinv.
        rewrite hlen in hinv.
        apply lookup_lt_is_Some_2 in hinv.
        rewrite hty in hinv.
        by elim hinv.
    - destruct (σ !! n) as [ty | ] eqn:hty => //=.
      + by eapply h1.
      + apply lookup_lt_Some in hco.
        rewrite hlen in hco.
        apply lookup_lt_is_Some_2 in hco.
        rewrite hty in hco.
        by elim hco.
    - inv hb.
      apply lookup_lt_is_Some_2 in H0.
      rewrite hnone in H0.
      by elim H0.
    - inv hb.
      econstructor; first done.
      + move => i ci ti hci hi hc.
        apply list_lookup_fmap_inv in hi as [ty [-> hi]].
        eapply hicov => //.
        rewrite Forall_forall in H0.
        apply H0.
        by apply elem_of_list_lookup_2 in hi.
      + move => i ci ti hci hi hc.
        apply list_lookup_fmap_inv in hi as [ty [-> hi]].
        eapply hicontra => //.
        * rewrite Forall_forall in H0.
          rewrite map_length.
          apply H0.
          by apply elem_of_list_lookup_2 in hi.
        * by rewrite map_length.
        * move => j vj tj hj htj hcj.
          apply list_lookup_fmap_inv in hj as [vj' [-> hj]].
          rewrite neg_variance_fmap_idem.
          eapply h1 => //.
          by destruct vj'.
        * move => j vj tj hj htj hcj.
          apply list_lookup_fmap_inv in hj as [vj' [-> hj]].
          eapply h0 => //.
          by destruct vj'.
  Qed.

  Lemma extends_using_mono A B σ :
    map_Forall (λ _cname, wf_cdef_mono) Δ →
    extends_using A B σ →
    ∀ def, Δ !! A = Some def →
    mono def.(generics) (ClassT B σ).
  Proof.
    move => hmono h def hdef.
    inv h; simplify_eq.
    apply hmono in hdef.
    by rewrite /wf_cdef_mono H0 in hdef.
  Qed.

  Lemma inherits_using_mono A B σ :
    map_Forall (λ _ : string, wf_cdef_parent Δ) Δ →
    map_Forall (λ _cname, wf_cdef_mono) Δ →
    inherits_using A B σ →
    ∀ def, Δ !! A = Some def →
    mono def.(generics) (ClassT B σ).
  Proof.
    move => ? hmono.
    induction 1 as [A adef h | A B σ h | A B σ C σC hext h hi ] => def hdef.
    - simplify_eq.
      econstructor => //.
      + move => i wi ti hgi /lookup_gen_targs -> hc.
        destruct wi; by constructor.
      + move => i wi ti hgi /lookup_gen_targs -> hc.
        destruct wi => //.
        * apply MonoVInvGen.
          by rewrite list_lookup_fmap hgi.
        * apply MonoVCoGen.
          by rewrite list_lookup_fmap hgi.
    - by apply extends_using_mono with (def := def) in h.
    - apply inherits_using_wf in h => //.
      destruct h as (bdef & cdef & hb & hc & hF & hL & hwf).
      assert (hb' := hb).
      assert (hext' := hext).
      apply hi in hb'.
      apply extends_using_mono with (def := def) in hext' => //.
      inv hext'.
      simplify_eq.
      change (ClassT C (subst_ty σ <$> σC)) with (subst_ty σ (ClassT C σC)).
      apply mono_subst with (generics bdef) => //.
      + by constructor.
      + apply extends_using_wf in hext => //.
        repeat destruct hext as [? hext].
        by simplify_eq.
  Qed.

  Lemma has_field_mono f t vis ty orig:
    map_Forall (λ _cname, wf_field_mono) Δ →
    map_Forall (λ _cname, wf_cdef_mono) Δ →
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
    has_field f t vis ty orig →
    ∃ def, Δ !! t = Some def ∧
    match vis with
    | Public => invariant def.(generics) ty
    | Private => True
    end.
  Proof.
    move => hwfΔ hmono hp hfb.
    induction 1 as [ tag cdef [vis typ] hΔ hf
      | tag targs parent cdef vis typ orig hΔ hf hs h hi ].
      - exists cdef; split => //.
        apply hwfΔ in hΔ.
        by apply hΔ in hf.
      - destruct hi as [def [hdef hvis]].
        exists cdef; split => //.
        destruct vis; last done.
        destruct hvis as [h0 h1].
        assert (htag := hΔ).
        apply hp in htag.
        rewrite /wf_cdef_parent hs in htag.
        destruct htag as (? & ? & hlen & hwf & hb); simplify_eq.
        apply has_field_bounded in h => //.
        destruct h as (? & ? & hbt).
        assert (htag := hΔ).
        apply hmono in htag.
        rewrite /wf_cdef_mono hs in htag.
        inv htag.
        simplify_eq.
        split.
        + by apply mono_subst with (generics x).
        + apply mono_subst with (neg_variance <$> generics x) => //.
          * by rewrite map_length.
          * by rewrite map_length.
          * rewrite !neg_variance_fmap_idem.
            move => i vi ti hvi hti hc.
            apply list_lookup_fmap_inv in hvi.
            destruct hvi as [wi [-> hwi]].
            eapply H4 => //.
            by destruct wi.
          * move => i vi ti hvi hti hc.
            apply list_lookup_fmap_inv in hvi.
            destruct hvi as [wi [-> hwi]].
            eapply H5 => //.
            by destruct wi.
  Qed.

  Definition check_variance v ty0 ty1 :=
    match v with
    | Invariant => (ty0 <: ty1) ∧ (ty1 <: ty0)
    | Covariant => ty0 <: ty1
    | Contravariant => ty1 <: ty0
    end.

  Lemma subtype_targs_lookup_0 vs σ0 σ1:
    σ0 <:vs:> σ1 →
    ∀ k ty0, σ0 !! k = Some ty0 →
    ∃ v ty1, vs !! k = Some v ∧ σ1 !! k = Some ty1 ∧
    check_variance v ty0 ty1.
  Proof.
    induction 1 as [ | ????? h0 h1 h hi | ????? h0 h hi | ????? h0 h hi] => k tk.
    - by rewrite lookup_nil.
    - destruct k as [ | k] => //=.
      + case => <-; clear tk.
        exists Invariant, ty1; by repeat split.
      + move => hk.
        apply hi in hk as (v & t2 & -> & -> & hv).
        exists v, t2; by repeat split.
    - destruct k as [ | k] => //=.
      + case => <-; clear tk.
        exists Covariant, ty1; by repeat split.
      + move => hk.
        apply hi in hk as (v & t2 & -> & -> & hv).
        exists v, t2; by repeat split.
    - destruct k as [ | k] => //=.
      + case => <-; clear tk.
        exists Contravariant, ty1; by repeat split.
      + move => hk.
        apply hi in hk as (v & t2 & -> & -> & hv).
        exists v, t2; by repeat split.
  Qed.

  Lemma subtype_targs_lookup_1 vs σ0 σ1:
    σ0 <:vs:> σ1 →
    ∀ k ty1, σ1 !! k = Some ty1 →
    ∃ v ty0, vs !! k = Some v ∧ σ0 !! k = Some ty0 ∧
    check_variance v ty0 ty1.
  Proof.
    move => hsub k ty1 h1.
    destruct (σ0 !! k) as [ty0 | ] eqn:h0; last first.
    { apply length_subtype_targs_01 in hsub.
      apply mk_is_Some in h1.
      apply lookup_lt_is_Some_1 in h1.
      rewrite -hsub in h1.
      apply lookup_lt_is_Some_2 in h1.
      rewrite h0 in h1.
      by elim h1.
    }
    apply subtype_targs_lookup_0 with (k := k) (ty0 := ty0) in hsub => //.
    destruct hsub as (v & ty1' & hv & ? & h); simplify_eq.
    exists v, ty0.
    by repeat split.
  Qed.

  Lemma subtype_targs_lookup_v vs σ0 σ1:
    σ0 <:vs:> σ1 →
    ∀ k v, vs !! k = Some v →
    ∃ ty0 ty1, σ0 !! k = Some ty0 ∧ σ1 !! k = Some ty1 ∧
    check_variance v ty0 ty1.
  Proof.
    move => hsub k v hv.
    destruct (σ0 !! k) as [ty0 | ] eqn:h0; last first.
    { apply length_subtype_targs_v0 in hsub.
      apply mk_is_Some in hv.
      apply lookup_lt_is_Some_1 in hv.
      rewrite hsub in hv.
      apply lookup_lt_is_Some_2 in hv.
      rewrite h0 in hv.
      by elim hv.
    }
    apply subtype_targs_lookup_0 with (k := k) (ty0 := ty0) in hsub => //.
    destruct hsub as (v' & ty1 & ? & ? & h); simplify_eq.
    exists ty0, ty1.
    by repeat split.
  Qed.
      
  Lemma subtype_targs_forall vs σ0 σ1:
    length σ0 = length vs →
    length σ1 = length vs →
    (∀ k v ty0 ty1,
         vs !! k = Some v → σ0 !! k = Some ty0 → σ1 !! k = Some ty1 → 
         check_variance v ty0 ty1) →
    σ0 <:vs:> σ1.
  Proof.
    move : σ0 σ1.
    induction vs as [ | v vs hi] => σ0 σ1 h0 h1 h.
    - apply nil_length_inv in h0.
      apply nil_length_inv in h1.
      by rewrite h0 h1.
    - destruct σ0 as [ | ty0 σ0]; first by discriminate h0.
      destruct σ1 as [ | ty1 σ1]; first by discriminate h1.
      case : h0 => h0.
      case : h1 => h1.
      destruct v.
      + constructor.
        * by apply (h 0 Invariant ty0 ty1).
        * by apply (h 0 Invariant ty0 ty1).
        * apply hi => //.
          move => k v ty2 ty3 hv h2 h3.
          by apply (h (S k) v ty2 ty3).
      + constructor.
        * by apply (h 0 Covariant ty0 ty1).
        * apply hi => //.
          move => k v ty2 ty3 hv h2 h3.
          by apply (h (S k) v ty2 ty3).
      + constructor.
        * by apply (h 0 Contravariant ty0 ty1).
        * apply hi => //.
          move => k v ty2 ty3 hv h2 h3.
          by apply (h (S k) v ty2 ty3).
  Qed.

  Lemma subtype_targs_cons v t0 t1 vs σ0 σ1:
    check_variance v t0 t1 →
    σ0 <:vs:> σ1 →
    (t0::σ0) <:(v::vs):> (t1::σ1).
  Proof.
    rewrite /check_variance => hc hs.
    destruct v; constructor => //.
    - by destruct hc.
    - by destruct hc.
  Qed.

  Lemma subtype_wf A B:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    wf_ty A → A <: B → wf_ty B.
  Proof.
    move => hp hwf.
    induction 1 as [ ty | ty h | A σA B σB adef hΔ hA hext
      | A adef σ0 σ1 hΔ hwfσ hσ | | | | A args | s t h
      | s t h | s t u hs his ht hit | s t | s t | s t u hs his ht hit | s
      | s t u hst hist htu hitu ] => //=; try (by constructor).
    - inv hext; simplify_eq.
      rewrite /map_Forall_lookup in hp.
      apply hp in hΔ.
      rewrite /wf_cdef_parent H0 in hΔ.
      destruct hΔ as (bdef & hB & hL & hσB & hb).
      econstructor; first done.
      + by rewrite map_length.
      + move => k ty.
        rewrite list_lookup_fmap.
        destruct (σB !! k) as [ tyk | ] eqn:hty => //=.
        case => <-.
        apply wf_ty_subst; first by apply wf_ty_class_inv in hwf.
        rewrite Forall_forall in hσB.
        apply elem_of_list_lookup_2 in hty.
        by apply hσB in hty.
    - apply length_subtype_targs_v1 in hσ.
      inv hwf; simplify_eq; econstructor.
      + exact hΔ.
      + by rewrite hσ.
      + rewrite Forall_forall in hwfσ => k ty hty.
        apply elem_of_list_lookup_2 in hty.
        by apply hwfσ in hty.
    - inv hwf; by eauto.
    - inv hwf; by eauto.
    - inv hwf; by eauto.
    - constructor; by eauto.
    - by eauto.
  Qed.

  Lemma subtype_subst A B:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    A <: B → ∀ σ,
    Forall wf_ty σ →
    (subst_ty σ A) <: (subst_ty σ B)
  with subtype_targs_subst vs As Bs:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    As <:vs:> Bs → ∀ σ,
    Forall wf_ty σ →
    (subst_ty σ <$> As) <:vs:> (subst_ty σ <$> Bs).
  Proof.
    - move => hp.
      destruct 1 as [ ty | ty h | A σA B σB adef hΔ hA hext
      | A adef σ0 σ1 hΔ hwfσ hσ01 | | | | A args
      | s t h | s t h | s t u hs ht | s t | s t | s t u hs ht | s
      | s t u hst htu ] => σ hσ => /=; try (by constructor).
      + constructor.
        by apply wf_ty_subst.
      + rewrite map_subst_ty_subst.
        * econstructor; [exact hΔ | | by assumption].
          by rewrite map_length.
        * apply extends_using_wf in hext; last done.
          destruct hext as (? & bdef & ? & hB & hF & hL).
          simplify_eq.
          by rewrite hA.
      + eapply SubVariance.
        * exact hΔ.
        * rewrite Forall_forall => ty /elem_of_list_fmap [ty' [-> hin]].
          apply wf_ty_subst => //.
          rewrite Forall_forall in hwfσ; by apply hwfσ in hin.
        * apply subtype_targs_subst; by assumption.
      + constructor.
        by apply wf_ty_subst.
      + constructor.
        by apply wf_ty_subst.
      + constructor; by apply subtype_subst.
      + constructor; by apply subtype_subst.
      + econstructor; by apply subtype_subst.
    - move => hp.
      destruct 1 as [ | ????? h0 h1 h | ????? h0 h | ????? h0 h] => σ hσ /=.
      + by constructor.
      + constructor.
        * by apply subtype_subst.
        * by apply subtype_subst.
        * by apply subtype_targs_subst.
      + constructor.
        * by apply subtype_subst.
        * by apply subtype_targs_subst.
      + constructor.
        * by apply subtype_subst.
        * by apply subtype_targs_subst.
  Qed.

  Lemma subtype_subst_class A B σA σB:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    ClassT A σA <: ClassT B σB → ∀ σ,
    Forall wf_ty σ →
    ClassT A (subst_ty σ <$> σA) <: ClassT B (subst_ty σ <$> σB).
  Proof.
    move => ? hsub σ h.
    by apply subtype_subst with (σ := σ) in hsub.
  Qed.

  Lemma subtype_lift vs ty :
    mono vs ty →
    ∀ σ0 σ1,
    wf_ty ty →
    Forall wf_ty σ0 →
    Forall wf_ty σ1 →
    σ0 <:vs:> σ1 →
    subst_ty σ0 ty <: subst_ty σ1 ty.
  Proof.
    induction 1 as [ vs | vs | vs | vs | vs | vs
      | vs s t hs his ht hit
      | vs s t hs his ht hit
      | vs n hinv | vs n hco | vs n hnone | vs cname
      | vs cname cdef targs hΔ hcov hicov hcontra hicontra ] => σ0 σ1 hwf hwf0 hwf1 hsub //=.
    - inv hwf.
      constructor.
      + econstructor; first by eapply his.
        econstructor.
        by apply wf_ty_subst.
      + econstructor; first by eapply hit.
        econstructor.
        by apply wf_ty_subst.
    - inv hwf.
      constructor.
      + eapply SubTrans with (subst_ty σ0 s); last by eapply his.
        by constructor.
      + eapply SubTrans with (subst_ty σ0 t); last by eapply hit.
        by constructor.
    - apply subtype_targs_lookup_v with (k := n) (v := Invariant) in hsub => //.
      by destruct hsub as (ty0 & ty1 & -> & -> & h0 & h1).
    - apply subtype_targs_lookup_v with (k := n) (v := Covariant) in hsub => //.
      by destruct hsub as (ty0 & ty1 & -> & -> & h).
    - destruct (σ0 !! n) as [? | ] eqn:h0.
      { apply length_subtype_targs_v0 in hsub.
        apply mk_is_Some in h0.
        apply lookup_lt_is_Some_1 in h0.
        rewrite -hsub in h0.
        apply lookup_lt_is_Some_2 in h0.
        rewrite hnone in h0.
        by elim h0.
      }
      destruct (σ1 !! n) as [? | ] eqn:h1.
      { apply length_subtype_targs_v1 in hsub.
        apply mk_is_Some in h1.
        apply lookup_lt_is_Some_1 in h1.
        rewrite -hsub in h1.
        apply lookup_lt_is_Some_2 in h1.
        rewrite hnone in h1.
        by elim h1.
      }
      done.
    - assert (hwftargs : Forall wf_ty targs) by (by apply wf_ty_class_inv in hwf).
      apply SubVariance with cdef => //; first by apply wf_ty_subst_map.
      apply subtype_targs_forall.
      + rewrite map_length.
        inv hwf; by simplify_eq.
      + rewrite map_length.
        inv hwf; by simplify_eq.
      + move => k v ty0 ty1 hk h0 h1.
        apply list_lookup_fmap_inv in h0.
        destruct h0 as [t0' [-> h0]].
        apply list_lookup_fmap_inv in h1.
        destruct h1 as [t1' [-> h1]].
        simplify_eq.
        destruct v; first split.
        * eapply hicov => //.
          rewrite Forall_forall in hwftargs.
          apply hwftargs.
          by apply elem_of_list_lookup_2 in h0.
        * eapply hicontra => //.
          rewrite Forall_forall in hwftargs.
          apply hwftargs.
          by apply elem_of_list_lookup_2 in h0.
          by apply neg_subtype_targs.
        * eapply hicov => //.
          rewrite Forall_forall in hwftargs.
          apply hwftargs.
          by apply elem_of_list_lookup_2 in h0.
        * eapply hicontra => //.
          rewrite Forall_forall in hwftargs.
          apply hwftargs.
          by apply elem_of_list_lookup_2 in h0.
          by apply neg_subtype_targs.
  Qed.

  Lemma subtype_targs_lift σ:
    ∀ vs σ0 σ1 ws,
    Forall wf_ty σ →
    Forall wf_ty σ0 →
    Forall wf_ty σ1 →
    σ0 <:vs:> σ1 →
    length σ = length ws →
    (∀ i wi ti, ws !! i = Some wi →
                σ !! i = Some ti →
                not_contra wi →
                mono vs ti) →
    (∀ i wi ti, ws !! i = Some wi →
                σ !! i = Some ti →
                not_cov wi →
                mono (neg_variance <$> vs) ti) →
    (subst_ty σ0 <$> σ) <:ws:> (subst_ty σ1 <$> σ)
    .
  Proof.
    induction σ as [ | ty σ hi] => vs σ0 σ1 ws hwf hwf0 hwf1 h hlen hcov hcontra;
      first by rewrite (nil_length_inv ws).
    destruct ws as [ | w ws]; first by discriminate hlen.
    case: hlen => hlen /=.
    apply Forall_cons_1 in hwf as [hty hwf].
    apply subtype_targs_cons.
    { destruct w => /=.
      - split.
        + apply subtype_lift with vs => //.
          by apply (hcov 0 Invariant).
        + apply subtype_lift with (neg_variance <$> vs) => //; last by apply neg_subtype_targs.
          by apply (hcontra 0 Invariant).
      - apply subtype_lift with vs => //.
        by apply (hcov 0 Covariant).
      - apply subtype_lift with (neg_variance <$> vs) => //; last by apply neg_subtype_targs.
        by apply (hcontra 0 Contravariant).
    }
    apply hi with vs => //.
    - move => i wi ti hwi hti hc.
      by apply (hcov (S i) wi ti).
    - move => i wi ti hwi hti hc.
      by apply (hcontra (S i) wi ti).
  Qed.

  Lemma subtype_targs_inv_0 vs σ ty0 σ0:
    (ty0 :: σ0) <:vs:> σ →
    ∃ w ws ty1 σ1,
    vs = w :: ws ∧
    σ = ty1 :: σ1 ∧
    check_variance w ty0 ty1 ∧
    σ0 <:ws:> σ1.
  Proof.
    move => h; inv h.
    - by exists Invariant, vs0, ty2, ty1s.
    - by exists Covariant, vs0, ty2, ty1s.
    - by exists Contravariant, vs0, ty2, ty1s.
  Qed.

  Lemma subtype_targs_inv_1 vs σ ty1 σ1:
    σ <:vs:> (ty1 :: σ1) →
    ∃ w ws ty0 σ0,
    vs = w :: ws ∧
    σ = ty0 :: σ0 ∧
    check_variance w ty0 ty1 ∧
    σ0 <:ws:> σ1.
  Proof.
    move => h; inv h.
    - by exists Invariant, vs0, ty0, ty0s.
    - by exists Covariant, vs0, ty0, ty0s.
    - by exists Contravariant, vs0, ty0, ty0s.
  Qed.

  Lemma subtype_targs_trans σ:
    ∀ vs σ0 σ1,
    σ0 <:vs:> σ1 →
    σ <:vs:> σ0 →
    σ <:vs:> σ1.
  Proof.
    induction σ as [ | ty σ hi] => vs σ0 σ1 h01 h0.
    - inv h0.
      by inv h01.
    - apply subtype_targs_inv_0 in h0.
      destruct h0 as (w & ws & ty0 & ty0s & -> & -> & hc & hsub).
      apply subtype_targs_inv_0 in h01.
      destruct h01 as (? & ? & ty1 & ty1s & heq & -> & hc' & hsub').
      case : heq.
      intros <- <-.
      apply subtype_targs_cons; last by eapply hi.
      move : hc hc'; destruct w => /=.
      + move => [??] [??]; split; by eauto.
      + move => ? ?; by eauto.
      + move => ? ?; by eauto.
  Qed.

  (* Sanity checks: Some derived rules *)
  Lemma subtype_union_comm : ∀ A B,
    wf_ty A → wf_ty B →
    (UnionT A B) <: (UnionT B A).
  Proof. by auto. Qed.

  Lemma subtype_inter_comm : ∀ A B,
    wf_ty A → wf_ty B →
    (InterT A B) <: (InterT B A).
  Proof. by auto. Qed.

  Lemma subtype_union_assoc:
    ∀ A B C,
    wf_ty A → wf_ty B → wf_ty C →
    (UnionT (UnionT A B) C) <: (UnionT A (UnionT B C)).
  Proof.
    move => A B C wfA wfB wfC.
    apply SubUnionLeast; last by eauto.
    apply SubUnionLeast; last by eauto.
    apply SubUnionUpper1.
    constructor; by eauto.
  Qed.

  Lemma subtype_inter_assoc:
    ∀ A B C, 
    wf_ty A → wf_ty B → wf_ty C →
    (InterT (InterT A B) C) <: (InterT A (InterT B C)).
  Proof. by eauto. Qed.

  (* Generalized version of SubClass to any inheritance sequence *)
  Lemma subtype_inherits_using A B σ σA adef:
    map_Forall (λ _ : string, wf_cdef_parent Δ) Δ →
    Δ !! A = Some adef →
    length σA = length (adef.(generics)) →
    inherits_using A B σ →
    ClassT A σA <: ClassT B (subst_ty σA <$> σ).
  Proof.
    move => hp hA hl h.
    move : h σA adef hA hl.
    induction 1 as [ A ? h | A B σ0 hext | A B σ0 C σC hext h hi ] => σA ? hA hl.
    - simplify_eq.
      by rewrite subst_ty_gen_targs.
    - by econstructor.
    - eapply SubTrans; first by eapply SubClass.
      apply extends_using_wf in hext => //.
      destruct hext as (? & bdef & hadef' & hbdef & hF0 & hL0 & _).
      apply inherits_using_wf in h => //.
      destruct h as (? & cdef & hbdef' & hcdef & hF1 & hL1 & _).
      simplify_eq.
      rewrite map_subst_ty_subst; last by rewrite hL0.
      apply hi with bdef => //.
      by rewrite map_length.
  Qed.

  (* Typing contexts *)
  Record local_tys := {
    type_of_this: tag * list lang_ty;
    ctxt: stringmap lang_ty;
  }.

  Definition this_type lty :=
    ClassT lty.(type_of_this).1 lty.(type_of_this).2.

  (* Subtype / Inclusion of typing contexts *)
  Definition lty_sub (lty rty: local_tys) :=
    this_type lty = this_type rty ∧
    ∀ k A, rty.(ctxt) !! k = Some A → ∃ B, lty.(ctxt) !! k = Some B ∧ B <: A.

  Notation "lty <:< rty" := (lty_sub lty rty) (at level 70, no associativity).

  Lemma lty_sub_reflexive: reflexive _ lty_sub.
  Proof.
    move => [this lty]; split => // k A ->.
    by exists A.
  Qed.

  Lemma lty_sub_transitive: transitive _ lty_sub.
  Proof.
    move => [[t0 σ0] lty] [[t1 σ1] rty] [[t2 σ2] zty] [h0 hlr] [h1 hrz].
    move : h0 h1.
    rewrite /this_type /=.
    case => -> ->.
    case => -> ->.
    split; first by eauto.
    move => k A hA.
    apply hrz in hA as (C & hC & hsub).
    apply hlr in hC as (B & hB & hsub').
    exists B; by eauto.
  Qed.

  Global Instance local_tys_insert : Insert string lang_ty local_tys :=
    λ x ty lty, 
    {| type_of_this := lty.(type_of_this);
      ctxt := <[x := ty]>lty.(ctxt);
    |}.

  Definition subst_lty σ lty :=
    {| type_of_this := (lty.(type_of_this).1, subst_ty σ <$> lty.(type_of_this).2);
        ctxt := subst_ty σ <$> lty.(ctxt);
    |}.

  Lemma lty_sub_insert_1 lhs ty lty0 lty1:
    lty0 <:< lty1 →
    <[lhs:=ty]> lty0 <:< <[lhs:=ty]> lty1.
  Proof.
    move => [hthis h]; split => // x xty.
    rewrite lookup_insert_Some.
    case => [[<- <-] | [hne hin]].
    - rewrite lookup_insert; by exists ty.
    - rewrite lookup_insert_ne //.
      apply h in hin.
      destruct hin as [B [hin hsub]].
      by exists B.
  Qed.

  Lemma lty_sub_insert_2 ty0 ty1 lhs lty:
    ty0 <: ty1 →
    <[lhs := ty0]>lty <:< <[lhs := ty1]> lty.
  Proof.
    move => hsub; split => // k ty.
    rewrite lookup_insert_Some.
    case => [[<- <-] | [hne hin]].
    - exists ty0; by rewrite lookup_insert.
    - exists ty; by rewrite lookup_insert_ne.
  Qed.

  Lemma lty_sub_subst σ lty rty:
    map_Forall (λ _ : string, wf_cdef_parent Δ) Δ →
    Forall wf_ty σ →
    lty <:< rty → (subst_lty σ lty) <:< (subst_lty σ rty).
  Proof.
    destruct lty as [[lt lσ] lty].
    destruct rty as [[rt rσ] rty].
    rewrite /subst_lty => hp hσ [].
    rewrite /this_type /=.
    case => -> -> hsub.
    split => //.
    move => k A.
    rewrite lookup_fmap_Some.
    case => B [<- hk].
    apply hsub in hk as [ B' [HB' hsub']].
    exists (subst_ty σ B').
    rewrite lookup_fmap HB'; split; first done.
    by apply subtype_subst.
  Qed.

  (* We allow method override: children can redeclare a method if types
   * are compatible:
   * - return type must be a subtype
   * - argument types must be a supertype
   *)
  Definition mdef_incl sub super :=
    dom stringset sub.(methodargs) = dom _ super.(methodargs) ∧
    (∀ k A B, sub.(methodargs) !! k = Some A →
    super.(methodargs) !! k = Some B → B <: A) ∧
    sub.(methodrettype) <: super.(methodrettype).

  Lemma mdef_incl_reflexive: reflexive _ mdef_incl.
  Proof.
    move => mdef; split; first done.
    split; last done.
    by move => k A B -> [] ->.
  Qed.

  Lemma mdef_incl_transitive: transitive _ mdef_incl.
  Proof.
    move => m0 m1 m2 [hdom1 [h1 ?]] [hdom2 [h2 ?]]; split; first by etransitivity.
    split; last by eauto.
    move => k A B hA hB.
    destruct (methodargs m1 !! k) as [C | ] eqn:hC; last first.
    { apply mk_is_Some in hA.
      apply elem_of_dom in hA.
      rewrite hdom1 in hA.
      apply elem_of_dom in hA.
      rewrite hC in hA.
      by elim: hA.
    }
    apply SubTrans with C.
    - by eapply h2.
    - by eapply h1.
  Qed.

  Lemma mdef_incl_subst mdef0 mdef1 σ :
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    Forall wf_ty σ →
    mdef_incl mdef0 mdef1 →
    mdef_incl (subst_mdef σ mdef0) (subst_mdef σ mdef1).
  Proof.
    move => hp hσ.
    rewrite /mdef_incl /subst_mdef /=.
    case => [hdom [hargs hret]]; split; first by rewrite !dom_fmap_L.
    split; last by apply subtype_subst.
    move => k A B.
    rewrite !lookup_fmap_Some.
    case => tyA [<- hA].
    case => tyB [<- hB].
    apply subtype_subst => //.
    by eapply hargs.
  Qed.

  (* any redeclared method must correctly override its parent methods *)
  Definition wf_method_override (prog: stringmap classDef) :=
    ∀ A B adef bdef m σ mA mB,
    prog !! A = Some adef →
    prog !! B = Some bdef →
    inherits_using A B σ →
    adef.(classmethods) !! m = Some mA →
    bdef.(classmethods) !! m = Some mB →
    mdef_incl mA (subst_mdef σ mB).

  (* Key lemma for adequacy of method call:
   * if A <: B and they both have a method m (from resp. origA, origB), then
   * the origins must be ordered in the same way, meaning origA <: origB.
   * This implies some relations on all the inheritance substitution.
   *)
  Lemma has_method_ordered A B σ m origA mdefA origB mdefB:
    wf_no_cycle Δ →
    wf_method_override Δ →
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _cname, cdef_methods_bounded) Δ →
    inherits_using A B σ →
    has_method m A origA mdefA →
    has_method m B origB mdefB →
    ∃ σin σA σB oA oB mA mB,
      subst_ty σ <$> σB = subst_ty σA <$> σin ∧
      Δ !! origA = Some oA ∧
      Δ !! origB = Some oB ∧
      oA.(classmethods) !! m = Some mA ∧
      oB.(classmethods) !! m = Some mB ∧
      inherits_using origA origB σin ∧
      inherits_using A origA σA ∧
      inherits_using B origB σB ∧
      mdefA = subst_mdef σA mA ∧
      mdefB = subst_mdef σB mB ∧
      mdef_incl mA (subst_mdef σin mB) ∧
      mdef_incl mdefA (subst_mdef σ mdefB).
  Proof.
    move => hc ho hp hm hin hA hB.
    assert (hhA := hA).
    assert (hhB := hB).
    apply has_method_from_def in hA => //.
    apply has_method_from_def in hB => //.
    destruct hA as (oadef & oaorig & hoA & hmA & hmoA & [σA [hiA ->]]).
    destruct hB as (obdef & oborig & hoB & hmB & hmoB & [σB [hiB ->]]).
    destruct (inherits_using_chain _ _ _ hp hin _ _ hiA) as [σ'' [ [<- h] | [<- h]]].
    - destruct (has_method_below_orig _ _ _ _ hc hp hm hhA _ _ _ hin h) as
        (? & ? & mbdef & ? & ? & hbm & ->); simplify_eq.
      destruct (has_method_fun _ _ _ _ _ _ hhB hbm) as [-> ->].
      simplify_eq.
      exists (gen_targs (length oadef.(generics))),
             (subst_ty σ <$> σ''),
             σ'',
             oadef, oadef,
             oaorig, oaorig.
      split.
      { rewrite subst_ty_gen_targs //.
        apply inherits_using_wf in hiA => //.
        repeat destruct hiA as [? hiA]; by simplify_eq.
      }
      do 4 (split => //).
      split; first by econstructor.
      do 4 (split => //).
      split.
      + repeat split.
        * by rewrite /subst_mdef /= dom_fmap_L.
        * move => k X Y hX.
          rewrite /subst_mdef /= lookup_fmap hX /= subst_ty_id.
          { by case => ->. }
          apply hm in hoA.
          apply hoA in hmA.
          by apply hmA in hX.
        * rewrite /subst_mdef /= subst_ty_id //.
          apply hm in hoA.
          by apply hoA in hmA as [].
      + rewrite subst_mdef_mdef; first by apply mdef_incl_reflexive.
        assert (hoA' := hoA).
        apply hm in hoA'.
        apply hoA' in hmA.
        apply inherits_using_wf in h => //.
        repeat destruct h as [? h]; simplify_eq.
        by rewrite H2.
    - exists (subst_ty σ'' <$> σB), σA, σB, oadef, obdef, oaorig, oborig.
      split.
      { rewrite map_subst_ty_subst //.
        apply inherits_using_wf in hiB => //.
        repeat destruct hiB as [? hiB].
        apply inherits_using_wf in h => //.
        repeat destruct h as [? h].
        simplify_eq.
        by rewrite H6.
      }
      assert (hh: inherits_using origA origB (subst_ty σ'' <$> σB))
        by (by eapply inherits_using_trans).
      assert (hincl : mdef_incl oaorig (subst_mdef (subst_ty σ'' <$> σB) oborig))
        by (by eapply (ho origA origB) in hh).
      do 10 (split => //).
      rewrite -subst_mdef_mdef; last first.
      { assert (hoB' := hoB).
        apply hm in hoB'.
        apply hoB' in hmB.
        apply inherits_using_wf in hiB => //.
        repeat destruct hiB as [? hiB].
        simplify_eq.
        apply bounded_subst_mdef with (length (generics obdef)) => //.
        apply inherits_using_wf in h => //.
        repeat destruct h as [? h].
        simplify_eq.
        rewrite Forall_forall => ty hty.
        rewrite H5.
        rewrite Forall_forall in H1.
        by apply H1 in hty.
      }
      apply mdef_incl_subst => //.
      { apply inherits_using_wf in hiA => //.
        by repeat destruct hiA as [? hiA].
      }
      rewrite subst_mdef_mdef //.
      { assert (hoB' := hoB).
        apply hm in hoB'.
        apply hoB' in hmB.
        apply inherits_using_wf in hiB => //.
        repeat destruct hiB as [? hiB].
        simplify_eq.
        by rewrite H2.
      }
  Qed.
End Subtype.
 
(* Hints and notations are local to the section. Re-exporting them *)
Global Hint Constructors subtype : core.
Global Hint Constructors subtype_targs : core.
