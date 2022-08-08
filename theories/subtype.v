(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
From stdpp Require Import base strings gmap stringmap fin_maps list.
(* Not using iris but importing their ssreflect dependencies *)
From iris.proofmode Require Import tactics.
From shack Require Import lang progdef.

(* Abstract definition of the SDT constraints at the class level *)
Class SDTClassConstraints := {
  Δsdt : tag → list variance → list lang_ty → list constraint;
}.

Section Subtype.
  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.
  (* assume some SDT constraints *)
  Context `{SDTCC: SDTClassConstraints}.

  Inductive subtype_kind := Aware | Plain.

  (* Type well-formdness is mostly introduced to be able to define
   * subtyping rule correctly, like unions.
   *)
  Inductive subtype (Δ : list constraint) : subtype_kind → lang_ty → lang_ty → Prop :=
    | SubMixed: ∀ kd ty, subtype Δ kd ty MixedT
    | SubNothing: ∀ kd ty, wf_ty ty → subtype Δ kd NothingT ty
    | SubClass: ∀ kd A σA B σB adef,
        pdefs !! A = Some adef →
        length σA = length adef.(generics) →
        extends_using A B σB →
        subtype Δ kd (ClassT A σA) (ClassT B (subst_ty σA <$> σB))
    | SubVariance: ∀ kd A adef σ0 σ1,
        pdefs !! A = Some adef →
        Forall wf_ty σ1 →
        subtype_targs Δ kd adef.(generics) σ0 σ1 →
        subtype Δ kd (ClassT A σ0) (ClassT A σ1)
    | SubMixed2 kd: subtype Δ kd MixedT (UnionT NonNullT NullT)
    | SubIntNonNull kd: subtype Δ kd IntT NonNullT
    | SubBoolNonNull kd: subtype Δ kd BoolT NonNullT
    | SubIntBoolDisj kd: subtype Δ kd (InterT IntT BoolT) NothingT
    | SubClassNonNull: ∀ kd A targs, subtype Δ kd (ClassT A targs) NonNullT
    | SubUnionUpper1: ∀ kd s t, wf_ty t → subtype Δ kd s (UnionT s t)
    | SubUnionUpper2: ∀ kd s t, wf_ty s → subtype Δ kd t (UnionT s t)
    | SubUnionLower : ∀ kd s t u, subtype Δ kd s u → subtype Δ kd t u → subtype Δ kd (UnionT s t) u
    | SubInterLower1: ∀ kd s t, subtype Δ kd (InterT s t) s
    | SubInterLower2: ∀ kd s t, subtype Δ kd (InterT s t) t
    | SubInterUpper: ∀ kd s t u, subtype Δ kd u s → subtype Δ kd u t → subtype Δ kd u (InterT s t)
    | SubRefl: ∀ kd s, subtype Δ kd s s
    | SubTrans: ∀ kd s t u, subtype Δ kd s t → subtype Δ kd t u → subtype Δ kd s u
    | SubConstraint: ∀ kd s t, (s, t) ∈ Δ → subtype Δ kd s t
    | SubClassDyn: ∀ kd A adef σA,
        pdefs !! A = Some adef →
        adef.(support_dynamic) = true →
        (∀ k s t, (Δsdt A adef.(generics) σA) !! k = Some (s, t) → subtype Δ kd s t) →
        subtype Δ kd (ClassT A σA) SupportDynT
    | SubIntDyn kd: subtype Δ kd IntT SupportDynT
    | SubBoolDyn kd: subtype Δ kd BoolT SupportDynT
    | SubNullDyn kd: subtype Δ kd NullT SupportDynT
    | SubSupDyn: subtype Δ Aware SupportDynT DynamicT
    | SubDynPrim kd : subtype Δ kd DynamicT SupportDynT
  with subtype_targs (Δ: list constraint) : subtype_kind → list variance → list lang_ty → list lang_ty → Prop :=
    | subtype_targs_nil kd: subtype_targs Δ kd [] [] []
    | subtype_targs_invariant: ∀ kd ty0 ty1 vs ty0s ty1s,
        subtype Δ kd ty0 ty1 →
        subtype Δ kd ty1 ty0 →
        subtype_targs Δ kd vs ty0s ty1s →
        subtype_targs Δ kd (Invariant :: vs) (ty0 :: ty0s) ( ty1 :: ty1s)
    | subtype_targs_covariant: ∀ kd ty0 ty1 vs ty0s ty1s,
        subtype Δ kd ty0 ty1 →
        subtype_targs Δ kd vs ty0s ty1s →
        subtype_targs Δ kd (Covariant :: vs) (ty0 :: ty0s) ( ty1 :: ty1s)
    | subtype_targs_contravariant: ∀ kd ty0 ty1 vs ty0s ty1s,
        subtype Δ kd ty1 ty0 →
        subtype_targs Δ kd vs ty0s ty1s →
        subtype_targs Δ kd (Contravariant :: vs) (ty0 :: ty0s) ( ty1 :: ty1s)
  .

  Definition Δentails kd (Δ0 Δ1: list constraint) :=
    ∀ i c, Δ1 !! i = Some c → subtype Δ0 kd c.1 c.2.

  (* Properties of Δsdt *)
  Class SDTClassSpec := {
    (* Δsdt preserves the wf_ty of σ *)
    Δsdt_wf: ∀ A vars σ, Forall wf_ty σ → Forall wf_constraint (Δsdt A vars σ);
    (* Δsdt commutes with subst_ty *)
    Δsdt_subst_ty: ∀ A vars σ0 σ,
      subst_constraints σ (Δsdt A vars σ0) = Δsdt A vars (subst_ty σ <$> σ0);
    (* Δsdt preserves the bounded of σ *)
    Δsdt_bounded: ∀ A vars σ n,
      Forall (bounded n) σ → Forall (bounded_constraint n) (Δsdt A vars σ);
    (* Δsdt commutes with σ *)
    Δsdt_lift: ∀ n A vars σ,
      lift_constraints n (Δsdt A vars σ) = Δsdt A vars (lift_ty n <$> σ);
    (* Δsdt is compatible with the variance of a class *)
    Δsdt_variance: ∀ Δ kd A vars σ0 σ1,
      subtype_targs Δ kd vars σ0 σ1 → Δentails kd (Δ ++ Δsdt A vars σ1) (Δsdt A vars σ0);
  }.
End Subtype.

Section SubtypeFacts.
  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.
  (* assume some SDT constraints *)
  Context `{SDTCC: SDTClassConstraints}.
  (* assume the good properties of SDT constraints *)
  Context `{SDTCP: SDTClassSpec}.

  Corollary length_subtype_targs_v1 Δ kd: ∀ vs ty0s ty1s,
    subtype_targs Δ kd vs ty0s ty1s → length vs = length ty1s.
  Proof.
    induction 1 as [ | ???????? h hi | ??????? h hi | ??????? h hi] => //=; by rewrite hi.
  Qed.

  Hint Constructors subtype : core.
  Hint Constructors subtype_targs : core.

  Notation "Δ ⊢ s <: t" := (subtype Δ Plain s t) (at level 70, s at next level, no associativity).
  Notation "Δ ⊢ s <D: t" := (subtype Δ Aware s t) (at level 70, s at next level, no associativity).
  Notation "Δ ⊢ lts <: vs :> rts" := (subtype_targs Δ Plain vs lts rts) (at level 70, lts, vs at next level).

  Lemma subtype_weaken Δ kd s t: subtype Δ kd s t → ∀ Δ', Δ ⊆ Δ' → subtype Δ' kd s t
   with subtype_targs_weaken Δ kd lhs vs rhs:
     subtype_targs Δ kd vs lhs rhs → ∀ Δ', Δ ⊆ Δ' → subtype_targs Δ' kd vs lhs rhs.
  Proof.
    - destruct 1 as [ kd ty | kd ty hwf | kd A σA B σB adef hadef hL hext
      | kd A adef σ0 σ1 hadef hwf hσ | | | | | kd A targs
      | kd s t ht | kd s t hs | kd s t u hs ht | kd s t | kd s t | kd s t u hs ht
      | kd s | kd s t u hs ht | kd s t hin | kd A adef σA hpdefs hsupdyn hf
      | | | | | ] => Δ' hΔ; try by econstructor.
      + econstructor; [ done | done | ].
        by eapply subtype_targs_weaken.
      + econstructor; by eapply subtype_weaken.
      + econstructor; by eapply subtype_weaken.
      + econstructor; by eapply subtype_weaken.
      + apply SubConstraint.
        by set_solver.
      + eapply SubClassDyn => // k s t hst.
        eapply subtype_weaken; last done.
        by eapply hf.
    - destruct 1 as [ | ???????? h | ??????? h | ??????? h ] => Δ' hΔ.
      + by constructor.
      + econstructor; [ by eapply subtype_weaken | by eapply subtype_weaken | ].
        by eapply subtype_targs_weaken.
      + econstructor; [ by eapply subtype_weaken | ].
        by eapply subtype_targs_weaken.
      + econstructor; [ by eapply subtype_weaken | ].
        by eapply subtype_targs_weaken.
  Qed.

  Lemma subtype_constraint_elim_ G kd S T:
    subtype G kd S T →
    ∀ Δ Δ', G = Δ ++ Δ' →
    (∀ i c, Δ' !! i = Some c → subtype Δ kd c.1 c.2) →
    subtype Δ kd S T
  with subtype_targs_constraint_elim_ G kd lhs vs rhs:
    subtype_targs G kd vs lhs rhs →
    ∀ Δ Δ', G = Δ ++ Δ' →
    (∀ i c, Δ' !! i = Some c → subtype Δ kd c.1 c.2) →
    subtype_targs Δ kd vs lhs rhs.
  Proof.
    - destruct 1 as [ kd ty | kd ty hwf | kd A σA B σB adef hadef hL hext
      | kd A adef σ0 σ1 hadef hwf hσ | kd | kd | kd | kd |  kd A targs
      | kd s t ht | kd s t hs | kd s t u hs ht | kd s t | kd s t | kd s t u hs ht | kd s
      | kd s t u hs ht | kd s t hin | kd A adef σA hpdefs hsupdyn hf
      | | | | | ]
      => Δ Δ' heq hΔ; subst; try by econstructor.
      + econstructor; [done | done | ].
        by eapply subtype_targs_constraint_elim_.
      + econstructor; by eapply subtype_constraint_elim_.
      + econstructor; by eapply subtype_constraint_elim_.
      + econstructor; by eapply subtype_constraint_elim_.
      + apply elem_of_app in hin as [hin | hin].
        { by apply SubConstraint. }
        apply elem_of_list_lookup_1 in hin as [i hin].
        by apply hΔ in hin.
      + eapply SubClassDyn => // k s t hst.
        eapply subtype_constraint_elim_; by eauto.
    - destruct 1 as [ | ???????? h | ??????? h | ??????? h ] => Δ Δ' heq hΔ; subst.
      + by constructor.
      + econstructor; [ by eapply subtype_constraint_elim_ | by eapply subtype_constraint_elim_ | ].
        by eapply subtype_targs_constraint_elim_.
      + econstructor; [ by eapply subtype_constraint_elim_ | ].
        by eapply subtype_targs_constraint_elim_.
      + econstructor; [ by eapply subtype_constraint_elim_ | ].
        by eapply subtype_targs_constraint_elim_.
  Qed.

  Lemma subtype_constraint_elim kd Δ Δ' S T:
    subtype (Δ ++ Δ') kd  S T →
    (∀ i c, Δ' !! i = Some c → subtype Δ kd c.1 c.2) →
    subtype Δ kd S T.
  Proof. intros; by eapply subtype_constraint_elim_. Qed.

  Lemma subtype_constraint_trans Δ kd s t:
    subtype Δ kd s t →
    ∀ Δ', (∀ i c, Δ !! i = Some c → subtype Δ' kd c.1 c.2) →
    subtype Δ' kd s t
  with subtype_targs_constraint_trans Δ kd lhs vs rhs:
    subtype_targs Δ kd vs lhs rhs →
    ∀ Δ', (∀ i c, Δ !! i = Some c → subtype Δ' kd c.1 c.2) →
    subtype_targs Δ' kd vs lhs rhs.
  Proof.
    - destruct 1 as [ kd ty | kd ty hwf | kd A σA B σB adef hadef hL hext
      | kd A adef σ0 σ1 hadef hwf hσ | | | | | kd A targs
      | kd s t ht | kd s t hs | kd s t u hs ht | kd s t | kd s t | kd s t u hs ht
      | kd s | kd s t u hs ht | kd s t hin | kd A adef σA hpdefs hsupdyn hf
      | | | | | ] => Δ' hΔ; try by econstructor.
      + eapply SubVariance; [exact hadef | assumption | ].
        eapply subtype_targs_constraint_trans.
        * by apply hσ.
        * exact hΔ.
      + econstructor; by eapply subtype_constraint_trans.
      + econstructor; by eapply subtype_constraint_trans.
      + apply SubTrans with t; by eapply subtype_constraint_trans.
      + apply elem_of_list_lookup in hin as [i hin].
        by apply hΔ in hin.
      + eapply SubClassDyn => // k s t hst.
        eapply subtype_constraint_trans; by eauto.
    - destruct 1 as [ | ???????? h | ??????? h | ??????? h ] => Δ' hΔ.
      + by constructor.
      + econstructor; [ by eapply subtype_constraint_trans | by eapply subtype_constraint_trans | ].
        by eapply subtype_targs_constraint_trans.
      + econstructor; [ by eapply subtype_constraint_trans | ].
        by eapply subtype_targs_constraint_trans.
      + econstructor; [ by eapply subtype_constraint_trans | ].
        by eapply subtype_targs_constraint_trans.
  Qed.

  (* See Andrew Kennedy's paper:
     Variance and Generalized Constraints for C♯ Generics
  *)
  Inductive mono (vs: list variance) : lang_ty → Prop :=
    | MonoInt : mono vs IntT
    | MonoBool : mono vs BoolT
    | MonoNothing : mono vs NothingT
    | MonoMixed : mono vs MixedT
    | MonoNull : mono vs NullT
    | MonoNonNull : mono vs NonNullT
    | MonoUnion s t : mono vs s → mono vs t → mono vs (UnionT s t)
    | MonoInter s t : mono vs s → mono vs t → mono vs (InterT s t)
    | MonoVInvGen n: vs !! n = Some Invariant → mono vs (GenT n)
    | MonoVCoGen n: vs !! n = Some Covariant → mono vs (GenT n)
    | MonoClass cname cdef targs:
        pdefs !! cname = Some cdef →
        (∀ i wi ti, cdef.(generics) !! i = Some wi →
                    targs !! i = Some ti →
                    not_contra wi →
                    mono vs ti) →
        (∀ i wi ti, cdef.(generics) !! i = Some wi →
                    targs !! i = Some ti →
                    not_cov wi →
                    mono (neg_variance <$> vs) ti) →
        mono vs (ClassT cname targs)
    | MonoDynamic : mono vs DynamicT
    | MonoSupportDyn : mono vs SupportDynT
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
    induction 1 as [ | | | | | | vs s t hs his ht hit
      | vs s t hs his ht hit | vs n hinv | vs n hco
      | vs cname cdef targs hpdefs hcov hicov hcontra hicontra | | ]
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
      econstructor; first done.
      + move => i ci ti hci hi hc.
        apply list_lookup_fmap_inv in hi as [ty [-> hi]].
        eapply hicov => //.
        rewrite Forall_lookup in H0.
        by apply H0 in hi.
      + move => i ci ti hci hi hc.
        apply list_lookup_fmap_inv in hi as [ty [-> hi]].
        eapply hicontra => //.
        * rewrite Forall_lookup in H0.
          rewrite map_length.
          by apply H0 in hi.
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
    map_Forall (λ _cname, wf_cdef_mono) pdefs →
    extends_using A B σ →
    ∀ def, pdefs !! A = Some def →
    mono def.(generics) (ClassT B σ).
  Proof.
    move => hmono h def hdef.
    inv h; simplify_eq.
    apply hmono in hdef.
    by rewrite /wf_cdef_mono H0 in hdef.
  Qed.

  Lemma inherits_using_mono A B σ :
    map_Forall (λ _ : string, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _cname, wf_cdef_mono) pdefs →
    inherits_using A B σ →
    ∀ def, pdefs !! A = Some def →
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
      destruct h as (bdef & hbdef & hF & hwf).
      assert (hbdef' := hbdef).
      assert (hext' := hext).
      apply hi in hbdef.
      apply extends_using_mono with (def := def) in hext' => //.
      inv hext'.
      simplify_eq.
      change (ClassT C (subst_ty σ <$> σC)) with (subst_ty σ (ClassT C σC)).
      apply mono_subst with (generics bdef) => //.
      + by constructor.
      + apply extends_using_wf in hext => //.
        destruct hext as (? & ? & ? & hwfB).
        inv hwfB; simplify_eq.
        by rewrite H6.
  Qed.

  Lemma has_field_mono f t vis ty orig:
    map_Forall (λ _cname, wf_field_mono) pdefs →
    map_Forall (λ _cname, wf_cdef_mono) pdefs →
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _cname, wf_cdef_fields_bounded) pdefs →
    has_field f t vis ty orig →
    ∃ def, pdefs !! t = Some def ∧
    match vis with
    | Public => invariant def.(generics) ty
    | Private => True
    end.
  Proof.
    move => hwfpdefs hmono hp hfb.
    induction 1 as [ tag cdef [vis typ] hpdefs hf
      | tag targs parent cdef vis typ orig hpdefs hf hs h hi ].
      - exists cdef; split => //.
        apply hwfpdefs in hpdefs.
        by apply hpdefs in hf.
      - destruct hi as [def [hdef hvis]].
        exists cdef; split => //.
        destruct vis; last done.
        destruct hvis as [h0 h1].
        assert (htag := hpdefs).
        apply hp in htag.
        rewrite /wf_cdef_parent hs in htag.
        destruct htag as (hwf & hf0); simplify_eq.
        inv hwf.
        apply has_field_bounded in h => //.
        destruct h as (? & ? & hbt).
        assert (htag := hpdefs).
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
            eapply H6 => //.
            by destruct wi.
          * move => i vi ti hvi hti hc.
            apply list_lookup_fmap_inv in hvi.
            destruct hvi as [wi [-> hwi]].
            eapply H7 => //.
            by destruct wi.
  Qed.

  Lemma subtype_wf Δ kd A B:
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    Forall wf_constraint Δ →
    wf_ty A → subtype Δ kd A B → wf_ty B.
  Proof.
    move => hp hΔ hwf.
    induction 1 as [ kd ty | kd ty h | kd A σA B σB adef hpdefs hA hext
      | kd A adef σ0 σ1 hpdefs hwfσ hσ | | | | | kd A args | kd s t h
      | kd s t h | kd s t u hs his ht hit | kd s t | kd s t | kd s t u hs his ht hit | kd s
      | kd s t u hst hist htu hitu | kd s t hin | kd A adef σA hpdefs hsupdyn hf hi
      | | | | | ]
      => //=; try (by constructor).
    - inv hext; simplify_eq.
      rewrite /map_Forall_lookup in hp.
      apply hp in hpdefs.
      rewrite /wf_cdef_parent H0 in hpdefs.
      destruct hpdefs as (hwfB & hF).
      inv hwfB.
      econstructor; first done.
      + by rewrite map_length.
      + move => k ty.
        rewrite list_lookup_fmap.
        destruct (σB !! k) as [ tyk | ] eqn:hty => //=.
        case => <-.
        apply wf_ty_subst; first by apply wf_ty_class_inv in hwf.
        by eauto.
    - apply length_subtype_targs_v1 in hσ.
      inv hwf; simplify_eq; econstructor.
      + exact hpdefs.
      + by rewrite hσ.
      + rewrite Forall_lookup in hwfσ => k ty hty.
        by eauto.
    - inv hwf; by eauto.
    - inv hwf; by eauto.
    - inv hwf; by eauto.
    - constructor; by eauto.
    - by eauto.
    - rewrite Forall_forall in hΔ.
      by apply hΔ in hin as [].
  Qed.

  Lemma subtype_subst Δ kd A B:
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    subtype Δ kd A B → ∀ σ,
    Forall wf_ty σ →
    subtype (subst_constraints σ Δ) kd (subst_ty σ A) (subst_ty σ B)
  with subtype_targs_subst Δ kd vs As Bs:
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    subtype_targs Δ kd vs As Bs → ∀ σ,
    Forall wf_ty σ →
    subtype_targs (subst_constraints σ Δ) kd vs (subst_ty σ <$> As) (subst_ty σ <$> Bs).
  Proof.
    - move => hp.
      destruct 1 as [ kd ty | kd ty h | kd A σA B σB adef hpdefs hA hext
      | kd A adef σ0 σ1 hpdefs hwfσ hσ01 | | | | | kd A args
      | kd s t h | kd s t h | kd s t u hs ht | kd s t | kd s t | kd s t u hs ht | kd s
      | kd s t u hst htu | kd s t hin | kd A adef σA hpdefs hsupdyn hf
      | | | | | ]
      => σ hσ => /=; try (by constructor).
      + constructor.
        by apply wf_ty_subst.
      + rewrite map_subst_ty_subst.
        * econstructor; [exact hpdefs | | by assumption].
          by rewrite map_length.
        * apply extends_using_wf in hext; last done.
          destruct hext as (? & hadef & hF & hwfB).
          inv hwfB; simplify_eq.
          by rewrite hA.
      + eapply SubVariance.
        * exact hpdefs.
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
      + apply SubConstraint.
        apply elem_of_list_lookup_1 in hin as [i hin].
        apply elem_of_list_lookup; exists i.
        by rewrite /subst_constraints list_lookup_fmap hin.
      + eapply SubClassDyn => // k s t hst.
        rewrite -Δsdt_subst_ty in hst.
        apply list_lookup_fmap_inv in hst as [[] [[= -> ->] h]].
        eapply subtype_subst; [done | | done].
        by apply hf with k.
    - move => hp.
      destruct 1 as [ | ?????? h0 h1 h | ?????? h0 h | ?????? h0 h] => σ hσ /=.
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

  (* Sanity checks: Some derived rules *)
  Lemma subtype_union_comm Δ: ∀ A B,
    wf_ty A → wf_ty B →
    Δ ⊢ (UnionT A B) <: (UnionT B A).
  Proof. by auto. Qed.

  Lemma subtype_inter_comm Δ : ∀ A B,
    wf_ty A → wf_ty B →
    Δ ⊢ (InterT A B) <: (InterT B A).
  Proof. by auto. Qed.

  Lemma subtype_union_assoc Δ:
    ∀ A B C,
    wf_ty A → wf_ty B → wf_ty C →
    Δ ⊢ (UnionT (UnionT A B) C) <: (UnionT A (UnionT B C)).
  Proof.
    move => A B C wfA wfB wfC.
    apply SubUnionLower; last by eauto.
    apply SubUnionLower; last by eauto.
    apply SubUnionUpper1.
    constructor; by eauto.
  Qed.

  Lemma subtype_inter_assoc Δ:
    ∀ A B C,
    wf_ty A → wf_ty B → wf_ty C →
    Δ ⊢ (InterT (InterT A B) C) <: (InterT A (InterT B C)).
  Proof. by eauto. Qed.

  (* Typing contexts *)
  Record local_tys := {
    type_of_this: tag * list lang_ty;
    ctxt: stringmap lang_ty;
  }.

  Definition this_type lty :=
    ClassT lty.(type_of_this).1 lty.(type_of_this).2.

  (* Subtype / Inclusion of typing contexts *)
  Definition lty_sub Δ kd (Γ0 Γ1: local_tys) :=
    this_type Γ0 = this_type Γ1 ∧
    ∀ k A, Γ1.(ctxt) !! k = Some A → ∃ B, Γ0.(ctxt) !! k = Some B ∧ subtype Δ kd B A.

  Notation "Δ ⊢ Γ0 <:< Γ1" := (lty_sub Δ Plain Γ0 Γ1) (Γ0 at next level, at level 70, no associativity).

  Global Instance local_tys_insert : Insert string lang_ty local_tys :=
    λ x ty Γ,
    {| type_of_this := Γ.(type_of_this);
      ctxt := <[x := ty]>Γ.(ctxt);
    |}.

  (* We allow method override: children can redeclare a method if types
   * are compatible:
   * - return type must be a subtype
   * - argument types must be a supertype
   *)
  Definition mdef_incl (Δ: list constraint) (sub super: methodDef) :=
    dom sub.(methodargs) = dom super.(methodargs) ∧
    (∀ k A B, sub.(methodargs) !! k = Some A →
    super.(methodargs) !! k = Some B → Δ ⊢ B <D: A) ∧
    Δ ⊢ sub.(methodrettype) <D: super.(methodrettype).

  Lemma mdef_incl_reflexive Δ: reflexive _ (mdef_incl Δ).
  Proof.
    move => mdef; split; first done.
    split; last done.
    by move => k A B -> [] ->.
  Qed.

  Lemma mdef_incl_subst Δ mdef0 mdef1 σ :
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    Forall wf_ty σ →
    mdef_incl Δ mdef0 mdef1 →
    mdef_incl (subst_constraints σ Δ) (subst_mdef σ mdef0) (subst_mdef σ mdef1).
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
    mdef_incl adef.(constraints) mA (subst_mdef σ mB).

  (* Key lemma for soundness of method call:
   * if A <: B and they both have a method m (from resp. origA, origB), then
   * the origins must be ordered in the same way, meaning origA <: origB.
   * This implies some relations on all the inheritance substitution.
   *)
  Lemma has_method_ordered A B σAB m origA mdefA origB mdefB:
    wf_no_cycle pdefs →
    wf_method_override pdefs →
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _cname, cdef_methods_bounded) pdefs →
    inherits_using A B σAB →
    has_method m A origA mdefA →
    has_method m B origB mdefB →
    ∃ oA oB σA σB mA mB,
      pdefs !! origA = Some oA ∧
      pdefs !! origB = Some oB ∧
      oA.(classmethods) !! m = Some mA ∧
      oB.(classmethods) !! m = Some mB ∧
      inherits_using A origA σA ∧
      inherits_using B origB σB ∧
      mdefA = subst_mdef σA mA ∧
      mdefB = subst_mdef σB mB ∧
      mdef_incl (subst_constraints σA oA.(constraints)) mdefA (subst_mdef σAB mdefB) ∧
      (* A <: B <: orig A = orig B *)
      ((inherits_using B origA σB ∧
          origA = origB ∧
          mA = mB ∧
          subst_ty σAB <$> σB = σA) ∨
      (* A <: origA <: B <: origB *)
       (∃ σ, inherits_using origA B σ ∧
             subst_ty σA <$> σ = σAB ∧
             mdef_incl oA.(constraints) mA (subst_mdef σ (subst_mdef σB mB)))).
  Proof.
    move => hc ho hp hm hin hA hB.
    assert (hhA := hA).
    assert (hhB := hB).
    apply has_method_from_def in hA => //.
    apply has_method_from_def in hB => //.
    destruct hA as (oadef & oaorig & hoA & hmA & hmoA & [σA [hiA ->]]).
    destruct hB as (obdef & oborig & hoB & hmB & hmoB & [σB [hiB ->]]).
    exists oadef, obdef, σA, σB, oaorig, oborig.
    do 8 split => //.
    destruct (inherits_using_chain _ _ _ hp hin _ _ hiA) as [σ'' [ [<- h] | [<- h]]].
    - destruct (has_method_below_orig _ _ _ _ hc hp hm hhA _ _ _ hin h) as
        (? & ? & mbdef & ? & ? & hbm & ->); simplify_eq.
      destruct (has_method_fun _ _ _ _ _ _ hhB hbm) as [-> ->].
      simplify_eq.
      assert (mdef_bounded (length σ'') oaorig).
      { assert (hoA' := hoA).
        apply hm in hoA.
        apply hoA in hmA.
        apply inherits_using_wf in h => //.
        destruct h as (? & ? & ? & h).
        inv h; simplify_eq.
        by rewrite H4.
      }
      split.
      { rewrite subst_mdef_mdef //.
        by apply mdef_incl_reflexive.
      }
      left.
      repeat split => //.
      assert (hh : inherits_using A origA (subst_ty σAB <$> σB))
        by by eapply inherits_using_trans.
      by rewrite (inherits_using_fun _ _ _ hc hp hiA _ hh).
    - assert (mdef_bounded (length σB) oborig).
      { assert (hoB' := hoB).
        apply hm in hoB.
        apply hoB in hmB.
        apply inherits_using_wf in hiB => //.
        destruct hiB as (? & ? & ? & hiB).
        inv hiB; simplify_eq.
        by rewrite H4.
      }
      assert (mdef_bounded (length σ'') (subst_mdef σB oborig)).
      { apply mdef_bounded_subst with (n := length σB) => //.
        apply inherits_using_wf in hiB => //.
        destruct hiB as (bdef & ? & ? & ?).
        apply inherits_using_wf in h => //.
        destruct h as (? & ? & ? & h).
        inv h; simplify_eq.
        by rewrite H8.
      }
      assert ( mdef_incl (constraints oadef) oaorig (subst_mdef σ'' (subst_mdef σB oborig))).
      { rewrite subst_mdef_mdef //.
        eapply ho => //.
        by eapply inherits_using_trans.
      }
      split.
      { rewrite -subst_mdef_mdef //.
        apply mdef_incl_subst => //.
        apply inherits_using_wf in hiA => //.
        destruct hiA as (? & ? & ? & hiA).
        by apply wf_ty_class_inv in hiA.
      }
      right.
      exists σ''.
      by repeat split => //.
  Qed.
End SubtypeFacts.

(* Hints and notations are local to the section. Re-exporting them *)
Global Hint Constructors subtype : core.
Global Hint Constructors subtype_targs : core.
