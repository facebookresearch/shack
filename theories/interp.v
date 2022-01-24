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

(* the interpretation of types is simply given by
     the carrier set of the sem_typeO ofe *)
Record interp Σ := Interp {
    interp_car :> value → iPropO Σ;
    interp_persistent v : Persistent (interp_car v)
  }.

Lemma interp_car_unfold : ∀ Σ c p, @interp_car Σ (Interp _ c p) = c.
Proof.
  by intros.
Qed.

Arguments Interp {_} _%I {_}.
Arguments interp_car {_} _ _ : simpl never.

Global Existing Instance interp_persistent.

Section interp_cofe.
  Context {Σ : gFunctors}.

  Instance interp_equiv : Equiv (interp Σ) := λ A B, ∀ w, A w ≡ B w.
  Instance interp_dist : Dist (interp Σ) := λ n A B, ∀ w, A w ≡{n}≡ B w.

  Lemma interp_ofe_mixin : OfeMixin (interp Σ).
  Proof. by apply (iso_ofe_mixin (interp_car : _ → value -d> _)). Qed.

  Canonical Structure interpO := Ofe (interp Σ) interp_ofe_mixin.
  Global Instance interp_cofe : Cofe interpO.
  Proof.
    apply (iso_cofe_subtype' (λ A : value -d> iPropO Σ, ∀ w, Persistent (A w))
      (@Interp _) interp_car)=> //.
    - apply _.
    - apply limit_preserving_forall=> w.
      by apply bi.limit_preserving_Persistent=> n ??.
  Qed.

  Global Instance interp_inhabited : Inhabited (interp Σ) := populate (Interp inhabitant).

  Global Instance interp_car_ne n : Proper (dist n ==> (=) ==> dist n) interp_car.
  Proof. by intros A A' ? w ? <-. Qed.

  Global Instance interp_car_proper : Proper ((≡) ==> (=) ==> (≡)) interp_car.
  Proof. by intros A A' ? w ? <-. Qed.
End interp_cofe.

Arguments interpO : clear implicits.

Section proofs.
  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.

  (* Iris semantic context *)
  Context `{!sem_heapGS Σ}.

  Notation γ := sem_heap_name.

  (* Helping the inference with this notation that hides Δ *)
  Local Notation "s <: t" := (@subtype _ s t) (at level 70, no associativity).
  Local Notation "lty <:< rty" := (@lty_sub _ lty rty) (at level 70, no associativity).

  (* now, let's interpret some types ! *)
  Definition interp_null_car (v: value) : iProp Σ := ⌜v = NullV⌝%I.
  Definition interp_null_persistent v : Persistent (interp_null_car v).
  Proof. by apply _. Qed.

  Definition interp_null : interp Σ :=
    Interp (λ(v: value), ⌜v = NullV⌝%I).

  Definition interp_int : interp Σ :=
    Interp (λ (v : value), (∃ z, ⌜v = IntV z⌝)%I).

  Definition interp_bool : interp Σ :=
    Interp (λ (v : value), (∃ b, ⌜v = BoolV b⌝)%I).

  Definition interp_union (iA : interp Σ) (iB : interp Σ) : interp Σ :=
    Interp (λ (v : value), (iA v ∨ iB v)%I).

  Definition interp_inter (iA : interp Σ) (iB : interp Σ) : interp Σ :=
    Interp (λ (v : value), (iA v ∧ iB v)%I).

  Definition interp_nothing : interp Σ :=
    Interp (λ (_: value), False%I).

  Notation ty_interpO := (lang_ty -d> sem_typeO Σ).

  Definition interp_fields (rec: ty_interpO) (ftys: stringmap lang_ty) :
    gmapO string (laterO (sem_typeO Σ)) :=
    let f := λ (typ: lang_ty), Next (rec typ) in
    @fmap _ _ _ (later (sem_typeO Σ)) f ftys
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
  Definition interp_class (cname : tag) (rec : ty_interpO) : interp Σ :=
    Interp (
      λ (w : value),
      (∃ ℓ t (fields:stringmap lang_ty),
      ⌜w = LocV ℓ ∧ inherits t cname ∧ has_fields t fields⌝ ∗
      (ℓ ↦ (t , interp_fields rec fields)))%I
    ).

  Definition interp_nonnull (rec : ty_interpO) : interp Σ :=
    Interp (
      λ (v : value),
      ((interp_int v) ∨
      (interp_bool v) ∨
      (∃ t, interp_class t rec v))%I
    ).

  Definition interp_mixed (rec: ty_interpO) : interp Σ :=
    Interp (λ (v: value), (interp_nonnull rec v ∨ interp_null v)%I).

  (* we use a blend of Coq/Iris recursion, the
     Coq recursion lets us handle simple structural
     cases, and we use Iris' recursion to deal with
     the more complicated case of class types *)
  Definition interp_type_pre (rec : ty_interpO) : ty_interpO :=
    λ (typ : lang_ty),
    (fix go (typ : lang_ty) : interp Σ :=
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

  Lemma interp_class_contractive cname:
    Contractive (interp_class cname).
  Proof.
    rewrite /interp_class => n i1 i2 hdist v.
    rewrite !interp_car_unfold.
    f_equiv ; intro l.
    f_equiv; intro t.
    f_equiv; intro fields.
    f_equiv.
    set (f := λ i, interp_fields i fields).
    assert (hf : Contractive f) by apply interp_fields_contractive.
    by apply (mapsto_contractive _ _ f).
  Qed.

  Lemma interp_nonnull_contractive: Contractive interp_nonnull.
  Proof.
    rewrite /interp_nonnull => n i1 i2 hdist v.
    rewrite !interp_car_unfold.
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
    elim : ty; intros; rewrite /interp_type_pre //=;
    [ (* mixed *)| (*class*) | (*nonnull*) 
    | solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv])
    | solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv])
    ].
     - move => v; rewrite /interp_mixed !interp_car_unfold.
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

  Definition interp_local_tys
    (lty : local_tys) (le : local_env) : iProp Σ :=
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
End proofs.
