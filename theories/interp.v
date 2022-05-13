(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
From stdpp Require Import base strings gmap stringmap fin_maps natmap list.
From iris.base_logic Require Import upred derived.
From iris.base_logic.lib Require Import iprop own.
From iris.algebra Require Import ofe cmra gmap_view.
From iris.proofmode Require Import tactics.

From shack Require Import lang progdef subtype typing eval heap modality.

(* the interpretation of types is simply given by
     the carrier set of the sem_typeO ofe *)
Record interp Σ := Interp {
    interp_car :> sem_typeO Σ;
    interp_persistent v : Persistent (interp_car v)
  }.

Definition interp_fun Σ (i: interp Σ) : value → iPropO Σ := interp_car Σ i.

Coercion interp_fun : interp >-> Funclass.

Lemma interp_car_simpl : ∀ Σ c p, @interp_car Σ (Interp _ c p) = c.
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

  Global Instance interp_car_ne2 : NonExpansive interp_car.
  Proof. by move => n i j h. Qed.

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
  Local Notation "Γ ⊢ s <: t" := (@subtype _ Γ s t) (at level 70, s at next level, no associativity).
  Local Notation "Γ ⊢ lts <: vs :> rts" := (@subtype_targs _ Γ vs lts rts) (at level 70, lts, vs at next level).
  Local Notation "Γ ⊢ lty <:< rty" := (@lty_sub _ Γ lty rty) (lty at next level, at level 70, no associativity).

  (* now, let's interpret some types ! *)

  (* Most interpretation functions are parametrized by Σi: tvar -> interp
   * and Σc: list constraint.
   * Σi is here to interpret generic types.
   * Σc is there to put constraints on generic types.
   *
   * We could only consider closed types and eagerly apply all top level
   * substitution, but this way makes things a bit more compositional.
   *)
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

  Notation ty_interpO := (lang_ty -d> interpO Σ).

  Variable Σc : list constraint.
  Variable Σi : list (interp Σ).

  Definition interp_fields
    (C: tag)
    σC
    (dom_fields: stringset)
    (ifields: gmapO string (laterO (sem_typeO Σ)))
    (rec: ty_interpO) : iProp Σ :=
    (⌜dom ifields = dom_fields⌝ ∗
    (∀ f vis ty orig, ⌜has_field f C vis ty orig⌝ -∗ ifields !! f ≡ Some (Next (interp_car (rec (subst_ty σC ty)))))
    )%I.

  Definition interp_class C σC (rec : ty_interpO) : interp Σ :=
    Interp (
      λ (w : value),
      (∃ ℓ t cdef σ σt (fields: stringmap ((visibility * lang_ty) * tag)) (ifields: gmapO string (laterO (sem_typeO Σ))),
      ⌜w = LocV ℓ ∧
       inherits_using t C σ ∧
       wf_ty (ClassT t σt) ∧
       ok_ty Σc (ClassT t σt) ∧
       Δ !! C = Some cdef ∧

       Σc ⊢ (subst_ty σt <$> σ) <: cdef.(generics) :> σC ∧

       has_fields t fields⌝ ∗
      interp_fields t σt (dom fields) ifields rec ∗
      (ℓ ↦ (t, ifields)))%I
    ).

  Definition interp_class_strict C σC (rec : ty_interpO) : interp Σ :=
    Interp (
      λ (w : value),
      (∃ ℓ t σ σt (fields: stringmap ((visibility * lang_ty) * tag)) (ifields: gmapO string (laterO (sem_typeO Σ))),
      ⌜w = LocV ℓ ∧ inherits_using t C σ ∧
       wf_ty (ClassT t σt) ∧ ok_ty Σc (ClassT t σt) ∧
       (subst_ty σt <$> σ) = σC ∧
       has_fields t fields⌝ ∗
      interp_fields t σt (dom fields) ifields rec ∗
      (ℓ ↦ (t, ifields)))%I
    ).

  Lemma interp_class_from_strict C σC (rec: ty_interpO) v:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    interp_class_strict C σC rec v -∗ interp_class C σC rec v.
  Proof.
    iIntros (hp) "H".
    iDestruct "H" as (??????) "[%hpure [Hfields Hl]]".
    destruct hpure as (-> & hin & hwf & hok & heqp & hfs).
    assert (hin' := hin).
    apply inherits_using_wf in hin' => //.
    destruct hin' as (def & ? & ? & hwfC); inv hwfC; simplify_eq.
    iExists _, _, def0, _, _, _, _.
    iSplit; last by iSplit.
    iPureIntro.
    repeat split => //.
    apply subtype_targs_refl.
    by rewrite map_length.
  Qed.

  Definition interp_ex (cname: tag) (rec: ty_interpO): interp Σ :=
    Interp (λ (w: value), (∃ σc, ⌜wf_ty (ClassT cname σc)⌝ ∗ interp_class cname σc rec w)%I).

  Definition interp_nonnull (rec : ty_interpO) : interp Σ :=
    Interp (
      λ (v : value),
      ((interp_int v) ∨
      (interp_bool v) ∨
      (∃ t, interp_ex t rec v))%I
    ).

  Definition interp_mixed (rec: ty_interpO) : interp Σ :=
    Interp (λ (v: value), (interp_nonnull rec v ∨ interp_null v)%I).

  Definition interp_generic (tv: nat) : interp Σ :=
    default interp_nothing (Σi !! tv).

  (* we use a blend of Coq/Iris recursion, the
     Coq recursion lets us handle simple structural
     cases, and we use Iris' recursion to deal with
     the more complicated case of class types.
  *)
  Section interp_type_pre_rec.
    Variable (rec: ty_interpO).

    Fixpoint go (typ: lang_ty) : interp Σ :=
      match typ with
      | IntT => interp_int
      | BoolT => interp_bool
      | NothingT => interp_nothing
      | MixedT => interp_mixed rec
      | ClassT A σA => interp_class A σA rec
      | NullT => interp_null
      | NonNullT => interp_nonnull rec
      | UnionT A B => interp_union (go A) (go B)
      | InterT A B => interp_inter (go A) (go B)
      | GenT n => interp_generic n
      | ExT cname => interp_ex cname rec
      end.
  End interp_type_pre_rec.

  (* TODO: find a better name for go *)
  Definition interp_type_pre (rec : ty_interpO) : ty_interpO :=
    λ (typ : lang_ty), go rec typ.

  Global Instance interp_type_pre_persistent (rec: ty_interpO) :
    ∀ t v, Persistent (interp_type_pre rec t v).
  Proof. by move => ??; apply _. Qed.

  Global Instance interp_class_contractive cname σc:
    Contractive (interp_class cname σc).
  Proof.
    rewrite /interp_class => n i1 i2 hdist v.
    rewrite /interp_fun !interp_car_simpl.
    do 7 (f_equiv; intros ?).
    f_equiv.
    rewrite /interp_fields.
    do 13 f_equiv.
    f_contractive.
    apply interp_car_ne2.
    by f_equiv.
  Qed.

  Global Instance interp_ex_contractive cname: Contractive (interp_ex cname).
  Proof.
    rewrite /interp_ex => n i1 i2 hdist v.
    rewrite /interp_fun !interp_car_simpl.
    do 3 f_equiv.
    by apply interp_class_contractive.
  Qed.

  Global Instance interp_nonnull_contractive: Contractive interp_nonnull.
  Proof.
    rewrite /interp_nonnull => n i1 i2 hdist v.
    rewrite /interp_fun !interp_car_simpl.
    do 4 f_equiv.
    by apply interp_ex_contractive.
  Qed.

  (* we cannot use solve_contractive out of the box because of
   * the 'fix' combinator above
   *)
  Local Instance interp_type_pre_contractive : Contractive interp_type_pre.
  Proof.
    rewrite /interp_type_pre => n rec1 rec2 hdist ty /=.
    induction ty
      as [ | | | | cname σ hi | | | A B hA hB | A B hA hB | i | cname ] => /=.
    - done.
    - done.
    - done.
    - rewrite /interp_mixed => v.
      rewrite /interp_fun !interp_car_simpl.
      f_equiv.
      revert v; by apply interp_nonnull_contractive.
    - by apply interp_class_contractive.
    - done.
    - by apply interp_nonnull_contractive.
    - solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv]).
    - solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv]).
    - done.
    - by apply interp_ex_contractive.
  Qed.

  (* the interpretation of types can now be
     defined as a fixpoint (because class types
     can be (mutually) recursive) *)
  Definition interp_type := fixpoint interp_type_pre.

  (* Helper lemmas to control unfolding of some definitions *)
  Lemma interp_type_unfold (ty : lang_ty) (v : value) :
    interp_type ty v ⊣⊢ interp_type_pre interp_type ty v.
  Proof.
    rewrite {1}/interp_type.
    apply (fixpoint_unfold interp_type_pre ty v).
  Qed.

  Lemma interp_ex_unfold t v:
    interp_type (ExT t) v ⊣⊢ interp_ex t interp_type v.
  Proof. by rewrite interp_type_unfold /= /interp_ex /=. Qed.

  Lemma interp_nonnull_unfold v:
    interp_type NonNullT v ⊣⊢
      (interp_int v) ∨ (interp_bool v) ∨ (∃ t, interp_ex t interp_type v)%I.
  Proof. by rewrite interp_type_unfold /= /interp_nonnull /=. Qed.

  Lemma interp_mixed_unfold v:
    interp_type MixedT v ⊣⊢ interp_nonnull interp_type v ∨ interp_null v.
  Proof. by rewrite interp_type_unfold /interp_mixed /=. Qed.

  Lemma interp_class_unfold A σA v:
    interp_type (ClassT A σA) v ⊣⊢
    interp_class A σA interp_type v.
  Proof. by rewrite interp_type_unfold. Qed.

  Lemma interp_union_unfold A B v:
    interp_type (UnionT A B) v ⊣⊢
    interp_union (interp_type A) (interp_type B) v.
  Proof.
    rewrite interp_type_unfold /=.
    iSplit; iIntros "[H | H]".
    - iLeft; by rewrite interp_type_unfold.
    - iRight; by rewrite interp_type_unfold.
    - iLeft; by rewrite interp_type_unfold.
    - iRight; by rewrite interp_type_unfold.
  Qed.

  Lemma interp_inter_unfold A B v:
    interp_type (InterT A B) v ⊣⊢
    interp_inter (interp_type A) (interp_type B) v.
  Proof.
    rewrite interp_type_unfold /=.
    iSplit; iIntros "[HL HR]".
    - rewrite !interp_type_unfold; by iSplit.
    - rewrite !interp_type_unfold; by iSplit.
  Qed.

  (* #hyp *)
  Global Instance interp_type_persistent :
    ∀ t v, Persistent (interp_type t v).
  Proof.
    move => t v.
    rewrite interp_type_unfold.
    by apply _.
  Qed.

  (* if class A<..> extends B<σB>, then for any valid substitution σA,
   * [| A<σA> |] ⊆ [| B<σA o σB> |]
   *)
  Lemma extends_using_is_inclusion:
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _cname, wf_cdef_mono) Δ →
    ∀ A B σB, extends_using A B σB →
    ∀ v σA, Forall wf_ty σA →
    interp_type (ClassT A σA) v -∗
    interp_type (ClassT B (subst_ty σA <$> σB)) v.
  Proof.
    move => hwf hwfb hwp hmono A B σB hext v σA hwfσA.
    rewrite !interp_type_unfold /=.
    iIntros "h".
    iDestruct "h" as (ℓ t adef σ σt fields ifields) "[%h [hsem hl]]".
    destruct h as (-> & hin & hσwf & hσok & hadef & hσ & hfields).
    destruct (extends_using_wf _ _ _ hwp hext) as (adef' & hadef' & hF & hwfB).
    simplify_eq.
    assert (hwfσt : Forall wf_ty σt) by (by apply wf_ty_class_inv in hσwf).
    assert (hwfσ : Forall wf_ty σ).
    { apply inherits_using_wf in hin => //.
      destruct hin as (? & ? & ? &h).
      by apply wf_ty_class_inv in h.
    }
    rewrite /interp_fields.
    iDestruct "hsem" as "[%hdom hfields]".
    inv hwfB.
    iExists ℓ, t, def, (subst_ty σ <$> σB), σt, fields, ifields.
    iSplit.
    { iPureIntro; split; first done.
      split.
      { by eapply inherits_using_trans; last by econstructor. }
      split; first done.
      split; first done.
      split; first done.
      split; last done.
      assert (hwfB: wf_ty (ClassT B σB)).
      { apply extends_using_wf in hext => //.
        by repeat destruct hext as [? hext].
      }
      rewrite map_subst_ty_subst; last first.
      { apply inherits_using_wf in hin => //.
        destruct hin as (? & ? & ? & h); inv h; simplify_eq.
        by rewrite H7.
      }
      assert (hadef' := hadef).
      apply hmono in hadef'.
      rewrite /wf_cdef_mono in hadef'.
      clear hdom.
      inv hext; simplify_eq.
      rewrite H0 in hadef'.
      apply subtype_targs_lift with (vs := adef.(generics)) => //.
      - by apply wf_ty_class_inv in hwfB.
      - by apply wf_ty_subst_map.
      - move => i wi ti hwi hti hc.
        inv hadef'; simplify_eq.
        by apply (H7 i wi).
      - move => i wi ti hwi hti hc.
        inv hadef'; simplify_eq.
        by apply (H8 i wi).
    }
    iSplit; last done.
    iSplit; first by iPureIntro.
    iIntros (f vis ty orig) "%hf".
    by iApply "hfields".
  Qed.

  Definition interp_variance v ty0 ty1 : iProp Σ :=
    match v with
    | Invariant => ∀ w,
        interp_type_pre interp_type ty0 w ∗-∗ interp_type_pre interp_type ty1 w
    | Covariant => ∀ w,
        interp_type_pre interp_type ty0 w -∗ interp_type_pre interp_type ty1 w
    | Contravariant => ∀ w,
        interp_type_pre interp_type ty1 w -∗ interp_type_pre interp_type ty0 w
    end.

  Fixpoint iForall3 {A B C : Type} (P : A → B → C → iProp Σ)
    (As : list A) (Bs: list B) (Cs : list C) {struct As}  : iProp Σ :=
    match As, Bs, Cs with
    | [], [], [] => True%I
    | A :: As, B :: Bs, C :: Cs => (P A B C ∗ iForall3 P As Bs Cs)%I
    | _, _, _ => False%I
    end.

  Definition interp_env_as_mixed :=
    ∀ i (ϕi: interp Σ),  Σi !! i = Some ϕi → ∀ v,  ϕi v -∗ interp_mixed interp_type v.

  Definition Σinterp :=
    ∀ i c, Σc !! i = Some c →
    ∀ v, interp_type_pre interp_type c.1 v -∗ interp_type_pre interp_type c.2 v.

  Definition interp_local_tys
    (lty : local_tys) (le : local_env) : iProp Σ :=
    interp_class_strict lty.(type_of_this).1 lty.(type_of_this).2 interp_type (LocV le.(vthis)) ∗
    (∀ v ty, ⌜lty.(ctxt) !! v = Some ty⌝ -∗
    ∃ val, ⌜le.(lenv) !! v = Some val⌝ ∗ interp_type ty val)%I.

  Section inclusion.
    Hypothesis Σcoherency : Σinterp.

    Hypothesis wfΣc : Forall wf_constraint Σc.

    Hypothesis wfΣi : interp_env_as_mixed.

    (* Main meat for A <: B → [|A|] ⊆ [|B|] *)
    Theorem subtype_is_inclusion_aux A B:
      map_Forall (λ _cname, wf_cdef_fields) Δ →
      map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
      map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
      map_Forall (λ _cname, wf_cdef_mono) Δ →
      Σc ⊢ A <: B →
      ∀ v,
      wf_ty A →
      interp_type_pre interp_type A v -∗
      interp_type_pre interp_type B v
      with subtype_targs_is_inclusion_aux Vs As Bs:
      map_Forall (λ _cname, wf_cdef_fields) Δ →
      map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
      map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
      map_Forall (λ _cname, wf_cdef_mono) Δ →
      Forall wf_ty As →
      Forall wf_ty Bs →
      Σc ⊢ As <:Vs:> Bs →
      ⊢ iForall3 interp_variance Vs As Bs.
    Proof.
      { move => ????.
        destruct 1 as [A | A h | A σA B σB adef hΔ hlen hext
        | A adef hadef hL | A def σ0 σ1 hΔ hwfσ σ | | | | A | A B h
        | A B h | A B C h0 h1 | A B | A B | A B C h0 h1
        | A | A B C h0 h1 | A B hin] => v hwfA.
        - rewrite /interp_mixed.
          clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
          elim: A v hwfA => //.
          + move => v _; iIntros "h"; by repeat iLeft.
          + move => v _; iIntros "h"; by iLeft; iRight; iLeft.
          + move => v _; by rewrite /interp_nothing; iIntros "h".
          + move => cname targs ? v hwf.
            iIntros "h".
            iLeft; iRight; iRight.
            iExists cname, targs.
            iSplitR; last done.
            by iPureIntro.
          + move => v _; iIntros "h"; by iRight.
          + move => v _; by iIntros "h"; iLeft.
          + move => s t hs ht v hwf.
            inv hwf.
            rewrite /interp_union.
            iIntros "h".
            iDestruct "h" as "[ h | h ]"; first by iApply hs.
            by iApply ht.
          + move => s t hs ht v hwf.
            inv hwf.
            rewrite /interp_inter.
            iIntros "h".
            iDestruct "h" as "[? _]"; by iApply hs.
          + move => n v _.
            rewrite /interp_generic.
            iIntros "hv".
            destruct (decide (n < length Σi)) as [hlt | hge].
            * apply lookup_lt_is_Some_2 in hlt as [ϕ hϕ].
              iApply wfΣi; last done.
              by rewrite /= /interp_generic hϕ /=.
            * rewrite /= /interp_generic lookup_ge_None_2 /=; last by apply not_lt.
              done.
          + move => cname v _;
            rewrite /interp_ex.
            iIntros "hv".
            iDestruct "hv" as (targs) "hv".
            iLeft; iRight; iRight.
            by iExists _, _.
        - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
          rewrite /=.
          by iIntros "H".
        - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
          apply wf_ty_class_inv in hwfA.
          rewrite -!interp_type_unfold; by iApply extends_using_is_inclusion.
        - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
          simpl.
          iIntros "h".
          iDestruct "h" as (σc hσc l t cdef σ σt fields ifields hpure) "[h hl]".
          repeat destruct hpure as [? hpure]; simplify_eq.
          iExists l, t, adef, σ, σt , fields, ifields; iSplit; last by iSplit.
          iPureIntro.
          repeat split => //.
          inv hσc; simplify_eq.
          replace [] with σc => //.
          apply nil_length_inv.
          by rewrite -hL.
        - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
          iIntros "h".
          iDestruct "h" as (l t adef Σin σt fields ifields) "[%hpure [#hifields #hl]]".
          destruct hpure as (-> & hin & hwft & hokt & hadef & hsub & hfields).
          iExists l, t, adef, Σin, σt, fields, ifields.
          iSplitR; last by iSplit.
          iPureIntro.
          repeat split => //.
          simplify_eq.
          by eapply subtype_targs_trans.
        - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
          by rewrite /= /interp_mixed.
        - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
          iIntros "h"; by iLeft.
        - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
          iIntros "h"; by iRight; iLeft.
        - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
          iIntros "H".
          iRight; iRight.
          iExists A, targs.
          iSplitR; last done.
          by iPureIntro.
        - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
          by iIntros "h"; iLeft.
        - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
          by iIntros "h"; iRight.
        - rewrite /interp_union.
          iIntros "[h | h]".
          + iApply subtype_is_inclusion_aux; [done | done | done | done | exact h0 | | ].
            * inv hwfA; by assumption.
            * by iAssumption.
          + iApply subtype_is_inclusion_aux; [done | done | done | done | exact h1 | | ].
            * inv hwfA; by assumption.
            * by iAssumption.
        - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
          iIntros "[h _]".
          by iAssumption.
        - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
          iIntros "[_ ?]".
          by iAssumption.
        - iIntros "h".
          iSplit.
          + iApply subtype_is_inclusion_aux; [done | done | done | done | exact h0 | done | ].
            by iAssumption.
          + iApply subtype_is_inclusion_aux; [done | done | done | done | exact h1 | done | ].
            by iAssumption.
        - done.
        - iIntros "h".
          iApply subtype_is_inclusion_aux; [done | done | done | done | exact h1 | | ].
          + apply subtype_wf in h0; [ | done | done | done ].
            by assumption.
          + iApply subtype_is_inclusion_aux; [done | done | done | done | exact h0 | done | ].
            by iAssumption.
        - apply elem_of_list_lookup_1 in hin as [i hin].
          by apply Σcoherency in hin.
      }
      move => ???? hwfA hwfB.
      destruct 1 as [ | ????? h0 h1 h | ????? h0 h | ????? h0 h].
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        done.
      - simpl.
        apply Forall_cons_1 in hwfA as [hA hwfA].
        apply Forall_cons_1 in hwfB as [hB hwfB].
        iSplitR.
        + iIntros (w); iSplit.
          * by iApply subtype_is_inclusion_aux.
          * by iApply subtype_is_inclusion_aux.
        + by iApply subtype_targs_is_inclusion_aux.
      - simpl.
        apply Forall_cons_1 in hwfA as [hA hwfA].
        apply Forall_cons_1 in hwfB as [hB hwfB].
        iSplitR.
        + iIntros (w).
          by iApply subtype_is_inclusion_aux.
        + by iApply subtype_targs_is_inclusion_aux.
      - simpl.
        apply Forall_cons_1 in hwfA as [hA hwfA].
        apply Forall_cons_1 in hwfB as [hB hwfB].
        iSplitR.
        + iIntros (w).
          by iApply subtype_is_inclusion_aux.
        + by iApply subtype_targs_is_inclusion_aux.
    Qed.

    (* A <: B → [|A|] ⊆ [|B|] *)
    Theorem subtype_is_inclusion:
      map_Forall (λ _cname, wf_cdef_fields) Δ →
      map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
      map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
      map_Forall (λ _cname, wf_cdef_mono) Δ →
      ∀ A B, Σc ⊢ A <: B →
      ∀ v,
      wf_ty A →
      interp_type A v -∗ interp_type B v.
    Proof.
      move => ???? A B hAB v ?.
    rewrite !interp_type_unfold.
    by iApply subtype_is_inclusion_aux.
    Qed.

    Lemma interp_local_tys_is_inclusion lty rty le:
      map_Forall (λ _cname, wf_cdef_fields) Δ →
      map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
      map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
      map_Forall (λ _ : string, wf_cdef_mono) Δ →
      wf_lty lty →
      Forall (λ (i: interp Σ), ∀ v, Persistent (i v)) Σi →
      Σc ⊢ lty <:< rty →
      interp_local_tys lty le -∗
      interp_local_tys rty le.
    Proof.
      move => ???? hlty hpers hsub; iIntros "[#Hthis Hle]".
      destruct hsub as [hthis hsub].
      assert (hthis2: type_of_this lty = type_of_this rty).
      { rewrite /this_type in hthis.
        rewrite (surjective_pairing (type_of_this lty))
        (surjective_pairing (type_of_this rty)).
        by case : hthis => -> ->.
      }
      rewrite hthis2.
      iSplitR; first done.
      iIntros (v ty) "%Hv".
      apply hsub in Hv as (B & hB & hsubB).
      iDestruct ("Hle" $! v B hB) as (val) "[%Hv' #H]".
      iExists val; iSplitR; first done.
      iApply subtype_is_inclusion => //.
      by apply hlty in hB.
    Qed.
  End inclusion.

  (* Specialized version for existential types. Will help during the
   * proof of adequacy for runtime checks.
   *)
  Theorem inherits_is_ex_inclusion:
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _cname, wf_cdef_mono) Δ →
    ∀ A B, inherits A B →
    ∀ v, interp_type (ExT A) v -∗ interp_type (ExT B) v.
  Proof.
    move => ?? hp ?.
    induction 1 as [ x | x y z hxy hyz hi ] => // v.
    rewrite interp_ex_unfold.
    iIntros "H".
    iApply hi; clear hyz hi.
    iDestruct "H" as (σx) "[%hσx H]".
    destruct hxy as [x y xdef σy hxdef hsuper].
    assert (hext: extends_using x y σy) by (econstructor; by eauto).
    assert (hydef : is_Some (Δ !! y)).
    { apply hp in hxdef.
      rewrite /wf_cdef_parent hsuper in hxdef.
      destruct hxdef as [h _]; inv h; by simplify_eq.
    }
    destruct hydef as [ydef hydef].
    iAssert (interp_type (ClassT y (subst_ty σx <$> σy)) v) with "[H]" as "Hext".
    { iApply extends_using_is_inclusion => //.
      - by apply wf_ty_class_inv in hσx.
      - by rewrite interp_class_unfold.
    }
    rewrite interp_class_unfold interp_ex_unfold.
    iExists (subst_ty σx <$> σy); iSplitR; last done.
    iPureIntro.
    apply wf_ty_class with ydef => //.
    { rewrite map_length.
      apply hp in hxdef.
      rewrite /wf_cdef_parent hsuper in hxdef.
      destruct hxdef as [h _]; inv h; by simplify_eq.
    }
    apply wf_ty_subst_map; first by apply wf_ty_class_inv in hσx.
    apply hp in hxdef.
    rewrite /wf_cdef_parent hsuper in hxdef.
    destruct hxdef as [h _].
    by apply wf_ty_class_inv in h.
  Qed.

  (* Helper to lift the conclusions of interp_class into a super class *)
  Lemma interp_fields_inclusion t σt fields ifields σ C rec:
    wf_no_cycle Δ →
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
    inherits_using t C σ →
    interp_fields t σt fields ifields rec -∗
    interp_fields C (subst_ty σt <$> σ) fields ifields rec.
  Proof.
    move => ??? hb hin.
    rewrite /interp_fields.
    iIntros "[%hdom #hfields]".
    iSplit; first done.
    iIntros (f vis ty orig) "%hf".
    assert (hfC: has_field f t vis (subst_ty σ ty) orig) by (by eapply has_field_inherits_using).
    iSpecialize ("hfields" $! f vis (subst_ty σ ty) orig hfC).
    rewrite subst_ty_subst //.
    apply has_field_bounded in hf => //.
    destruct hf as (def & hdef & hfty).
    apply inherits_using_wf in hin => //.
    destruct hin as (? & ? & ? & hwf).
    inv hwf; simplify_eq.
    by rewrite H4.
  Qed.

End proofs.
