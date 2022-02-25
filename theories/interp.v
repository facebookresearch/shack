(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 * 
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
From stdpp Require Import base strings gmap stringmap fin_maps natmap.
From iris.base_logic Require Import upred derived.
From iris.base_logic.lib Require Import iprop own.
From iris.algebra Require Import ofe cmra gmap_view.
From iris.proofmode Require Import tactics.

From shack Require Import lang heap modality.

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
  Local Notation "s <: t" := (@subtype _ s t) (at level 70, no associativity).
  Local Notation "lty <:< rty" := (@lty_sub _ lty rty) (at level 70, no associativity).

  (* now, let's interpret some types ! *)

  (* Most interpretation functions are parametrized by σi: tvar -> interp.
   * This environment is here to interpret generic types.
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

   Notation ty_interpO := (lang_ty -d> listO (interpO Σ) -n> interpO Σ).

   Lemma ty_interpO_ne : ∀ (rec: ty_interpO) ty, NonExpansive (rec ty).
   Proof.
     move => rec ty.
     apply _.
   Qed.

  Definition interp_fields
    (σi: list (interp Σ))
    (C: tag)
    σC
    (fields: stringmap lang_ty)
    (ifields: gmapO string (laterO (sem_typeO Σ)))
    (rec: ty_interpO) : iProp Σ :=
    (⌜dom stringset fields = dom _ ifields⌝ ∗
    ∀ f ty, ⌜has_field f C ty⌝ -∗ ifields !! f ≡ Some (Next (interp_car (rec (subst_ty σC ty) σi))))%I.

  Definition interp_class C σC (σi: list (interp Σ)) (rec : ty_interpO) : interp Σ :=
    Interp (
      λ (w : value),
      (∃ ℓ t σ σt (fields: stringmap lang_ty) (ifields: gmapO string (laterO (sem_typeO Σ))),
      ⌜w = LocV ℓ ∧ inherits_using t C σ ∧ wf_ty (ClassT t σt) ∧ σC = subst_ty σt <$> σ ∧ has_fields t fields⌝ ∗
      interp_fields σi t σt fields ifields rec ∗
      (ℓ ↦ (t, ifields)))%I
    ).

  Definition interp_ex σi (cname: tag) (rec: ty_interpO): interp Σ :=
    Interp (λ (w: value), (∃ σc, interp_class cname σc σi rec w)%I).

  Definition interp_nonnull σi (rec : ty_interpO) : interp Σ :=
    Interp (
      λ (v : value),
      ((interp_int v) ∨
      (interp_bool v) ∨
      (∃ t, interp_ex σi t rec v))%I
    ).

  Definition interp_mixed σi (rec: ty_interpO) : interp Σ :=
    Interp (λ (v: value), (interp_nonnull σi rec v ∨ interp_null v)%I).

  Definition interp_generic (σi: list (interpO Σ)) (tv: nat) : interp Σ :=
    default interp_nothing (σi !! tv).

  (* we use a blend of Coq/Iris recursion, the
     Coq recursion lets us handle simple structural
     cases, and we use Iris' recursion to deal with
     the more complicated case of class types.
  *)
  Section interp_type_pre_rec.
    Variable (σi: listO (interpO Σ)).
    Variable (rec: ty_interpO).

    Fixpoint go (typ: lang_ty) : interp Σ :=
      match typ with
      | IntT => interp_int
      | BoolT => interp_bool
      | NothingT => interp_nothing
      | MixedT => interp_mixed σi rec
      | ClassT A σA => interp_class A σA σi rec
      | NullT => interp_null
      | NonNullT => interp_nonnull σi rec
      | UnionT A B => interp_union (go A) (go B)
      | InterT A B => interp_inter (go A) (go B)
      | GenT n => interp_generic σi n
      | ExT cname => interp_ex σi cname rec
      end.
  End interp_type_pre_rec.

  Local Instance interp_class_ne cname σc (rec: ty_interpO) :
    NonExpansive (λ σi, interp_class cname σc σi rec).
  Proof.
    move => n x y h.
    rewrite /interp_class => v.
    rewrite /interp_fun !interp_car_simpl.
    do 13 f_equiv.
    rewrite /interp_fields.
    do 10 f_equiv.
    by apply ty_interpO_ne.
  Qed.

  Local Instance interp_ex_ne cname (rec: ty_interpO) :
    NonExpansive (λ σi, interp_ex σi cname rec).
  Proof.
    move => n x y h.
    rewrite /interp_ex => v.
    rewrite /interp_fun !interp_car_simpl.
    do 3 f_equiv.
    by apply interp_class_ne.
  Qed.

  Local Instance interp_nonnull_ne (rec: ty_interpO) :
    NonExpansive (λ σi, interp_nonnull σi rec).
  Proof.
    move => n x y h.
    rewrite /interp_nonnull => v.
    rewrite /interp_fun !interp_car_simpl.
    do 5 f_equiv.
    by apply interp_ex_ne.
  Qed.

  Local Instance go_ne (rec: ty_interpO) (ty: lang_ty) :
    NonExpansive (λ σi, go σi rec ty).
  Proof.
    induction ty as [ | | | | A σ hi | | | A B hA hB | A B hA hB | i | cname ] => //= n x y h.
    - rewrite /interp_mixed => v.
      rewrite /interp_fun !interp_car_simpl.
      do 5 f_equiv.
      by apply interp_ex_ne.
    - by apply interp_class_ne.
    - by apply interp_nonnull_ne.
    - rewrite /interp_union => v.
      rewrite /interp_fun !interp_car_simpl.
      f_equiv.
      + revert v; by apply hA.
      + revert v; by apply hB.
    - rewrite /interp_inter => v.
      rewrite /interp_fun !interp_car_simpl.
      f_equiv.
      + revert v; by apply hA.
      + revert v; by apply hB.
    - rewrite /interp_generic => v.
      assert (hl: length x = length y) by now apply Forall2_length in h.
      elim : x y i h hl => [ | hd tl hi]; case => [ | hd' tl'] i h /= hl => //.
      apply Forall2_cons in h as [hhd htl].
      case: i hi => [ | i ] hi //=.
      apply:  hi; first done.
      by lia.
    - by apply interp_ex_ne.
  Qed.

  (* TODO: find a better name for go *)
  Definition interp_type_pre (rec : ty_interpO) : ty_interpO :=
    λ (typ : lang_ty), λne (σi: listO (interpO Σ)), go σi rec typ.

  Global Instance interp_type_pre_persistent (rec: ty_interpO) :
    ∀ t σi v, Persistent (interp_type_pre rec t σi v).
  Proof. by move => ???; apply _. Qed.

  Global Instance interp_class_contractive cname σc σi:
    Contractive (interp_class cname σc σi). 
  Proof.
    rewrite /interp_class => n i1 i2 hdist v.
    rewrite /interp_fun !interp_car_simpl.
    do 6 (f_equiv; intros ?).
    f_equiv.
    rewrite /interp_fields.
    do 9 f_equiv.
    f_contractive.
    apply interp_car_ne2.
    by f_equiv.
  Qed.

  Global Instance interp_ex_contractive σi cname: Contractive (interp_ex σi cname).
  Proof.
    rewrite /interp_ex => n i1 i2 hdist v.
    rewrite /interp_fun !interp_car_simpl.
    do 2 f_equiv.
    by apply interp_class_contractive.
  Qed.

  Global Instance interp_nonnull_contractive σi: Contractive (interp_nonnull σi).
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
    rewrite /interp_type_pre => n rec1 rec2 hdist ty σi /=.
    induction ty
      as [ | | | | cname σ hi | | | A B hA hB | A B hA hB | i | cname ] => //=.
    - rewrite /interp_mixed => v.
      rewrite /interp_fun !interp_car_simpl.
      f_equiv.
      revert v; by apply interp_nonnull_contractive.
    - by apply interp_class_contractive.
    - by apply interp_nonnull_contractive.
    - solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv]).
    - solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv]).
    - by apply interp_ex_contractive.
  Qed.

  (* the interpretation of types can now be
     defined as a fixpoint (because class types
     can be (mutually) recursive) *)
  Definition interp_type := fixpoint interp_type_pre.

  Record interp_env := InterpEnv {
    interp_env_car :> list (interpO Σ);
    interp_env_as_mixed:
      Forall (λ (e: interp Σ), ∀ v, e v -∗ interp_mixed interp_env_car interp_type v) interp_env_car
  }.

  Definition interp_env_empty : interp_env := InterpEnv [] (Forall_nil_2 _).

  (* Helper lemmas to control unfolding of some definitions *)
  Lemma interp_type_unfold (σi: list (interpO Σ)) (ty : lang_ty) (v : value) :
    interp_type ty σi v ⊣⊢ interp_type_pre interp_type ty σi v.
  Proof.
    rewrite {1}/interp_type.
    apply (fixpoint_unfold interp_type_pre ty σi v).
  Qed.

  Lemma interp_ex_unfold σi t v:
    interp_type (ExT t) σi v ⊣⊢ interp_ex σi t interp_type v.
  Proof. by rewrite interp_type_unfold /= /interp_ex /=. Qed.

  Lemma interp_nonnull_unfold σi v:
    interp_type NonNullT σi v ⊣⊢
      (interp_int v) ∨ (interp_bool v) ∨ (∃ t, interp_ex σi t interp_type v)%I.
  Proof. by rewrite interp_type_unfold /= /interp_nonnull /=. Qed.

  Lemma interp_mixed_unfold σi v:
    interp_type MixedT σi v ⊣⊢ interp_nonnull σi interp_type v ∨ interp_null v.
  Proof. by rewrite interp_type_unfold /interp_mixed /=. Qed.

  Lemma interp_class_unfold σi A σA v:
    interp_type (ClassT A σA) σi v ⊣⊢
    interp_class A σA σi interp_type v.
  Proof. by rewrite interp_type_unfold. Qed.

  Lemma interp_union_unfold σi A B v:
    interp_type (UnionT A B) σi v ⊣⊢
    interp_union (interp_type A σi) (interp_type B σi) v.
  Proof.
    rewrite interp_type_unfold /=.
    iSplit; iIntros "[H | H]".
    - iLeft; by rewrite interp_type_unfold.
    - iRight; by rewrite interp_type_unfold.
    - iLeft; by rewrite interp_type_unfold.
    - iRight; by rewrite interp_type_unfold.
  Qed.

  Lemma interp_inter_unfold σi A B v:
    interp_type (InterT A B) σi v ⊣⊢
    interp_inter (interp_type A σi) (interp_type B σi) v.
  Proof.
    rewrite interp_type_unfold /=.
    iSplit; iIntros "[HL HR]".
    - rewrite !interp_type_unfold; by iSplit.
    - rewrite !interp_type_unfold; by iSplit.
  Qed.

  (* #hyp *)
  Global Instance interp_type_persistent :
    ∀ t σi v, Persistent (interp_type t σi v).
  Proof.
    move => t σi v.
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
    ∀ A B σB, extends_using A B σB →
    ∀ σi v σA, interp_type (ClassT A σA) σi v -∗
    interp_type (ClassT B (subst_ty σA <$> σB)) σi v.
  Proof.
    move => hwf /map_Forall_lookup hwfb /map_Forall_lookup hwp A B σB hext σi v σA.
    rewrite !interp_type_unfold /=.
    iIntros "h".
    iDestruct "h" as (ℓ t σ σt fields ifields) "[%h [hsem hl]]".
    destruct h as [-> [hin [hσwf [hσ hfields]]]].
    rewrite /interp_fields.
    iDestruct "hsem" as "[%hdom hsem]".
    iExists ℓ, t, (subst_ty σ <$> σB), σt, fields, ifields. 
    iSplit.
    { iPureIntro; split; first done.
      split.
      { by eapply inherits_using_trans; last by econstructor. }
      split; first done.
      split; last done.
      rewrite hσ map_subst_ty_subst //.
      apply inherits_using_wf in hin => //.
      destruct hin as (? & ? &? &? & ? & hL & _).
      apply extends_using_wf in hext => //.
      destruct hext as (? & ? & ? & ? & hF & ? & _).
      clear hdom; simplify_eq.
      by rewrite hL.
    }
    iSplit; last done.
    iSplit; first by iPureIntro.
    iIntros (f ty) "%hf".
    by iApply "hsem".
  Qed.

  (* Main meat for A <: B → [|A|] ⊆ [|B|] *)
  Theorem subtype_is_inclusion_aux:
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    ∀ (A B: lang_ty), A <: B →
    ∀ (env: interp_env) v,
    interp_type_pre interp_type A env v -∗
    interp_type_pre interp_type B env v.
  Proof.
    move => ? ? ?.
    induction 1 as [A | A σA B σB adef hΔ hlen hext | | | | A | A B h
      | A B h | A B C h0 hi0 h1 hi1 | A B | A B | A B C h0 hi0 h1 hi1
      | A | A B C h0 hi0 h1 hi1 ];
    move => env v.
    - rewrite /interp_mixed.
      elim: A v => //.
      + move => v; iIntros "h"; by repeat iLeft.
      + move => v; iIntros "h"; by iLeft; iRight; iLeft.
      + move => v; by rewrite /interp_nothing; iIntros "h".
      + move => cname targs _ v.
        iIntros "h".
        iLeft; iRight; iRight.
        by iExists cname, targs.
      + move => v; iIntros "h"; by iRight.
      + move => v; by iIntros "h"; iLeft.
      + move => s t hs ht v.
        rewrite /interp_union.
        iIntros "h".
        iDestruct "h" as "[ h | h ]"; first by iApply hs.
        by iApply ht.
      + move => s t hs ht v.
        rewrite /interp_inter.
        iIntros "h".
        iDestruct "h" as "[? _]"; by iApply hs.
      + move => n v.
        rewrite /interp_generic.
        iIntros "hv".
        destruct env as [env henv] => /=.
        rewrite Forall_forall in henv.
        destruct (decide (n < length env)) as [hlt | hge].
        * iApply henv; last done.
          apply lookup_lt_is_Some_2 in hlt as [ t ht ].
          rewrite /interp_generic ht /=.
          by apply elem_of_list_lookup_2 in ht.
        * rewrite /interp_generic lookup_ge_None_2 /=; last by apply not_lt.
          done.
      + move => cname v;
        rewrite /interp_ex.
        iIntros "hv".
        iDestruct "hv" as (targs) "hv".
        iLeft; iRight; iRight.
        by iExists _, _.
    - by rewrite -!interp_type_unfold; iApply extends_using_is_inclusion.
    - by rewrite /= /interp_mixed.
    - iIntros "h"; by iLeft.
    - iIntros "h"; by iRight; iLeft.
    - iIntros "H".
      iRight; iRight.
      by iExists A, _.
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
      iApply hi1 => //.
      by iApply hi0.
  Qed.

  (* A <: B → [|A|] ⊆ [|B|] *)
  Theorem subtype_is_inclusion:
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    ∀ A B, A <: B →
    ∀ (env: interp_env),
    ∀ v, interp_type A env v -∗ interp_type B env v.
  Proof.
    move => ??? A B hAB env v.
    rewrite !interp_type_unfold.
    by iApply subtype_is_inclusion_aux.
  Qed.

  (* Specialized version for existential types. Will help during the
   * proof of adequacy for runtime checks.
   *)
  Theorem inherits_is_ex_inclusion:
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    ∀ A B, inherits A B →
    ∀ (env: interp_env),
    ∀ v, interp_type (ExT A) env v -∗ interp_type (ExT B) env v.
  Proof.
    move => ???.
    induction 1 as [ x | x y z hxy hyz hi ] => // σi v.
    rewrite interp_ex_unfold.
    iIntros "H".
    iApply hi; clear hyz hi.
    iDestruct "H" as (σx) "H".
    inv hxy.
    iAssert (interp_type (ClassT y (subst_ty σx <$> σB)) σi v) with "[H]" as "Hext".
    { iApply extends_using_is_inclusion => //.
      - by econstructor.
      - by rewrite interp_class_unfold.
    }
    rewrite interp_class_unfold interp_ex_unfold.
    by iExists (subst_ty σx <$> σB).
  Qed.

  Definition interp_local_tys
    σi (lty : local_tys) (le : local_env) : iProp Σ :=
    (∀ v ty, ⌜lty !! v = Some ty⌝ -∗
    ∃ val, ⌜le !! v = Some val⌝ ∗ interp_type ty σi val)%I.

  Lemma interp_local_tys_is_inclusion (σi: interp_env)  lty rty le:
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    Forall (λ (i: interp Σ), ∀ v, Persistent (i v)) σi →
    lty <:< rty →
    interp_local_tys σi lty le -∗
    interp_local_tys σi rty le.
  Proof.
    move => ??? hpers hsub; iIntros "Hle" (v ty) "%Hv".
    apply hsub in Hv as (B & hB & hsubB).
    iDestruct ("Hle" $! v B hB) as (val) "[%Hv' #H]".
    iExists val; iSplitR; first done.
    by iApply subtype_is_inclusion.
  Qed.

  (* Helper to lift the conclusions of interp_class into a super class *)
  Lemma interp_fields_inclusion σi t σt fields ifields σ C rec:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
    inherits_using t C σ →
    interp_fields σi t σt fields ifields rec -∗
    interp_fields σi C (subst_ty σt <$> σ) fields ifields rec.
  Proof.
    move => ?? hb hin.
    rewrite /interp_fields.
    iIntros "[%hdom #H]".
    iSplit; first done.
    iIntros (f ty) "%hf".
    assert (hfC: has_field f t (subst_ty σ ty)) by (by eapply has_field_inherits_using).
    iSpecialize ("H" $! f (subst_ty σ ty) hfC).
    rewrite subst_ty_subst //.
    apply has_field_bounded in hf => //.
    destruct hf as (def & hdef & hfty).
    apply inherits_using_wf in hin => //.
    destruct hin as (? & ? & ? & ? & _ & hL & _).
    simplify_eq.
    by rewrite hL.
  Qed.
End proofs.
