(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
From stdpp Require Import base strings gmap stringmap fin_maps natmap list.

Section MissingHelpers.
  Context {A B: Type} (f: A → B).

  Lemma list_fmap_equiv_ext_elem_of `{!Equiv B} (g : A → B) l :
        (∀ x, x ∈ l → f x ≡ g x) → f <$> l ≡ g <$> l.
  Proof.
    induction l as [ | hd tl hi]; intro h; simpl in *.
    { by constructor. }
    f_equiv.
    { apply h; by constructor. }
    apply hi; intros x hin.
    apply h; by constructor.
  Qed.
End MissingHelpers.


From iris.base_logic Require Import upred derived.
From iris.base_logic.lib Require Import iprop own.
From iris.algebra Require Import ofe cmra gmap_view.
From iris.proofmode Require Import tactics.

From shack Require Import lang progdef subtype typing eval heap modality.

Section Helpers.
  Context { Σ: gFunctors }.

  Fixpoint iForall3 {A B C : Type} (P : A → B → C → iProp Σ)
    (As : list A) (Bs: list B) (Cs : list C) {struct As}  : iProp Σ :=
    match As, Bs, Cs with
    | [], [], [] => True%I
    | A :: As, B :: Bs, C :: Cs => (P A B C ∗ iForall3 P As Bs Cs)%I
    | _, _, _ => False%I
    end.

  Lemma iForall3_length {A B C : Type} (P: A → B → C → iProp Σ)
     As Bs Cs: ⊢ iForall3 P As Bs Cs → ⌜length As = length Bs ∧ length Bs = length Cs⌝.
  Proof.
    revert Bs Cs.
    induction As as [ | a As hi];
      case => [ | b Bs];
      case => [ | c Cs]; iIntros "h" => //=.
    iDestruct "h" as "[_ h]".
    iDestruct (hi with "h") as "%h".
    by destruct h as [-> ->].
  Qed.

  Lemma iForall3_forall_1 {A B C : Type} (P: A → B → C → iProp Σ)
     As Bs Cs: ⊢ iForall3 P As Bs Cs →
     ∀ k a b c, ⌜As !! k = Some a⌝ → ⌜Bs !! k = Some b⌝ → ⌜Cs !! k = Some c⌝ →
     P a b c.
  Proof.
    revert Bs Cs.
    induction As as [ | a As hi];
      case => [ | b Bs];
      case => [ | c Cs]; iIntros "h" (k u v w hu hv hw)=> //=.
    destruct k as [ | k].
    - case: hu => ->.
      case: hv => ->.
      case: hw => ->.
      by iDestruct "h" as "[? ?]".
    - iDestruct "h" as "[_ h]".
      iDestruct ((hi Bs Cs) with "h") as "h".
      by iApply "h".
  Qed.
End Helpers.

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
   * Σi is here to interpret generic types.
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

  Notation ty_interpO := (lang_ty -d> listO (interpO Σ) -n> interpO Σ).

  Lemma ty_interpO_ne : ∀ (rec: ty_interpO) ty, NonExpansive (rec ty).
  Proof.
    move => rec ty.
    apply _.
  Qed.

  Definition interp_variance (v: variance) (i0 i1: interp Σ) : iProp Σ :=
    match v with
    | Invariant => ∀ w, i0 w ∗-∗ i1 w
    | Covariant => ∀ w, i0 w -∗ i1 w
    | Contravariant => ∀ w, i1 w -∗ i0 w
    end.

  (* See
   * https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/base_logic/lib/invariants.v#L10
   * for example about `seal`.
   *)
  Definition interp_tag_def
    (rec : ty_interpO)
    (Σi : list (interp Σ))
    (C: tag)
    : interp Σ :=
    Interp (
      λ (w : value), (∃ ℓ t cdef σ (Σt: list (interp Σ))
       (fields: stringmap ((visibility * lang_ty) * tag))
       (ifields: gmapO string (laterO (sem_typeO Σ))),
      ⌜w = LocV ℓ ∧
       Δ !! C = Some cdef ∧
       inherits_using t C σ ∧
       has_fields t fields ∧
       dom fields = dom ifields⌝ ∗

       □ ▷ (∀ k v i0 i1,
         ⌜cdef.(generics) !! k = Some v⌝ →
         ((λ ty, rec ty Σt) <$> σ) !! k ≡ Some i0 →
         Σi !! k ≡ Some i1 →
         interp_variance v i0 i1) ∗

      (∀ f vis ty orig, ⌜has_field f t vis ty orig⌝ -∗
        ifields !! f ≡ Some (Next (interp_car (rec ty Σt)))) ∗

      (ℓ ↦ (t, ifields)))%I
    ).

   Local Definition interp_tag_aux
     (rec : ty_interpO) (Σi : list (interp Σ)) (C: tag)
     : seal (@interp_tag_def rec Σi C).
   Proof. by eexists. Qed.

   Definition interp_tag (rec: ty_interpO) (Σi: list (interp Σ)) (C: tag) :=
     (interp_tag_aux rec Σi C).(unseal).

   Definition interp_tag_unseal 
     (rec : ty_interpO) (Σi : list (interp Σ)) (C: tag)
     : interp_tag rec Σi C = interp_tag_def rec Σi C :=
     (interp_tag_aux rec Σi C).(seal_eq).

  Definition interp_ex (rec: ty_interpO) C : interp Σ :=
    Interp (λ (w: value),
      (∃ Σi cdef, ⌜Δ !! C = Some cdef ∧ length Σi = length cdef.(generics)⌝ ∗
      interp_tag rec Σi C w)%I).

  Definition interp_nonnull (rec : ty_interpO) : interp Σ :=
    Interp (
      λ (v : value),
      ((interp_int v) ∨
      (interp_bool v) ∨
      (∃ t, interp_ex rec t v))%I
    ).

  Definition interp_mixed (rec: ty_interpO) : interp Σ :=
    Interp (λ (v: value), (interp_nonnull rec v ∨ interp_null v)%I).

  Definition interp_generic (Σi : list (interp Σ)) (tv: nat) : interp Σ :=
    default interp_nothing (Σi !! tv).

  (* we use a blend of Coq/Iris recursion, the
     Coq recursion lets us handle simple structural
     cases, and we use Iris' recursion to deal with
     the more complicated case of class types.
  *)
  Section interp_type_pre_rec.
    Variable (rec: ty_interpO).

    Fixpoint go (Σi: listO (interpO Σ)) (typ: lang_ty) : interp Σ :=
      match typ with
      | IntT => interp_int
      | BoolT => interp_bool
      | NothingT => interp_nothing
      | MixedT => interp_mixed rec
      | ClassT A σA =>
          let Σi := (go Σi) <$> σA in
          interp_tag rec Σi A
      | NullT => interp_null
      | NonNullT => interp_nonnull rec
      | UnionT A B => interp_union (go Σi A) (go Σi B)
      | InterT A B => interp_inter (go Σi A) (go Σi B)
      | GenT n => interp_generic Σi n
      | ExT cname => interp_ex rec cname
      end.
  End interp_type_pre_rec.

 Local Instance interp_tag_ne C (rec: ty_interpO) :
    NonExpansive (λ Σi, interp_tag rec Σi C).
  Proof.
    move => n x y h.
    rewrite !interp_tag_unseal /interp_tag_def => v.
    rewrite /interp_fun !interp_car_simpl /interp_variance.
    by repeat f_equiv.
  Qed.

  Local Instance go_ne (rec: ty_interpO) (ty: lang_ty) :
    NonExpansive (λ Σi, go rec Σi ty).
  Proof.
    induction ty as [ | | | | A σ hi | | | A B hA hB | A B hA hB | i | cname ] => //= n x y h.
    - apply interp_tag_ne.
      rewrite Forall_forall in hi.
      apply list_dist_lookup => k.
      rewrite !list_lookup_fmap.
      destruct (σ !! k) as [ ty | ] eqn:hty => //=.
      f_equiv.
      apply hi => //.
      by apply elem_of_list_lookup_2 in hty.
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
  Qed.

  Definition interp_type_pre (rec : ty_interpO) : ty_interpO :=
    λ (typ : lang_ty), λne (Σi: listO (interpO Σ)), go rec Σi typ.

  Global Instance interp_type_pre_persistent (rec: ty_interpO) :
    ∀ t σi v, Persistent (interp_type_pre rec t σi v).
  Proof. by move => ???; apply _. Qed.

  Global Instance interp_tag_contractive Σi C:
    Contractive (λ rec, interp_tag rec Σi C). 
  Proof.
    move => n x y h.
    rewrite !interp_tag_unseal /interp_tag_def => v.
    rewrite /interp_fun !interp_car_simpl /interp_variance.
    do 16 f_equiv.
    - f_equiv; f_contractive.
      do 12 f_equiv.
      apply Forall2_fmap, Forall_Forall2_diag, Forall_forall => ? hin.
      f_equiv.
      by  f_equiv.
    - do 12 f_equiv.
      f_contractive.
      by repeat f_equiv.
  Qed.

  Global Instance interp_ex_contractive C: Contractive (λ rec, interp_ex rec C).
  Proof.
    rewrite /interp_ex => n i1 i2 hdist v.
    rewrite /interp_fun !interp_car_simpl.
    do 5 f_equiv.
    by apply interp_tag_contractive.
  Qed.

  Global Instance interp_nonnull_contractive: Contractive interp_nonnull.
  Proof.
    rewrite /interp_nonnull => n i1 i2 hdist v.
    rewrite /interp_fun !interp_car_simpl.
    do 4 f_equiv.
    by apply interp_ex_contractive.
  Qed.

  Local Instance interp_type_pre_contractive : Contractive interp_type_pre.
  Proof.
    rewrite /interp_type_pre => n rec1 rec2 hdist ty Σi /=.
    induction ty as [ | | | | C σ hi | | | A B hA hB | A B hA hB | i | C ] => /=.
    - done.
    - done.
    - done.
    - rewrite /interp_mixed => v.
      rewrite /interp_fun !interp_car_simpl.
      f_equiv.
      revert v; by apply interp_nonnull_contractive.
    - rewrite !interp_tag_unseal /interp_tag_def => v.
      rewrite /interp_fun !interp_car_simpl /interp_variance.
      rewrite Forall_forall in hi.
			do 16 f_equiv.
      + f_equiv; f_contractive.
        do 10 f_equiv.
        * do 2 f_equiv.
          apply Forall2_fmap, Forall_Forall2_diag, Forall_forall => ? hin.
          f_equiv.
          by  f_equiv.
        * do 2 f_equiv.
          rewrite !list_lookup_fmap.
          destruct (σ !! a6) as [ ty | ] eqn:hty => //=.
          f_equiv.
          apply dist_S.
          apply hi.
          by apply elem_of_list_lookup_2 in hty. 
      + do 12 f_equiv.
        f_contractive.
        by apply hdist.
    - done.
    - by apply interp_nonnull_contractive.
    - by solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv]).
    - by solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv]).
    - done.
    - by apply interp_ex_contractive.
  Qed.

  (* the interpretation of types can now be
     defined as a fixpoint (because class types
     can be (mutually) recursive) *)
  Definition interp_type := fixpoint interp_type_pre.

  Section Unfold.
    Variable Σi : list (interpO Σ).

    (* Helper lemmas to control unfolding of some definitions *)
    Lemma interp_type_unfold (ty : lang_ty) (v : value) :
      interp_type ty Σi v ⊣⊢ interp_type_pre interp_type ty Σi v.
    Proof.
      rewrite {1}/interp_type.
      apply (fixpoint_unfold interp_type_pre ty Σi v).
    Qed.

    Lemma interp_ex_unfold t v:
      interp_type (ExT t) Σi v ⊣⊢ interp_ex interp_type t v.
    Proof. by rewrite interp_type_unfold /= /interp_ex /=. Qed.

    Lemma interp_nonnull_unfold v:
      interp_type NonNullT Σi v ⊣⊢
      (interp_int v) ∨ (interp_bool v) ∨ (∃ t, interp_ex interp_type t v)%I.
    Proof. by rewrite interp_type_unfold /= /interp_nonnull /=. Qed.

    Lemma interp_mixed_unfold v:
      interp_type MixedT Σi v ⊣⊢ interp_nonnull interp_type v ∨ interp_null v.
    Proof. by rewrite interp_type_unfold /interp_mixed /=. Qed.

    Lemma interp_union_unfold A B v:
      interp_type (UnionT A B) Σi v ⊣⊢
      interp_union (interp_type A Σi) (interp_type B Σi) v.
    Proof.
      rewrite interp_type_unfold /=.
    iSplit; iIntros "[H | H]".
    - iLeft; by rewrite interp_type_unfold.
    - iRight; by rewrite interp_type_unfold.
    - iLeft; by rewrite interp_type_unfold.
    - iRight; by rewrite interp_type_unfold.
    Qed.

    Lemma interp_inter_unfold A B v:
      interp_type (InterT A B) Σi v ⊣⊢
      interp_inter (interp_type A Σi) (interp_type B Σi) v.
    Proof.
      rewrite interp_type_unfold /=.
    iSplit; iIntros "[HL HR]".
    - rewrite !interp_type_unfold; by iSplit.
    - rewrite !interp_type_unfold; by iSplit.
    Qed.
  End Unfold.

  Lemma interp_class_unfold Σi A σA v:
    interp_type (ClassT A σA) Σi v ⊣⊢
    interp_tag interp_type ((λ ty, interp_type ty Σi) <$> σA) A v.
  Proof.
    rewrite interp_type_unfold /=.
    rewrite !interp_tag_unseal /interp_tag_def.
    rewrite /interp_fun !interp_car_simpl.
    do 31 f_equiv.
    apply list_fmap_equiv_ext => ty w.
    by rewrite interp_type_unfold.
  Qed.

  (* #hyp *)
  Global Instance interp_type_persistent :
    ∀ Σi t v, Persistent (interp_type t Σi v).
  Proof.
    move => Σi t v.
    rewrite interp_type_unfold.
    by apply _.
  Qed.

  Definition interp_list (Σi: list (interp Σ)) (σ: list lang_ty) :=
    (λ ty, interp_type ty Σi) <$> σ.

  Lemma interp_list_fold Σi σ: go interp_type Σi <$> σ ≡ interp_list Σi σ.
  Proof.
    rewrite /interp_list.
    apply list_fmap_equiv_ext_elem_of => tc htc /= w.
    by rewrite interp_type_unfold.
  Qed.

  Lemma interp_list_gen_targs Σi n:
    length Σi = n →
    interp_list Σi (gen_targs n) ≡ Σi.
  Proof.
    rewrite /interp_list => hlen.
    apply list_equiv_lookup => k.
    rewrite list_lookup_fmap.
    destruct (decide (k < n)) as [hlt | hge].
    - rewrite (lookup_gen_targs_lt n k) //=.
      rewrite -hlen in hlt.
      assert (h: is_Some (Σi !! k)) by by apply lookup_lt_is_Some_2.
      destruct h as [σi hi].
      rewrite hi.
      constructor.
      move => v.
      by rewrite interp_type_unfold /= /interp_generic hi.
    - assert (h: Σi !! k = None).
      { apply lookup_ge_None_2.
        by lia.
      }
      rewrite h.
      rewrite /gen_targs list_lookup_fmap lookup_seq_ge //.
      by lia.
  Qed.

  Lemma interp_type_subst Σi ty σ v:
    bounded (length σ) ty →
    interp_type (subst_ty σ ty) Σi v ≡
    interp_type ty (interp_list Σi σ) v.
  Proof.
    move => hbounded.
    rewrite !interp_type_unfold; revert v.
    induction ty as [ | | | | C σC hi | | | A B hA hB | A B hA hB | i | C ] => //= v.
    - rewrite !interp_tag_unseal /interp_tag_def /= /interp_variance.
      do 31 f_equiv.
      rewrite -list_fmap_compose.
      apply list_fmap_equiv_ext_elem_of => ty hin w.
      rewrite Forall_forall in hi.
      apply hi with (v := w) in hin; first by rewrite hin.
      inv hbounded.
      rewrite Forall_forall in H0.
      by apply H0.
    - inv hbounded; by rewrite hA // hB.
    - inv hbounded; by rewrite hA // hB.
    - rewrite /interp_generic list_lookup_fmap.
      destruct (σ !! i) as [ty | ] eqn:hty => /=.
      + by rewrite interp_type_unfold.
      + inv hbounded. 
        apply lookup_ge_None_1 in hty.
        by lia.
  Qed.

  Lemma interp_tag_equivI (Σ0 Σ1: list (interp Σ)):
    Σ0 ≡ Σ1 →
    ∀ A v, interp_tag interp_type Σ0 A v ≡ interp_tag interp_type Σ1 A v.
  Proof.
    move => h A v.
    rewrite !interp_tag_unseal /interp_tag_def /interp_variance /=.
    by repeat f_equiv.
  Qed.

  Lemma interp_type_equivI (Σ0 Σ1: list (interp Σ)):
    Σ0 ≡ Σ1 →
    ∀ ty v, interp_type ty Σ0 v ≡ interp_type ty Σ1 v.
  Proof.
    move => hΣ ty v.
    rewrite !interp_type_unfold; revert v.
    induction ty as [ | | | | C σC hi | | | A B hA hB | A B hA hB | i | C ] => //= v.
    - apply interp_tag_equivI.
      apply list_fmap_equiv_ext_elem_of => ty hin w.
      rewrite Forall_forall in hi.
      move: (hi ty hin w).
      by rewrite /interp_type_pre /= => ->.
    - by rewrite hA hB.
    - by rewrite hA hB.
    - rewrite /interp_generic.
      assert (hh: (∀ i0 : nat, Σ0 !! i0 ≡ Σ1 !! i0)).
      { move => j. by rewrite hΣ. }
      by rewrite (hh i).
  Qed.

  Lemma neg_interp_variance vs Σ0 Σ1:
    iForall3 interp_variance vs Σ0 Σ1 -∗
    iForall3 interp_variance (neg_variance <$> vs) Σ1 Σ0.
  Proof.
    revert Σ0 Σ1.
    induction vs as [ | v vs hi]; intros [ | ty0 Σ0] [ | ty1 Σ1] => //=.
    iIntros "[hv hi]".
    iSplitL "hv".
    - rewrite /interp_variance.
      destruct v => //=.
      iIntros (w).
      iSplit; iSpecialize ("hv" $! w); iIntros "?"; by iApply "hv".
    - by iApply hi.
  Qed.

  Lemma interp_with_mono ty vs:
    map_Forall (λ _ : string, wf_cdef_mono) Δ →
    map_Forall (λ _ : string, wf_cdef_parent Δ) Δ →
    ∀ Σ0 Σ1,
    mono vs ty →
    wf_ty ty →
    □ iForall3 interp_variance vs Σ0 Σ1 -∗
    ∀ v,
    interp_type ty Σ0 v -∗ interp_type ty Σ1 v.
  Proof.
    move => ??.
    iIntros (Σ0 Σ1 hmono hwf) "#h".
    iInduction ty as [ | | | | C σC hi | | | A B hA hB | A B hA hB | i | C ] 
        "IHty" forall (Σ0 Σ1 vs hmono) "h"; iIntros (v); rewrite !interp_type_unfold //=.
    - by iIntros.
    - rewrite !interp_tag_unseal /interp_tag_def /interp_fun !interp_car_simpl.
      iIntros "htag".
      iDestruct "htag" as (l t cdef σ Σt fields ifields h) "[#hinst [hdyn hloc]]".
      destruct h as (-> & hcdef & hinherits & hfields & hdom).
      iExists l, t, cdef, σ, Σt, fields, ifields.
      iSplitR; first by iPureIntro.
      iSplitR; last by iSplit.
      iModIntro; iNext.
      iDestruct (iForall3_length with "h") as "%hlen".
      destruct hlen as [hl0 hl1].
      iIntros (k v i0 i1 hk) "h0 h1".
      rewrite !list_lookup_fmap.
      destruct (σ !! k) as [t0 | ] eqn:ht0; last first.
      { by rewrite !option_equivI. }
      destruct (σC !! k) as [t1 | ] eqn:ht1; last first.
      { by rewrite !option_equivI. }
      rewrite /= !option_equivI.
      iAssert (iForall3 interp_variance (neg_variance <$> vs) Σ1 Σ0) as "hneg".
      { by iApply neg_interp_variance. }
      rewrite /interp_variance.
      assert (hwf1: wf_ty t1).
      { inv hwf; simplify_eq.
        by apply H3 with k.
      }
      iAssert (Some (interp_type t0 Σt) ≡ Some (interp_type t0 Σt))%I as "heq0"; first done.
      iAssert (Some (go interp_type Σ0 t1) ≡ Some (go interp_type Σ0 t1))%I as "heq1"; first done.
      iSpecialize ("hinst" $! k v (interp_type t0 Σt)  (go interp_type Σ0 t1) hk).
      rewrite !list_lookup_fmap /= ht0 ht1.
      iSpecialize ("hinst" with "heq0 heq1").
      destruct v.
      + assert (hmono0: mono vs t1).
        { inv hmono; simplify_eq.
          by apply H3 with k Invariant.
        }
        assert (hmono1: mono (neg_variance <$> vs) t1).
        { inv hmono; simplify_eq.
          by apply H4 with k Invariant.
        }
        iAssert (□ ∀ w, interp_type t1 Σ0 w -∗ interp_type t1 Σ1 w)%I as "#hc0".
        { iDestruct (big_sepL_lookup with "IHty") as "#hk"; first by exact ht1.
          by iApply ("hk" $! hwf1 Σ0 Σ1 _ hmono0 with "h").
        }
        iAssert (□ ∀ w, interp_type t1 Σ1 w -∗ interp_type t1 Σ0 w)%I as "#hc1".
        { iDestruct (big_sepL_lookup with "IHty") as "#hk"; first by exact ht1.
          by iApply ("hk" $! hwf1 Σ1 Σ0 _ hmono1 with "hneg").
        }
        iIntros (w).
        iRewrite -"h0".
        iRewrite -"h1".
        iSplit; iIntros "#?".
        * iAssert (interp_type t1 Σ1 w) as "hr"; last by rewrite !interp_type_unfold.
          iApply "hc0".
          iAssert (go interp_type Σ0 t1 w) as "hh"; last by rewrite !interp_type_unfold.
          by iApply "hinst".
        * iApply "hinst".
          iAssert (interp_type t1 Σ0 w) as "hr"; last by rewrite !interp_type_unfold.
          iApply "hc1".
          by rewrite !interp_type_unfold.
      + assert (hmono0: mono vs t1).
        { inv hmono; simplify_eq.
          by apply H3 with k Covariant.
        }
        iAssert (□ ∀ w, interp_type t1 Σ0 w -∗ interp_type t1 Σ1 w)%I as "#hc0".
        { iDestruct (big_sepL_lookup with "IHty") as "#hk"; first by exact ht1.
          by iApply ("hk" $! hwf1 Σ0 Σ1 _ hmono0 with "h").
        }
        iIntros (w).
        iRewrite -"h0".
        iRewrite -"h1".
        iIntros "#?".
        iAssert (interp_type t1 Σ1 w) as "hr"; last by rewrite !interp_type_unfold.
        iApply "hc0".
        iAssert (go interp_type Σ0 t1 w) as "hh"; last by rewrite !interp_type_unfold.
        by iApply "hinst".
      + assert (hmono1: mono (neg_variance <$> vs) t1).
        { inv hmono; simplify_eq.
          by apply H4 with k Contravariant.
        }
        iAssert (□ ∀ w, interp_type t1 Σ1 w -∗ interp_type t1 Σ0 w)%I as "#hc1".
        { iDestruct (big_sepL_lookup with "IHty") as "#hk"; first by exact ht1.
          by iApply ("hk" $! hwf1 Σ1 Σ0 _ hmono1 with "hneg").
        }
        iIntros (w).
        iRewrite -"h0".
        iRewrite -"h1".
        iIntros "#?".
        iApply "hinst".
        iAssert (interp_type t1 Σ0 w) as "hr"; last by rewrite !interp_type_unfold.
        iApply "hc1".
        by rewrite !interp_type_unfold.
    - iIntros "hh".
      iDestruct "hh" as "[hint | hh]"; first by iLeft.
      iDestruct "hh" as "[hbool | hh]"; first by (iRight; iLeft).
      by iRight; iRight.
    - inv hmono.
      inv hwf.
      iIntros "hh".
      iDestruct "hh" as "[hh | hh]".
      + iLeft.
        rewrite -!interp_type_unfold /=.
        by iApply "IHty".
      + iRight.
        rewrite -!interp_type_unfold /=.
        by iApply "IHty1".
    - inv hmono.
      inv hwf.
      iIntros "hh".
      iDestruct "hh" as "[h0 h1]".
      rewrite -!interp_type_unfold /=.
      iSplit; first by iApply "IHty".
      by iApply "IHty1".
    - iDestruct (iForall3_length with "h") as "%hl".
      destruct hl as [hl0 hl1].
      destruct (vs !! i) as [vi | ] eqn:hvi; last first.
      { destruct (Σ0 !! i) as [ ? | ] eqn:h0.
        { apply lookup_ge_None_1 in hvi.
          apply lookup_lt_Some in h0.
          by lia.
        }
        destruct (Σ1 !! i) as [ ? | ] eqn:h1.
        { apply lookup_ge_None_1 in hvi.
          apply lookup_lt_Some in h1.
          by lia.
        }
        by rewrite /interp_generic h0 h1.
      }
      destruct (Σ0 !! i) as [ i0 | ] eqn:h0; last first.
      { apply lookup_ge_None_1 in h0.
        apply lookup_lt_Some in hvi.
        by lia.
      }
      destruct (Σ1 !! i) as [ i1 | ] eqn:h1; last first.
      { apply lookup_ge_None_1 in h1.
        apply lookup_lt_Some in hvi.
        by lia.
      }
      simpl.
      iDestruct (iForall3_forall_1 with "h") as "hf".
      iSpecialize ("hf" $! i vi i0 i1 hvi h0 h1).
      iClear "h".
      rewrite /interp_variance.
      rewrite /interp_generic /= h0 h1 /=.
      inv hmono; simplify_eq.
      * iSpecialize ("hf" $! v).
        by iDestruct "hf" as "[? ?]".
      * by iSpecialize ("hf" $! v).
    - iIntros "hh".
      iDestruct "hh" as (Σt cdef h) "hh".
      destruct h as [hcdef hlen].
      iExists Σt, cdef; by iSplit.
  Qed.

  Lemma tag_extends_using_is_inclusion:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _ : string, wf_cdef_mono) Δ →
    ∀ A B σB, extends_using A B σB →
    ∀ Σi v adef,
    Δ !! A = Some adef →
    length Σi = length adef.(generics) →
    interp_tag interp_type Σi A v -∗
    interp_tag interp_type (interp_list Σi σB) B v.
  Proof.
    move => hwp hmono A B σB hext Σi v adef hadef hlen.
    rewrite !interp_tag_unseal /interp_tag_def /interp_fun !interp_car_simpl.
    iIntros "h".
    iDestruct "h" as (ℓ t adef' σ Σt fields ifields) "[%h [#hinst [hdyn hl]]]".
    destruct h as (-> & hadef' & hin & hfields & hdom); simplify_eq.
    destruct (extends_using_wf _ _ _ hwp hext) as (adef' & hadef' & hF & hwfB).
    destruct (inherits_using_wf _ _ _ hwp hin) as (tdef & htdef & htF & hwfA).
    simplify_eq.
    assert (hb: is_Some (Δ !! B)) by by inv hwfB.
    destruct hb as [bdef hbdef].
    iExists ℓ, t, bdef, (subst_ty σ <$> σB), Σt, fields, ifields.
    iSplit.
    { iPureIntro; repeat split => //.
      by eapply inherits_using_trans; last by econstructor.
    }
    iSplitR; last by iSplit.
    iModIntro; iNext.
    iIntros (k v i0 i1 hv) "h0 h1".
    destruct (σB !! k) as [tb | ] eqn:htb; last first.
    { by rewrite !list_lookup_fmap htb /= !option_equivI. }
    assert (h := hadef).
    apply hmono in h.
    rewrite /wf_cdef_mono in h.
    destruct hext as [A B adef' σB hadef' hsuper]; simplify_eq.
    rewrite hsuper in h.
    inv h; simplify_eq.
    specialize (H4 k v tb hv htb).
    specialize (H3 k v tb hv htb).
    rewrite !list_lookup_fmap htb /= !option_equivI.
    assert (hσ : length σ = length adef'.(generics)).
    { inv hwfA; by simplify_eq. }
    assert (wftb: wf_ty tb).
    { inv hwfB; simplify_eq.
      by eauto.
    }
    assert (hboundedtb:  bounded (length σ) tb).
    { rewrite Forall_forall in hF.
      rewrite hσ.
      apply hF.
      by apply elem_of_list_lookup_2 in htb.
    }
    iAssert (□ iForall3 interp_variance adef'.(generics) (interp_list Σt σ) Σi)%I as "hf0".
    { iModIntro.
      move: hlen hσ.
      generalize (generics adef') => l.
      clear.
      move => hlen hσ.
      iInduction l as [ | hd tl] "HI" forall (σ Σi hlen hσ).
      { by destruct σ; destruct Σi. }
      destruct σ as [ | ty σ] => //=.
      destruct Σi as [ | ii Σi] => //=.
      case: hlen => hlen.
      case: hσ => hσ.
      iSplitL; first by iApply ("hinst" $! 0).
      iApply "HI" => //.
      iModIntro; iIntros (k v i0 i1 hk) "#h0 #h1".
      by iApply ("hinst" $! (S k)).
    }
    iAssert (□ iForall3 interp_variance (neg_variance <$> adef'.(generics)) Σi (interp_list Σt σ))%I as "hf1".
    { by iModIntro; iApply neg_interp_variance. }
    iClear "hinst".
    destruct v.
    - assert (hmono0 : mono (generics adef') tb) by by apply H3.
      assert (hmono1 : mono (neg_variance <$> generics adef') tb) by by apply H4.
      rewrite /interp_variance /=; iIntros (w).
      iRewrite -"h0".
      iRewrite -"h1".
      iSplit; iIntros "#?".
      + iApply (interp_with_mono with "hf0") => //.
        by rewrite interp_type_subst.
      + rewrite interp_type_subst //.
        by iApply (interp_with_mono with "hf1").
    - assert (hmono0 : mono (generics adef') tb) by by apply H3.
      rewrite /interp_variance /=; iIntros (w).
      iRewrite -"h0".
      iRewrite -"h1".
      iIntros "#?".
      iApply (interp_with_mono with "hf0") => //.
      by rewrite interp_type_subst.
    - assert (hmono1 : mono (neg_variance <$> generics adef') tb) by by apply H4.
      rewrite /interp_variance /=; iIntros (w).
      iRewrite -"h0".
      iRewrite -"h1".
      iIntros "#?".
      rewrite interp_type_subst //.
      by iApply (interp_with_mono with "hf1").
  Qed.

  (* if class A<..> extends B<σB>, then for any valid substitution σA,
   * [| A<σA> |] ⊆ [| B<σA o σB> |]
   *)
  Lemma extends_using_is_inclusion:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _ : string, wf_cdef_mono) Δ →
    ∀ Σi A B σA σB v, extends_using A B σB →
    wf_ty (ClassT A σA) →
    interp_type (ClassT A σA) Σi v -∗
    interp_type (ClassT B (subst_ty σA <$> σB)) Σi v.
  Proof.
    move => ?? Σi A B σA σB v hext hwfA.
    rewrite !interp_class_unfold.
    iIntros "h".
    assert (hΣ : interp_list Σi (subst_ty σA <$> σB) ≡
                 interp_list (interp_list Σi σA) σB).
    { rewrite /interp_list -list_fmap_compose.
      apply list_fmap_equiv_ext_elem_of => ty0 hin0 /= w.
      rewrite -interp_type_subst //.
      apply extends_using_wf in hext => //.
      destruct hext as (adef & ? & hF & _).
      rewrite Forall_forall in hF.
      inv hwfA; simplify_eq.
      rewrite H3; by apply hF.
    }
    rewrite (interp_tag_equivI _ _ hΣ).
    inv hwfA.
    iApply tag_extends_using_is_inclusion => //.
    by rewrite /interp_list fmap_length.
  Qed.

  Definition interp_env_as_mixed (Σi: list (interp Σ)) :=
    ∀ i (ϕi: interp Σ),  Σi !! i = Some ϕi → ∀ v,  ϕi v -∗ interp_mixed interp_type v.

  Definition Σinterp (Σi: list (interp Σ)) (Σc : list constraint) :=
    ∀ i c, Σc !! i = Some c →
    ∀ v, interp_type_pre interp_type c.1 Σi v -∗ interp_type_pre interp_type c.2 Σi v.

  Section Inclusion.
    Hypothesis Σc: list constraint.
    Hypothesis wfΣc: Forall wf_constraint Σc.
    Hypothesis wf_parent : map_Forall (λ _cname, wf_cdef_parent Δ) Δ.
    Hypothesis wf_mono : map_Forall (λ _ : string, wf_cdef_mono) Δ.

  (* Extracting subproofs for clarity *)
  Lemma subvariance_is_inclusion_aux Σi:
    interp_env_as_mixed Σi →
    Σinterp Σi Σc →
    ∀ A adef σ0 σ1 v,
    Δ !! A = Some adef →
    wf_ty (ClassT A σ0) →
    Forall wf_ty σ1 →
    ⊢ □ iForall3 interp_variance adef.(generics) (interp_list Σi σ0) (interp_list Σi σ1) →
    interp_type (ClassT A σ0) Σi v -∗
    interp_type (ClassT A σ1) Σi v.
  Proof.
    move => ?? A adef σ0 σ1 v hadef hwfA hwfσ1.
    iIntros "#hσ #h".
    rewrite !interp_class_unfold !interp_tag_unseal /interp_tag_def /interp_fun !interp_car_simpl.
    iDestruct "h" as (l t adef' σtA Σt fields ifields h) "[#hinst [hdyn hl]]".
    destruct h as (-> & hadef' & hinherits & hfields & hdom); simplify_eq.
    iExists l, t, adef, σtA, Σt, fields, ifields.
    iSplit; first by iPureIntro.
    iSplit; last by iSplit.
    iClear "hdyn hl".
    iModIntro; iNext.
    iIntros (k v i0 i1 hv) "h0 h1".
    rewrite !list_lookup_fmap.
    destruct (σtA !! k) as [ta | ] eqn:hta; last first.
    { by rewrite !option_equivI /=. }
    destruct (σ0 !! k) as [t0 | ] eqn:ht0; last first.
    { apply inherits_using_wf in hinherits => //.
      destruct hinherits as (? & ? & ? & hwfA2).
      inv hwfA; inv hwfA2; simplify_eq.
      apply lookup_ge_None_1 in ht0.
      apply lookup_lt_Some in hv.
      by lia.
    }
    destruct (σ1 !! k) as [t1 | ] eqn:ht1; last first.
    { by rewrite !option_equivI /=. }
    iAssert (□ iForall3 interp_variance (neg_variance <$> adef.(generics)) (interp_list Σi σ1) (interp_list Σi σ0))%I as "#hσ2".
    { iModIntro. by iApply neg_interp_variance. }
    iSpecialize ("hinst" $! k v (interp_type ta Σt) (interp_type t0 Σi) hv).
    iDestruct (iForall3_forall_1 with "hσ") as "hvar".
    iDestruct (iForall3_forall_1 with "hσ2") as "hvar2".
    iClear "hσ hσ2".
    iSpecialize ("hvar" $! k v (interp_type t0 Σi) (interp_type t1 Σi) hv).
    iSpecialize ("hvar2" $! k (neg_variance v) (interp_type t1 Σi) (interp_type t0 Σi)).
    rewrite !list_lookup_fmap hta ht0 ht1 /= !option_equivI.
    rewrite /interp_variance; destruct v => /=.
    - iIntros (w).
      iRewrite -"h0".
      iRewrite -"h1".
      iSplit; iIntros "#?".
      + iApply "hvar" => //.
        by iApply "hinst".
      + iApply "hinst" => //.
        by iApply "hvar".
    - iIntros (w).
      iRewrite -"h0".
      iRewrite -"h1".
      iIntros "#?".
      iApply "hvar" => //.
      by iApply "hinst".
    - iIntros (w).
      iRewrite -"h0".
      iRewrite -"h1".
      iIntros "#?".
      iApply "hinst" => //.
      by iApply "hvar".
  Qed.

  Lemma submixed_is_inclusion_aux Σi:
    interp_env_as_mixed Σi →
    Σinterp Σi Σc →
    ∀ A v, wf_ty A →
    interp_type A Σi v -∗
    interp_type MixedT Σi v.
  Proof.
    move => wfΣi ? A v.
    rewrite !interp_type_unfold /=.
    elim: A v.
    - move => v _; iIntros "h"; by repeat iLeft.
    - move => v _; iIntros "h"; by iLeft; iRight; iLeft.
    - move => v _; by rewrite /interp_nothing; iIntros "h".
    - done.
    - move => cname targs ? v hwf.
      iIntros "h".
      iLeft; iRight; iRight.
      iExists cname.
      iExists (interp_list Σi targs).
      rewrite /= !interp_tag_unseal /interp_tag_def.
      rewrite /interp_fun !interp_car_simpl.
      iDestruct "h" as (l t cdef σ Σt fields ifields h) "[#hinst [hdyn hloc]]".
      destruct h as (-> & hcdef & ? & ? & ?).
      iExists cdef; iSplitR.
      { iPureIntro; split => //.
        rewrite fmap_length.
        inv hwf; by simplify_eq.
      }
      iExists l, t, cdef, σ, Σt, fields, ifields.
      iSplitR; first done.
      iSplit; last by iSplit.
      iClear "hdyn hloc".
      iModIntro; iNext.
      iIntros (k v i0 i1 hv) "#h0 #h1".
      iApply "hinst" => //.
      destruct (targs !! k) as [ty | ] eqn:hty; last first.
      { by rewrite !list_lookup_fmap hty !option_equivI /=. }
      rewrite /interp_list !list_lookup_fmap hty !option_equivI /=.
      iRewrite -"h1".
      iPureIntro.
      move => x.
      by rewrite interp_type_unfold.
    - move => v _; iIntros "h"; by iRight.
    - move => v _; by iIntros "h"; iLeft.
    - move => s t hs ht v hwf.
      inv hwf.
      rewrite /interp_union.
      iIntros "h".
      iDestruct "h" as "[ h | h ]"; first by iApply hs.
      by iApply ht.
    - move => s t hs ht v hwf.
      inv hwf.
      rewrite /interp_inter.
      iIntros "h".
      iDestruct "h" as "[? _]"; by iApply hs.
    - move => n v _.
      rewrite /interp_generic.
      iIntros "hv".
      destruct (decide (n < length Σi)) as [hlt | hge].
      + apply lookup_lt_is_Some_2 in hlt as [ϕ hϕ].
        iApply wfΣi; last done.
        by rewrite /= /interp_generic hϕ /=.
      + rewrite /= /interp_generic lookup_ge_None_2 /=; last by apply not_lt.
        done.
    - move => cname v _;
      rewrite /interp_ex.
      iIntros "hv".
      iDestruct "hv" as (targs) "hv".
      iLeft; iRight; iRight.
      by iExists _, _.
  Qed.

  (* Main meat for A <: B → [|A|] ⊆ [|B|] *)
  Theorem subtype_is_inclusion_aux Σi A B:
    interp_env_as_mixed Σi →
    Σinterp Σi Σc →
    Σc ⊢ A <: B →
    ∀ v,
    wf_ty A →
    interp_type_pre interp_type A Σi v -∗
    interp_type_pre interp_type B Σi v
    with subtype_targs_is_inclusion_aux Σi Vs As Bs:
    interp_env_as_mixed Σi →
    Σinterp Σi Σc →
    Forall wf_ty As →
    Forall wf_ty Bs →
    Σc ⊢ As <:Vs:> Bs →
    ⊢ □ iForall3 interp_variance Vs (interp_list Σi As) (interp_list Σi Bs).
  Proof.
    { move => wfΣi Σcoherency.
      destruct 1 as [A | A h | A σA B σB adef hΔ hlen hext
      | A adef hadef hL | A def σ0 σ1 hΔ hwfσ hσ | | | | A | A B h
      | A B h | A B C h0 h1 | A B | A B | A B C h0 h1
      | A | A B C h0 h1 | A B hin] => v hwfA.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        rewrite -!interp_type_unfold.
        by eapply submixed_is_inclusion_aux.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        rewrite /=.
        by iIntros "H".
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        rewrite -!interp_type_unfold; by iApply extends_using_is_inclusion.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        simpl.
        iIntros "h".
        iDestruct "h" as (Σt cdef h) "h".
        destruct h as (hadef' & hLt); simplify_eq.
        replace Σt with (@nil (interp Σ)) => //.
        rewrite hL in hLt.
        apply nil_length_inv in hLt.
        by rewrite hLt.
      - apply subtype_targs_is_inclusion_aux with (Σi := Σi) in hσ => //; last first.
        { by apply wf_ty_class_inv in hwfA. }
        clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        rewrite -!interp_type_unfold.
        by iApply subvariance_is_inclusion_aux.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        by rewrite /= /interp_mixed.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        iIntros "h"; by iLeft.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        iIntros "h"; by iRight; iLeft.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        iIntros "H".
        iRight; iRight.
        iExists A, (interp_list Σi targs).
        inv hwfA.
        iExists def; iSplitR.
        + by rewrite fmap_length.
        + by rewrite -interp_type_unfold -interp_class_unfold.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        by iIntros "h"; iLeft.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        by iIntros "h"; iRight.
      - clear subtype_targs_is_inclusion_aux.
        rewrite /= /interp_union. iIntros "[h | h]".
        + iApply subtype_is_inclusion_aux; [done | done | exact h0 | | ].
          * inv hwfA; by assumption.
          * by iAssumption.
        + iApply subtype_is_inclusion_aux; [done | done | exact h1 | | ].
          * inv hwfA; by assumption.
          * by iAssumption.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        iIntros "[h _]".
        by iAssumption.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        iIntros "[_ ?]".
        by iAssumption.
      - clear subtype_targs_is_inclusion_aux.
        rewrite /= /interp_inter.
        iIntros "h".
        iSplit.
        + iApply subtype_is_inclusion_aux; [done | done | exact h0 | done | ].
          by iAssumption.
        + iApply subtype_is_inclusion_aux; [done | done | exact h1 | done | ].
          by iAssumption.
      - done.
      - iIntros "h".
        iApply subtype_is_inclusion_aux; [done | done | exact h1 | | ].
        + apply subtype_wf in h0; [ | done | done | done ].
          by assumption.
        + iApply subtype_is_inclusion_aux; [done | done | exact h0 | done | ].
          by iAssumption.
      - apply elem_of_list_lookup_1 in hin as [i hin].
        by apply Σcoherency in hin.
    }
    move => wfΣi ? hwfA hwfB.
    destruct 1 as [ | ????? h0 h1 h | ????? h0 h | ????? h0 h].
    - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
      by iStartProof.
    - simpl.
      apply Forall_cons_1 in hwfA as [hA hwfA].
      apply Forall_cons_1 in hwfB as [hB hwfB].
      iSplitR.
      + iIntros (w); iModIntro; iSplit.
        * rewrite !interp_type_unfold.
          by iApply subtype_is_inclusion_aux.
        * rewrite !interp_type_unfold.
          by iApply subtype_is_inclusion_aux.
      + by iApply subtype_targs_is_inclusion_aux.
    - simpl.
      apply Forall_cons_1 in hwfA as [hA hwfA].
      apply Forall_cons_1 in hwfB as [hB hwfB].
      iSplitR.
      + iIntros (w); iModIntro.
        rewrite !interp_type_unfold.
        by iApply subtype_is_inclusion_aux.
      + by iApply subtype_targs_is_inclusion_aux.
    - simpl.
      apply Forall_cons_1 in hwfA as [hA hwfA].
      apply Forall_cons_1 in hwfB as [hB hwfB].
      iSplitR.
      + iIntros (w); iModIntro.
        rewrite !interp_type_unfold.
        by iApply subtype_is_inclusion_aux.
      + by iApply subtype_targs_is_inclusion_aux.
  Qed.

  (* A <: B → [|A|] ⊆ [|B|] *)
  Theorem subtype_is_inclusion Σi:
    interp_env_as_mixed Σi →
    Σinterp Σi Σc →
    ∀ A B, Σc ⊢ A <: B →
    ∀ v,
    wf_ty A →
    interp_type A Σi v -∗ interp_type B Σi v.
  Proof.
    move => ?? A B hAB v ?.
    rewrite !interp_type_unfold.
    by iApply subtype_is_inclusion_aux.
  Qed.

  Definition interp_this
    (C: tag)
    (Σi : list (interp Σ))
    : interp Σ :=
    Interp (
      λ (w : value), (∃ ℓ t σ (Σt: list (interp Σ))
       (fields: stringmap ((visibility * lang_ty) * tag))
       (ifields: gmapO string (laterO (sem_typeO Σ))),
      ⌜w = LocV ℓ ∧
       inherits_using t C σ ∧
       has_fields t fields ∧
       dom fields = dom ifields⌝ ∗

      ((λ ty, interp_type ty Σt) <$> σ) ≡ Σi ∗

      (∀ f vis ty orig, ⌜has_field f t vis ty orig⌝ -∗
        ifields !! f ≡ Some (Next (interp_car (interp_type ty Σt)))) ∗

      (ℓ ↦ (t, ifields)))%I
    ).

  Definition interp_this_type C (σC: list lang_ty) Σi : interp Σ :=
    interp_this C (interp_list Σi σC).

  Definition interp_local_tys Σi
    (lty : local_tys) (le : local_env) : iProp Σ := 
    interp_this_type lty.(type_of_this).1 lty.(type_of_this).2 Σi (LocV le.(vthis)) ∗
    (∀ v ty, ⌜lty.(ctxt) !! v = Some ty⌝ -∗
    ∃ val, ⌜le.(lenv) !! v = Some val⌝ ∗ interp_type ty Σi val)%I.

  Lemma interp_local_tys_is_inclusion Σi lty rty le:
    interp_env_as_mixed Σi →
    Σinterp Σi Σc →
    wf_lty lty →
    Forall (λ (i: interp Σ), ∀ v, Persistent (i v)) Σi →
    Σc ⊢ lty <:< rty →
    interp_local_tys Σi lty le -∗
    interp_local_tys Σi rty le.
  Proof.
    move => ?? hlty hpers hsub; iIntros "[#Hthis Hle]".
    destruct hsub as [hthis hsub].
    assert (hthis2: type_of_this lty = type_of_this rty).
    { rewrite /this_type in hthis.
      rewrite (surjective_pairing (type_of_this lty))
      (surjective_pairing (type_of_this rty)).
      by case : hthis => -> ->.
    }
    rewrite /this_type hthis2.
    iSplitR; first done.
    iIntros (v ty) "%Hv".
    apply hsub in Hv as (B & hB & hsubB).
    iDestruct ("Hle" $! v B hB) as (val) "[%Hv' #H]".
    iExists val; iSplitR; first done.
    iApply subtype_is_inclusion => //.
    by apply hlty in hB.
  Qed.

  (* Specialized version for existential types. Will help during the
   * proof of adequacy for runtime checks.
   *)
  Theorem inherits_is_ex_inclusion Σi:
    ∀ A B, inherits A B →
    ∀ v, interp_type (ExT A) Σi v -∗ interp_type (ExT B) Σi v.
  Proof.
    induction 1 as [ x | x y z hxy hyz hi ] => // v.
    rewrite interp_ex_unfold.
    iIntros "H".
    iApply hi; clear hyz hi.
    iDestruct "H" as (Σx xdef h) "H".
    destruct h as [hxdef hlen].
    destruct hxy as [x y xdef' σy hxdef' hsuper]; simplify_eq.
    assert (hext: extends_using x y σy) by (econstructor; by eauto).
    iDestruct ((tag_extends_using_is_inclusion wf_parent wf_mono x y σy) with "H") as "H" => //.
    rewrite interp_ex_unfold /interp_ex /=.
    apply wf_parent in hxdef'.
    rewrite /wf_cdef_parent hsuper in hxdef'.
    destruct hxdef' as [hwf _].
    inv hwf.
    iExists _, def; iSplitR; last done.
    iPureIntro.
    split => //.
    by rewrite fmap_length.
  Qed.
  End Inclusion.
End proofs.
