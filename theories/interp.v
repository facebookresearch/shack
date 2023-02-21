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

From shack Require Import lang progdef subtype eval heap modality.

Section Helpers.
  Context { Θ: gFunctors }.

  Fixpoint iForall3 {A B C : Type} (P : A → B → C → iProp Θ)
    (As : list A) (Bs: list B) (Cs : list C) {struct As}  : iProp Θ :=
    match As, Bs, Cs with
    | [], [], [] => True%I
    | A :: As, B :: Bs, C :: Cs => (P A B C ∗ iForall3 P As Bs Cs)%I
    | _, _, _ => False%I
    end.

  Lemma iForall3_length {A B C : Type} (P: A → B → C → iProp Θ) As Bs Cs:
    ⊢ iForall3 P As Bs Cs → ⌜length As = length Bs ∧ length Bs = length Cs⌝.
  Proof.
    revert Bs Cs.
    induction As as [ | a As hi];
      case => [ | b Bs];
      case => [ | c Cs]; iIntros "h" => //=.
    iDestruct "h" as "[_ h]".
    iDestruct (hi with "h") as "%h".
    by destruct h as [-> ->].
  Qed.

  Lemma iForall3_forall_1 {A B C : Type} (P: A → B → C → iProp Θ) As Bs Cs:
    ⊢ iForall3 P As Bs Cs →
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
Record interp Θ := Interp {
    interp_car :> sem_typeO Θ;
    interp_persistent v : Persistent (interp_car v)
  }.

Definition interp_fun Θ (i: interp Θ) : value → iPropO Θ := interp_car Θ i.

Coercion interp_fun : interp >-> Funclass.

Lemma interp_car_simpl : ∀ Θ c p, @interp_car Θ (Interp _ c p) = c.
Proof.
  by intros.
Qed.

Arguments Interp {_} _%I {_}.
Arguments interp_car {_} _ _ : simpl never.

Global Existing Instance interp_persistent.

Section interp_cofe.
  Context {Θ : gFunctors}.

  Global Instance interp_equiv : Equiv (interp Θ) := λ A B, ∀ w, A w ≡ B w.
  Global Instance interp_dist : Dist (interp Θ) := λ n A B, ∀ w, A w ≡{n}≡ B w.

  Lemma interp_ofe_mixin : OfeMixin (interp Θ).
  Proof. by apply (iso_ofe_mixin (interp_car : _ → value -d> _)). Qed.

  Canonical Structure interpO := Ofe (interp Θ) interp_ofe_mixin.
  Global Instance interp_cofe : Cofe interpO.
  Proof.
    apply (iso_cofe_subtype' (λ A : value -d> iPropO Θ, ∀ w, Persistent (A w))
      (@Interp _) interp_car)=> //.
    - apply _.
    - apply limit_preserving_forall=> w.
      by apply bi.limit_preserving_Persistent=> n ??.
  Qed.

  Global Instance interp_inhabited : Inhabited (interp Θ) := populate (Interp inhabitant).

  Global Instance interp_car_ne n : Proper (dist n ==> (=) ==> dist n) interp_car.
  Proof. by intros A A' ? w ? <-. Qed.

  Global Instance interp_car_ne2 : NonExpansive interp_car.
  Proof. by move => n i j h. Qed.

  Global Instance interp_car_proper : Proper ((≡) ==> (=) ==> (≡)) interp_car.
  Proof. by intros A A' ? w ? <-. Qed.

  Global Instance list_interp_cofe : Cofe (listO interpO).
  Proof. by apply _. Qed.

  Global Instance list_interp_to_interp_cofe : Cofe (listO interpO -n> interpO).
  Proof. by apply _. Qed.

  Global Instance list_interp_inhabited : Inhabited (list (interp Θ)) :=
    populate [].

  Global Instance list_interp_to_interp_inhabited :
    Inhabited (list (interp Θ) -n> interp Θ).
  Proof.  by apply _. Qed.

End interp_cofe.

Arguments interpO : clear implicits.

Section VarianceSpec.
  Class SDTClassVarianceSpec `{SDTCS: SDTClassSpec} := {
    (* Δsdt is compatible with the variance of a class *)
    Δsdt_variance: ∀ Δ kd A adef σ0 σ1,
      pdefs !! A = Some adef →
      subtype_targs Δ kd adef.(generics) σ0 σ1 →
      Δentails kd (Δ ++
                   (subst_constraints σ0 adef.(constraints)) ++
                   (subst_constraints σ1 adef.(constraints)) ++
                   (subst_constraints σ1 (Δsdt A))) (subst_constraints σ0 (Δsdt A));
  }.
End VarianceSpec.

Section proofs.
  (* assume a given set of class definitions and their SDT annotations. *)
  Context `{SDTCVS: SDTClassVarianceSpec}.

  (* Iris semantic context *)
  Context `{!sem_heapGS Θ}.

  Notation γ := sem_heap_name.

  (* now, let's interpret some types ! *)

  (* Most interpretation functions are parametrized by Σ: tvar -> interp
   * Σ is here to interpret generic types.
   *
   * We could only consider closed types and eagerly apply all top level
   * substitution, but this way makes things a bit more compositional.
   *)
  Definition interp_null : interp Θ :=
    Interp (λ(v: value), ⌜v = NullV⌝%I).

  Definition interp_int : interp Θ :=
    Interp (λ (v : value), (∃ z, ⌜v = IntV z⌝)%I).

  Definition interp_bool : interp Θ :=
    Interp (λ (v : value), (∃ b, ⌜v = BoolV b⌝)%I).

  Definition interp_union (iA : interp Θ) (iB : interp Θ) : interp Θ :=
    Interp (λ (v : value), (iA v ∨ iB v)%I).

  Definition interp_inter (iA : interp Θ) (iB : interp Θ) : interp Θ :=
    Interp (λ (v : value), (iA v ∧ iB v)%I).

  Definition interp_nothing : interp Θ :=
    Interp (λ (_: value), False%I).

  Notation ty_interpO := (lang_ty -d> interpO Θ -n> listO (interpO Θ) -n> interpO Θ).

  Lemma ty_interpO_ne : ∀ (rec: ty_interpO) ty Σthis, NonExpansive (rec ty Σthis).
  Proof.
    move => rec ty.
    by apply _.
  Qed.

  Definition interp_variance (v: variance) (i0 i1: interp Θ) : iProp Θ :=
    match v with
    | Invariant => ∀ w, i0 w ∗-∗ i1 w
    | Covariant => ∀ w, i0 w -∗ i1 w
    | Contravariant => ∀ w, i1 w -∗ i0 w
    end.

  Lemma interp_variance_reflexive v: ∀ i, ⊢ interp_variance v i i.
  Proof.
    rewrite /interp_variance; destruct v; iIntros (i) => /=.
    - by iIntros (w); iSplit; iIntros.
    - by iIntros (w); iIntros.
    - by iIntros (w); iIntros.
  Qed.

  Lemma interp_variance_equiv_l v (i0 i1 j: interp Θ):
    i0 ≡ i1 → interp_variance v i0 j ≡ interp_variance v i1 j.
  Proof.
    rewrite /interp_variance => heq.
    case: v; do 2 f_equiv; by rewrite heq.
  Qed.

  Lemma interp_variance_equiv_r v (i0 i1 j: interp Θ):
    i0 ≡ i1 → interp_variance v j i0 ≡ interp_variance v j i1.
  Proof.
    rewrite /interp_variance => heq.
    case: v; do 2 f_equiv; by rewrite heq.
  Qed.

  Lemma interp_variance_equiv_l_2 v (i0 i1 j: interp Θ):
    (i0 ≡ i1 -∗ interp_variance v i0 j ∗-∗ interp_variance v i1 j).
  Proof.
    rewrite /interp_variance.
    iIntros "heq".
    case: v.
    - iSplit; iIntros "h".
      + iIntros (w); iSplit; iIntros "h1".
        * iApply "h".
          by iRewrite "heq".
        * iRewrite -"heq".
          by iApply "h".
      + iIntros (w); iSplit; iIntros "h1".
        * iApply "h".
          by iRewrite -"heq".
        * iRewrite "heq".
          by iApply "h".
    - iSplit; iIntros "h".
      + iIntros (w) "h1".
        iApply "h".
        by iRewrite "heq".
      + iIntros (w) "h1".
        iApply "h".
        by iRewrite -"heq".
    - iSplit; iIntros "h".
      + iIntros (w) "h1".
        iRewrite -"heq".
        by iApply "h".
      + iIntros (w) "h1".
        iRewrite "heq".
        by iApply "h".
  Qed.

  Lemma interp_variance_equiv_r_2 v (i0 i1 j: interp Θ):
    (i0 ≡ i1 -∗ interp_variance v j i0 ∗-∗ interp_variance v j i1).
  Proof.
    rewrite /interp_variance.
    iIntros "heq".
    case: v.
    - iSplit; iIntros "h".
      + iIntros (w); iSplit; iIntros "h1".
        * iRewrite -"heq".
          by iApply "h".
        * iApply "h".
          by iRewrite "heq".
      + iIntros (w); iSplit; iIntros "h1".
        * iRewrite "heq".
          by iApply "h".
        * iApply "h".
          by iRewrite -"heq".
    - iSplit; iIntros "h".
      + iIntros (w) "h1".
        iRewrite -"heq".
        by iApply "h".
      + iIntros (w) "h1".
        iRewrite "heq".
        by iApply "h".
    - iSplit; iIntros "h".
      + iIntros (w) "h1".
        iApply "h".
        by iRewrite "heq".
      + iIntros (w) "h1".
        iApply "h".
        by iRewrite -"heq".
  Qed.

  Lemma iForall3_interp_reflexive vs :
    ∀ Σ, length vs = length Σ → ⊢ iForall3 interp_variance vs Σ Σ.
  Proof.
    induction vs as [ | v vs hi]; intros [ | i Σ] hlen => //=.
    case : hlen => hlen.
    iSplitL.
    - by iApply interp_variance_reflexive.
    - by iApply hi.
  Qed.

  Notation "X ≡≡ Y" := (∀ (w: value), X w ∗-∗ Y w)%I (at level 50, no associativity).

  Lemma equiv_trans (Σ0 Σ1 Σ2: sem_typeO Θ):
    Σ0 ≡≡ Σ1 -∗
    Σ1 ≡≡ Σ2 -∗
    Σ0 ≡≡ Σ2.
  Proof.
    iIntros "h0 h1" (w); iSplit; iIntros "h".
    - iApply "h1".
      by iApply "h0".
    - iApply "h0".
      by iApply "h1".
  Qed.

  (* See
   * https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/base_logic/lib/invariants.v#L10
   * for example about `seal`.
   *)
  Definition interp_tag_def
    (rec: ty_interpO)
    (C: tag)
    (Σ : list (interp Θ))
    : interp Θ :=
    (* We know the runtime tag `t` and the interpretation of the original
     * generics, `Σt`. Therefore no `Σthis` is required in here.
     * This, and some typing constraints that `this` can't appear in certain
     * positions, like constraints or extend clauses.
     *)
    let Σthis := interp_nothing in
    Interp (
      λ (w : value), (∃ ℓ t cdef tdef σ (Σt: list (interp Θ))
       (fields: stringmap ((visibility * lang_ty) * tag))
       (ifields: gmapO string (sem_typeO Θ)),
      ⌜w = LocV ℓ ∧
       pdefs !! C = Some cdef ∧
       pdefs !! t = Some tdef ∧
       length Σt = length tdef.(generics) ∧
       inherits_using t C σ ∧
       has_fields t fields ∧
       dom fields = dom ifields⌝ ∗

      □ ▷ (∀ i (ϕi: interp Θ),  ⌜Σt !! i = Some ϕi⌝ →
           ∀ v,  ϕi v -∗ rec MixedT Σthis [] v) ∗
      (* Constraints can't mention `this` *)
      □ ▷ (∀ i c, ⌜tdef.(constraints) !! i = Some c⌝ →
           ∀ v, rec c.1 Σthis Σt v -∗ rec c.2 Σthis Σt v) ∗
      (* Extend clauses can't mention `this` *)
      □ ▷ (∀ k v i0 i1,
         ⌜cdef.(generics) !! k = Some v⌝ →
         ((λ ty, rec ty Σthis Σt) <$> σ) !! k ≡ Some i0 →
         Σ !! k ≡ Some i1 →
         interp_variance v i0 i1) ∗

      □ ▷ (∀ f vis ty orig, ⌜has_field f t vis ty orig⌝ -∗
        ∃ iF, ifields !! f ≡ Some iF ∗
        iF ≡≡ (interp_car (rec (subst_gen t tdef ty) Σthis Σt))) ∗

      (ℓ ↦ (t, ifields)))%I
    ).

  Local Definition interp_tag_aux (rec : ty_interpO) C Σ
    : seal (@interp_tag_def rec C Σ).
  Proof. by eexists. Qed.

  Definition interp_tag (rec : ty_interpO) C Σ :=
    (interp_tag_aux rec C Σ).(unseal).

  Definition interp_tag_unseal (rec : ty_interpO) C Σ:
    interp_tag rec C Σ = interp_tag_def rec C Σ :=
    (interp_tag_aux rec C Σ).(seal_eq).

  Local Instance interp_tag_ne C (rec: ty_interpO):
  NonExpansive (λ Σ, interp_tag rec C Σ).
  Proof.
    move => n x y h.
    rewrite !interp_tag_unseal /interp_tag_def => v.
    rewrite /interp_fun !interp_car_simpl /interp_variance.
    by repeat f_equiv.
  Qed.

  Global Instance interp_tag_contractive C Σ:
  Contractive (λ rec, interp_tag rec C Σ).
  Proof.
    move => n x y h.
    rewrite !interp_tag_unseal /interp_tag_def => v.
    rewrite /interp_fun !interp_car_simpl /interp_variance.
    do 18 f_equiv.
    { f_equiv; f_contractive.
      by repeat f_equiv.
    }
    f_equiv.
    { f_equiv; f_contractive.
      by repeat f_equiv.
    }
    f_equiv.
    { f_equiv; f_contractive.
      do 12 f_equiv.
      apply Forall2_fmap, Forall_Forall2_diag, Forall_forall => ? hin.
      f_equiv.
      by  f_equiv.
    }
    f_equiv.
    f_equiv; f_contractive.
    by repeat f_equiv.
  Qed.

  Definition interp_exact_tag_def
    (rec : ty_interpO)
    (C: tag)
    (Σc : list (interp Θ))
    : interp Θ :=
    let Σthis := interp_nothing in
    Interp (
      λ (w : value), (∃ ℓ cdef
       (fields: stringmap ((visibility * lang_ty) * tag))
       (ifields: gmapO string (sem_typeO Θ)),
      ⌜w = LocV ℓ ∧
       pdefs !! C = Some cdef ∧
       has_fields C fields ∧
       dom fields = dom ifields⌝ ∗

      (* constraints are "no_this" so Σthis here is irrelevant *)
      □ ▷ (∀ i c, ⌜cdef.(constraints) !! i = Some c⌝ →
           ∀ v, rec c.1 Σthis Σc v -∗ rec c.2 Σthis Σc v) ∗

      (* We replace `this` with the exact runtime tag/class, so
       * Σthis here is irrelevant.
       *)
      □ ▷ (∀ f vis ty orig, ⌜has_field f C vis ty orig⌝ -∗
        ∃ iF, ifields !! f ≡ Some iF ∗
        iF ≡≡ (interp_car (rec (subst_gen C cdef ty) Σthis Σc))) ∗

      (ℓ ↦ (C, ifields)))%I
    ).

  Local Definition interp_exact_tag_aux (rec : ty_interpO) C Σ
    : seal (@interp_exact_tag_def rec C Σ).
  Proof. by eexists. Qed.

  Definition interp_exact_tag (rec : ty_interpO) C Σ :=
    (interp_exact_tag_aux rec C Σ).(unseal).

  Definition interp_exact_tag_unseal (rec : ty_interpO) C Σ:
    interp_exact_tag rec C Σ = interp_exact_tag_def rec C Σ :=
    (interp_exact_tag_aux rec C Σ).(seal_eq).

  Global Instance interp_exact_tag_contractive C Σ:
    Contractive (λ rec, interp_exact_tag rec C Σ).
  Proof.
    move => n x y h.
    rewrite !interp_exact_tag_unseal /interp_exact_tag_def => v.
    rewrite /interp_fun !interp_car_simpl /interp_variance.
    do 10 f_equiv.
    { f_equiv; f_contractive.
      by repeat f_equiv.
    }
    f_equiv.
    f_equiv; f_contractive.
    by repeat f_equiv.
  Qed.

  Definition interp_nonnull (rec : ty_interpO) : interp Θ :=
    Interp (
    λ (v : value),
    ((interp_int v) ∨
    (interp_bool v) ∨
    (∃ t (Σ: list (interp Θ)) tdef, ⌜pdefs !! t = Some tdef ∧
    length Σ = length tdef.(generics)⌝ ∗
    interp_tag rec t Σ v))%I
    ).

  Definition interp_mixed (rec: ty_interpO) : interp Θ :=
    Interp (λ (v: value), (interp_nonnull rec v ∨ interp_null v)%I).

  Definition interp_generic (Σ: list (interp Θ)) (tv: nat) : interp Θ :=
    default interp_nothing (Σ !! tv).

  Definition interp_sdt (rec: ty_interpO) : interp Θ :=
    Interp (λ (v: value),
    (∃ A (Σa: list (interp Θ)) adef, ⌜pdefs !! A = Some adef ∧
    length Σa = length adef.(generics)⌝ ∗
    (* Like normal class constraints, SDT constraints are not allowed to
     * mention the `this` type.
     *)
    let Σthisa := interp_nothing in
    (* Σa |= Δsdt A *)
    □ ▷ (∀ i c, ⌜Δsdt A !! i = Some c⌝ →
    ∀ w, rec c.1 Σthisa Σa w -∗ rec c.2 Σthisa Σa w) ∗
    (* Σa included in [| mixed |] *)
    □ ▷ (∀ i (ϕi: interp Θ),  ⌜Σa !! i = Some ϕi⌝ →
    ∀ v,  ϕi v -∗ rec MixedT Σthisa [] v) ∗
    (* Σa |= Δa *)
    □ ▷ (∀ i c, ⌜adef.(constraints) !! i = Some c⌝ →
    ∀ v, rec c.1 Σthisa Σa v -∗ rec c.2 Σthisa Σa v) ∗
    interp_tag rec A Σa v))%I.

  Definition interp_support_dynamic (rec: ty_interpO) : interp Θ :=
    Interp (λ (v: value),
    interp_int v ∨
    interp_bool v ∨
    interp_null v ∨
    interp_sdt rec v)%I.

  Definition interp_dynamic (rec: ty_interpO) : interp Θ :=
    interp_support_dynamic rec.

  (* we use a blend of Coq/Iris recursion, the
     Coq recursion lets us handle simple structural
     cases, and we use Iris' recursion to deal with
     the more complicated case of class types.
   *)
  Section interp_type_pre_rec.
    Variable (rec: ty_interpO).
    Variable (Σthis : interp Θ).

    Fixpoint go (Σ: list (interp Θ)) (typ: lang_ty) : interp Θ :=
      match typ with
      | IntT => interp_int
      | BoolT => interp_bool
      | NothingT => interp_nothing
      | MixedT => interp_mixed rec
      | ClassT true A σA =>
          let Σ := (go Σ) <$> σA in
          interp_exact_tag rec A Σ
      | ClassT false A σA =>
          let Σ := (go Σ) <$> σA in
          interp_tag rec A Σ
      | NullT => interp_null
      | NonNullT => interp_nonnull rec
      | UnionT A B => interp_union (go Σ A) (go Σ B)
      | InterT A B => interp_inter (go Σ A) (go Σ B)
      | GenT n => interp_generic Σ n
      | DynamicT => interp_dynamic rec
      | SupportDynT => interp_support_dynamic rec
      | ThisT => Σthis
      end.
  End interp_type_pre_rec.

  Local Instance interp_exact_tag_ne (rec: ty_interpO) t :
    NonExpansive (interp_exact_tag rec t).
  Proof.
    move => n x y h.
    rewrite !interp_exact_tag_unseal /interp_tag_def => v.
    rewrite /interp_fun !interp_car_simpl /interp_variance.
    by repeat f_equiv.
  Qed.

  Local Instance go_ne (rec: ty_interpO) Σthis (ty: lang_ty) :
    NonExpansive (λ Σ, go rec Σthis Σ ty).
  Proof.
    elim: ty => //=.
    - move => exact_ t σ hi n x y h.
      assert (heq : go rec Σthis x <$> σ ≡{n}≡ go rec Σthis y <$> σ).
      { rewrite Forall_lookup in hi.
        apply list_dist_lookup => k.
        rewrite !list_lookup_fmap.
        destruct (σ !! k) as [ ty | ] eqn:hty => //=.
        f_equiv.
        apply hi with (n := n) in hty.
        by apply hty.
      }
      destruct exact_.
      + by apply interp_exact_tag_ne.
      + by apply interp_tag_ne.
    - move => A B hA hB n x y h v /=.
      f_equiv.
      + revert v; by apply hA.
      + revert v; by apply hB.
    - move => A B hA hB n x y h v /=.
      f_equiv.
      + revert v; by apply hA.
      + revert v; by apply hB.
    - move => k n x y h v /=.
      assert (hl: length x = length y) by now apply Forall2_length in h.
      elim : x y k h hl => [ | hd tl hi]; case => [ | hd' tl'] i h /= hl => //.
      apply Forall2_cons in h as [hhd htl].
      case: i hi => [ | i ] hi //=.
      apply: hi; first done.
      by lia.
  Qed.

  Local Instance go_this_ne (rec: ty_interpO) (ty: lang_ty) :
    NonExpansive (λ Σthis, λne Σ, go rec Σthis Σ ty).
  Proof.
    elim : ty => //=.
    - move => exact_ t σ hi n x y h Σ v /=.
      assert (heq: go rec x Σ <$> σ ≡{n}≡ go rec y Σ <$> σ).
      { rewrite Forall_lookup in hi.
        apply list_dist_lookup => k.
        rewrite !list_lookup_fmap.
        destruct (σ !! k) as [ty | ] eqn:hty => //=.
        f_equiv.
        apply hi with (n := n) in hty.
        by apply hty.
      }
      destruct exact_.
      + by apply interp_exact_tag_ne.
      + by apply interp_tag_ne.
    - move => A B hA hB n x y h Σ v /=.
      f_equiv.
      + revert v; by apply hA.
      + revert v; by apply hB.
    - move => A B hA hB n x y h Σ v /=.
      f_equiv.
      + revert v; by apply hA.
      + revert v; by apply hB.
    - move => n x y h Σ v /=.
      by rewrite h.
  Qed.

  Definition interp_type_pre (rec : ty_interpO) : ty_interpO :=
    λ (typ : lang_ty), λne (Σthis: interp Θ), λne Σ, go rec Σthis Σ typ.

  Global Instance interp_type_pre_persistent (rec: ty_interpO) :
    ∀ t Σthis Σ v, Persistent (interp_type_pre rec t Σthis Σ v).
  Proof. by move => ???; apply _. Qed.

  Global Instance interp_nonnull_contractive: Contractive interp_nonnull.
  Proof.
    rewrite /interp_nonnull => n i1 i2 hdist v.
    rewrite /interp_fun !interp_car_simpl.
    do 10 f_equiv.
    by apply interp_tag_contractive.
  Qed.

  Local Instance interp_type_pre_contractive : Contractive interp_type_pre.
  Proof.
    rewrite /interp_type_pre => n rec1 rec2 hdist ty Σthis Σ /=.
    induction ty as [ | | | | exact_ C σ hi | | | A B hA hB | A B hA hB | i | | | ] => /=.
    - done.
    - done.
    - done.
    - rewrite /interp_mixed => v.
      rewrite /interp_fun !interp_car_simpl.
      f_equiv.
      revert v; by apply interp_nonnull_contractive.
    - destruct exact_.
      + move => w.
        rewrite !interp_exact_tag_unseal /interp_exact_tag_def.
        rewrite /interp_fun !interp_car_simpl /interp_variance.
        rewrite Forall_forall in hi.
        do 10 f_equiv.
        { f_equiv; f_contractive.
          do 8 f_equiv.
          - do 2 f_equiv; first by repeat f_equiv.
            apply Forall2_fmap, Forall_Forall2_diag, Forall_forall => ? hin.
            apply dist_S.
            by apply hi.
          - do 2 f_equiv; first by repeat f_equiv.
            apply Forall2_fmap, Forall_Forall2_diag, Forall_forall => ? hin.
            apply dist_S.
            by apply hi.
        }
        f_equiv.
        f_equiv; f_contractive.
        do 17 f_equiv.
        { by apply hdist. }
        apply Forall2_fmap, Forall_Forall2_diag, Forall_forall => ? hin.
        apply dist_S.
        by apply hi.
      + move => w.
        rewrite !interp_tag_unseal /interp_tag_def.
        rewrite /interp_fun !interp_car_simpl /interp_variance.
        rewrite Forall_forall in hi.
        do 18 f_equiv.
        { f_equiv; f_contractive.
          by repeat f_equiv.
        }
        f_equiv.
        { f_equiv; f_contractive.
          by repeat f_equiv.
        }
        f_equiv.
        { f_equiv; f_contractive.
          do 10 f_equiv.
          * do 2 f_equiv.
            apply Forall2_fmap, Forall_Forall2_diag, Forall_forall => ? hin.
            by apply hdist.
          * do 3 f_equiv.
            apply Forall2_fmap, Forall_Forall2_diag, Forall_forall => ? hin.
            apply dist_S.
            by apply hi.
        }
        f_equiv.
        f_equiv; f_contractive.
        do 16 f_equiv.
        by apply hdist.
    - done.
    - by apply interp_nonnull_contractive.
    - by solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv]).
    - by solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv]).
    - done.
    - rewrite /interp_dynamic /interp_support_dynamic /interp_sdt => v /=.
      do 11 f_equiv.
      { f_equiv; f_contractive; by repeat f_equiv. }
      f_equiv.
      { f_equiv; f_contractive; by repeat f_equiv. }
      f_equiv.
      { f_equiv; f_contractive; by repeat f_equiv. }
      by apply interp_tag_contractive.
    - rewrite /interp_dynamic /interp_support_dynamic /interp_sdt => v /=.
      do 11 f_equiv.
      { f_equiv; f_contractive; by repeat f_equiv. }
      f_equiv.
      { f_equiv; f_contractive; by repeat f_equiv. }
      f_equiv.
      { f_equiv; f_contractive; by repeat f_equiv. }
      f_equiv.
      by apply interp_tag_contractive.
    - done.
  Qed.

  Implicit Types Σ : list (interp Θ).
  Implicit Types Σthis : interp Θ.

  (* the interpretation of types can now be
     defined as a fixpoint (because class types
     can be (mutually) recursive) *)
  Definition interp_type := fixpoint interp_type_pre.

  (* TODO: use interp_inclusion a bit more, maybe introduce a notation *)
  Definition interp_inclusion (ϕ0 ϕ1: interp Θ) := (∀ v, ϕ0 v -∗ ϕ1 v)%I.
  Definition interp_as_mixed ϕ := interp_inclusion ϕ (interp_mixed interp_type).
  Definition interp_env_as_mixed Σ :=
    (∀ i (ϕi: interp Θ),  ⌜Σ !! i = Some ϕi⌝ → interp_as_mixed ϕi)%I.

  Definition Σinterp Σthis Σ (Δ : list constraint) :=
    (∀ i c, ⌜Δ !! i = Some c⌝ →
    ∀ v, interp_type c.1 Σthis Σ v -∗ interp_type c.2 Σthis Σ v)%I.

  Lemma Σinterp_cons Σthis Σ c Δ:
    interp_inclusion (interp_type c.1 Σthis Σ) (interp_type c.2 Σthis Σ) -∗
    Σinterp Σthis Σ Δ -∗
    Σinterp Σthis Σ (c :: Δ).
  Proof.
    iIntros "hc hΔ".
    iIntros (i c0 hc0 v) "#h".
    destruct i as [ | i].
    - case: hc0 => <- {c0}.
      by iApply "hc".
    - by iApply "hΔ".
  Qed.

  Lemma Σinterp_app Σthis Σ Δ0 Δ1:
    Σinterp Σthis Σ Δ0 -∗ Σinterp Σthis Σ Δ1 -∗ Σinterp Σthis Σ (Δ0 ++ Δ1).
  Proof.
    iIntros "h0 h1".
    iIntros (i c hc v) "#h".
    rewrite lookup_app in hc.
    destruct (Δ0 !! i) as [i0 | ] eqn:h0.
    - rewrite h0 in hc; case : hc => <-.
      by iApply "h0".
    - rewrite h0 in hc.
      by iApply "h1".
  Qed.

  Definition interp_list Σthis Σ (σ: list lang_ty) : list (interp Θ) :=
    (λ ty, interp_type ty Σthis Σ) <$> σ
  .

  Lemma interp_list_lookup Σthis Σ σ k:
    (interp_list Σthis Σ σ) !! k = (λ ty, interp_type ty Σthis Σ) <$> (σ !! k).
  Proof. by rewrite /interp_list list_lookup_fmap. Qed.

  Section Unfold.
    Variable Σthis : interp Θ.
    Variable Σ : list (interp Θ).

    (* Helper lemmas to control unfolding of some definitions *)
    Lemma interp_type_unfold (ty : lang_ty) :
      interp_type ty Σthis Σ ≡ interp_type_pre interp_type ty Σthis Σ.
    Proof.
      rewrite {1}/interp_type => v.
      apply (fixpoint_unfold interp_type_pre ty Σthis Σ v).
    Qed.

    Lemma interp_type_unfold_v (ty : lang_ty) (v: value):
      interp_type ty Σthis Σ v ≡ interp_type_pre interp_type ty Σthis Σ v.
    Proof.
      rewrite {1}/interp_type.
      apply (fixpoint_unfold interp_type_pre ty Σthis Σ v).
    Qed.

    (* #hyp *)
    Global Instance interp_type_persistent :
    ∀ t v, Persistent (interp_type t Σthis Σ v).
    Proof.
      move => t v.
      rewrite interp_type_unfold.
      by apply _.
    Qed.

    Lemma interp_nonnull_unfold:
      interp_type NonNullT Σthis Σ ≡ interp_nonnull interp_type.
    Proof. by rewrite interp_type_unfold /= /interp_nonnull /=. Qed.

    Lemma interp_mixed_unfold:
      interp_type MixedT Σthis Σ ≡ interp_mixed interp_type.
    Proof. by rewrite interp_type_unfold /interp_mixed /=. Qed.

    Lemma interp_mixed_unfold_v v:
      interp_type MixedT Σthis Σ v ≡ interp_mixed interp_type v.
    Proof. by rewrite interp_type_unfold /interp_mixed /=. Qed.

    Lemma interp_union_unfold A B:
      interp_type (UnionT A B) Σthis Σ ≡
      interp_union (interp_type A Σthis Σ) (interp_type B Σthis Σ).
    Proof.
      rewrite interp_type_unfold /= => v.
      iSplit; iIntros "[H | H]".
      - iLeft; by rewrite interp_type_unfold.
      - iRight; by rewrite interp_type_unfold.
      - iLeft; by rewrite interp_type_unfold.
      - iRight; by rewrite interp_type_unfold.
    Qed.

    Lemma interp_inter_unfold A B:
      interp_type (InterT A B) Σthis Σ ≡
      interp_inter (interp_type A Σthis Σ) (interp_type B Σthis Σ).
    Proof.
      rewrite interp_type_unfold /interp_inter => v /=.
      iSplit; iIntros "[HL HR]".
      - rewrite !interp_type_unfold; by iSplit.
      - rewrite !interp_type_unfold; by iSplit.
    Qed.

    Lemma interp_support_dynamic_unfold:
      interp_type SupportDynT Σthis Σ ≡ interp_support_dynamic interp_type.
    Proof.  by rewrite interp_type_unfold. Qed.

    Lemma interp_dynamic_unfold:
      interp_type DynamicT Σthis Σ ≡ interp_support_dynamic interp_type.
    Proof.  by rewrite interp_type_unfold. Qed.
  End Unfold.

  Definition interp_tag_alt
    (C: tag)
    (Σ : list (interp Θ))
    : interp Θ :=
    let Σthis := interp_nothing in
    Interp (
      λ (w : value), (∃ ℓ t cdef tdef σ (Σt : list (interp Θ))
       (fields: stringmap ((visibility * lang_ty) * tag))
       (ifields: gmapO string (sem_typeO Θ)),
      ⌜w = LocV ℓ ∧
       pdefs !! C = Some cdef ∧
       pdefs !! t = Some tdef ∧
       length Σt = length tdef.(generics) ∧
       inherits_using t C σ ∧
       has_fields t fields ∧
       dom fields = dom ifields⌝ ∗

      □ ▷ interp_env_as_mixed Σt ∗

      □ ▷ Σinterp Σthis Σt tdef.(constraints) ∗

      □ ▷ iForall3 interp_variance cdef.(generics) (interp_list Σthis Σt σ) Σ ∗

      □ ▷ (∀ f vis ty orig, ⌜has_field f t vis ty orig⌝ -∗
        ∃ iF, ifields !! f ≡ Some iF ∗
        iF ≡≡ (interp_car (interp_type (subst_gen t tdef ty) Σthis Σt))) ∗

      (ℓ ↦ (t, ifields)))%I
    ).

  Lemma interp_tag_equiv A Σ v:
    map_Forall (λ _cname, wf_cdef_parent) pdefs →
    ∀ adef, pdefs !! A = Some adef →
    length Σ = length adef.(generics) →
    interp_tag interp_type A Σ v ⊣⊢
    interp_tag_alt A Σ v.
  Proof.
    move => hwfp adef hadef hlΣ.
    rewrite !interp_tag_unseal /interp_tag_def.
    rewrite /interp_fun !interp_car_simpl /=.
    rewrite /interp_env_as_mixed /Σinterp.
    iStartProof; iSplit; iIntros "#h".
    - iDestruct "h" as (l t adef' tdef σ Σt fields ifields h) "(#hmixed & #hconstr & #hinst & #hdyn & hloc)".
      destruct h as (-> & hadef' & htdef & hlΣt &  hin & hfields & hidom); simplify_eq.
      iExists l, t, adef, tdef, σ, Σt, fields, ifields.
      iSplit => //.
      iSplit.
      { iModIntro; iNext; iIntros (i ii heq v) "hii".
        iSpecialize ("hmixed" $! i ii heq v with "hii").
        by rewrite interp_mixed_unfold.
      }
      iSplit.
      { iModIntro; iNext; iIntros (i c heq v) "hc".
        by iSpecialize ("hconstr" $! i c heq v with "hc").
      }
      iSplit; last by iSplit.
      iModIntro; iNext.
      assert (hl1 : length Σ = length σ).
      { apply inherits_using_wf in hin => //.
        destruct hin as (?&?&?&h&_).
        apply wf_tyI in h as (? & ? & ? & ?); simplify_eq.
        by rewrite hlΣ.
      }
      move: hlΣ hl1.
      generalize (generics adef) => vs; clear => hl0 hl1.
      iClear "hmixed hdyn hloc".
      iInduction vs as [ | hd tl] "HI" forall (σ Σ hl0 hl1).
      { rewrite hl0 in hl1.
        symmetry in hl1.
        apply nil_length_inv in hl1 as ->.
        by apply nil_length_inv in hl0 as ->.
      }
      destruct σ as [ | t0 σ] => /=.
      { by rewrite hl1 in hl0. }
      destruct Σ as [ | i Σ] => //=.
      case: hl0 => hl0.
      case: hl1 => hl1.
      iSplitL.
      + by iApply ("hinst" $! 0).
      + iApply "HI" => //.
        iModIntro; iIntros (k v j0 j1 hk) "#h0 #h1".
        by iApply ("hinst" $! (S k)).
    - iDestruct "h" as (l t adef' tdef σ Σt fields ifields h) "(#hmixed & #hconstr & #hinst & #hdyn & hloc)".
      destruct h as (-> & hadef' & htdef & hlΣt & hin & hfields & hidom); simplify_eq.
      iExists l, t, adef, tdef, σ, Σt, fields, ifields.
      iSplit => //.
      iSplit.
      { iModIntro; iNext; iIntros (i ii heq v) "hii".
        iSpecialize ("hmixed" $! i ii heq v with "hii").
        by rewrite interp_mixed_unfold.
      }
      iSplit.
      { iModIntro; iNext; iIntros (i c heq v) "hc".
        by iSpecialize ("hconstr" $! i c heq v with "hc").
      }
      iSplit; last by iSplit.
      iModIntro; iNext.
      assert (hl1 : length Σ = length σ).
      { apply inherits_using_wf in hin => //.
        destruct hin as (?&?&?&h&_).
        apply wf_tyI in h as (? & ? & ? & ?); simplify_eq.
        by rewrite hlΣ.
      }
      iIntros (k v i0 i1 heq) "#h0 #h1".
      move : heq hlΣ hl1.
      generalize adef.(generics); clear => vs heq hl0 hl1.
      iClear "hconstr hmixed hdyn hloc".
      iInduction vs as [ | hd tl] "HI" forall (k σ Σ heq hl0 hl1) "hinst h0 h1".
      { by destruct σ; destruct Σ. }
      destruct σ as [ | t0 σ] => //.
      destruct Σ as [ | i Σ] => //.
      case: hl0 => hl0.
      case: hl1 => hl1.
      simpl iForall3.
      iDestruct "hinst" as "[h hf]".
      destruct k as [ | k].
      + case : heq => ->.
        rewrite /= !option_equivI.
        destruct v; iIntros (w);
          iRewrite -"h0";
          iRewrite -"h1";
          by iApply "h".
      + by iApply ("HI" $! k).
  Qed.

  Definition interp_exact_tag_alt
    (C: tag)
    (Σc : list (interp Θ))
    : interp Θ :=
    let Σthis := interp_nothing in
    Interp (
      λ (w : value), (∃ ℓ cdef
       (fields: stringmap ((visibility * lang_ty) * tag))
       (ifields: gmapO string (sem_typeO Θ)),
      ⌜w = LocV ℓ ∧
       pdefs !! C = Some cdef ∧
       has_fields C fields ∧
       dom fields = dom ifields⌝ ∗

      (* constraints are "no_this" so Σthis here is irrelevant *)
      □ ▷ Σinterp Σthis Σc cdef.(constraints) ∗

      (* We replace `this` with the exact runtime tag/class, so
       * Σthis here is irrelevant.
       *)
      □ ▷ (∀ f vis ty orig, ⌜has_field f C vis ty orig⌝ -∗
        ∃ iF, ifields !! f ≡ Some iF ∗
        iF ≡≡ (interp_car (interp_type (subst_gen C cdef ty) Σthis Σc))) ∗

      (ℓ ↦ (C, ifields)))%I
    ).

  Lemma interp_exact_tag_equiv A Σ v:
    interp_exact_tag interp_type A Σ v ⊣⊢
    interp_exact_tag_alt A Σ v.
  Proof.
    rewrite !interp_exact_tag_unseal /interp_exact_tag_def.
    rewrite /interp_fun !interp_car_simpl /=.
    rewrite /Σinterp.
    by f_equiv.
  Qed.

  Definition interp_sdt_alt : interp Θ :=
    let Σthisa := interp_nothing in
    Interp (λ (v: value),
      (∃ A (Σa: list (interp Θ))  adef, ⌜pdefs !! A = Some adef ∧
        length Σa = length adef.(generics)⌝ ∗
      □ ▷ (Σinterp Σthisa Σa (Δsdt A)) ∗
      □ ▷ (interp_env_as_mixed Σa) ∗
      □ ▷ (Σinterp Σthisa Σa adef.(constraints)) ∗
      interp_tag_alt A Σa v))%I.

  Lemma interp_sdt_equiv v:
    map_Forall (λ _cname, wf_cdef_parent) pdefs →
    interp_sdt interp_type v ⊣⊢
    interp_sdt_alt v.
  Proof.
    move => hwp.
    rewrite /interp_sdt /interp_sdt_alt /interp_variance /=.
    do 6 f_equiv.
    iSplit.
    - iIntros "(%h0 & #h1 & #hmixed & #h3 & #h4)".
      destruct h0 as [hadef hlen].
      iSplit; first done.
      iSplit; first done.
      iSplit.
      { iModIntro; iNext.
        iIntros (i phi hi w) "#hphi".
        rewrite -(interp_type_unfold interp_nothing [] MixedT w).
        by iApply "hmixed".
      }
      iSplit; first done.
      by iApply interp_tag_equiv.
    - iIntros "(%h0 & #h1 & #hmixed & #h3 & #h4)".
      destruct h0 as [hadef hlen].
      iSplit; first done.
      iSplit; first done.
      iSplit.
      { iModIntro; iNext.
        iIntros (i phi hi w) "#hphi".
        rewrite interp_type_unfold.
        by iApply "hmixed".
      }
      iSplit; first done.
      by iApply interp_tag_equiv.
  Qed.

  Lemma interp_tag_equivI (Σ0 Σ1: list (interp Θ)):
    Σ0 ≡ Σ1 →
    ∀ A v, interp_tag interp_type A Σ0 v ≡ interp_tag interp_type A Σ1 v.
  Proof.
    move => h A v.
    rewrite !interp_tag_unseal /interp_tag_def /interp_variance /=.
    by repeat f_equiv.
  Qed.

  Lemma interp_exact_tag_equivI (Σ0 Σ1: list (interp Θ)):
    Σ0 ≡ Σ1 →
    ∀ A v, interp_exact_tag interp_type A Σ0 v ≡ interp_exact_tag interp_type A Σ1 v.
  Proof.
    move => heq A v.
    rewrite !interp_exact_tag_unseal /interp_exact_tag_def /interp_fun !interp_car_simpl.
    do 10 f_equiv.
    { by repeat f_equiv. }
    f_equiv.
    do 17 f_equiv.
    by rewrite heq.
  Qed.

  Lemma interp_type_pre_this_equivI (Σ0 Σ1: interp Θ) Σ:
    Σ0 ≡ Σ1 →
    ∀ ty v, interp_type_pre interp_type ty Σ0 Σ v ≡ interp_type_pre interp_type ty Σ1 Σ v.
  Proof.
    move => h.
    elim => //=.
    - move => [] t σ /Forall_lookup hi v.
      + apply interp_exact_tag_equivI.
        apply list_fmap_equiv_ext => k ty hk w.
        by apply hi with (v := w) in hk.
      + apply interp_tag_equivI.
        apply list_fmap_equiv_ext => k ty hk w.
        by apply hi with (v := w) in hk.
    - move => s t hs ht v; f_equiv; by eauto.
    - move => s t hs ht v; f_equiv; by eauto.
  Qed.

  Lemma interp_type_this_equivI (Σ0 Σ1: interp Θ) Σ:
    Σ0 ≡ Σ1 →
    ∀ ty v, interp_type ty Σ0 Σ v ≡ interp_type ty Σ1 Σ v.
  Proof.
    move => heq ty v.
    rewrite !interp_type_unfold; by apply interp_type_pre_this_equivI.
  Qed.

  Lemma interp_tag_alt_equivI (Σ0 Σ1: list (interp Θ)):
    map_Forall (λ _cname, wf_cdef_parent) pdefs →
    Σ0 ≡ Σ1 →
    ∀ A adef v,
    pdefs !! A = Some adef →
    length Σ0 = length adef.(generics) →
    interp_tag_alt A Σ0 v ≡ interp_tag_alt A Σ1 v.
  Proof.
    move => hp h A adef v hadef hlen.
    rewrite -!(interp_tag_equiv A) //; first by rewrite interp_tag_equivI.
    by rewrite -hlen h.
  Qed.

  Lemma interp_type_pre_equivI Σthis (Σ0 Σ1: list (interp Θ)):
    Σ0 ≡ Σ1 →
    ∀ ty v, interp_type_pre interp_type ty Σthis Σ0 v ≡ interp_type_pre interp_type ty Σthis Σ1 v.
  Proof.
    move => h ty.
    induction ty as [ | | | | exact_ C σ hi | | | A B hA hB | A B hA hB | i | | | ] => v //=.
    - assert (heq: go interp_type Σthis Σ0 <$> σ ≡ go interp_type Σthis Σ1 <$> σ).
      { apply list_fmap_equiv_ext => k ty hty w.
        rewrite Forall_lookup in hi.
        by eapply hi.
      }
      destruct exact_.
      + by rewrite interp_exact_tag_equivI.
      + by rewrite interp_tag_equivI.
    - f_equiv; by eauto.
    - f_equiv; by eauto.
    - rewrite /interp_generic.
      by rewrite /= h.
  Qed.

  Lemma interp_type_equivI Σthis (Σ0 Σ1: list (interp Θ)):
    Σ0 ≡ Σ1 →
    ∀ ty v, interp_type ty Σthis Σ0 v ≡ interp_type ty Σthis Σ1 v.
  Proof.
    move => h ty v.
    rewrite !interp_type_unfold.
    by rewrite interp_type_pre_equivI.
  Qed.

  Lemma interp_tag_unfold Σthis Σ A σA v:
    interp_type (ClassT false A σA) Σthis Σ v ⊣⊢
    interp_tag interp_type A (interp_list Σthis Σ σA) v.
  Proof.
    rewrite interp_type_unfold /=.
    apply interp_tag_equivI.
    rewrite /interp_list.
    apply list_fmap_equiv_ext => ? ty ? w.
    by rewrite interp_type_unfold.
  Qed.

  Lemma interp_exact_tag_unfold Σthis Σ A σA v:
    interp_type (ClassT true A σA) Σthis Σ v ⊣⊢
    interp_exact_tag interp_type A (interp_list Σthis Σ σA) v.
  Proof.
    rewrite interp_type_unfold /=.
    apply interp_exact_tag_equivI.
    rewrite /interp_list.
    apply list_fmap_equiv_ext => ? ty ? w.
    by rewrite interp_type_unfold.
  Qed.

  Lemma interp_generic_unfold Σthis Σ k:
    interp_type (GenT k) Σthis Σ ≡ interp_generic Σ k.
  Proof. by rewrite interp_type_unfold /=. Qed.

  Lemma interp_generic_unfold_v Σthis Σ k v:
    interp_type (GenT k) Σthis Σ v ⊣⊢
    interp_generic Σ k v.
  Proof. by rewrite interp_type_unfold /=. Qed.

  Lemma interp_this_unfold Σthis Σ v:
    interp_type ThisT Σthis Σ v ⊣⊢ Σthis v.
  Proof. by rewrite interp_type_unfold /=. Qed.

  Lemma interp_type_subst Σthis Σ ty σ v:
    bounded (length σ) ty →
    interp_type (subst_ty σ ty) Σthis Σ v ≡
    interp_type ty Σthis (interp_list Σthis Σ σ) v.
  Proof.
    move => hbounded.
    rewrite !interp_type_unfold; revert v.
    induction ty as [ | | | | exact_ C σC hi | | | A B hA hB | A B hA hB | i | | | ] => //= v.
    - assert (heq: go interp_type Σthis Σ <$> (subst_ty σ <$> σC) ≡
                   go interp_type Σthis (interp_list Σthis Σ σ) <$> σC).
      { rewrite -list_fmap_compose.
        apply list_fmap_equiv_ext => ? ty hin w.
        apply elem_of_list_lookup_2 in hin.
        rewrite Forall_forall in hi.
        apply hi with (v := w) in hin; first by rewrite hin.
        apply boundedI in hbounded.
        rewrite Forall_forall in hbounded.
        by apply hbounded.
      }
      destruct exact_.
      + by apply interp_exact_tag_equivI.
      + by apply interp_tag_equivI.
    - apply boundedI in hbounded as [??]; by rewrite hA // hB.
    - apply boundedI in hbounded as [??]; by rewrite hA // hB.
    - rewrite /interp_generic list_lookup_fmap.
      destruct (σ !! i) as [ty | ] eqn:hty => /=.
      + by rewrite interp_type_unfold.
      + apply boundedI in hbounded.
        apply lookup_ge_None_1 in hty.
        by lia.
  Qed.

  Lemma interp_type_no_this Σ ty v (Σ0 Σ1: interp Θ):
    no_this ty → interp_type ty Σ0 Σ v ≡ interp_type ty Σ1 Σ v.
  Proof.
    rewrite !interp_type_unfold; revert v.
    induction ty as [ | | | | exact_ C σC hi | | | A B hA hB | A B hA hB | i | | | ] => //= v hnothis.
    - assert (heq: go interp_type Σ0 Σ <$> σC ≡
                   go interp_type Σ1 Σ <$> σC).
      { apply list_fmap_equiv_ext => ? ty hin w.
        apply elem_of_list_lookup_2 in hin.
        rewrite Forall_forall in hi.
        apply hi with (v := w) in hin; first by rewrite hin.
        apply forallb_True in hnothis.
        rewrite Forall_forall in hnothis.
        by apply hnothis.
      }
      destruct exact_.
      + by apply interp_exact_tag_equivI.
      + by apply interp_tag_equivI.
    - apply andb_prop_elim in hnothis as [h0 h1].
      apply hA with v in h0.
      apply hB with v in h1.
      by f_equiv.
    - apply andb_prop_elim in hnothis as [h0 h1].
      apply hA with v in h0.
      apply hB with v in h1.
      by f_equiv.
  Qed.

  Lemma interp_list_no_this Σ σ (Σ0 Σ1: interp Θ):
    Forall no_this σ → interp_list Σ0 Σ σ ≡ interp_list Σ1 Σ σ.
  Proof.
    induction σ as [ | ty σ hi]; first done.
    case/Forall_cons => hty hσ /=.
    f_equiv; last by apply hi.
    move => v.
    by apply interp_type_no_this.
  Qed.

  Lemma Σinterp_no_this (Σ0 Σ1: interp Θ) Σ Δ:
    Forall no_this_constraint Δ →
    Σinterp Σ0 Σ Δ -∗
    Σinterp Σ1 Σ Δ.
  Proof.
    move => /Forall_lookup hno.
    iIntros "h0".
    iIntros (k c hc w) "hw".
    assert (hc0 := hc).
    apply hno in hc0 as [].
    rewrite (interp_type_no_this _ _ _ Σ1 Σ0); last done.
    rewrite (interp_type_no_this _ _ _ Σ1 Σ0); last done.
    by iApply "h0".
  Qed.

  Lemma interp_type_subst_this t tdef Σthis Σ ty v:
    pdefs !! t = Some tdef →
    length Σ = length tdef.(generics) →
    interp_type (subst_this (ClassT true t (gen_targs (length Σ))) ty) Σthis Σ v ≡
    interp_type ty (interp_exact_tag interp_type t Σ) Σ v.
  Proof.
    move => htdef hlen.
    rewrite !interp_type_unfold; revert v.
    induction ty as [ | | | | ? C σC hi | | | A B hA hB | A B hA hB | i | | | ] => //= v.
    - do 2 f_equiv.
      + move => w.
        apply interp_exact_tag_equivI.
        rewrite -list_fmap_compose.
        apply list_fmap_equiv_ext => ? ty hin w0.
        rewrite Forall_forall in hi.
        apply elem_of_list_lookup_2 in hin.
        apply hi with (v := w0) in hin.
        by rewrite hin.
      + move => w.
        apply interp_tag_equivI.
        rewrite -list_fmap_compose.
        apply list_fmap_equiv_ext => ? ty hin w0.
        rewrite Forall_forall in hi.
        apply elem_of_list_lookup_2 in hin.
        apply hi with (v := w0) in hin.
        by rewrite hin.
    - by rewrite hA hB.
    - by rewrite hA hB.
    - apply interp_exact_tag_equivI.
      apply equiv_Forall2; apply Forall2_lookup => k.
      rewrite !list_lookup_fmap.
      destruct (decide (k < length Σ)) as [hlt | hge].
      + assert (hk: is_Some (Σ !! k)) by by apply lookup_lt_is_Some_2.
        destruct hk as [phi hphi].
        rewrite lookup_seq_lt /=; last done.
        by rewrite /interp_generic hphi.
      + rewrite lookup_seq_ge /=; last by lia.
        rewrite lookup_ge_None_2; first done.
        by lia.
  Qed.

  Lemma interp_type_pre_app ty Σthis: ∀ (Σ0 Σ1: list (interp Θ)),
    bounded (length Σ0) ty →
    interp_type_pre interp_type ty Σthis Σ0 ≡
    interp_type_pre interp_type ty Σthis (Σ0 ++ Σ1).
  Proof.
    induction ty as [ | | | | exact_ A σ hi | | | A B hA hB | A B hA hB | i | | | ]
        => Σ0 Σ1 hb w //=.
    - assert (heq: go interp_type Σthis Σ0 <$> σ ≡ go interp_type Σthis (Σ0 ++ Σ1) <$> σ).
      { rewrite Forall_lookup in hi.
        apply list_fmap_equiv_ext => k ty hin w0.
        apply hi with (Σ0 := Σ0) (Σ1 := Σ1) in hin; first done.
        apply boundedI in hb.
        rewrite Forall_lookup in hb.
        by eauto.
      }
      destruct exact_.
      + by apply interp_exact_tag_equivI.
      + by apply interp_tag_equivI.
    - apply boundedI in hb as [h1 h2].
      f_equiv.
      + by apply hA with (Σ1 := Σ1) in h1.
      + by apply hB with (Σ1 := Σ1) in h2.
    - apply boundedI in hb as [h1 h2].
      f_equiv.
      + by apply hA with (Σ1 := Σ1) in h1.
      + by apply hB with (Σ1 := Σ1) in h2.
    - apply boundedI in hb.
      by rewrite /interp_generic lookup_app_l.
  Qed.

  Lemma interp_type_app ty Σthis: ∀ (Σ0 Σ1: list (interp Θ)),
    bounded (length Σ0) ty →
    interp_type ty Σthis Σ0 ≡
    interp_type ty Σthis (Σ0 ++ Σ1).
  Proof.
    move => Σ0 Σ1 hb v.
    by rewrite !interp_type_unfold interp_type_pre_app.
  Qed.

  Lemma interp_type_pre_lift ty Σthis: ∀ (Σ0 Σ1: list (interp Θ)),
    interp_type_pre interp_type (lift_ty (length Σ0) ty) Σthis (Σ0 ++ Σ1) ≡
    interp_type_pre interp_type ty Σthis Σ1.
  Proof.
    induction ty as [ | | | | exact_ A σ hi | | | A B hA hB | A B hA hB | i | | | ]
        => Σ0 Σ1 w //=.
    - assert (heq: go interp_type Σthis (Σ0 ++ Σ1) <$> (lift_ty (length Σ0) <$> σ) ≡
                   go interp_type Σthis Σ1 <$> σ).
      { rewrite Forall_lookup in hi.
        rewrite -list_fmap_compose.
        apply list_fmap_equiv_ext => k ty hin w0.
        by apply hi with (Σ0 := Σ0) (Σ1 := Σ1) in hin.
      }
      destruct exact_.
      + by apply interp_exact_tag_equivI.
      + by apply interp_tag_equivI.
    - f_equiv.
      + by apply hA with (Σ1 := Σ1).
      + by apply hB with (Σ1 := Σ1).
    - f_equiv.
      + by apply hA with (Σ1 := Σ1).
      + by apply hB with (Σ1 := Σ1).
    - rewrite /interp_generic lookup_app_r; last by apply Nat.le_add_l.
      by rewrite Nat.add_sub.
  Qed.

  Lemma interp_type_lift ty Σthis: ∀ Σ0 Σ1,
    interp_type (lift_ty (length Σ0) ty) Σthis (Σ0 ++ Σ1) ≡
    interp_type ty Σthis Σ1.
  Proof.
    move => Σ0 Σ1 v.
    by rewrite !interp_type_unfold interp_type_pre_lift.
  Qed.

  Lemma Σinterp_lift Δ Σthis: ∀ Σ0 Σ1,
    Σinterp Σthis (Σ0 ++ Σ1) (lift_constraints (length Σ0) Δ) ≡
    Σinterp Σthis Σ1 Δ.
  Proof.
    iIntros (Σ0 Σ1).
    iSplit; iIntros "hΣ"; iIntros (i c heq v) "#h".
    - rewrite -(interp_type_lift c.2 Σthis Σ0 Σ1).
      assert (heq2: (lift_constraints (length Σ0) Δ) !! i = Some (lift_constraint (length Σ0) c)).
      { by rewrite /lift_constraints list_lookup_fmap heq. }
      iApply ("hΣ" $! i (lift_constraint (length Σ0) c) heq2 v).
      by rewrite interp_type_lift.
    - apply list_lookup_fmap_inv in heq as [c0 [-> hc]].
      rewrite !interp_type_lift //.
      by iApply ("hΣ" $! i).
  Qed.

  Lemma iForall3_interp_equivI_l (Σ0 Σ1: list (interp Θ)):
    Σ0 ≡ Σ1 →
    ∀ vs (Σ: list (interp Θ)),
    iForall3 interp_variance vs Σ0 Σ ≡ iForall3 interp_variance vs Σ1 Σ.
  Proof.
    move => heq vs Σ.
    assert (hl: length Σ0 = length Σ1) by by rewrite heq.
    move : Σ Σ0 Σ1 heq hl.
    induction vs as [ | v vs hi] => Σ Σ0 Σ1 heq hl.
    { by destruct Σ0; destruct Σ1; destruct Σ. }
    destruct Σ0 as [ | i0 Σ0] => //=.
    { symmetry in hl.
      by apply nil_length_inv in hl; rewrite hl.
    }
    destruct Σ1 as [ | i1 Σ1] => //=.
    destruct Σ as [ | i Σ] => //=.
    case : hl => hl.
    apply cons_equiv_eq in heq as (i1' & Σ1' & [= -> ->] & h0 & h1).
    f_equiv.
    - rewrite /interp_variance.
      by repeat f_equiv.
    - by rewrite (hi Σ _ _ h1 hl).
  Qed.

  Lemma iForall3_interp_equivI_r (Σ0 Σ1: list (interp Θ)):
    Σ0 ≡ Σ1 →
    ∀ vs (Σ: list (interp Θ)),
    iForall3 interp_variance vs Σ Σ0 ≡ iForall3 interp_variance vs Σ Σ1.
  Proof.
    move => heq vs Σ.
    assert (hl: length Σ0 = length Σ1) by by rewrite heq.
    move : Σ Σ0 Σ1 heq hl.
    induction vs as [ | v vs hi] => Σ Σ0 Σ1 heq hl.
    { by destruct Σ0; destruct Σ1; destruct Σ. }
    destruct Σ0 as [ | i0 Σ0] => //=.
    { symmetry in hl.
      by apply nil_length_inv in hl; rewrite hl.
    }
    destruct Σ1 as [ | i1 Σ1] => //=.
    destruct Σ as [ | i Σ] => //=.
    case : hl => hl.
    apply cons_equiv_eq in heq as (i1' & Σ1' & [= -> ->] & h0 & h1).
    f_equiv.
    - rewrite /interp_variance.
      by repeat f_equiv.
    - by rewrite (hi Σ _ _ h1 hl).
  Qed.

  Lemma interp_type_rigid Σthis (Σ0 Σ1 : list (interp Θ)) t:
    map_Forall (λ _ : string, wf_cdef_parent) pdefs →
    wf_ty (ClassT true t (map GenT (seq (length Σ0) (length Σ1)))) →
    interp_tag interp_type t Σ1 ≡
    interp_type (ClassT false t (map GenT (seq (length Σ0) (length Σ1)))) Σthis (Σ0 ++ Σ1).
  Proof.
    move => hp hwf v.
    assert (h0 := hwf).
    apply wf_tyI in h0 as (? & ? & hlen & ?).
    rewrite map_length seq_length in hlen.
    assert (h:
      (λ ty, interp_type ty Σthis (Σ0 ++ Σ1)) <$> map GenT (seq (length Σ0) (length Σ1)) ≡ Σ1
    ).
    { apply list_equiv_lookup => k /=.
      rewrite !list_lookup_fmap.
      destruct (Σ1 !! k) as [ϕ | ] eqn:heq; last first.
      { rewrite heq.
        apply lookup_ge_None_1 in heq.
        by rewrite lookup_seq_ge /=.
      }
      rewrite lookup_seq_lt; last first.
      { apply mk_is_Some in heq.
        by apply lookup_lt_is_Some_1 in heq.
      }
      rewrite heq /=.
      f_equiv => w.
      rewrite interp_generic_unfold /interp_generic /= lookup_app_r; last by apply Nat.le_add_r.
      rewrite Nat.sub_add'.
      by rewrite heq.
    }
    rewrite interp_tag_unfold.
    rewrite interp_tag_equiv //.
    rewrite interp_tag_equiv //; last first.
    { by rewrite /interp_list !fmap_length seq_length. }
    rewrite /interp_tag_alt /=.
    do 22 f_equiv.
    by rewrite (iForall3_interp_equivI_r _ _ h).
  Qed.

  Lemma interp_list_gen_targs Σthis Σ n:
      length Σ = n → interp_list Σthis Σ (gen_targs n) ≡ Σ.
  Proof.
    move => hlen.
    apply list_equiv_lookup => k.
    rewrite /interp_list list_lookup_fmap.
    destruct (decide (k < n)) as [hlt | hge].
    - rewrite lookup_gen_targs_lt //= interp_generic_unfold /interp_generic /=.
      rewrite -hlen in hlt.
      by apply lookup_lt_is_Some_2 in hlt as [phi ->].
    - rewrite lookup_gen_targs_ge //=.
      rewrite lookup_ge_None_2; first done.
      + by lia.
      + by lia.
  Qed.

  Lemma iForall3_interp_gen_targs vs n Σthis Σ:
    length vs = n →
    length Σ = n →
    ⊢ iForall3 interp_variance vs (interp_list Σthis Σ (gen_targs n)) Σ.
  Proof.
    move => hl0 hl1.
    assert (heq: interp_list Σthis Σ (gen_targs n) ≡ Σ).
    { rewrite /interp_list /=.
      apply list_equiv_lookup => k.
      destruct (Σ !! k) as [i | ] eqn:hi.
      - rewrite !list_lookup_fmap !lookup_seq_lt //=.
        { f_equiv => w.
          by rewrite !interp_generic_unfold /interp_generic /= hi.
        }
        apply lookup_lt_Some in hi.
        by lia.
      - apply lookup_ge_None_1 in hi.
        rewrite /gen_targs !list_lookup_fmap /= lookup_seq_ge //.
        by lia.
    }
    rewrite (iForall3_interp_equivI_l _ _ heq).
    apply iForall3_interp_reflexive => //.
    by rewrite hl0.
  Qed.

  Lemma iForall3_interp_trans vs:
    ∀ (Σ0 Σ1 Σ2: list (interp Θ)),
    iForall3 interp_variance vs Σ0 Σ1 -∗
    iForall3 interp_variance vs Σ1 Σ2 -∗
    iForall3 interp_variance vs Σ0 Σ2.
  Proof.
    induction vs as [ | v vs hi]; move => [ | i0 Σ0] [ | i1 Σ1] [ | i2 Σ2];
        iIntros "h0 h1" => //=.
    iDestruct "h0" as "[h00 h01]".
    iDestruct "h1" as "[h10 h11]".
    iSplitL "h00 h10".
    - destruct v; iIntros (w).
      + iSplit; iIntros "h".
        * iApply "h10".
          by iApply "h00".
        * iApply "h00".
          by iApply "h10".
      + iIntros "h".
        iApply "h10".
        by iApply "h00".
      + iIntros "h".
        iApply "h00".
        by iApply "h10".
    - by iApply (hi with "h01 h11").
  Qed.

  Lemma neg_interp_variance vs (Σ0 Σ1: list (interp Θ)):
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

  Lemma iForall_invariant_sym vs Σ0 Σ1:
    iForall3 interp_variance ((λ _ : variance, Invariant) <$> vs) Σ0 Σ1 -∗
    iForall3 interp_variance ((λ _ : variance, Invariant) <$> vs) Σ1 Σ0.
  Proof.
    iIntros "h".
    iDestruct (iForall3_length with "h") as "%hlen".
    destruct hlen as [hl0 hl1].
    rewrite map_length in hl0.
    iInduction vs as [ | v vs] "IHty" forall (Σ0 Σ1 hl1 hl0) "h" => /=.
    { symmetry in hl0.
      apply nil_length_inv in hl0 as ->.
      symmetry in hl1.
      by apply nil_length_inv in hl1 as ->.
    }
    destruct Σ0 as [ | i0 Σ0]; first done.
    case: hl0 => hl0.
    destruct Σ1 as [ | i1 Σ1]; first done.
    case: hl1 => hl1.
    iDestruct "h" as "[hhd htl]".
    iSplitL "hhd".
    { iIntros (w); iSpecialize ("hhd" $! w).
      iSplit; iIntros "h"; by iApply "hhd".
    }
    by iApply "IHty".
  Qed.

  (* TODO: Find a better name *)
  Lemma interp_with_mono_helper:
    map_Forall (λ _ : string, wf_cdef_parent) pdefs →
    map_Forall (λ _ : string, wf_cdef_fields_wf) pdefs →
    map_Forall (λ _cname, wf_cdef_constraints_wf) pdefs →
    ∀ (Σ0 Σ1: list (interp Θ)),
    length Σ0 = length Σ1 →
    □ (∀ k i0 i1, ⌜Σ0 !! k = Some i0⌝ -∗ ⌜Σ1 !! k = Some i1⌝ -∗
      interp_fun _ i0 ≡≡ interp_fun _ i1) -∗
    ∀ ty Σthis, ⌜wf_ty ty⌝ -∗ (interp_type ty Σthis Σ0) ≡≡ (interp_type ty Σthis Σ1).
  Proof.
    move => ?? hwfc.
    iLöb as "IHL".
    iIntros (Σ0 Σ1 hlen) "#heq".
    iIntros (ty Σthis hwf v).
    rewrite !interp_type_unfold /=.
    iInduction ty as [ | | | | exact_ C σC hi | | | A B hA hB | A B hA hB | i | | | ]
        "IHty" forall (Σ0 Σ1 v hlen) "heq" => /=.
    - iSplit; by iIntros.
    - iSplit; by iIntros.
    - iSplit; by iIntros.
    - iSplit; by iIntros.
    - assert (hlen2: length (go interp_type Σthis Σ0 <$> σC) =
        length (go interp_type Σthis Σ1 <$> σC)) by by rewrite !fmap_length.
      iAssert ( □ (∀ (k0 : nat) (i0 i1 : interp Θ),
          ⌜(go interp_type Σthis Σ0 <$> σC) !! k0 = Some i0⌝ -∗
          ⌜(go interp_type Σthis Σ1 <$> σC) !! k0 = Some i1⌝ -∗
            i0 ≡≡ i1))%I as "#hh".
      { iModIntro; iIntros (j i0 i1 h0 h1 w).
        apply list_lookup_fmap_inv in h0 as [tj [-> htj]].
        rewrite list_lookup_fmap htj /= in h1.
        case : h1 => h1.
        iDestruct (big_sepL_lookup with "IHty") as "#hj"; first by exact htj.
        rewrite -h1.
        iApply "hj" => //.
        iPureIntro.
        apply wf_tyI in hwf as (? & ?& ? & hwf); simplify_eq.
        rewrite Forall_lookup in hwf; by apply hwf in htj.
      }
      destruct exact_.
      + rewrite !interp_exact_tag_unseal /interp_exact_tag_def /interp_fun !interp_car_simpl.
        iSplit; iIntros "h".
        * iDestruct "h" as (l cdef fields ifields h) "(#hconstr & #hfields & hloc)".
          destruct h as (-> & hcdef & hfields & hdom).
          iExists l, cdef, fields, ifields.
          iSplit; first done.
          iSplit.
          { iModIntro; iNext; iIntros (k c hc v) "#h".
            assert (hwf_c : wf_constraint c).
            { apply hwfc in hcdef.
              rewrite /wf_cdef_constraints_wf Forall_lookup in hcdef.
              by apply hcdef in hc.
            }
            destruct hwf_c as [].
            iSpecialize ("IHL" $!
              (go interp_type Σthis Σ0 <$> σC) (go interp_type Σthis Σ1 <$> σC)
              hlen2 with "hh").
            iSpecialize ("hconstr" $! k c hc v).
            iApply "IHL" => //.
            iApply "hconstr".
            by iApply "IHL".
          }
          iSplit; last done.
          iModIntro; iNext; iIntros (f vis ty orig hf).
          assert (hwf_f : wf_ty (subst_gen C cdef ty)).
          { apply has_field_wf in hf => //.
            apply wf_ty_subst_this => //.
            econstructor => //.
            - by rewrite length_gen_targs.
            - by apply gen_targs_wf_2.
          }
          iSpecialize ("IHL" $!
            (go interp_type Σthis Σ0 <$> σC) (go interp_type Σthis Σ1 <$> σC)
            hlen2 with "hh").
          iSpecialize ("hfields" $! f vis ty orig hf).
          iDestruct "hfields" as (iF) "[hiF hiF_eq]".
          iExists iF; iSplit; first done.
          iIntros (w); iSplit; iIntros "hw".
          -- iApply "IHL" => //.
             by iApply "hiF_eq".
          -- iApply "hiF_eq".
             by iApply "IHL".
        * iDestruct "h" as (l cdef fields ifields h) "(#hconstr & #hfields & hloc)".
          destruct h as (-> & hcdef & hfields & hdom).
          iExists l, cdef, fields, ifields.
          iSplit; first done.
          iSplit.
          { iModIntro; iNext; iIntros (k c hc v) "#h".
            assert (hwf_c : wf_constraint c).
            { apply hwfc in hcdef.
              rewrite /wf_cdef_constraints_wf Forall_lookup in hcdef.
              by apply hcdef in hc.
            }
            destruct hwf_c as [].
            iSpecialize ("IHL" $!
              (go interp_type Σthis Σ0 <$> σC) (go interp_type Σthis Σ1 <$> σC)
              hlen2 with "hh").
            iSpecialize ("hconstr" $! k c hc v).
            iApply "IHL" => //.
            iApply "hconstr".
            by iApply "IHL".
          }
          iSplit; last done.
          iModIntro; iNext; iIntros (f vis ty orig hf).
          assert (hwf_f : wf_ty (subst_gen C cdef ty)).
          { apply has_field_wf in hf => //.
            apply wf_ty_subst_this => //.
            econstructor => //.
            - by rewrite length_gen_targs.
            - by apply gen_targs_wf_2.
          }
          iSpecialize ("IHL" $!
            (go interp_type Σthis Σ0 <$> σC) (go interp_type Σthis Σ1 <$> σC)
            hlen2 with "hh").
          iSpecialize ("hfields" $! f vis ty orig hf).
          iDestruct "hfields" as (iF) "[hiF hiF_eq]".
          iExists iF; iSplit; first done.
          iIntros (w); iSplit; iIntros "hw".
          -- iApply "IHL" => //.
             by iApply "hiF_eq".
          -- iApply "hiF_eq".
             by iApply "IHL".
      + rewrite !interp_tag_unseal /interp_tag_def /interp_fun !interp_car_simpl.
        iSplit; iIntros "h".
        * iDestruct "h" as (l t cdef tdef σ Σt fields ifields h) "(#hmixed & #hconstr & #hinst & #hdyn & hloc)".
          destruct h as (-> & hcdef & htdef & hlenΣt & hinherits & hfields & hdom).
          iExists l, t, cdef, tdef, σ, Σt, fields, ifields.
          iSplit; first done.
          iSplit; first done.
          iSplit; first done.
          iSplit; last by iSplit.
          iClear "hmixed hconstr hdyn".
          iModIntro; iNext; iIntros (k var i0 i1 hk) "#hi0 #hi1".
          destruct (σC !! k) as [t1 | ] eqn:ht1; last first.
          { apply lookup_ge_None_1 in ht1.
            apply lookup_lt_Some in hk.
            apply wf_tyI in hwf as (? & ? & ?hlen & _); simplify_eq.
            by lia.
          }
          iAssert ((go interp_type Σthis Σ0 <$> σC) !! k ≡ Some (go interp_type Σthis Σ0 t1))%I as "heq1".
          { by rewrite !list_lookup_fmap /= ht1. }
          iSpecialize ("hinst" $! k var i0 (go interp_type Σthis Σ0 t1) hk with "hi0 heq1").
          iSpecialize ("hh" $! k (go interp_type Σthis Σ0 t1) (go interp_type Σthis Σ1 t1)).
          rewrite !list_lookup_fmap !ht1 /=.
          iSpecialize ("hh" $! refl_equal refl_equal).
          iClear "hi0 heq1".
          rewrite option_equivI /=.
          destruct var.
          -- iIntros (w); iSplit; iIntros "hw".
             ++ iRewrite -"hi1".
                iApply "hh".
                by iApply "hinst".
             ++ iApply "hinst".
                iApply "hh".
                by iRewrite "hi1".
          -- iIntros (w); iIntros "hw".
             iRewrite -"hi1".
             iApply "hh".
             by iApply "hinst".
          -- iIntros (w); iIntros "hw".
             iApply "hinst".
             iApply "hh".
             by iRewrite "hi1".
        * iDestruct "h" as (l t cdef tdef σ Σt fields ifields h) "(#hmixed & #hconstr & #hinst & #hdyn & hloc)".
          destruct h as (-> & hcdef & htdef & hlenΣt & hinherits & hfields & hdom).
          iExists l, t, cdef, tdef, σ, Σt, fields, ifields.
          iSplit; first done.
          iSplit; first done.
          iSplit; first done.
          iSplit; last by iSplit.
          iClear "hmixed hconstr hdyn".
          iModIntro; iNext; iIntros (k var i0 i1 hk) "#hi0 #hi1".
          destruct (σC !! k) as [t1 | ] eqn:ht1; last first.
          { apply lookup_ge_None_1 in ht1.
            apply lookup_lt_Some in hk.
            apply wf_tyI in hwf as (? & ? & ?hlen & _); simplify_eq.
            by lia.
          }
          iAssert ((go interp_type Σthis Σ1 <$> σC) !! k ≡ Some (go interp_type Σthis Σ1 t1))%I as "heq1".
          { by rewrite !list_lookup_fmap /= ht1. }
          iSpecialize ("hinst" $! k var i0 (go interp_type Σthis Σ1 t1) hk with "hi0 heq1").
          iSpecialize ("hh" $! k (go interp_type Σthis Σ0 t1) (go interp_type Σthis Σ1 t1)).
          rewrite !list_lookup_fmap !ht1 /=.
          iSpecialize ("hh" $! refl_equal refl_equal).
          iClear "hi0 heq1".
          rewrite option_equivI /=.
          destruct var.
          -- iIntros (w); iSplit; iIntros "hw".
             ++ iRewrite -"hi1".
                iApply "hh".
                by iApply "hinst".
             ++ iApply "hinst".
                iApply "hh".
                by iRewrite "hi1".
          -- iIntros (w); iIntros "hw".
             iRewrite -"hi1".
             iApply "hh".
             by iApply "hinst".
          -- iIntros (w); iIntros "hw".
             iApply "hinst".
             iApply "hh".
             by iRewrite "hi1".
    - iSplit; by iIntros.
    - iSplit; by iIntros.
    - apply wf_tyI in hwf as [].
      iSplit; iIntros "[h | h]".
      + iLeft; iApply "IHty" => //.
        iModIntro; iIntros (k i1 i0 h1 h0).
        iSpecialize ("heq" $! k i0 i1 h0 h1).
        iIntros (w); iSplit; iIntros "h"; by iApply "heq".
      + iRight; iApply "IHty1" => //.
        iModIntro; iIntros (k i1 i0 h1 h0).
        iSpecialize ("heq" $! k i0 i1 h0 h1).
        iIntros (w); iSplit; iIntros "h"; by iApply "heq".
      + iLeft; by iApply "IHty".
      + iRight; by iApply "IHty1".
    - apply wf_tyI in hwf as [].
      iSplit; iIntros "[hl hr]"; iSplit.
      + iApply "IHty" => //.
        iModIntro; iIntros (k i1 i0 h1 h0).
        iSpecialize ("heq" $! k i0 i1 h0 h1).
        iIntros (w); iSplit; iIntros "h"; by iApply "heq".
      + iApply "IHty1" => //.
        iModIntro; iIntros (k i1 i0 h1 h0).
        iSpecialize ("heq" $! k i0 i1 h0 h1).
        iIntros (w); iSplit; iIntros "h"; by iApply "heq".
      + by iApply "IHty".
      + by iApply "IHty1".
    - rewrite /interp_generic.
      destruct (Σ0 !! i) as [i0 | ] eqn:h0; last first.
      { destruct (Σ1 !! i) as [i1 | ] eqn:h1; last done.
        apply lookup_ge_None_1 in h0.
        apply lookup_lt_Some in h1.
        by lia.
      }
      destruct (Σ1 !! i) as [i1 | ] eqn:h1; last first.
      { apply lookup_ge_None_1 in h1.
        apply lookup_lt_Some in h0.
        by lia.
      }
      simpl.
      by iApply ("heq" $! i i0 i1 h0 h1).
    - iSplit; iIntros "h".
      + iDestruct "h" as "[? | h]"; first by iLeft.
        iDestruct "h" as "[? | h]"; first by iRight; iLeft.
        iDestruct "h" as "[? | h]"; first by iRight; iRight; iLeft.
        by iRight; iRight; iRight.
      + iDestruct "h" as "[? | h]"; first by iLeft.
        iDestruct "h" as "[? | h]"; first by iRight; iLeft.
        iDestruct "h" as "[? | h]"; first by iRight; iRight; iLeft.
        by iRight; iRight; iRight.
    - iSplit; iIntros "h".
      + iDestruct "h" as "[? | h]"; first by iLeft.
        iDestruct "h" as "[? | h]"; first by iRight; iLeft.
        iDestruct "h" as "[? | h]"; first by iRight; iRight; iLeft.
        by iRight; iRight; iRight.
      + iDestruct "h" as "[? | h]"; first by iLeft.
        iDestruct "h" as "[? | h]"; first by iRight; iLeft.
        iDestruct "h" as "[? | h]"; first by iRight; iRight; iLeft.
        by iRight; iRight; iRight.
    - iSplit; by iIntros.
  Qed.

  Lemma iForall3_inv_equiv vs Σ0 Σ1:
    map_Forall (λ _ : string, wf_cdef_parent) pdefs →
    map_Forall (λ _ : string, wf_cdef_fields_wf) pdefs →
    map_Forall (λ _cname, wf_cdef_constraints_wf) pdefs →
    □ iForall3 interp_variance ((λ _ : variance, Invariant) <$> vs) Σ0 Σ1 -∗
    ∀ ty Σthis,
    ⌜wf_ty ty⌝ →
    interp_type ty Σthis Σ0 ≡≡ interp_type ty Σthis Σ1.
  Proof.
    move => ???.
    iIntros "#h" (ty Σthis hwf).
    iDestruct (iForall3_length with "h") as "%hlen".
    case: hlen.
    rewrite fmap_length => h0 h1.
    iApply interp_with_mono_helper => //.
    iModIntro; iIntros (k i0 i1 hi0 hi1).
    iDestruct (iForall3_forall_1 with "h") as "hf".
    assert (hv: ((λ _, Invariant) <$> vs) !! k = Some Invariant).
    { rewrite list_lookup_fmap.
      destruct (vs !! k) as [ v | ] eqn:hv => //=.
      apply lookup_ge_None_1 in hv.
      apply lookup_lt_Some in hi0.
      by lia.
    }
    by iSpecialize ("hf" $! k Invariant i0 i1 hv hi0 hi1).
  Qed.

  Lemma interp_with_mono ty vs:
    map_Forall (λ _ : string, wf_cdef_mono) pdefs →
    map_Forall (λ _ : string, wf_cdef_parent) pdefs →
    map_Forall (λ _ : string, wf_cdef_fields_wf) pdefs →
    map_Forall (λ _cname, wf_cdef_constraints_wf) pdefs →
    ∀ (Σ0 Σ1: list (interp Θ)) (Σthis: interp Θ),
    mono vs ty →
    wf_ty ty →
    □ iForall3 interp_variance vs Σ0 Σ1 -∗
    ∀ v,
    interp_type ty Σthis Σ0 v -∗ interp_type ty Σthis Σ1 v.
  Proof.
    move => ? hwfp hwff hwfc.
    iIntros (Σ0 Σ1 Σthis hmono hwf) "#h".
    iInduction ty as [ | | | | exact_ C σC hi | | | A B hA hB | A B hA hB | i | | | ]
        "IHty" forall (Σ0 Σ1 Σthis vs hmono) "h"; iIntros (v); rewrite !interp_type_unfold /=.
    - by iIntros.
    - by iIntros.
    - by iIntros.
    - by iIntros.
    - iDestruct (iForall3_length with "h") as "%hlen".
      destruct hlen as [hl0 hl1].
      destruct exact_.
      + iIntros "htag".
        rewrite !interp_exact_tag_unseal /interp_exact_tag_def /interp_fun !interp_car_simpl.
        iDestruct "htag" as (l cdef fields ifields h) "(#hconstr & #hfields & hloc)".
        destruct h as (-> & hcdef & hfields & hdom).
        iExists l, cdef, fields, ifields.
        assert (hlen: length (go interp_type Σthis Σ0 <$> σC) =
                      length (go interp_type Σthis Σ1 <$> σC)) by by rewrite !fmap_length.
        iAssert (□ (∀ k i0 i1,
          ⌜(go interp_type Σthis Σ0 <$> σC) !! k = Some i0⌝ -∗
          ⌜(go interp_type Σthis Σ1 <$> σC) !! k = Some i1⌝ -∗
          interp_fun _ i0 ≡≡ interp_fun _ i1))%I as "#hiff".
        { iModIntro; iIntros (k i0 i1 h0 h1 w).
          apply list_lookup_fmap_inv in h0 as [ty0 [-> hty0]].
          rewrite list_lookup_fmap hty0 /= in h1.
          case : h1 => <-.
          iDestruct (neg_interp_variance with "h") as "hneg".
          assert (hwf_ty0: wf_ty ty0).
          { apply wf_tyI in hwf as (? & ? & ? & hwf); simplify_eq.
            rewrite Forall_lookup in hwf.
            by apply hwf with k.
          }
          iDestruct (big_sepL_lookup with "IHty") as "#hk"; first by exact hty0.
          iSpecialize ("hk" $! hwf_ty0).
          destruct (cdef.(generics) !! k) as [ck | ] eqn:hck; last first.
          { apply lookup_ge_None_1 in hck.
            apply lookup_lt_Some in hty0.
            apply wf_tyI in hwf as (? & ? & hl & ?); simplify_eq.
            by lia.
          }
          elim/mono_classI : hmono => cdef' hcdef' hnotcontra hnotcov; simplify_eq.
          assert (hmono0: mono vs ty0).
          { eapply hnotcontra => //; by right. }
          assert (hmono1: mono (neg_variance <$> vs) ty0).
          { eapply hnotcov => //; by right. }
          iSplit; iIntros "hh".
          - iSpecialize ("hk" $! _ _ Σthis _ hmono0 with "h").
            iSpecialize ("hk" $! w).
            rewrite !interp_type_unfold.
            by iApply "hk".
          - iSpecialize ("hk" $! _ _ Σthis _ hmono1 with "hneg").
            iSpecialize ("hk" $! w).
            rewrite !interp_type_unfold.
            by iApply "hk".
        }
        iSplit; first done.
        iDestruct ((interp_with_mono_helper hwfp hwff hwfc _ _ hlen) with "hiff") as "hiff2".
        iClear "hiff".
        iSplit.
        { iModIntro; iNext; iIntros (k c hc v) "#hv".
          apply hwfc in hcdef.
          rewrite /wf_cdef_constraints_wf Forall_lookup in hcdef.
          assert (hc0 := hc).
          apply hcdef in hc0 as [].
          iApply "hiff2" => //.
          iApply "hconstr" => //.
          by iApply "hiff2".
        }
        iSplit; last done.
        iModIntro; iNext; iIntros (f vis ty orig hf).
        assert (hwf_f : wf_ty (subst_gen C cdef ty)).
        { apply has_field_wf in hf => //.
          apply wf_ty_subst_this => //.
          econstructor => //.
          - by rewrite length_gen_targs.
          - by apply gen_targs_wf_2.
        }
        iSpecialize ("hfields" $! f vis ty orig hf).
        iDestruct "hfields" as (iF) "[hiF hiff_iF]".
        iExists iF; iSplit; first done.
        iIntros (w); iSplit; iIntros "hw".
        -- iApply "hiff2" => //.
           by iApply "hiff_iF".
        -- iApply "hiff_iF".
           by iApply "hiff2".
      + iIntros "#htag".
        rewrite !interp_tag_unseal /interp_tag_def /interp_fun !interp_car_simpl.
        iDestruct "htag" as (l t cdef tdef σ Σt fields ifields h) "(#hmixed & #hconstr & #hinst & hfields & hloc)".
        destruct h as (-> & hcdef & htdef & hlΣt & hinherits & hfields & hdom).
        iExists l, t, cdef, tdef, σ, Σt, fields, ifields.
        iSplitR; first done.
        iSplitR.
        { iModIntro; iNext; iIntros (i ii heq w0) "hii".
          iSpecialize ("hmixed" $! i ii heq w0 with "hii").
          iClear "IHty h hinst".
          by rewrite interp_mixed_unfold.
        }
        iSplitR.
        { iModIntro; iNext; iIntros (i c heq w0) "hc".
          by iSpecialize ("hconstr" $! i c heq w0 with "hc").
        }
        iSplitR; last by iSplit.
        iModIntro; iNext.
        iIntros (k var i0 i1 hk) "h0 h1".
        rewrite !list_lookup_fmap /= !option_equivI /=.
        destruct (σ !! k) as [t0 | ] eqn:ht0; last done.
        destruct (σC !! k) as [t1 | ] eqn:ht1; last done.
        iDestruct (neg_interp_variance with "h") as "hneg".
        rewrite /= /interp_variance.
        assert (hwf1: wf_ty t1).
        { apply wf_tyI in hwf as (? & ? & ? & hwf); simplify_eq.
          rewrite Forall_lookup in hwf.
          by apply hwf with k.
        }
        pose (Σthis0 := interp_nothing).
        iAssert (((λ ty : lang_ty, interp_type ty Σthis0 Σt) <$> σ) !! k ≡ Some (interp_type t0 Σthis0 Σt))%I as "heq0".
        { by rewrite list_lookup_fmap ht0. }
        iAssert ((go interp_type Σthis Σ0 <$> σC) !! k ≡ Some (go interp_type Σthis Σ0 t1))%I as "heq1".
        { by rewrite !list_lookup_fmap /= ht1. }
        iSpecialize ("hinst" $! k var (interp_type t0 Σthis0 Σt) (go interp_type Σthis Σ0 t1) hk).
        iSpecialize ("hinst" with "heq0 heq1").
        destruct var.
        * assert (hmono0: mono vs t1).
          { elim/mono_classI: hmono => ?? hh ?; simplify_eq.
            apply hh with k Invariant => //; by left.
          }
          assert (hmono1: mono (neg_variance <$> vs) t1).
          { elim/mono_classI: hmono => ??? hh; simplify_eq.
            apply hh with k Invariant => //; by left.
          }
          iAssert (□ ∀ w, interp_type t1 Σthis Σ0 w -∗ interp_type t1 Σthis Σ1 w)%I as "#hc0".
          { iDestruct (big_sepL_lookup with "IHty") as "#hk"; first by exact ht1.
            by iApply ("hk" $! hwf1 Σ0 Σ1 _ _ hmono0 with "h").
          }
          iAssert (□ ∀ w, interp_type t1 Σthis Σ1 w -∗ interp_type t1 Σthis Σ0 w)%I as "#hc1".
          { iDestruct (big_sepL_lookup with "IHty") as "#hk"; first by exact ht1.
            by iApply ("hk" $! hwf1 Σ1 Σ0 _ _ hmono1 with "hneg").
          }
          iIntros (w).
          iRewrite -"h0".
          iRewrite -"h1".
          iSplit; iIntros "#?".
          { iAssert (interp_type t1 Σthis Σ1 w) as "hr"; last by rewrite !interp_type_unfold_v.
            iApply "hc0".
            iAssert (go interp_type Σthis Σ0 t1 w) as "hh"; last by rewrite !interp_type_unfold_v.
            by iApply "hinst".
          }
          { iApply "hinst".
            iAssert (interp_type t1 Σthis Σ0 w) as "hr"; last by rewrite !interp_type_unfold_v.
            iApply "hc1".
            by rewrite !interp_type_unfold_v.
          }
        * assert (hmono0: mono vs t1).
          { elim/mono_classI: hmono => ?? hh ?; simplify_eq.
            apply hh with k Covariant => //; by left.
          }
          iAssert (□ ∀ w, interp_type t1 Σthis Σ0 w -∗ interp_type t1 Σthis Σ1 w)%I as "#hc0".
          { iDestruct (big_sepL_lookup with "IHty") as "#hk"; first by exact ht1.
            by iApply ("hk" $! hwf1 Σ0 Σ1 _ _ hmono0 with "h").
          }
          iIntros (w).
          iRewrite -"h0".
          iRewrite -"h1".
          iIntros "#?".
          iAssert (interp_type t1 Σthis Σ1 w) as "hr"; last by rewrite !interp_type_unfold_v.
          iApply "hc0".
          iAssert (go interp_type Σthis Σ0 t1 w) as "hh"; last by rewrite !interp_type_unfold_v.
          by iApply "hinst".
        * assert (hmono1: mono (neg_variance <$> vs) t1).
          { elim/mono_classI: hmono => ??? hh; simplify_eq.
            apply hh with k Contravariant => //; by left.
          }
          iAssert (□ ∀ w, interp_type t1 Σthis Σ1 w -∗ interp_type t1 Σthis Σ0 w)%I as "#hc1".
          { iDestruct (big_sepL_lookup with "IHty") as "#hk"; first by exact ht1.
            by iApply ("hk" $! hwf1 Σ1 Σ0 _ _ hmono1 with "hneg").
          }
          iIntros (w).
          iRewrite -"h0".
          iRewrite -"h1".
          iIntros "#?".
          iApply "hinst".
          iAssert (interp_type t1 Σthis Σ0 w) as "hr"; last by rewrite !interp_type_unfold_v.
          iApply "hc1".
          by rewrite !interp_type_unfold_v.
    - by iIntros "hh".
    - iIntros "hh".
      iDestruct "hh" as "[hint | hh]"; first by iLeft.
      iDestruct "hh" as "[hbool | hh]"; first by (iRight; iLeft).
      by iRight; iRight.
    - inv hmono.
      apply wf_tyI in hwf as [??].
      iIntros "hh".
      iDestruct "hh" as "[hh | hh]".
      + iLeft.
        rewrite -!interp_type_unfold_v /=.
        by iApply "IHty".
      + iRight.
        rewrite -!interp_type_unfold_v /=.
        by iApply "IHty1".
    - inv hmono.
      apply wf_tyI in hwf as [??].
      iIntros "hh".
      iDestruct "hh" as "[h0 h1]".
      rewrite -!interp_type_unfold_v /=.
      iSplit; first by iApply "IHty".
      by iApply "IHty1".
    - iDestruct (iForall3_length with "h") as "%hl".
      destruct hl as [hl0 hl1].
      destruct (vs !! i) as [vi | ] eqn:hvi; last first.
      { destruct (Σ0 !! i) as [ ? | ] eqn:h0.
        { apply lookup_ge_None_1 in hvi.
          apply lookup_lt_Some in h0.
          simpl in *.
          by lia.
        }
        destruct (Σ1 !! i) as [ ? | ] eqn:h1.
        { apply lookup_ge_None_1 in hvi.
          apply lookup_lt_Some in h1.
          simpl in *.
          by lia.
        }
        by rewrite /interp_generic h0 h1.
      }
      destruct (Σ0 !! i) as [ i0 | ] eqn:h0; last first.
      { apply lookup_ge_None_1 in h0.
        apply lookup_lt_Some in hvi.
        simpl in *.
        by lia.
      }
      destruct (Σ1 !! i) as [ i1 | ] eqn:h1; last first.
      { apply lookup_ge_None_1 in h1.
        apply lookup_lt_Some in hvi.
        simpl in *.
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
    - by iIntros "hh".
    - by iIntros "hh".
    - by iIntros "hh".
  Qed.

  Lemma interp_env_with_mono :
    map_Forall (λ _ : string, wf_cdef_mono) pdefs →
    map_Forall (λ _ : string, wf_cdef_parent) pdefs →
    map_Forall (λ _ : string, wf_cdef_fields_wf) pdefs →
    map_Forall (λ _cname, wf_cdef_constraints_wf) pdefs →
    ∀ σ vs (Σthis : interp Θ) (Σ0 Σ1: list (interp Θ)) ws,
    Forall wf_ty σ →
    length σ = length ws →
    (∀ i wi ti, ws !! i = Some wi →
                σ !! i = Some ti →
                not_contra wi →
                mono vs ti) →
    (∀ i wi ti, ws !! i = Some wi →
                σ !! i = Some ti →
                not_cov wi →
                mono (neg_variance <$> vs) ti) →
    □ iForall3 interp_variance vs Σ0 Σ1 -∗
    iForall3 interp_variance ws
      (interp_list Σthis Σ0 σ) (interp_list Σthis Σ1 σ).
  Proof.
    move => hmono hp ??.
    induction σ as [ | ty σ hi] => //= vs Σthis Σ0 Σ1 ws hwf hlen hcov hcontra.
    { rewrite (nil_length_inv ws) //.
      by iIntros.
    }
    destruct ws as [ | w ws]; first by discriminate hlen.
    case: hlen => hlen /=.
    apply Forall_cons_1 in hwf as [hty hwf].
    iIntros "#hvs".
    iDestruct (neg_interp_variance with "hvs") as "hvs2".
    iSplitR.
    { destruct w => /=; iIntros (w).
      - iSplit.
        + iApply (interp_with_mono with "hvs") => //.
          by apply (hcov 0 Invariant).
        + iApply (interp_with_mono with "hvs2") => //.
          by apply (hcontra 0 Invariant).
      - iApply (interp_with_mono with "hvs") => //.
        by apply (hcov 0 Covariant).
      - iApply (interp_with_mono with "hvs2") => //.
        by apply (hcontra 0 Contravariant).
    }
    iApply (hi vs) => //.
    - move => i wi ti hwi hti hc.
      by apply (hcov (S i) wi ti).
    - move => i wi ti hwi hti hc.
      by apply (hcontra (S i) wi ti).
  Qed.

  Lemma tag_extends_using_is_inclusion:
    map_Forall (λ _ : string, wf_cdef_parent) pdefs →
    map_Forall (λ _ : string, wf_cdef_mono) pdefs →
    map_Forall (λ _ : string, wf_cdef_fields_wf) pdefs →
    map_Forall (λ _cname, wf_cdef_constraints_wf) pdefs →
    ∀ A B σB, extends_using A B σB →
    ∀ Σthis Σ v, interp_tag_alt A Σ v -∗
    interp_tag_alt B (interp_list Σthis Σ σB) v.
  Proof.
    move => hwp hmono hfs hcs A B σB hext Σthis Σ v.
    iIntros "#h".
    iDestruct "h" as (ℓ t adef tdef σ Σt fields ifields) "(%h & #hmixed & #hconstr & #hinst & hdyn & hl)".
    destruct h as (-> & hadef & htdef & hlΣt & hin & hfields & hdom); simplify_eq.
    assert (hb: ∃ bdef, pdefs !! B = Some bdef ∧ length bdef.(generics) = length (interp_list Σthis Σ σB)).
    { apply extends_using_wf in hext => //.
      destruct hext as (? & ? & ? & h & _).
      apply wf_tyI in h as (bdef & ? & ? & ?); simplify_eq.
      exists bdef; repeat split => //.
      by rewrite /interp_list fmap_length.
    }
    destruct hb as (bdef & hbdef & hlen2).
    destruct (extends_using_wf _ _ _ hwp hext) as (adef' & hadef' & hF & hwfB & _).
    destruct (inherits_using_wf _ _ _ hwp hin) as (tdef' & htdef' & htF & hwfA & _).
    simplify_eq.
    iExists ℓ, t, bdef, tdef, (subst_ty σ <$> σB), Σt, fields, ifields.
    iSplit.
    { iPureIntro; repeat split => //.
      by eapply inherits_using_trans; last by econstructor.
    }
    iSplitR => //.
    iSplitR => //.
    iSplitR; last by iSplit.
    iModIntro; iNext.
    assert (heq: interp_list interp_nothing Σt (subst_ty σ <$> σB) ≡ interp_list Σthis (interp_list interp_nothing Σt σ) σB).
    { rewrite /interp_list -!list_fmap_compose /=.
      apply list_fmap_equiv_ext => ? ty0 hin0 /= w.
      assert (no_this ty0).
      { apply extends_using_wf in hext as (? & ? & _ & _ & hnothis) => //.
        rewrite Forall_lookup in hnothis.
        by apply hnothis in hin0.
      }
      apply elem_of_list_lookup_2 in hin0.
      assert (bounded (length σ) ty0).
      { rewrite Forall_forall in hF.
        apply wf_tyI in hwfA as [? [? [hlen ?]]]; simplify_eq.
        rewrite hlen; by apply hF.
      }
      rewrite interp_type_subst //.
      by rewrite (interp_type_no_this _ _ _ _ Σthis).
    }
    rewrite (iForall3_interp_equivI_l _ _ heq bdef.(generics) (interp_list Σthis Σ σB)) => {heq}.
    iApply (interp_env_with_mono hmono hwp hfs hcs _ _ Σthis with "hinst").
    + by apply wf_ty_classI in hwfB.
    + apply wf_tyI in hwfB as [? [? [??]]]; by simplify_eq.
    + move => i wi ti hwi hti hc.
      apply extends_using_mono with (def := adef) in hext => //.
      elim/mono_classI : hext => bdef' hbdef' ??; simplify_eq; by eauto.
    + move => i wi ti hwi hti hc.
      apply extends_using_mono with (def := adef) in hext => //.
      elim/mono_classI : hext => bdef' hbdef' ??; simplify_eq; by eauto.
  Qed.

  (* if class A<..> extends B<σB>, then for any valid substitution σA,
   * [| A<σA> |] ⊆ [| B<σA o σB> |]
   *)
  Lemma extends_using_is_inclusion:
    map_Forall (λ _cname, wf_cdef_parent) pdefs →
    map_Forall (λ _ : string, wf_cdef_mono) pdefs →
    map_Forall (λ _ : string, wf_cdef_fields_wf) pdefs →
    map_Forall (λ _cname, wf_cdef_constraints_wf) pdefs →
    ∀ Σthis Σ A B σA σB v, extends_using A B σB →
    wf_ty (ClassT true A σA) →
    interp_type (ClassT false A σA) Σthis Σ v -∗
    interp_type (ClassT false B (subst_ty σA <$> σB)) Σthis Σ v.
  Proof.
    move => hp hmono hfs hcs Σthis Σ A B σA σB v hext hwfA.
    rewrite !interp_tag_unfold //.
    assert (h0 := hwfA); apply wf_tyI in h0 as (adef & hadef & hlen & hFA).
    rewrite interp_tag_equiv //; last by rewrite /interp_list fmap_length.
    assert (hb: wf_ty (ClassT true B σB)).
    { apply extends_using_wf in hext => //.
      by repeat destruct hext as [? hext].
    }
    assert (hb0 := hb).
    apply wf_tyI in hb0 as (bdef & hbdef & hlen_ & hFB).
    rewrite interp_tag_equiv //; last by rewrite /interp_list !fmap_length.
    iIntros "h".
    iDestruct ((tag_extends_using_is_inclusion hp hmono hfs hcs _ _ _ hext) with "h") as "hA".
    assert (hΣ : interp_list Σthis Σ (subst_ty σA <$> σB) ≡
                 interp_list Σthis (interp_list Σthis Σ σA) σB).
    { rewrite /interp_list -list_fmap_compose.
      apply list_fmap_equiv_ext  => ? ty0 hin0 /= w.
      apply elem_of_list_lookup_2 in hin0.
      rewrite -interp_type_subst //.
      apply extends_using_wf in hext => //.
      destruct hext as (? & ? & hF & _); simplify_eq.
      rewrite Forall_forall in hF.
      apply wf_tyI in hwfA as (? & ? & hlenA & ?); simplify_eq.
      rewrite hlenA; by apply hF.
    }
    rewrite (interp_tag_alt_equivI _ _ hp hΣ) //.
    by rewrite /interp_list !map_length.
  Qed.

  Lemma inherits_using_is_inclusion:
    map_Forall (λ _cname, wf_cdef_parent) pdefs →
    map_Forall (λ _ : string, wf_cdef_mono) pdefs →
    map_Forall (λ _ : string, wf_cdef_fields_wf) pdefs →
    map_Forall (λ _cname, wf_cdef_constraints_wf) pdefs →
    ∀ Σthis Σ A B σA σB v, inherits_using A B σB →
    wf_ty (ClassT true A σA) →
    interp_type (ClassT false A σA) Σthis Σ v -∗
    interp_type (ClassT false B (subst_ty σA <$> σB)) Σthis Σ v.
  Proof.
    move => ???? Σthis Σ A B σA σB v h.
    move : σA v.
    induction h as [ A adef hpdefs | A B σ hext | A B σ C σC hext h hi ]
        => σA v hwf.
    - rewrite subst_ty_gen_targs; first done.
      apply wf_tyI in hwf as (? & ? & ? & ?); by simplify_eq.
    - iIntros "h".
      by iApply extends_using_is_inclusion.
    - iIntros "h".
      iDestruct (extends_using_is_inclusion with "h") as "he" => //.
      apply extends_using_wf in hext => //.
      destruct hext as (? & ? & ? & hwfB & _).
      rewrite map_subst_ty_subst; last first.
      { apply inherits_using_wf in h => //.
        destruct h as (bdef & hbdef & hb & hwfC & _).
        replace (length σ) with (length bdef.(generics)); first done.
        apply wf_tyI in hwfB as (? & ? & ? & ?); by simplify_eq.
      }
      iApply hi => //.
      assert (h_ := hwfB).
      apply wf_tyI in hwfB as (bdef & ? & ? & ?).
      econstructor => //.
      + by rewrite fmap_length.
      + apply wf_ty_subst_map; first by apply wf_ty_classI in hwf.
        by apply wf_ty_classI in h_.
  Qed.

  Lemma tag_inherits_using_is_inclusion:
    map_Forall (λ _cname, wf_cdef_parent) pdefs →
    map_Forall (λ _ : string, wf_cdef_mono) pdefs →
    map_Forall (λ _ : string, wf_cdef_fields_wf) pdefs →
    map_Forall (λ _cname, wf_cdef_constraints_wf) pdefs →
    ∀ Σthis Σ A adef B σ v,
    pdefs !! A = Some adef →
    inherits_using A B σ →
    length Σ = length adef.(generics) →
    interp_tag interp_type A Σ v -∗
    interp_tag interp_type B (interp_list Σthis Σ σ) v.
  Proof.
    move => hwfp hwfm hwff hwfc Σthis Σ A adef B σ v hadef hin hlen.
    iIntros "h".
    assert (h := hin).
    apply inherits_using_wf in h => //.
    destruct h as (? & ? & ? & hwfB & ?); simplify_eq.
    apply wf_tyI in hwfB.
    destruct hwfB as (bdef & hbdef & ? & ?).
    iDestruct (inherits_using_is_inclusion hwfp hwfm hwff hwfc
      Σthis Σ A B (gen_targs (length adef.(generics))) σ v hin) as "hh".
    { econstructor => //.
      - by rewrite length_gen_targs.
      - by apply gen_targs_wf_2.
    }
    rewrite interp_tag_unfold.
    assert (heq:
      interp_list Σthis Σ (gen_targs (length (generics adef))) ≡ Σ).
    { by apply interp_list_gen_targs. }
    rewrite (interp_tag_equivI _ _ heq A v).
    rewrite interp_tag_unfold.
    rewrite subst_tys_id; last done.
    by iApply "hh".
  Qed.

  Lemma interp_type_pre_take ty:
    ∀ Σthis Σ n,
    bounded n ty →
    length Σ ≥ n →
    interp_type_pre interp_type ty Σthis (take n Σ) ≡
    interp_type_pre interp_type ty Σthis Σ.
  Proof.
    elim: ty => //=.
    - move => exact_ t σ /Forall_lookup hi Σthis Σ n /boundedI /Forall_lookup hb hlen v.
      assert (go interp_type Σthis (take n Σ) <$> σ ≡ go interp_type Σthis Σ <$> σ).
      { apply list_equiv_lookup => k.
        rewrite !list_lookup_fmap.
        destruct (σ !! k) as [ty | ] eqn:hk => //=.
        f_equiv => w.
        apply hi with k => //.
        by apply hb in hk.
      }
      case: exact_.
      + by apply interp_exact_tag_equivI.
      + by apply interp_tag_equivI.
    - move => s t hs ht Σthis Σ n /boundedI [hbs hbt] hlen w /=.
      f_equiv.
      + by apply hs.
      + by apply ht.
    - move => s t hs ht Σthis Σ n /boundedI [hbs hbt] hlen w /=.
      f_equiv.
      + by apply hs.
      + by apply ht.
    - rewrite /interp_generic => n _ Σ p /boundedI hb hge /=.
      by rewrite lookup_take; last done.
  Qed.

  Lemma interp_type_take ty Σthis Σ n:
    bounded n ty →
    length Σ ≥ n →
    interp_type ty Σthis (take n Σ) ≡ interp_type ty Σthis Σ.
  Proof.
    move => ?? w.
    rewrite !interp_type_unfold_v.
    by rewrite interp_type_pre_take.
  Qed.

  Section Inclusion.
    Hypothesis Δ: list constraint.
    Hypothesis wfΣc: Forall wf_constraint Δ.
    Hypothesis wf_parent : map_Forall (λ _cname, wf_cdef_parent) pdefs.
    Hypothesis wf_mono : map_Forall (λ _ : string, wf_cdef_mono) pdefs.
    Hypothesis wf_constraints_wf : map_Forall (λ _cname, wf_cdef_constraints_wf) pdefs.
    Hypothesis wf_constraints_no_this : map_Forall (λ _cname, wf_cdef_constraints_no_this) pdefs.
    Hypothesis wf_constraints_bounded : map_Forall (λ _cname, wf_cdef_constraints_bounded) pdefs.
    Hypothesis wf_fields_wf : map_Forall (λ _ : string, wf_cdef_fields_wf) pdefs.
    Hypothesis wf_fields_bounded: map_Forall (λ _ : string, wf_cdef_fields_bounded) pdefs.

  (* Extracting subproofs for clarity *)
  Lemma subvariance_is_inclusion_aux Σthis Σ:
    ∀ A adef σ0 σ1 v,
    pdefs !! A = Some adef →
    wf_ty (ClassT true A σ0) →
    Forall wf_ty σ1 →
    ⊢ □ iForall3 interp_variance adef.(generics) (interp_list Σthis Σ σ0) (interp_list Σthis Σ σ1) →
    interp_type (ClassT false A σ0) Σthis Σ v -∗
    interp_type (ClassT false A σ1) Σthis Σ v.
  Proof.
    move => A adef σ0 σ1 v hadef hwfA hwfσ1.
    iIntros "#hσ #h".
    iAssert (⌜length σ0 = length σ1⌝)%I as "%hl0".
    { iDestruct (iForall3_length with "hσ") as "%hh".
      iPureIntro.
      rewrite /interp_list !fmap_length in hh.
      by destruct hh.
    }
    rewrite !interp_tag_unfold.
    assert (h0 := hwfA).
    apply wf_tyI in h0 as (? & ? & ? & ?); simplify_eq.
    rewrite interp_tag_equiv //; last by rewrite /interp_list fmap_length.
    rewrite interp_tag_equiv //; last by rewrite /interp_list fmap_length -hl0.
    iDestruct "h" as (l t adef' tdef σ Σt fields ifields h) "(#hmixed & #hconstr & #hinst & hfields & hl)".
    destruct h as (-> & hadef' & tdef' & hlΣa & hin &  hfields & hdom); simplify_eq.
    iExists l, t, adef, tdef, σ, Σt, fields, ifields.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iSplit; last by iSplit.
    iModIntro; iNext.
    by iApply (iForall3_interp_trans with "hinst hσ").
  Qed.

  Lemma exact_subvariance_is_inclusion_aux Σthis Σ:
    ∀ A adef σ0 σ1 v,
    pdefs !! A = Some adef →
    wf_ty (ClassT true A σ0) →
    Forall wf_ty σ1 →
    ⊢ □ iForall3 interp_variance ((λ _, Invariant) <$> adef.(generics))
      (interp_list Σthis Σ σ0) (interp_list Σthis Σ σ1) →
    interp_type (ClassT true A σ0) Σthis Σ v -∗
    interp_type (ClassT true A σ1) Σthis Σ v.
  Proof.
    move => A adef σ0 σ1 v hadef hwfA hwfσ1.
    iIntros "#hσ #h".
    iAssert (⌜length σ0 = length σ1⌝)%I as "%hl0".
    { iDestruct (iForall3_length with "hσ") as "%hh".
      iPureIntro.
      rewrite /interp_list !fmap_length in hh.
      by destruct hh.
    }
    rewrite !interp_exact_tag_unfold.
    rewrite !interp_exact_tag_equiv.
    assert (h0 := hwfA).
    apply wf_tyI in h0 as (? & ? & ? & ?); simplify_eq.
    iDestruct "h" as (l adef' fields ifields h) "(#hconstr & hfields & hl)".
    destruct h as (-> & hadef' & hfields & hdom); simplify_eq.
    iExists l, adef, fields, ifields.
    iSplit; first done.
    iDestruct (iForall_invariant_sym with "hσ") as "hσ2".
    iSplit.
    { iModIntro; iNext.
      iIntros (k c hc w) "#hw".
      assert (hwfc: wf_constraint c).
      { apply wf_constraints_wf in hadef.
        rewrite /wf_cdef_constraints_wf Forall_lookup in hadef.
        by apply hadef in hc.
      }
      destruct hwfc as [].
      iSpecialize ("hconstr" $! k c hc w).
      iApply (iForall3_inv_equiv with "hσ2") => //.
      iApply "hconstr".
      by iApply (iForall3_inv_equiv with "hσ").
    }
    iSplit; last by done.
    iModIntro; iNext; iIntros (f vis ty orig hf).
    iSpecialize ("hfields" $! f vis ty orig hf).
    iDestruct "hfields" as (iF) "[#hiF #hiff]".
    iExists (iF); iSplit; first done.
    iApply (equiv_trans with "hiff").
    iApply iForall3_inv_equiv => //.
    iPureIntro.
    apply wf_ty_subst_this.
    - econstructor => //.
      + by rewrite length_gen_targs.
      + by apply gen_targs_wf_2.
    - by apply has_field_wf in hf.
  Qed.

  Lemma exact_subtype_is_inclusion_aux Σ A v:
    ∀ adef, pdefs !! A = Some adef →
    length Σ = length adef.(generics) →
    □ interp_env_as_mixed Σ -∗
    interp_exact_tag interp_type A Σ v -∗
    interp_tag interp_type A Σ v.
  Proof.
    move => adef hadef hlen0.
    iIntros "#hmixed".
    rewrite interp_exact_tag_unseal /interp_exact_tag_def /=.
    iIntros "h".
    iDestruct "h" as (l adef' fields ifields h) "(#hconstr & #hfields & #hloc)".
    destruct h as (-> & hadef' & hfields & hdom); simplify_eq.
    rewrite interp_tag_unseal /interp_tag_def /=.
    iExists l, A, adef, adef, (gen_targs (length adef.(generics))), Σ, fields, ifields.
    iSplit.
    { iPureIntro; repeat split => //.
      by econstructor.
    }
    iSplit.
    { iModIntro; iNext; iIntros (k phi hk w) "hw".
      iSpecialize ("hmixed" $! k phi hk w with "hw").
      by rewrite !interp_mixed_unfold.
    }
    iSplit.
    { iModIntro; iNext; iIntros (k c hc w) "hw".
      by iApply ("hconstr" $! k c hc w with "hw").
    }
    iSplit.
    { iModIntro; iNext; iIntros (k var i0 i1 hk) "#h0 #h1".
      assert (hlt: k < length (generics adef)) by by apply lookup_lt_Some in hk.
      rewrite list_lookup_fmap lookup_gen_targs_lt; last done.
      simpl.
      rewrite option_equivI interp_generic_unfold /interp_generic.
      iAssert (Σ !! k ≡ Some i0)%I as "ha".
      { iRewrite -"h0".
        rewrite !option_equivI.
        by destruct (Σ !! k) as [ ? | ] eqn:h.
      }
      iRewrite "h1" in "ha".
      rewrite !option_equivI.
      destruct var.
      - iIntros (w); iSplit; iIntros "h".
        + by iRewrite "ha".
        + by iRewrite -"ha".
      - iIntros (w); iIntros "h".
        by iRewrite "ha".
      - iIntros (w); iIntros "h".
        by iRewrite -"ha".
    }
    by iSplit.
  Qed.

  Lemma submixed_is_inclusion_aux Σthis Σ:
    ∀ A v, wf_ty A →
    □ interp_as_mixed Σthis -∗
    □ interp_env_as_mixed Σ -∗
    interp_type A Σthis Σ v -∗
    interp_type MixedT Σthis Σ v.
  Proof.
    iIntros (A v hwf) "#wfThis #wfΣ h".
    rewrite !interp_type_unfold /=.
    iInduction A as [ | | | | exact_ C σC hi | | | A B hA hB | A B hA hB | i | | | ]
        "IHty" forall (v hwf).
    - by repeat iLeft.
    - by iLeft; iRight; iLeft.
    - done.
    - done.
    - iLeft; iRight; iRight => /=.
      iExists C, (interp_list Σthis Σ σC).
      assert (heq: go interp_type Σthis Σ <$> σC ≡ interp_list Σthis Σ σC).
      { rewrite /interp_list.
        apply list_fmap_equiv_ext => ? ty ? w.
        by rewrite interp_type_unfold.
      }
      apply wf_tyI in hwf as (cdef & ? & ? & hwf).
      iExists cdef; iSplit.
      { by rewrite /interp_list map_length. }
      destruct exact_.
      + iApply exact_subtype_is_inclusion_aux => //.
        { by rewrite /interp_list fmap_length. }
        { iModIntro; iIntros (k phi hk w) "hw".
          rewrite /interp_list in hk.
          apply list_lookup_fmap_inv in hk as [ty [-> hty]].
          iDestruct (big_sepL_lookup with "IHty") as "#hk"; first by exact hty.
          iClear "IHty".
          assert (hwf0 : wf_ty ty).
          { rewrite Forall_lookup in hwf.
            by apply hwf in hty.
          }
          rewrite interp_type_unfold /=.
          by iApply ("hk" $! w hwf0 with "hw").
        }
        by rewrite (interp_exact_tag_equivI _ _ heq C v).
      + by rewrite -(interp_tag_equivI _ _ heq C v).
    - by iRight.
    - by iLeft.
    - apply wf_tyI in hwf as [??].
      iDestruct "h" as "[ h | h ]"; first by iApply "IHty".
      by iApply "IHty1".
    - apply wf_tyI in hwf as [??].
      iDestruct "h" as "[? _]"; by iApply "IHty".
    - rewrite /= /interp_generic.
      destruct (decide (i < length Σ)) as [hlt | hge].
      + apply lookup_lt_is_Some_2 in hlt as [ϕ hϕ].
        iApply ("wfΣ" $! i); last done.
        by rewrite hϕ /=.
      + by rewrite /= /interp_generic lookup_ge_None_2 /=; last by apply not_lt.
    - rewrite /= /interp_dynamic.
      iDestruct "h" as "[? | h]".
      { by iLeft; iLeft. }
      iDestruct "h" as "[? | h]".
      { by iLeft; iRight; iLeft. }
      iDestruct "h" as "[? | h]".
      { by iRight. }
      iLeft; iRight; iRight.
      iDestruct "h" as (t Σt def [h0 h1]) "(? & ? & ? & ?)".
      iExists t, Σt, def.
      by iSplit.
    - iDestruct "h" as "[hz | h]".
      { iLeft; by iLeft. }
      iDestruct "h" as "[hb | h]".
      { iLeft; iRight; by iLeft. }
      iDestruct "h" as "[hn | h]".
      { by iRight. }
      iLeft; iRight; iRight.
      iDestruct "h" as (t Σt def h) "(? & ? & ? & ?)".
      iExists _, _, _.
      by iSplit.
    - by iSpecialize ("wfThis" $! v with "h").
  Qed.

  Lemma exact_subtype_is_inclusion Σthis Σ exact_ A σ v:
    wf_ty (ClassT true A σ) →
    □ interp_env_as_mixed Σ -∗
    □ interp_as_mixed Σthis -∗
    interp_type (ClassT exact_ A σ) Σthis Σ v -∗
    interp_type (ClassT false A σ) Σthis Σ v.
  Proof.
    move => /wf_tyI [adef [? [hlen hwf]]].
    iIntros "#hm0 #hm1 h".
    destruct exact_; last done.
    rewrite interp_type_unfold /=.
    rewrite interp_type_unfold_v /=.
    iApply exact_subtype_is_inclusion_aux => //.
    { by rewrite fmap_length. }
    iModIntro; iIntros (k phi hphi w) "hw".
    apply list_lookup_fmap_inv in hphi as [ty [-> hty]].
    rewrite -(interp_mixed_unfold Σthis Σ).
    iApply (submixed_is_inclusion_aux _ _ ty) => //.
    { rewrite Forall_lookup in hwf.
      by apply hwf in hty.
    }
    by rewrite interp_type_unfold /=.
  Qed.

  (* Main meat for A <: B → [|A|] ⊆ [|B|] *)
  Theorem subtype_is_inclusion_aux kd Σthis Σ A B:
    subtype Δ kd A B →
    ∀ v,
    wf_ty A →
    □ interp_as_mixed Σthis -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis Σ Δ -∗
    interp_type_pre interp_type A Σthis Σ v -∗
    interp_type_pre interp_type B Σthis Σ v
    with subtype_targs_is_inclusion_aux kd Σthis Σ Vs As Bs:
    Forall wf_ty As →
    Forall wf_ty Bs →
    subtype_targs Δ kd Vs As Bs →
    □ interp_as_mixed Σthis -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis Σ Δ -∗
    □ iForall3 interp_variance Vs (interp_list Σthis Σ As) (interp_list Σthis Σ Bs).
  Proof.
    { destruct 1 as [ kd A | kd A h | kd A σA B σB adef hadef hlen hext
      | kd A σA adef hadef hlen
      | kd A def σ0 σ1 hadef hwfσ hσ
      | kd A def σ0 σ1 hadef hwfσ hσ
      | | | | | kd exact_ ?? | kd A B h
      | kd A B h | kd A B C h0 h1 | kd A B | kd A B | kd A B C h0 h1
      | | kd A B C h0 h1 | kd A B hin | kd exact_ A adef σA hadef _ hf0 hf1
      | | | | | | kd A B hwf h ]; iIntros (v hwfA) "#wfThis #wfΣ #Σcoherency #h".
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        rewrite -!interp_type_unfold.
        by iApply submixed_is_inclusion_aux.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        done.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        assert (hwfA2: wf_ty (ClassT true A σA)).
        { apply wf_tyI in hwfA as (? & ? & ?& ?); simplify_eq; by econstructor. }
        rewrite -!interp_type_unfold; by iApply extends_using_is_inclusion.
      - clear subtype_targs_is_inclusion_aux subtype_is_inclusion_aux.
        rewrite -!interp_type_unfold.
        by iApply exact_subtype_is_inclusion.
      - apply subtype_targs_is_inclusion_aux with (Σthis := Σthis) (Σ := Σ) in hσ => //; last first.
        { by apply wf_ty_classI in hwfA. }
        clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        rewrite -!interp_type_unfold.
        assert (hwfA2: wf_ty (ClassT true A σ0)).
        { apply wf_tyI in hwfA as (? & ? & ?& ?); simplify_eq; by econstructor. }
        iApply subvariance_is_inclusion_aux => //.
        by iApply hσ.
      - apply subtype_targs_is_inclusion_aux with (Σthis := Σthis) (Σ := Σ) in hσ => //; last first.
        { by apply wf_ty_classI in hwfA. }
        clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        rewrite -!interp_type_unfold.
        assert (hwfA2: wf_ty (ClassT true A σ0)).
        { apply wf_tyI in hwfA as (? & ? & ?& ?); simplify_eq; by econstructor. }
        iApply exact_subvariance_is_inclusion_aux => //.
        by iApply hσ.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        by rewrite /= /interp_mixed.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        by iLeft.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        by iRight; iLeft.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        iDestruct "h" as "[#hint #hbool]".
        iDestruct "hint" as (z) "%hz".
        iDestruct "hbool" as (b) "%hb".
        by simplify_eq.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        iRight; iRight.
        assert (h0 := hwfA).
        apply wf_tyI in h0 as (adef & ? & ?& ?); simplify_eq.
        iExists A, (interp_list Σthis Σ targs), adef; iSplit.
        { by rewrite map_length. }
        destruct exact_.
        + iApply exact_subtype_is_inclusion_aux => //.
          { by rewrite /interp_list fmap_length. }
          { iModIntro; iIntros (k phi hphi w) "hw".
            apply list_lookup_fmap_inv in hphi as [ty [-> hty]].
            rewrite -(interp_mixed_unfold Σthis Σ).
            iApply (submixed_is_inclusion_aux _ _ ty) => //.
            apply wf_ty_classI in hwfA.
            rewrite Forall_lookup in hwfA; by apply hwfA in hty.
          }
          rewrite -interp_type_unfold.
          by rewrite interp_exact_tag_unfold.
        + rewrite -interp_type_unfold.
          by rewrite interp_tag_unfold.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        by iLeft.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        by iRight.
      - clear subtype_targs_is_inclusion_aux.
        rewrite /= /interp_union.
        iDestruct "h" as "[h | h]".
        + iApply (subtype_is_inclusion_aux with "wfThis wfΣ Σcoherency"); [exact h0 | | ].
          * apply wf_tyI in hwfA as [??]; by assumption.
          * by iAssumption.
        + iApply (subtype_is_inclusion_aux with "wfThis wfΣ Σcoherency"); [exact h1 | | ].
          * apply wf_tyI in hwfA as [??]; by assumption.
          * by iAssumption.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        iDestruct "h" as "[h _]".
        by iAssumption.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        iDestruct "h" as "[_ h]".
        by iAssumption.
      - clear subtype_targs_is_inclusion_aux.
        rewrite /= /interp_inter.
        iSplit.
        + iApply (subtype_is_inclusion_aux with "wfThis wfΣ Σcoherency"); [exact h0 | done | ].
          by iAssumption.
        + iApply (subtype_is_inclusion_aux with "wfThis wfΣ Σcoherency"); [exact h1 | done | ].
          by iAssumption.
      - done.
      - iApply (subtype_is_inclusion_aux with "wfThis wfΣ Σcoherency"); [exact h1 | | ].
        + apply subtype_wf in h0; [ | done | done | done ].
          by assumption.
        + iApply (subtype_is_inclusion_aux with "wfThis wfΣ Σcoherency"); [exact h0 | done | ].
          by iAssumption.
      - apply elem_of_list_lookup_1 in hin as [i hin].
        rewrite -!interp_type_unfold /=.
        by iApply ("Σcoherency" $! i (A, B) hin).
      - iRight; iRight; iRight.
        assert (hl : length σA = length adef.(generics)).
        { apply wf_tyI in hwfA as (? & ? & ?& ?); by simplify_eq. }
        simpl.
        iAssert (interp_tag interp_type A (go interp_type Σthis Σ <$> σA) v) as "#htag".
        { destruct exact_; last done.
          iApply exact_subtype_is_inclusion_aux => //.
          { by rewrite fmap_length. }
          iModIntro; iIntros (k phi hk w) "hw".
          rewrite /interp_list in hk.
          apply list_lookup_fmap_inv in hk as [ty [-> hty]].
          rewrite -(interp_mixed_unfold Σthis Σ).
          iApply (submixed_is_inclusion_aux _ _ ty) => //.
          { apply wf_ty_classI in hwfA; rewrite Forall_lookup in hwfA.
            by apply hwfA in hty.
          }
          by rewrite interp_type_unfold /=.
        }
        iClear "h".
        iExists A, (interp_list Σthis Σ σA), adef; iSplit.
        { by rewrite /interp_list map_length. }
        iSplit.
        + iModIntro; iNext; iIntros (i c hc w) "#h1".
          assert (hc': subst_constraints σA (Δsdt A) !! i = Some (subst_constraint σA c)).
          { by rewrite /subst_constraints list_lookup_fmap hc. }
          apply hf0 in hc'.
          assert (hwfc: wf_constraint c).
          { by apply Δsdt_wf in hc. }
          destruct hwfc as [].
          assert (hbc : bounded_constraint (length σA) c).
          { rewrite hl.
            by eapply Δsdt_bounded in hc.
          }
          destruct hbc as [].
          assert (hno: no_this_constraint c).
          { destruct SDTCS.
            by apply Δsdt_no_this in hc.
          }
          destruct hno as [].
          rewrite (interp_type_no_this _ _ _ interp_nothing Σthis) //.
          rewrite (interp_type_no_this _ _ _ interp_nothing Σthis) //.
          rewrite -!interp_type_subst //.
          rewrite !interp_type_unfold_v.
          iApply subtype_is_inclusion_aux => //.
          apply wf_ty_classI in hwfA.
          by apply wf_ty_subst.
        + iSplit; last iSplit.
          * iModIntro; iNext; iIntros (i phi hi w) "#hphi".
            apply list_lookup_fmap_inv in hi as [ty [-> hi]].
            assert (hwf: wf_ty ty).
            { apply wf_tyI in hwfA as (? & ? & ? & hwf).
              rewrite Forall_lookup in hwf.
              by eauto.
            }
            rewrite (interp_type_unfold _ [] MixedT w).
            rewrite -(interp_type_unfold Σthis Σ MixedT w).
            by iApply (submixed_is_inclusion_aux Σthis Σ).
          * iModIntro; iNext; iIntros (i [s t] hc w) "#h1".
            assert (hwf: wf_ty (subst_ty σA s)).
            { apply wf_ty_subst => //; first by apply wf_ty_classI in hwfA.
              apply wf_constraints_wf in hadef.
              rewrite /wf_cdef_constraints_wf Forall_lookup in hadef.
              by apply hadef in hc as [].
            }
            assert (hb: bounded_constraint (length σA) (s, t)).
            { apply wf_constraints_bounded in hadef.
              rewrite /wf_cdef_constraints_bounded Forall_lookup in hadef.
              apply hadef in hc.
              by rewrite hl.
            }
            destruct hb as [].
            assert (hc0 := hc).
            apply hf1 in hc0; simpl in *.
            assert (hno: no_this_constraint (s, t)).
            { apply wf_constraints_no_this in hadef.
              rewrite /wf_cdef_constraints_no_this Forall_lookup in hadef.
              by apply hadef in hc.
            }
            destruct hno as [].
            rewrite (interp_type_no_this _ _ _ interp_nothing Σthis) //.
            rewrite (interp_type_no_this _ _ _ interp_nothing Σthis) //.
            rewrite -!interp_type_subst //.
            rewrite !interp_type_unfold_v.
            by iApply subtype_is_inclusion_aux.
          * assert (heq: interp_list Σthis Σ σA ≡ go interp_type Σthis Σ <$> σA).
            { rewrite /interp_list.
              apply list_fmap_equiv_ext => ? ty hty w.
              by rewrite interp_type_unfold.
            }
            by rewrite (interp_tag_equivI _ _ heq A v).
      - by iLeft.
      - by iRight; iLeft.
      - by iRight; iRight; iLeft.
      - done.
      - done.
      - iDestruct ((subtype_is_inclusion_aux _ _ _ _ _ h (IntV 3)) with "wfThis wfΣ Σcoherency") as "hfalse".
        { by constructor. }
        iAssert (∃ z, ⌜IntV 3 = IntV z⌝)%I as "hh"; first by iExists _.
        rewrite /=.
        iDestruct ("hfalse" with "hh") as "%hfalse".
        by destruct hfalse.
    }
    move => hwfA hwfB.
    destruct 1 as [ | ?????? h0 h1 h | ?????? h0 h | ?????? h0 h]; iIntros "#wfThis #wfΣ #Σcoherency".
    - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
      done.
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
  Theorem subtype_is_inclusion kd Σthis Σ:
    ∀ A B, subtype Δ kd A B →
    ∀ v,
    wf_ty A →
    □ interp_as_mixed Σthis -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis Σ Δ -∗
    interp_type A Σthis Σ v -∗ interp_type B Σthis Σ v.
  Proof.
    iIntros (A B hAB v ?) "#wfThis #wfΣ #Σcoherency".
    rewrite !interp_type_unfold.
    by iApply (subtype_is_inclusion_aux with "wfThis wfΣ Σcoherency").
  Qed.

  Theorem inconsistency Σthis Σ kd:
    subtype Δ kd IntT BoolT →
    □ interp_as_mixed Σthis -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis Σ Δ -∗
    False%I.
  Proof.
    iIntros (h) "#hmixed0 #hmixed #hΣΔ".
    iDestruct ((subtype_is_inclusion _ _ _ _ _ h (IntV 3)) with "hmixed0 hmixed hΣΔ") as "hfalse".
    { by constructor. }
    iAssert (∃ z, ⌜IntV 3 = IntV z⌝)%I as "hh"; first by iExists _.
    rewrite !interp_type_unfold /=.
    iDestruct ("hfalse" with "hh") as "%hfalse".
    by destruct hfalse.
  Qed.

  Definition interp_local_tys Σthis Σ
    (Γ : local_tys) (le : local_env) : iProp Θ :=
    (Σthis (LocV le.(vthis))) ∗
    (∀ v ty, ⌜Γ !! v = Some ty⌝ -∗
     ∃ val, ⌜le.(lenv) !! v = Some val⌝ ∗ interp_type ty Σthis Σ val)%I.

  Lemma interp_local_app Γ st Σthis Σ0 Σ1:
    bounded_lty (length Σ0) Γ →
    interp_local_tys Σthis Σ0 Γ st ≡
    interp_local_tys Σthis (Σ0 ++ Σ1) Γ st.
  Proof.
    move => hb.
    rewrite /interp_local_tys.
    f_equiv.
    iStartProof; iSplit; iIntros "h"; iIntros (v ty hv).
    + iDestruct ("h" $! v ty hv) as (w hw) "#hw".
      iExists w; iSplit; first done.
      rewrite -interp_type_app; first done.
      by apply hb in hv.
    + iDestruct ("h" $! v ty hv) as (w hw) "#hw".
      iExists w; iSplit; first done.
      rewrite -interp_type_app; first done.
      by apply hb in hv.
  Qed.

  Lemma interp_local_tys_is_inclusion kd Σthis Σ Γ0 Γ1 le:
    wf_lty Γ0 →
    Forall (λ (i: interp Θ), ∀ v, Persistent (i v)) Σ →
    lty_sub Δ kd Γ0 Γ1 →
    □ interp_as_mixed Σthis -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis Σ Δ -∗
    interp_local_tys Σthis Σ Γ0 le -∗
    interp_local_tys Σthis Σ Γ1 le.
  Proof.
    move => hlty hpers hsub; iIntros "#wfThis #wfΣ #? [#Hthis Hle]".
    iSplitR; first done.
    iIntros (v ty) "%Hv".
    apply hsub in Hv as (B & hB & hsubB).
    iDestruct ("Hle" $! v B hB) as (val) "[%Hv' #H]".
    iExists val; iSplitR; first done.
    iApply subtype_is_inclusion => //.
    by apply hlty in hB.
  Qed.
  End Inclusion.

  Fixpoint helper_fun n k (vars : list variance) :=
    match vars with
    | [] => []
    | hd :: tl =>
        let Δ01 := helper_fun n (S k) tl in
        match hd with
        | Invariant => (GenT k, GenT (k + n)) :: (GenT (k + n), GenT k) :: Δ01
        | Covariant => (GenT k, GenT (k + n)) :: Δ01
        | Contravariant => (GenT (k + n), GenT k) :: Δ01
        end
    end.

  Lemma helper_spec n : ∀ vars k,
    let Δ01 := helper_fun n k vars in
    let σ0 := lift_ty k <$> gen_targs (length vars) in
    Forall wf_constraint Δ01 ∧
    subtype_targs Δ01 Aware vars σ0 (lift_ty n <$> σ0) ∧
    (∀ i v,
      vars !! i = Some v →
      ∃ j, match v with
             | Invariant =>
                 Δ01 !! j = Some (GenT (k + i), GenT (k + i + n)) ∧
                 Δ01 !! (S j) = Some (GenT (k + i + n), GenT (k + i))
             | Covariant => Δ01 !! j = Some (GenT (k + i), GenT (k + i + n))
             | Contravariant => Δ01 !! j = Some (GenT (k + i + n), GenT (k + i))
             end) ∧
    (∀ i A B, Δ01 !! i = Some (A, B) →
      ∃ j v,
        vars !! j = Some v ∧
        match v with
        | Invariant => (A = GenT (k + j) ∧ B = GenT (k + j + n)) ∨
            (A = GenT (k + j + n) ∧ B = GenT (k + j))
        | Covariant => A = GenT (k + j) ∧ B = GenT (k + j + n)
        | Contravariant => A = GenT (k + j + n) ∧ B = GenT (k + j)
        end).
  Proof.
    elim => [| v vars hi] k //=.
    move : {hi} (hi (S k)) => /=.
    pose (Δ01 := helper_fun n (S k) vars).
    case => hwf [hσ hi].
    split.
    { destruct v; by repeat constructor. }
    split.
    {
      assert (heq:
            list_fmap lang_ty lang_ty (lift_ty k) (map GenT (seq 1 (length vars)))
            =
            lift_ty (S k) <$> gen_targs (length vars)).
      { apply list_eq => i.
        rewrite !list_lookup_fmap.
        destruct (decide (i < length vars)) as [hlt | hge].
        - rewrite !lookup_seq_lt //=.
          f_equal; f_equal; by lia.
        - rewrite !lookup_seq_ge //; by lia.
      }
      destruct v.
      - constructor.
        + apply SubConstraint; by constructor.
        + apply SubConstraint; by repeat constructor.
        + rewrite heq.
          apply subtype_targs_weaken with Δ01 => //.
          by set_solver.
      - constructor.
        + apply SubConstraint; by constructor.
        + rewrite heq.
          apply subtype_targs_weaken with Δ01 => //.
          by set_solver.
      - constructor.
        + apply SubConstraint; by repeat constructor.
        + rewrite heq.
          apply subtype_targs_weaken with Δ01 => //.
          by set_solver.
    }
    split.
    {
      move => [ | i] w /=.
      + case => <-.
        exists 0.
        case: v => /=.
        * split; repeat f_equal; by lia.
        * repeat f_equal; by lia.
        * repeat f_equal; by lia.
      + move => hv.
        case : hi => [hi _].
        case : {hi} (hi i w hv) => j hj.
        destruct w.
        * case: hj => hj0 hj1.
          destruct v.
          - exists (S (S j)); rewrite /= hj0 hj1; split.
            { f_equal; f_equal; f_equal; by lia. }
            { f_equal; f_equal; f_equal; by lia. }
          - exists (S j); rewrite /= hj0 hj1; split.
            { f_equal; f_equal; f_equal; by lia. }
            { f_equal; f_equal; f_equal; by lia. }
          - exists (S j); rewrite /= hj0 hj1; split.
            { f_equal; f_equal; f_equal; by lia. }
            { f_equal; f_equal; f_equal; by lia. }
        * destruct v.
          - exists (S (S j)); rewrite /= hj.
            f_equal; f_equal; f_equal; by lia.
          - exists (S j); rewrite /= hj.
            f_equal; f_equal; f_equal; by lia.
          - exists (S j); rewrite /= hj.
            f_equal; f_equal; f_equal; by lia.
        * destruct v.
          - exists (S (S j)); rewrite /= hj.
            f_equal; f_equal; f_equal; by lia.
          - exists (S j); rewrite /= hj.
            f_equal; f_equal; f_equal; by lia.
          - exists (S j); rewrite /= hj.
            f_equal; f_equal; f_equal; by lia.
    }
    { case: hi => [_ hi].
      case : v.
      - move => [ | [ | i]] A B /=.
        + case => <- <-.
          exists 0, Invariant.
          split => //.
          left; split; f_equal; by lia.
        + case => <- <-.
          exists 0, Invariant.
          split => //.
          right; split; f_equal; by lia.
        + move => h.
          case: {hi} (hi i A B h) => j [v [hv hh]].
          exists (S j), v; split => //.
          case: {hv} v hh => hh.
          * case: hh => [[-> ->] | [-> ->]].
            { left; split; f_equal; by lia. }
            { right; split; f_equal; by lia. }
          * case: hh => -> ->.
            split; f_equal; by lia.
          * case: hh => -> ->.
            split; f_equal; by lia.
      - move => [ | i] A B /=.
        + case => <- <-.
          exists 0, Covariant.
          split => //.
          split; f_equal; by lia.
        + move => h.
          case: {hi} (hi i A B h) => j [v [hv hh]].
          exists (S j), v; split => //.
          case: {hv} v hh => hh.
          * case: hh => [[-> ->] | [-> ->]].
            { left; split; f_equal; by lia. }
            { right; split; f_equal; by lia. }
          * case: hh => -> ->.
            split; f_equal; by lia.
          * case: hh => -> ->.
            split; f_equal; by lia.
      - move => [ | i] A B /=.
        + case => <- <-.
          exists 0, Contravariant.
          split => //.
          split; f_equal; by lia.
        + move => h.
          case: {hi} (hi i A B h) => j [v [hv hh]].
          exists (S j), v; split => //.
          case: {hv} v hh => hh.
          * case: hh => [[-> ->] | [-> ->]].
            { left; split; f_equal; by lia. }
            { right; split; f_equal; by lia. }
          * case: hh => -> ->.
            split; f_equal; by lia.
          * case: hh => -> ->.
            split; f_equal; by lia.
    }
  Qed.

  Lemma Δsdt_variance_interp: ∀ Σthis (Σ0 Σ1: list (interp Θ)) A adef,
    map_Forall (λ _ : string, wf_cdef_mono) pdefs →
    map_Forall (λ _ : string, wf_cdef_parent) pdefs →
    map_Forall (λ _cname, wf_cdef_constraints_no_this) pdefs →
    map_Forall (λ _cname, wf_cdef_constraints_bounded) pdefs →
    map_Forall (λ _cname, wf_cdef_constraints_wf) pdefs →
    map_Forall (λ _ : string, wf_cdef_fields_wf) pdefs →
    pdefs !! A = Some adef →
    □ interp_as_mixed Σthis -∗
    □ interp_env_as_mixed Σ0 -∗
    □ interp_env_as_mixed Σ1 -∗
    □ iForall3 interp_variance adef.(generics) Σ0 Σ1 -∗
    □ Σinterp Σthis Σ0 adef.(constraints) -∗
    □ Σinterp Σthis Σ1 adef.(constraints) -∗
    □ Σinterp Σthis Σ1 (Δsdt A) -∗
    □ Σinterp Σthis Σ0 (Δsdt A).
  Proof.
    move => Σthis Σ0 Σ1 A adef hwfm hwfp hwfno hwfbc hwfc hwff hadef.
    (* assume T0s and T1s such that for all i
     * T0i <:vi:> T1i
     *)
    pose (n := length adef.(generics)).
    pose (σ0 := gen_targs (length adef.(generics))).
    pose (σ1 := lift_ty (length adef.(generics)) <$> σ0).
    move : (helper_spec n adef.(generics) 0) => /=.
    pose (Δ01 := helper_fun n 0 adef.(generics)).
    assert (hwf: Forall wf_ty σ0).
    { apply Forall_lookup; by apply gen_targs_wf. }
    assert (hl0 : length σ0 = length adef.(generics)).
    { by rewrite length_gen_targs. }
    case => hwfΔ01 [hσ [h0_Δ01 h1_Δ01]].
    rewrite !lift_tys_O in hσ.
    assert (hl1 : length σ1 = length adef.(generics)).
    { by rewrite /σ1 fmap_length. }
    pose (Δ := Δ01 ++ subst_constraints σ0 adef.(constraints) ++
              subst_constraints σ1 adef.(constraints) ++ subst_constraints σ1 (Δsdt A)).
    assert (hsub: Δentails Aware Δ (subst_constraints σ0 (Δsdt A))).
    { by eapply Δsdt_variance. }
    iIntros "#hthism #hmixed0 #hmixed1 #hForall #hΣ0 #hΣ1 #h1".
    iDestruct (iForall3_length with "hForall") as "[%hlΣ0 %hlΣ1]".
    iAssert (Σinterp Σthis (Σ0 ++ Σ1) Δ) with "[h1]" as "hΣΔ".
    { rewrite /Δ.
      iApply Σinterp_app.
      { iIntros (i [U V] heq v) "#h"; simpl.
        case: {h1_Δ01} (h1_Δ01 i U V heq) => j [w [hw hUV]].
        assert (hjb: bounded (length Σ0) (GenT j)).
        { constructor.
          apply lookup_lt_Some in hw.
          by rewrite -hlΣ0.
        }
        case : w hw hUV => hw hUV.
        + case: hUV => [ [-> ->]| [-> ->]] /=.
          * rewrite -(interp_type_app (GenT j) Σthis Σ0 Σ1) //.
            replace (GenT (j + n)) with (lift_ty (length Σ0) (GenT j)); last first.
            { by rewrite -hlΣ0. }
            rewrite interp_type_lift.
            iApply interp_with_mono => //.
            by constructor.
          * rewrite -(interp_type_app (GenT j) Σthis Σ0 Σ1) //.
            replace (GenT (j + n)) with (lift_ty (length Σ0) (GenT j)); last first.
            { by rewrite -hlΣ0. }
            rewrite interp_type_lift.
            iDestruct (neg_interp_variance with "hForall") as "hForall2".
            iClear "hForall".
            iApply interp_with_mono => //.
            constructor.
            by rewrite list_lookup_fmap hw.
        + case: hUV => -> -> /=.
          rewrite -(interp_type_app (GenT j) Σthis Σ0 Σ1) //.
          replace (GenT (j + n)) with (lift_ty (length Σ0) (GenT j)); last first.
          { by rewrite -hlΣ0. }
          rewrite interp_type_lift.
          iApply interp_with_mono => //.
          by constructor.
        + case: hUV => -> -> /=.
          rewrite -(interp_type_app (GenT j) Σthis Σ0 Σ1) //.
          replace (GenT (j + n)) with (lift_ty (length Σ0) (GenT j)); last first.
          { by rewrite -hlΣ0. }
          rewrite interp_type_lift.
          iDestruct (neg_interp_variance with "hForall") as "hForall2".
          iClear "hForall".
          iApply interp_with_mono => //.
          apply MonoVCoGen.
          by rewrite list_lookup_fmap hw.
      }
      iApply Σinterp_app.
      { rewrite subst_constraints_gen_targs; last by (by apply hwfbc in hadef).
        iIntros (i c hc w) "#h".
        assert (hb: bounded_constraint (length Σ0) c).
        { apply hwfbc in hadef.
          rewrite /wf_cdef_constraints_bounded Forall_lookup in hadef.
          apply hadef in hc.
          by rewrite -hlΣ0.
        }
        destruct hb as [].
        rewrite -!interp_type_app //.
        by iApply "hΣ0".
      }
      iApply Σinterp_app.
      { rewrite lift_subst_gen_targs_constraints; last by apply hwfbc in hadef.
        by rewrite hlΣ0 Σinterp_lift.
      }
      replace (subst_constraints σ1 (Δsdt A)) with
              (lift_constraints (length adef.(generics)) (Δsdt A)); last first.
      { rewrite lift_subst_gen_targs_constraints //.
        rewrite Forall_lookup => ??.
        by apply Δsdt_bounded.
      }
     by rewrite hlΣ0 Σinterp_lift.
    }
    iModIntro; iIntros (i c hc v) "#h".
    assert (hc0: subst_constraints σ0 (Δsdt A) !! i = Some (subst_constraint σ0 c)).
    { by rewrite /subst_constraints list_lookup_fmap hc. }
    assert (hwfΔ : Forall wf_constraint (Δsdt A)).
    { rewrite Forall_lookup => ??; by apply Δsdt_wf. }
    iAssert (□ interp_env_as_mixed (Σ0 ++ Σ1))%I as "#hmixed".
    { iModIntro; iIntros (j phi hj w) "hphi".
      rewrite lookup_app in hj.
      destruct (Σ0 !! j) as [i0 | ] eqn:hi0.
      - case : hj => <-.
        by iApply "hmixed0".
      - by iApply "hmixed1".
    }
    apply hsub in hc0.
    rewrite /subst_constraint /= in hc0.
    assert (wfΣc: Forall wf_constraint Δ).
    { apply Forall_app; split; first done.
      apply Forall_app; split.
      { rewrite subst_constraints_gen_targs; last by apply hwfbc in hadef.
        by apply hwfc in hadef.
      }
      apply Forall_app; split.
      { rewrite lift_subst_gen_targs_constraints; last by apply hwfbc in hadef.
        apply lift_constraints_wf.
        by apply hwfc in hadef.
      }
      assert (hwf1: Forall wf_ty σ1).
      { rewrite /σ1.
        apply Forall_fmap.
        apply Forall_lookup => k ty hty.
        apply lift_ty_wf.
        rewrite Forall_lookup in hwf; by apply hwf in hty.
      }
      apply Forall_lookup => k ck hck.
      apply list_lookup_fmap_inv in hck as [ck0 [-> hck]].
      rewrite Forall_lookup in hwfΔ.
      apply hwfΔ in hck as [].
      split; simpl; by apply wf_ty_subst.
    }
    iAssert (interp_type (subst_ty σ0 c.1) Σthis (Σ0 ++ Σ1) v -∗
             interp_type (subst_ty σ0 c.2) Σthis (Σ0 ++ Σ1) v)%I as "hsub2".
    { iIntros "hh".
      assert (hwfcc: wf_constraint c).
      { rewrite Forall_lookup in hwfΔ.
        by apply hwfΔ in hc.
      }
      assert (hwf2: wf_ty (subst_ty σ0 c.1)).
      { apply wf_ty_subst => //.
        by destruct hwfcc.
      }
      by iApply (subtype_is_inclusion _ wfΣc hwfp hwfm hwfc hwfno hwfbc
        hwff Aware Σthis (Σ0 ++ Σ1) _ _ hc0).
    }
    assert (hbc: bounded_constraint (length (adef.(generics))) c).
    { by eapply Δsdt_bounded in hc. }
    destruct hbc as [].
    rewrite !subst_ty_id //.
    rewrite (interp_type_app c.2 Σthis Σ0 Σ1); last by rewrite -hlΣ0.
    rewrite (interp_type_app c.1 Σthis Σ0 Σ1); last by rewrite -hlΣ0.
    by iApply "hsub2".
  Qed.
End proofs.
