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

  Lemma iForall3_length {A B C : Type} (P: A → B → C → iProp Σ) As Bs Cs:
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

  Lemma iForall3_forall_1 {A B C : Type} (P: A → B → C → iProp Σ) As Bs Cs:
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

  Lemma interp_variance_reflexive v: ∀ i, ⊢ interp_variance v i i.
  Proof.
    rewrite /interp_variance; destruct v; iIntros (i) => /=.
    - by iIntros (w); iSplit; iIntros.
    - by iIntros (w); iIntros.
    - by iIntros (w); iIntros.
  Qed.

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
      λ (w : value), (∃ ℓ t cdef tdef σ (Σt: list (interp Σ))
       (fields: stringmap ((visibility * lang_ty) * tag))
       (ifields: gmapO string (laterO (sem_typeO Σ))),
      ⌜w = LocV ℓ ∧
       Δ !! C = Some cdef ∧
       Δ !! t = Some tdef ∧
       length Σi = length cdef.(generics) ∧
       length Σt = length tdef.(generics) ∧
       inherits_using t C σ ∧
       has_fields t fields ∧
       dom fields = dom ifields⌝ ∗

      □ ▷ (∀ i (ϕi: interp Σ),  ⌜Σt !! i = Some ϕi⌝ →
           ∀ v,  ϕi v -∗ rec MixedT Σi v) ∗ (* Σi or Σt ? *)

      □ ▷ (∀ i c, ⌜tdef.(constraints) !! i = Some c⌝ →
           ∀ v, rec c.1 Σt v -∗ rec c.2 Σt v) ∗

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
    Interp (λ (w: value), (∃ Σi, interp_tag rec Σi C w)%I).

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
      | DynamicT => interp_nothing (* TODO Fix later *)
      end.
  End interp_type_pre_rec.

 Local Instance interp_tag_ne C (rec: ty_interpO) :
    NonExpansive (λ Σi, interp_tag rec Σi C).
  Proof.
    move => n x y h.
    rewrite !interp_tag_unseal /interp_tag_def => v.
    rewrite /interp_fun !interp_car_simpl /interp_variance.
    do 17 f_equiv.
    { f_equiv; split => hh.
      + repeat destruct hh as (? & hh).
        repeat split => //.
        apply length_ne in h.
        by rewrite -h.
      + repeat destruct hh as (? & hh).
        repeat split => //.
        apply length_ne in h.
        by rewrite h.
    }
    by repeat f_equiv.
  Qed.

  Local Instance go_ne (rec: ty_interpO) (ty: lang_ty) :
    NonExpansive (λ Σi, go rec Σi ty).
  Proof.
    induction ty as [ | | | | A σ hi | | | A B hA hB | A B hA hB | i
    | cname | ] => //= n x y h.
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
    do 12 f_equiv.
    f_contractive.
    by repeat f_equiv.
  Qed.

  Global Instance interp_ex_contractive C: Contractive (λ rec, interp_ex rec C).
  Proof.
    rewrite /interp_ex => n i1 i2 hdist v.
    rewrite /interp_fun !interp_car_simpl.
    do 2 f_equiv.
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
    induction ty as [ | | | | C σ hi | | | A B hA hB | A B hA hB | i | C|  ] => /=.
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
			do 17 f_equiv.
      { by rewrite !fmap_length. }
      f_equiv.
      { f_equiv; f_contractive.
        do 10 f_equiv.
        * by repeat f_equiv.
        * apply Forall2_fmap, Forall_Forall2_diag, Forall_forall => ? hin.
          apply dist_S.
          by apply hi.
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
      do 12 f_equiv.
      f_contractive.
      by apply hdist.
    - done.
    - by apply interp_nonnull_contractive.
    - by solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv]).
    - by solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv]).
    - done.
    - by apply interp_ex_contractive.
    - done.
  Qed.

  (* the interpretation of types can now be
     defined as a fixpoint (because class types
     can be (mutually) recursive) *)
  Definition interp_type := fixpoint interp_type_pre.

  Definition interp_env_as_mixed (Σi: list (interp Σ)) :=
    (∀ i (ϕi: interp Σ),  ⌜Σi !! i = Some ϕi⌝ → ∀ v,  ϕi v -∗ interp_mixed interp_type v)%I.

  Definition Σinterp (Σi: list (interp Σ)) (Σc : list constraint) :=
    (∀ i c, ⌜Σc !! i = Some c⌝ →
    ∀ v, interp_type c.1 Σi v -∗ interp_type c.2 Σi v)%I.

  Definition interp_list (Σi: list (interp Σ)) (σ: list lang_ty) :=
    (λ ty, interp_type ty Σi) <$> σ.

  Section Unfold.
    Variable Σi : list (interpO Σ).

    (* Helper lemmas to control unfolding of some definitions *)
    Lemma interp_type_unfold (ty : lang_ty) (v : value) :
      interp_type ty Σi v ⊣⊢ interp_type_pre interp_type ty Σi v.
    Proof.
      rewrite {1}/interp_type.
      apply (fixpoint_unfold interp_type_pre ty Σi v).
    Qed.

    (* #hyp *)
    Global Instance interp_type_persistent :
    ∀ t v, Persistent (interp_type t Σi v).
    Proof.
      move => t v.
      rewrite interp_type_unfold.
      by apply _.
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

  Definition interp_tag_alt
    (Σi : list (interp Σ))
    (C: tag)
    : interp Σ :=
    Interp (
      λ (w : value), (∃ ℓ t cdef tdef σ (Σt: list (interp Σ))
       (fields: stringmap ((visibility * lang_ty) * tag))
       (ifields: gmapO string (laterO (sem_typeO Σ))),
      ⌜w = LocV ℓ ∧
       Δ !! C = Some cdef ∧
       Δ !! t = Some tdef ∧
       length Σi = length cdef.(generics) ∧
       length Σt = length tdef.(generics) ∧
       inherits_using t C σ ∧
       has_fields t fields ∧
       dom fields = dom ifields⌝ ∗

      □ ▷ interp_env_as_mixed Σt ∗

      □ ▷ Σinterp Σt tdef.(constraints) ∗

      □ ▷ iForall3 interp_variance cdef.(generics) (interp_list Σt σ) Σi ∗

      (∀ f vis ty orig, ⌜has_field f t vis ty orig⌝ -∗
        ifields !! f ≡ Some (Next (interp_car (interp_type ty Σt)))) ∗

      (ℓ ↦ (t, ifields)))%I
    ).

  Lemma interp_tag_equiv A Σi v:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    interp_tag interp_type Σi A v ⊣⊢
    interp_tag_alt Σi A v.
  Proof.
    move => hwfp.
    rewrite !interp_tag_unseal /interp_tag_def.
    rewrite /interp_fun !interp_car_simpl /=.
    rewrite /interp_env_as_mixed /Σinterp.
    iStartProof; iSplit; iIntros "#h".
    - iDestruct "h" as (l t adef tdef σ Σt fields ifields h) "[#hmixed [#hconstr [#hinst [#hdyn hloc]]]]".
      destruct h as (-> & hadef & htdef & hlΣi & hlΣt &  hin & hfields & hidom); simplify_eq.
      iExists l, t, adef, tdef, σ, Σt, fields, ifields.
      iSplit => //.
      iSplit.
      { iModIntro; iNext; iIntros (i ii heq v) "hii".
        iSpecialize ("hmixed" $! i ii heq v with "hii").
        assert (h :
          interp_type MixedT Σi v ⊣⊢
          interp_type_pre interp_type MixedT Σi v) by by rewrite interp_type_unfold.
        rewrite /interp_fun !interp_car_simpl /= in h.
        by rewrite h /interp_mixed.
      }
      iSplit.
      { iModIntro; iNext; iIntros (i c heq v) "hc".
        by iSpecialize ("hconstr" $! i c heq v with "hc").
      }
      iSplit; last by iSplit.
      iModIntro; iNext.
      assert (hl1 : length Σi = length σ).
      { apply inherits_using_wf in hin => //.
        destruct hin as (?&?&?&h).
        inv h; simplify_eq.
        by rewrite hlΣi.
      }
      move: hlΣi hl1.
      generalize (generics adef) => vs; clear => hl0 hl1.
      iClear "hmixed hdyn hloc".
      iInduction vs as [ | hd tl] "HI" forall (σ Σi hl0 hl1).
      { by destruct σ; destruct Σi. }
      destruct σ as [ | t0 σ] => /=.
      { by rewrite hl1 in hl0. }
      destruct Σi as [ | i Σi] => //=.
      case: hl0 => hl0.
      case: hl1 => hl1.
      iSplitL.
      + by iApply ("hinst" $! 0).
      + iApply "HI" => //.
        iModIntro; iIntros (k v j0 j1 hk) "#h0 #h1".
        by iApply ("hinst" $! (S k)).
    - iDestruct "h" as (l t adef tdef σ Σt fields ifields h) "[#hmixed [#hconstr [#hinst [#hdyn hloc]]]]".
      destruct h as (-> & hadef & htdef & hlΣi & hlΣt & hin & hfields & hidom); simplify_eq.
      iExists l, t, adef, tdef, σ, Σt, fields, ifields.
      iSplit => //.
      iSplit.
      { iModIntro; iNext; iIntros (i ii heq v) "hii".
        iSpecialize ("hmixed" $! i ii heq v with "hii").
        assert (h :
          interp_type MixedT Σi v ⊣⊢
          interp_type_pre interp_type MixedT Σi v) by by rewrite interp_type_unfold.
        rewrite /interp_fun !interp_car_simpl /= in h.
        by rewrite h /interp_mixed.
      }
      iSplit.
      { iModIntro; iNext; iIntros (i c heq v) "hc".
        by iSpecialize ("hconstr" $! i c heq v with "hc").
      }
      iSplit; last by iSplit.
      iModIntro; iNext.
      assert (hl1 : length Σi = length σ).
      { apply inherits_using_wf in hin => //.
        destruct hin as (?&?&?&h).
        inv h; simplify_eq.
        by rewrite hlΣi.
      }
      iIntros (k v i0 i1 heq) "#h0 #h1".
      move : heq hlΣi hl1.
      generalize adef.(generics); clear => vs heq hl0 hl1.
      iClear "hconstr hmixed hdyn hloc".
      iInduction vs as [ | hd tl] "HI" forall (k σ Σi heq hl0 hl1) "hinst h0 h1".
      { by destruct σ; destruct Σi. }
      destruct σ as [ | t0 σ] => //.
      destruct Σi as [ | i Σi] => //.
      case: hl0 => hl0.
      case: hl1 => hl1.
      simpl iForall3.
      iDestruct "hinst" as "[h hf]".
      destruct k as [ | k].
      + case : heq => ->.
        rewrite /= !option_equivI.
        iAssert (∀ w, interp_type t0 Σt w ≡ i0 w)%I as "hh0".
        { by iIntros (w); iRewrite "h0". }
        iAssert (∀ w, i w ≡ i1 w)%I as "hh1".
        { by iIntros (w); iRewrite -"h1". }
        destruct v; iIntros (w).
        * iSpecialize ("hh0" $! w).
          iRewrite -"hh0".
          iSpecialize ("hh1" $! w).
          iRewrite -"hh1".
          simpl.
          iDestruct ("h" $! w) as "[hl hr]".
          iSplit; iIntros "hh".
          { by iApply "hl". }
          { by iApply "hr". }
        * iSpecialize ("hh0" $! w).
          iRewrite -"hh0".
          iSpecialize ("hh1" $! w).
          iRewrite -"hh1".
          simpl.
          iIntros "hh".
          by iApply "h".
        * iSpecialize ("hh0" $! w).
          iRewrite -"hh0".
          iSpecialize ("hh1" $! w).
          iRewrite -"hh1".
          simpl.
          iIntros "hh".
          by iApply "h".
      + by iApply ("HI" $! k).
  Qed.

  Lemma interp_tag_equivI (Σ0 Σ1: list (interp Σ)):
    Σ0 ≡ Σ1 →
    ∀ A v, interp_tag interp_type Σ0 A v ≡ interp_tag interp_type Σ1 A v.
  Proof.
    move => h A v.
    rewrite !interp_tag_unseal /interp_tag_def /interp_variance /=.
    do 17 f_equiv.
    { f_equiv; split => hh.
      + do 7 destruct hh as [? hh].
        repeat split => //.
        by rewrite -h.
      + do 7 destruct hh as [? hh].
        repeat split => //.
        by rewrite h.
    }
    by repeat f_equiv.
  Qed.

  Lemma interp_tag_alt_equivI (Σ0 Σ1: list (interp Σ)):
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    Σ0 ≡ Σ1 →
    ∀ A v,
    interp_tag_alt Σ0 A v ≡ interp_tag_alt Σ1 A v.
  Proof.
    move => hp h A v.
    rewrite -!(interp_tag_equiv A) //; last first.
    by rewrite interp_tag_equivI.
  Qed.

  Lemma interp_class_unfold Σi A σA v:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    wf_ty (ClassT A σA) →
    interp_type (ClassT A σA) Σi v ⊣⊢
    interp_tag_alt (interp_list Σi σA) A v.
  Proof.
    move => hwfp hwf.
    inv hwf.
    move : (interp_tag_equiv A (interp_list Σi σA) v hwfp) => heq.
    rewrite -heq interp_type_unfold /=.
    assert (h: go interp_type Σi <$> σA ≡ interp_list Σi σA).
    { rewrite /interp_list.
      apply list_fmap_equiv_ext => ty w.
      by rewrite interp_type_unfold.
    }
    by apply interp_tag_equivI with (A := A) (v := v) in h.
  Qed.

  Lemma interp_generic_unfold Σi k v:
    interp_type (GenT k) Σi v ⊣⊢
    interp_generic Σi k v.
  Proof.  by rewrite interp_type_unfold /=. Qed.

  Lemma interp_type_subst Σi ty σ v:
    bounded (length σ) ty →
    interp_type (subst_ty σ ty) Σi v ≡
    interp_type ty (interp_list Σi σ) v.
  Proof.
    move => hbounded.
    rewrite !interp_type_unfold; revert v.
    induction ty as [ | | | | C σC hi | | | A B hA hB | A B hA hB | i | C | ] => //= v.
    - rewrite !interp_tag_unseal /interp_tag_def /= /interp_variance.
      do 17 f_equiv.
      { f_equiv; by rewrite !fmap_length. }
      f_equiv.
      { do 12 f_equiv.
        rewrite -list_fmap_compose.
        apply list_fmap_equiv_ext_elem_of => ty hin w.
        rewrite Forall_forall in hi.
        apply hi with (v := w) in hin; first by rewrite hin.
        inv hbounded.
        rewrite Forall_forall in H0.
        by apply H0.
      }
      do 17 f_equiv.
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

  Lemma interp_type_equivI (Σ0 Σ1: list (interp Σ)):
    Σ0 ≡ Σ1 →
    ∀ ty v, interp_type ty Σ0 v ≡ interp_type ty Σ1 v.
  Proof.
    move => hΣ ty v.
    rewrite !interp_type_unfold; revert v.
    induction ty as [ | | | | C σC hi | | | A B hA hB | A B hA hB | i | C | ] => //= v.
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

  Lemma iForall3_interp_equivI (Σ0 Σ1 : list (interp Σ)):
    Σ0 ≡ Σ1 →
    ∀ vs Σi,
    iForall3 interp_variance vs Σ0 Σi ≡ iForall3 interp_variance vs Σ1 Σi.
  Proof.
    move => heq vs.
    assert (hl: length Σ0 = length Σ1) by by rewrite heq.
    move : Σ0 Σ1 heq hl.
    induction vs as [ | v vs hi] => Σ0 Σ1 heq hl Σi.
    { by destruct Σ0; destruct Σ1; destruct Σi. }
    destruct Σ0 as [ | i0 Σ0] => //=.
    { symmetry in hl.
      by apply nil_length_inv in hl; rewrite hl.
    }
    destruct Σ1 as [ | i1 Σ1] => //=.
    destruct Σi as [ | i Σi] => //=.
    case : hl => hl.
    apply cons_equiv_eq in heq as (i1' & Σ1' & [= -> ->] & h0 & h1).
    f_equiv.
    - rewrite /interp_variance.
      by repeat f_equiv.
    - by rewrite (hi _ _ h1 hl Σi).
  Qed.

  Lemma iForall3_interp_reflexive vs :
    ∀ Σi, length vs = length Σi → ⊢ iForall3 interp_variance vs Σi Σi.
  Proof.
    induction vs as [ | v vs hi]; intros [ | i Σi] hlen => //=.
    case : hlen => hlen.
    iSplitL.
    - by iApply interp_variance_reflexive.
    - by iApply hi.
  Qed.

  Lemma iForall3_interp_gen_targs vs n Σi:
    length vs = n →
    length Σi = n →
    ⊢ iForall3 interp_variance vs (interp_list Σi (gen_targs n)) Σi.
  Proof.
    move => hl0 hl1.
    assert (heq: interp_list Σi (gen_targs n) ≡ Σi).
    { rewrite /interp_list.
      apply list_equiv_lookup => k.
      destruct (Σi !! k) as [i | ] eqn:hi.
      - rewrite !list_lookup_fmap hi !lookup_seq_lt //=.
        { f_equiv => w.
          by rewrite !interp_generic_unfold /interp_generic /= hi.
        }
        apply lookup_lt_Some in hi.
        by lia.
      - rewrite hi.
        apply lookup_ge_None_1 in hi.
        rewrite /gen_targs !list_lookup_fmap /= lookup_seq_ge //.
        by lia.
    }
    rewrite (iForall3_interp_equivI _ _ heq).
    apply iForall3_interp_reflexive => //.
    by rewrite hl0.
  Qed.

  Lemma iForall3_interp_trans vs:
    ∀ Σ0 Σ1 Σ2,
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
    iInduction ty as [ | | | | C σC hi | | | A B hA hB | A B hA hB | i | C | ] 
        "IHty" forall (Σ0 Σ1 vs hmono) "h"; iIntros (v); rewrite !interp_type_unfold //=.
    - by iIntros.
    - rewrite !interp_tag_unseal /interp_tag_def /interp_fun !interp_car_simpl.
      iIntros "htag".
      iDestruct "htag" as (l t cdef tdef σ Σt fields ifields h) "[#hmixed [#hconstr [#hinst [hdyn hloc]]]]".
      destruct h as (-> & hcdef & htdef & hlΣc & hlΣt & hinherits & hfields & hdom).
      iExists l, t, cdef, tdef, σ, Σt, fields, ifields.
      iSplitR.
      { iPureIntro; repeat split=> //.
        rewrite fmap_length.
        by rewrite fmap_length in hlΣc.
      }
      iSplitR.
      { iModIntro; iNext; iIntros (i ii heq v) "hii".
        iSpecialize ("hmixed" $! i ii heq v with "hii").
        iClear "IHty h hinst".
        iDestruct (interp_mixed_unfold (go interp_type Σ0 <$> σC) v) as "[hm0 hm1]".
        iDestruct (interp_mixed_unfold (go interp_type Σ1 <$> σC) v) as "[hm2 hm3]".
        iDestruct ("hm0" with "hmixed") as "hm".
        by iApply "hm3".
      }
      iSplitR.
      { iModIntro; iNext; iIntros (i c heq v) "hc".
        by iSpecialize ("hconstr" $! i c heq v with "hc").
      }
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
      iDestruct (neg_interp_variance with "h") as "hneg".
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
          by apply H2 with k Invariant.
        }
        assert (hmono1: mono (neg_variance <$> vs) t1).
        { inv hmono; simplify_eq.
          by apply H3 with k Invariant.
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
          by apply H2 with k Covariant.
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
          by apply H3 with k Contravariant.
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
      iDestruct "hh" as (Σt) "hh".
      by iExists Σt.
  Qed.

  Lemma interp_env_with_mono :
    map_Forall (λ _ : string, wf_cdef_mono) Δ →
    map_Forall (λ _ : string, wf_cdef_parent Δ) Δ →
    ∀ σ vs Σ0 Σ1 ws,
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
    iForall3 interp_variance ws (interp_list Σ0 σ) (interp_list Σ1 σ).
  Proof.
    move => hmono hp.
    induction σ as [ | ty σ hi] => //= vs Σ0 Σ1 ws hwf hlen hcov hcontra.
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
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _ : string, wf_cdef_mono) Δ →
    ∀ A B σB, extends_using A B σB →
    ∀ Σi v,
    interp_tag_alt Σi A v -∗
    interp_tag_alt (interp_list Σi σB) B v.
  Proof.
    move => hwp hmono A B σB hext Σi v.
    assert (hb: ∃ bdef, Δ !! B = Some bdef ∧ length bdef.(generics) = length (interp_list Σi σB)).
    { apply extends_using_wf in hext => //.
      destruct hext as (? & ? & ? & h).
      inv h; simplify_eq.
      exists def; repeat split => //.
      by rewrite /interp_list fmap_length.
    }
    destruct hb as (bdef & hbdef & hlen2).
    iIntros "h".
    iDestruct "h" as (ℓ t adef tdef σ Σt fields ifields) "[%h [#hmixed [#hconstr [#hinst [hdyn hl]]]]]".
    destruct h as (-> & hadef & htdef & hlΣi & hlΣt & hin & hfields & hdom); simplify_eq.
    destruct (extends_using_wf _ _ _ hwp hext) as (adef' & hadef' & hF & hwfB).
    destruct (inherits_using_wf _ _ _ hwp hin) as (tdef' & htdef' & htF & hwfA).
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
    assert (heq: interp_list Σt (subst_ty σ <$> σB) ≡ interp_list (interp_list Σt σ) σB).
    { rewrite /interp_list -!list_fmap_compose.
      apply list_fmap_equiv_ext_elem_of => ty0 hin0 /= w.
      rewrite interp_type_subst //.
      rewrite Forall_forall in hF.
      inv hwfA; simplify_eq.
      rewrite H2.
      by apply hF.
    }
    rewrite (iForall3_interp_equivI _ _ heq bdef.(generics) (interp_list Σi σB)).
    iApply (interp_env_with_mono with "hinst") => //.
    + by apply wf_ty_class_inv in hwfB.
    + inv hwfB; by simplify_eq.
    + move => i wi ti hwi hti hc.
      apply extends_using_mono with (def := adef) in hext => //.
      inv hext; simplify_eq; by eauto.
    + move => i wi ti hwi hti hc.
      apply extends_using_mono with (def := adef) in hext => //.
      inv hext; simplify_eq; by eauto.
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
    move => hp ? Σi A B σA σB v hext hwfA.
    iIntros "h".
    assert (hb: wf_ty (ClassT B σB)).
    { apply extends_using_wf in hext => //.
      by destruct hext as (?&?&?&?).
    }
    assert (hb0 := hb).
    inv hb0.
    rewrite !interp_class_unfold //.
    - iDestruct (tag_extends_using_is_inclusion with "h") as "hh" => //.
      assert (hΣ : interp_list Σi (subst_ty σA <$> σB) ≡
                   interp_list (interp_list Σi σA) σB).
      { rewrite /interp_list -list_fmap_compose.
        apply list_fmap_equiv_ext_elem_of => ty0 hin0 /= w.
        rewrite -interp_type_subst //.
        apply extends_using_wf in hext => //.
        destruct hext as (adef & ? & hF & _); simplify_eq.
        rewrite Forall_forall in hF.
        inv hwfA; simplify_eq.
        rewrite H6; by apply hF.
      }
      by rewrite (interp_tag_alt_equivI _ _ hp hΣ).
    - change (wf_ty (ClassT B (subst_ty σA <$> σB))) with (wf_ty (subst_ty σA (ClassT B σB))).
      apply wf_ty_subst => //.
      by apply wf_ty_class_inv in hwfA.
  Qed.

  Section Inclusion.
    Hypothesis Σc: list constraint.
    Hypothesis wfΣc: Forall wf_constraint Σc.
    Hypothesis wf_parent : map_Forall (λ _cname, wf_cdef_parent Δ) Δ.
    Hypothesis wf_mono : map_Forall (λ _ : string, wf_cdef_mono) Δ.

  (* Extracting subproofs for clarity *)
  Lemma subvariance_is_inclusion_aux Σi:
    ∀ A adef σ0 σ1 v,
    Δ !! A = Some adef →
    wf_ty (ClassT A σ0) →
    Forall wf_ty σ1 →
    ⊢ □ iForall3 interp_variance adef.(generics) (interp_list Σi σ0) (interp_list Σi σ1) →
    interp_type (ClassT A σ0) Σi v -∗
    interp_type (ClassT A σ1) Σi v.
  Proof.
    move => A adef σ0 σ1 v hadef hwfA hwfσ1.
    iIntros "#hσ #h".
    iAssert (⌜length σ0 = length σ1⌝)%I as "%hl0".
    { iDestruct (iForall3_length with "hσ") as "%hh".
      iPureIntro.
      rewrite /interp_list !fmap_length in hh.
      by destruct hh.
    }
    rewrite !interp_class_unfold //; last first.
    { apply wf_ty_class with adef => //.
      inv hwfA; simplify_eq.
      by rewrite -hl0.
    }
    iDestruct "h" as (l t adef' tdef σtA Σt fields ifields h) "[#hmixed [#hconstr [#hinst [hdyn hl]]]]".
    destruct h as (-> & hadef' & htdef & hlΣ0 & hlΣt & hinherits & hfields & hdom); simplify_eq.
    iExists l, t, adef, tdef, σtA, Σt, fields, ifields.
    iSplit.
    { iPureIntro; repeat split => //.
      rewrite /interp_list fmap_length in hlΣ0.
      by rewrite /interp_list fmap_length -hl0.
    }
    iSplit => //.
    iSplit => //.
    iSplit; last by iSplit.
    iModIntro; iNext.
    iClear "hdyn hl hmixed".
    by iApply (iForall3_interp_trans with "hinst hσ").
  Qed.

  Lemma submixed_is_inclusion_aux Σi:
    ∀ A v, wf_ty A →
    □ interp_env_as_mixed Σi -∗
    interp_type A Σi v -∗
    interp_type MixedT Σi v.
  Proof.
    iIntros (A v hwf) "#wfΣi h".
    rewrite !interp_type_unfold /=.
    iInduction A as [ | | | | C σC hi | | | A B hA hB | A B hA hB | i | C | ] 
        "IHty" forall (v hwf) "h".
    - by repeat iLeft.
    - by iLeft; iRight; iLeft.
    - by rewrite /interp_nothing.
    - done.
    - iLeft; iRight; iRight => /=.
      iExists C.
      iExists (interp_list Σi σC).
      assert (heq: (go interp_type Σi <$> σC) ≡ interp_list Σi σC).
      { rewrite /interp_list.
        apply list_fmap_equiv_ext => ty w.
        by rewrite interp_type_unfold.
      }
      by rewrite (interp_tag_equivI _ _ heq C v).
    - by iRight.
    - by iLeft.
    - inv hwf.
      rewrite /interp_union.
      iDestruct "h" as "[ h | h ]"; first by iApply "IHty".
      by iApply "IHty1".
    - inv hwf.
      rewrite /interp_inter.
      iDestruct "h" as "[? _]"; by iApply "IHty".
    - rewrite /= /interp_generic.
      destruct (decide (i < length Σi)) as [hlt | hge].
      + apply lookup_lt_is_Some_2 in hlt as [ϕ hϕ].
        iApply "wfΣi"; last done.
        by rewrite /= /interp_generic hϕ /=.
      + rewrite /= /interp_generic lookup_ge_None_2 /=; last by apply not_lt.
        done.
    - rewrite /interp_ex.
      iLeft; iRight; iRight.
      by iExists _.
    - done.
  Qed.

  (* Main meat for A <: B → [|A|] ⊆ [|B|] *)
  Theorem subtype_is_inclusion_aux Σi A B:
    Σc ⊢ A <: B →
    ∀ v,
    wf_ty A →
    □ interp_env_as_mixed Σi -∗
    □ Σinterp Σi Σc -∗
    interp_type_pre interp_type A Σi v -∗
    interp_type_pre interp_type B Σi v
    with subtype_targs_is_inclusion_aux Σi Vs As Bs:
    Forall wf_ty As →
    Forall wf_ty Bs →
    Σc ⊢ As <:Vs:> Bs →
    □ interp_env_as_mixed Σi -∗
    □ Σinterp Σi Σc -∗
    □ iForall3 interp_variance Vs (interp_list Σi As) (interp_list Σi Bs).
  Proof.
    { destruct 1 as [A | A h | A σA B σB adef hΔ hlen hext
      | A adef hadef hL | A def σ0 σ1 hΔ hwfσ hσ | | | | A | A B h
      | A B h | A B C h0 h1 | A B | A B | A B C h0 h1
      | A | A B C h0 h1 | A B hin]; iIntros (v hwfA) "#wfΣi #Σcoherency h".
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        rewrite -!interp_type_unfold.
        by iApply submixed_is_inclusion_aux.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        done.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        rewrite -!interp_type_unfold; by iApply extends_using_is_inclusion.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        simpl.
        iDestruct "h" as (Σt) "h".
        iAssert (⌜Σt = []⌝)%I as "%hnil".
        { rewrite interp_tag_equiv => //.
          iDestruct "h" as (???????? h) "h".
          destruct h as (?&?&?&hl&h).
          simplify_eq.
          rewrite hL in hl.
          by apply nil_length_inv in hl.
        }
        by rewrite hnil.
      - apply subtype_targs_is_inclusion_aux with (Σi := Σi) in hσ => //; last first.
        { by apply wf_ty_class_inv in hwfA. }
        clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        rewrite -!interp_type_unfold.
        iApply subvariance_is_inclusion_aux => //.
        by iApply hσ.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        by rewrite /= /interp_mixed.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        by iLeft.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        by iRight; iLeft.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        iRight; iRight.
        iExists A, (go interp_type Σi <$> targs).
        by rewrite -interp_type_unfold interp_class_unfold.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        by iLeft.
      - clear subtype_is_inclusion_aux subtype_targs_is_inclusion_aux.
        by iRight.
      - clear subtype_targs_is_inclusion_aux.
        rewrite /= /interp_union.
        iDestruct "h" as "[h | h]".
        + iApply (subtype_is_inclusion_aux with "wfΣi Σcoherency"); [exact h0 | | ].
          * inv hwfA; by assumption.
          * by iAssumption.
        + iApply (subtype_is_inclusion_aux with "wfΣi Σcoherency"); [exact h1 | | ].
          * inv hwfA; by assumption.
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
        + iApply (subtype_is_inclusion_aux with "wfΣi Σcoherency"); [exact h0 | done | ].
          by iAssumption.
        + iApply (subtype_is_inclusion_aux with "wfΣi Σcoherency"); [exact h1 | done | ].
          by iAssumption.
      - done.
      - iApply (subtype_is_inclusion_aux with "wfΣi Σcoherency"); [exact h1 | | ].
        + apply subtype_wf in h0; [ | done | done | done ].
          by assumption.
        + iApply (subtype_is_inclusion_aux with "wfΣi Σcoherency"); [exact h0 | done | ].
          by iAssumption.
      - apply elem_of_list_lookup_1 in hin as [i hin].
        rewrite -!interp_type_unfold /=.
        by iApply ("Σcoherency" $! i (A, B) hin).
    }
    move => hwfA hwfB.
    destruct 1 as [ | ????? h0 h1 h | ????? h0 h | ????? h0 h]; iIntros "#wfΣi #Σcoherency".
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
  Theorem subtype_is_inclusion Σi:
    ∀ A B, Σc ⊢ A <: B →
    ∀ v,
    wf_ty A →
    □ interp_env_as_mixed Σi -∗
    □ Σinterp Σi Σc -∗
    interp_type A Σi v -∗ interp_type B Σi v.
  Proof.
    iIntros (A B hAB v ?) "#wfΣi #Σcoherency".
    rewrite !interp_type_unfold.
    by iApply (subtype_is_inclusion_aux with "wfΣi Σcoherency").
  Qed.

  Definition interp_this_def
    (C: tag)
    (Σi : list (interp Σ))
    : interp Σ :=
    Interp (
      λ (w : value), (∃ ℓ t cdef tdef σ (Σt: list (interp Σ))
       (fields: stringmap ((visibility * lang_ty) * tag))
       (ifields: gmapO string (laterO (sem_typeO Σ))),
      ⌜w = LocV ℓ ∧
       Δ !! C = Some cdef ∧
       Δ !! t = Some tdef ∧
       length Σi = length cdef.(generics) ∧
       length Σt = length tdef.(generics) ∧
       inherits_using t C σ ∧
       has_fields t fields ∧
       dom fields = dom ifields⌝ ∗

      □ ▷ interp_env_as_mixed Σt ∗

      □ ▷ Σinterp Σt tdef.(constraints) ∗

      ((λ ty, interp_type ty Σt) <$> σ) ≡ Σi ∗

      (∀ f vis ty orig, ⌜has_field f t vis ty orig⌝ -∗
        ifields !! f ≡ Some (Next (interp_car (interp_type ty Σt)))) ∗

      (ℓ ↦ (t, ifields)))%I
    ).

   Local Definition interp_this_aux
     (C: tag)
     (Σi : list (interp Σ))
     : seal (@interp_this_def C Σi).
   Proof. by eexists. Qed.

   Definition interp_this C (Σi: list (interp Σ)) :=
     (interp_this_aux C Σi).(unseal).

   Definition interp_this_unseal C (Σi : list (interp Σ))
     : interp_this C Σi = interp_this_def C Σi :=
     (interp_this_aux C Σi).(seal_eq).

  Definition interp_this_type C (σC: list lang_ty) Σi : interp Σ :=
    interp_this C (interp_list Σi σC).

  Definition interp_local_tys Σi
    (lty : local_tys) (le : local_env) : iProp Σ := 
    interp_this_type lty.(type_of_this).1 lty.(type_of_this).2 Σi (LocV le.(vthis)) ∗
    (∀ v ty, ⌜lty.(ctxt) !! v = Some ty⌝ -∗
    ∃ val, ⌜le.(lenv) !! v = Some val⌝ ∗ interp_type ty Σi val)%I.

  Lemma interp_local_tys_is_inclusion Σi lty rty le:
    wf_lty lty →
    Forall (λ (i: interp Σ), ∀ v, Persistent (i v)) Σi →
    Σc ⊢ lty <:< rty →
    □ interp_env_as_mixed Σi -∗
    □ Σinterp Σi Σc -∗
    interp_local_tys Σi lty le -∗
    interp_local_tys Σi rty le.
  Proof.
    move => hlty hpers hsub; iIntros "#wfΣi #? [#Hthis Hle]".
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
    iDestruct "H" as (Σx) "H".
    destruct hxy as [x y xdef' σy hxdef' hsuper]; simplify_eq.
    assert (hext: extends_using x y σy) by (econstructor; by eauto).
    rewrite (interp_tag_equiv x) //.
    iDestruct ((tag_extends_using_is_inclusion wf_parent wf_mono x y σy) with "H") as "H" => //.
    rewrite interp_ex_unfold /interp_ex /=.
    apply wf_parent in hxdef'.
    rewrite /wf_cdef_parent hsuper in hxdef'.
    destruct hxdef' as [hwf _].
    inv hwf.
    iExists (interp_list Σx σy).
    by rewrite (interp_tag_equiv y).
  Qed.
  End Inclusion.
End proofs.
