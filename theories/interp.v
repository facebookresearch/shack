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

  Definition interp_fields (env: list (interp Σ)) (ftys: stringmap lang_ty) (rec: ty_interpO) :
    gmapO string (laterO (sem_typeO Σ)) :=
    let f := λ (typ: lang_ty), Next (interp_car (rec typ env)) in
    @fmap _ _ _ (later (sem_typeO Σ)) f ftys
  .

  Lemma interp_fields_env env0 env1 ftys (rec: ty_interpO):
    (∀ ty, rec ty env0 ≡ rec ty env1) →
    env0 ≡ env1 →
    interp_fields env0 ftys rec ≡ interp_fields env1 ftys rec.
  Proof.
    rewrite /interp_fields => hrec henv.
    induction ftys as [| s ty ftys Hs IH] using map_ind; first by constructor.
    rewrite !fmap_insert IH.
    do 2 f_equiv.
    by apply hrec.
  Qed.

  Lemma interp_fields_contractive ftys env: Contractive (interp_fields env ftys).
  Proof.
    rewrite /interp_fields => n i1 i2 hdist.
    apply gmap_fmap_ne_ext => k ty hin.
    f_contractive; simpl.
    apply interp_car_ne2.
    by f_equiv.
  Qed.

  Lemma interp_fields_ne ftys (rec: ty_interpO):
    NonExpansive (λ env, interp_fields env ftys rec).
  Proof.
    rewrite /interp_fields => n l1 l2 h f.
    f_equiv.
    apply gmap_fmap_ne_ext => k ty hin.
    f_equiv.
    by apply ty_interpO_ne.
  Qed.

  (* interpret a class type given the tag and the
     interpretation of their fields *)
  Definition interp_class (cname : tag) (env: list (interp Σ)) (rec : ty_interpO) : interp Σ :=
    Interp (
      λ (w : value),
      (∃ ℓ t (fields:stringmap lang_ty),
      ⌜w = LocV ℓ ∧ inherits t cname ∧ has_fields t fields⌝ ∗
      (ℓ ↦ (t , interp_fields env fields rec)))%I
    ).

  (* Lemma interp_class_env env0 env1 cname (rec: ty_interpO): *)
  (*   (∀ ty, rec ty env0 ≡ rec ty env1) → *)
  (*   env0 ≡ env1 → *)
  (*   interp_class cname env0 rec ≡ interp_class cname env1 rec. *)
  (* Proof. *)
  (*   rewrite /interp_class => hrec henv v /=. *)
  (*   do 7 f_equiv. *)
  (*   iStartProof; iSplitR; iIntros "H". *)
  (*   rewrite interp_fields_env. *)

  Definition interp_ex (cname: tag) (rec: ty_interpO): interp Σ :=
    Interp (λ (w: value), (∃ env, interp_class cname env rec w)%I).

  Definition interp_nonnull (rec : ty_interpO) : interp Σ :=
    Interp (
      λ (v : value),
      ((interp_int v) ∨
      (interp_bool v) ∨
      (∃ t env, interp_class t env rec v))%I
    ).

  Definition interp_mixed (rec: ty_interpO) : interp Σ :=
    Interp (λ (v: value), (interp_nonnull rec v ∨ interp_null v)%I).

  Definition interp_generic (env: list (interpO Σ)) (tv: nat) : interp Σ :=
    default interp_nothing (env !! tv).

  (* we use a blend of Coq/Iris recursion, the
     Coq recursion lets us handle simple structural
     cases, and we use Iris' recursion to deal with
     the more complicated case of class types.
  *)
  Section interp_type_pre_rec.
    Variable (env: listO (interpO Σ)).
    Variable (rec: ty_interpO).

    Fixpoint go (typ: lang_ty) : interp Σ :=
      match typ with
      | IntT => interp_int
      | BoolT => interp_bool
      | NothingT => interp_nothing
      | MixedT => interp_mixed rec
      | ClassT t targs =>
          let env : list (interp Σ) := List.map go targs in
          interp_class t env rec
      | NullT => interp_null
      | NonNullT => interp_nonnull rec
      | UnionT A B => interp_union (go A) (go B)
      | InterT A B => interp_inter (go A) (go B)
      | GenT n => interp_generic env n
      | ExT cname => interp_ex cname rec
      end.
  End interp_type_pre_rec.

  Lemma interp_class_ne cname (rec: ty_interpO) :
    NonExpansive (λ env, interp_class cname env rec).
  Proof.
    move => n x y h.
    rewrite /interp_class => v.
    rewrite /interp_fun !interp_car_simpl.
    do 7 f_equiv.
    rewrite mapsto_eq /mapsto_def /loc_mapsto_def.
    do 3 f_equiv.
    by apply interp_fields_ne.
  Qed.

  Local Instance go_ne (rec: ty_interpO) (ty: lang_ty) :
    NonExpansive (λ env, go env rec ty).
  Proof.
    induction ty
      as [ | | | | cname targs htargs | | | A B hA hB | A B hA hB | i | cname ]
      using lang_ty_ind' => //= n x y h.
    - apply interp_class_ne => //.
      rewrite Forall_forall in htargs.
      induction targs as [ | hd tl hi] => //=.
      f_equiv.
      { apply htargs; last done.
        by constructor.
      }
      apply hi => ? hIn.
      apply htargs.
      now constructor.
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

  (* TODO: try to make this nicer by avoiding the pre definition of go/go_ne.
   * Right now if we remove what's before, Coq can't find the _ne proof
   * for the internal fixpoint
   *)
  Definition interp_type_pre (rec : ty_interpO) : ty_interpO :=
    λ (typ : lang_ty), λne (env: listO (interpO Σ)), 
    let go_rec :=
    (fix go (typ: lang_ty) : interp Σ :=
      match typ with
      | IntT => interp_int
      | BoolT => interp_bool
      | NothingT => interp_nothing
      | MixedT => interp_mixed rec
      | ClassT t targs =>
          let env : list (interp Σ) := List.map go targs in
          interp_class t env rec
      | NullT => interp_null
      | NonNullT => interp_nonnull rec
      | UnionT A B => interp_union (go A) (go B)
      | InterT A B => interp_inter (go A) (go B)
      | GenT n => interp_generic env n
      | ExT cname => interp_ex cname rec
      end)
    in go_rec typ.

  Global Instance interp_type_pre_persistent (rec: ty_interpO) :
    ∀ t env v, Persistent (interp_type_pre rec t env v).
  Proof. by move => ???; apply _. Qed.


  Lemma interp_class_contractive cname env: Contractive (interp_class cname env). 
  Proof.
    rewrite /interp_class => n i1 i2 hdist v.
    rewrite /interp_fun !interp_car_simpl.
    f_equiv ; intro l.
    f_equiv; intro t.
    f_equiv; intro fields.
    f_equiv.
    rewrite mapsto_eq /mapsto_def /loc_mapsto_def.
    do 3 f_equiv.
    by apply interp_fields_contractive.
  Qed.

  Lemma interp_nonnull_contractive : Contractive interp_nonnull.
  Proof.
    rewrite /interp_nonnull => n i1 i2 hdist v.
    rewrite /interp_fun !interp_car_simpl.
    do 6 f_equiv.
    revert v.
    by apply interp_class_contractive.
  Qed.

  (* we cannot use solve_contractive out of the box because of
   * the 'fix' combinator above
   *)
  Local Instance interp_type_pre_contractive : Contractive interp_type_pre.
  Proof.
    rewrite /interp_type_pre => n rec1 rec2 hdist ty env /=.
    induction ty
      as [ | | | | cname targs htargs | | | A B hA hB | A B hA hB | i | cname ]
      using lang_ty_ind' => //=.
    - rewrite /interp_mixed => v.
      rewrite /interp_fun !interp_car_simpl.
      f_equiv.
      revert v; by apply interp_nonnull_contractive.
    - move => v.
      transitivity (interp_class cname (map (go env rec2) targs) rec1 v).
      + revert v; apply interp_class_ne.
        (* copied from _ne proof *)  
        rewrite Forall_forall in htargs.
        induction targs as [ | hd tl hi] => //=.
        f_equiv.
        { apply htargs.  by constructor. }
        apply hi => ? hIn.
        apply htargs.
        now constructor.
      + revert v; by apply interp_class_contractive.
    - by apply interp_nonnull_contractive.
    - solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv]).
    - solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv]).
    - rewrite /interp_ex => v.
      rewrite /interp_fun !interp_car_simpl.
      do 2 f_equiv.
      by revert v; apply interp_class_contractive.
  Qed.

  (* the interpretation of types can now be
     defined as a fixpoint (because class types
     can be (mutually) recursive) *)
  Definition interp_type := fixpoint interp_type_pre.

  Record interp_env := InterpEnv {
    interp_env_car :> list (interpO Σ);
    interp_env_as_mixed:
      Forall (λ (e: interp Σ), ∀ v, e v -∗ interp_mixed interp_type v) interp_env_car
  }.

  Lemma interp_type_unfold (env: list (interpO Σ)) (ty : lang_ty) (v : value) :
    interp_type ty env v ⊣⊢ interp_type_pre interp_type ty env v.
  Proof.
    rewrite {1}/interp_type.
    apply (fixpoint_unfold interp_type_pre ty env v).
  Qed.

  Lemma interp_class_unfold env cname targs v:
    interp_type (ClassT cname targs) env v ⊣⊢
    interp_class cname (map (go env interp_type) targs) interp_type v.
  Proof. by rewrite interp_type_unfold. Qed.

  Lemma interp_union_unfold env A B v:
    interp_type (UnionT A B) env v ⊣⊢
    interp_union (interp_type A env) (interp_type B env) v.
  Proof.
    rewrite interp_type_unfold /=.
    iSplit; iIntros "[H | H]".
    - iLeft; by rewrite interp_type_unfold.
    - iRight; by rewrite interp_type_unfold.
    - iLeft; by rewrite interp_type_unfold.
    - iRight; by rewrite interp_type_unfold.
  Qed.

  Lemma interp_inter_unfold env A B v:
    interp_type (InterT A B) env v ⊣⊢
    interp_inter (interp_type A env) (interp_type B env) v.
  Proof.
    rewrite interp_type_unfold /=.
    iSplit; iIntros "[HL HR]".
    - rewrite !interp_type_unfold; by iSplit.
    - rewrite !interp_type_unfold; by iSplit.
  Qed.

  Lemma interp_type_go env ty :
    go env interp_type ty ≡ interp_type ty env.
  Proof.
    move => v.
    rewrite interp_type_unfold /=.
    by elim: ty.
  Qed.

  Lemma interp_type_env_ext env0 env1 ty v:
    (env0 ≡ env1)%I -∗
    interp_type ty env0 v  ∗-∗ interp_type ty env1 v.
  Proof.
    iIntros "H".
    iRewrite "H".
    iSplit; by iIntros "H".
  Qed.

  Lemma interp_type_map_go fty env targs v:
    interp_type fty (map (go env interp_type) targs) v ⊣⊢
    interp_type fty (map (λ ty : lang_ty, interp_type ty env) targs) v.
  Proof.
    iApply interp_type_env_ext.
    iApply list_equivI.
    iIntros (n).
    rewrite !list_lookup_fmap.
    destruct (decide (n < length targs)) as [heq | hne].
    - apply lookup_lt_is_Some_2 in heq as [ty ->].
      rewrite option_equivI; simpl.
      by rewrite interp_type_go.
    - rewrite !lookup_ge_None_2 /=; last by lia.
      done.
  Qed.

  (*
  (* MOVE TO HELPER FILE / STDPP *)
  Section fmap.
    Context {A B : Type} (f : A → B).
    Implicit Types l : list A.
    Lemma list_fmap_equiv_ext_in `{!Equiv B} (g : A → B) l :
      (∀ x, x ∈ l → f x ≡ g x) → f <$> l ≡ g <$> l.
    Proof.
      induction l as [ | hd tl hi] => h //=; first by constructor.
      constructor.
      - apply h; by constructor.
      - apply hi => x hx; apply h; by constructor.
    Qed.
  End fmap.

  Lemma go_subst ty : ∀ env targs v,
    go (map (λ ty0 : lang_ty, interp_type ty0 env) targs) interp_type ty v ⊣⊢
    go env interp_type (subst targs ty) v.
  Admitted.
  (*
  Proof.
    induction ty
      as [ | | | | cname args hargs | | | A B hA hB | A B hA hB | i | cname ]
      using lang_ty_ind' => env targs //=.
    - rewrite map_map.
      assert (hmap:
        (map (go (map (λ ty0 : lang_ty, interp_type ty0 env) targs) interp_type) args) ≡
        (map (λ x : lang_ty, go env interp_type (subst targs x)) args)).
      { apply list_fmap_equiv_ext_in => x hx.
        rewrite Forall_forall in hargs.
        by rewrite hargs; last done.
      }
      rewrite hmap.

      { rewrite map_map.
        apply list_equivI.
        apply map_ext_in  => a /elem_of_list_In ha.
      rewrite Forall_forall in hargs.
      apply hargs.
    - by rewrite hA hB.
    - by rewrite hA hB.
    - rewrite /interp_generic. 
      rewrite list_lookup_fmap.
      destruct (decide (i < length targs)) as [ hlt | hge].
      + apply lookup_lt_is_Some_2 in hlt as [a ->] => /=.
        symmetry.
        rewrite interp_type_go.
lookup_lt_is_Some_2:
  ∀ (A : Type) (l : list A) (i : nat), i < length l → is_Some (l !! i)
      Search lookup "map".

      replace interp_nothing with (interp_type NothingT env); last first.
      { rewrite interp_type_unfold .
      rewrite map_nth.


  Qed.

   *)
  (* Lemma *) 
  (*       assert (hmap: *)
  (*         (map (go (map (λ ty : lang_ty, interp_type ty env) fargs) interp_type) targs) = *)
  (*         (map (λ x : lang_ty, go env interp_type (subst fargs x)) targs) *)
  (*       ). *)

  Lemma interp_type_subst fty fargs env w:
    interp_type fty (map (λ ty : lang_ty, interp_type ty env) fargs) w -∗
    interp_type (subst fargs fty) env w.
  Proof.
    rewrite !interp_type_unfold.
    revert w.
    induction fty
      as [ | | | | cname targs htargs | | | A B hA hB | A B hA hB | i | cname ]
      using lang_ty_ind' => // w.
      - rewrite -!interp_type_unfold !interp_class_unfold.
        fold subst.
        rewrite map_map.
        iIntros "H".
        iDestruct "H" as (l t fields) "[%H Hl]".
        destruct H as [-> [hin hfs]].
        iExists l, t, fields; iSplitR; first done.
        assert (hmap:
          (map (go (map (λ ty : lang_ty, interp_type ty env) fargs) interp_type) targs) =
          (map (λ x : lang_ty, go env interp_type (subst fargs x)) targs)
        ).
        admit.
        rewrite hmap.
        done.
        admit.
        iRewrite "hmap".



        admit.
        iIntros "H".
        rewrite map_map.
        iRewrite "hmap".
        iDestruct "H" as (l t fields) "[%H Hl]".
        destruct H as [-> [hin hfs]].
        iExists l, t, fields; iSplitR; first done.
        assert (hmap:
              (map (go (map (λ ty : lang_ty, interp_type ty env) fargs) interp_type) targs)
              =
              (map (λ x : lang_ty, go env interp_type (subst fargs x)) targs)
              ).
              clear cname l t fields hin hfs.
              apply map_ext_in => ty hin.



    - rewrite -interp_type_unfold interp_union_unfold.
      iIntros "[H | H]".
      + iLeft.
        iApply hA.
        by rewrite -interp_type_unfold.
      + iRight.
        iApply hB.
        by rewrite -interp_type_unfold.
    - rewrite -interp_type_unfold interp_inter_unfold.
      iIntros "[HL HR]".
      iSplit.
      + iApply hA.
        by rewrite -interp_type_unfold.
      + iApply hB.
        by rewrite -interp_type_unfold.
    - iAssert (∀ i j, ⌜i ≤ j⌝ -∗
        nth i (map (λ ty : lang_ty, interp_type ty env) fargs) interp_nothing w -∗
        (fix go (typ : lang_ty) : interp Σ :=
        match typ with
        | IntT => interp_int
        | BoolT => interp_bool
        | NothingT => interp_nothing
        | MixedT => interp_mixed interp_type
        | ClassT t targs => interp_class t (map go targs) interp_type
        | NullT => interp_null
        | NonNullT => interp_nonnull interp_type
        | UnionT A B => interp_union (go A) (go B)
        | InterT A B => interp_inter (go A) (go B)
        | GenT n => nth n env interp_nothing
        | ExT cname => interp_ex cname interp_type
        end) (nth i fargs (GenT j)) w
        )%I as "Hgen".
      { iIntros (x y) "%hxy"; simpl; rewrite /interp_generic; iIntros "H". 
        iInduction fargs as [ | hd tl hi] "IH" forall (x y hxy) => //=; first by destruct x.
        destruct x as [ | x]; first by rewrite interp_type_unfold.
        iApply "IH"; last done.
        iPureIntro; by lia.
      }
      iApply "Hgen".
      by iPureIntro.
  Qed.
   *)

  (* #hyp *)
  Global Instance interp_type_persistent :
    ∀ t env v, Persistent (interp_type t env v).
  Proof.
    move => t env v.
    rewrite interp_type_unfold.
    by apply _.
  Qed.

  Lemma dom_interp_fields env fields:
    dom stringset (interp_fields env fields interp_type) ≡ dom _ fields.
  Proof. by rewrite /interp_fields dom_fmap. Qed.

  Lemma inherits_is_inclusion:
    ∀ A B, inherits A B →
    ∀ env v, interp_class A env interp_type v -∗ interp_class B env interp_type v.
  Proof.
    move => A B hAB env v.
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
    ∀ (env: interp_env) v,
    interp_type_pre interp_type A env v -∗
    interp_type_pre interp_type B env v.
  Proof.
    induction 1 as [A | A B hext | | | | A | A B| A B | A B C h0 hi0 h1 hi1
        | A B | A B | A B C h0 hi0 h1 hi1 | A | A B C h0 hi0 h1 hi1 | cname targs ];
    move => env v /=.
    - rewrite /interp_mixed.
      elim: A v => //=.
      + move => v; iIntros "h"; by repeat iLeft.
      + move => v; iIntros "h"; by iLeft; iRight; iLeft.
      + move => v; by rewrite /interp_nothing; iIntros "h".
      + move => cname targs v.
        iIntros "h".
        iLeft; iRight; iRight.
        iExists cname, _; by iApply inherits_is_inclusion. 
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
      + move => tvar v.
        rewrite /interp_generic.
        iIntros "hv".
        destruct env as [env henv] => /=.
        rewrite Forall_forall in henv.
        destruct (decide (tvar < length env)) as [hlt | hge].
        * iApply henv; last done.
          apply lookup_lt_is_Some_2 in hlt as [ t ht ].
          rewrite ht /=.
          by apply elem_of_list_lookup_2 in ht.
        * rewrite lookup_ge_None_2 /=; last by apply not_lt.
          done.
      + move => cname v;
        rewrite /interp_ex.
        iIntros "hv".
        iDestruct "hv" as (targs) "hv".
        iLeft; iRight; iRight.
        by iExists _, _.
    - by iApply inherits_is_inclusion.
    - by rewrite /= /interp_mixed.
    - iIntros "h"; by iLeft.
    - iIntros "h"; by iRight; iLeft.
    - iIntros "H".
      iRight; iRight.
      iExists A, _.
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
      iApply hi1 => //.
      by iApply hi0.
    - by iIntros "h"; iExists _. 
  Qed.

  Theorem subtype_is_inclusion:
    ∀ A B, A <: B →
    ∀ (env: interp_env),
    ∀ v, interp_type A env v -∗ interp_type B env v.
  Proof.
    move => A B hAB env v.
    rewrite !interp_type_unfold.
    by iApply subtype_is_inclusion_aux.
  Qed.

  Definition interp_local_tys
    env (lty : local_tys) (le : local_env) : iProp Σ :=
    (∀ v ty, ⌜lty !! v = Some ty⌝ -∗
    ∃ val, ⌜le !! v = Some val⌝ ∗ interp_type ty env val)%I.

  Lemma interp_local_tys_is_inclusion (env: interp_env)  lty rty le:
    Forall (λ (i: interp Σ), ∀ v, Persistent (i v)) env →
    lty <:< rty →
    interp_local_tys env lty le -∗
    interp_local_tys env rty le.
  Proof.
    move => hpers hsub; iIntros "Hle" (v ty) "%Hv".
    apply hsub in Hv as (B & hB & hsubB).
    iDestruct ("Hle" $! v B hB) as (val) "[%Hv' #H]".
    iExists val; iSplitR; first done.
    by iApply subtype_is_inclusion.
  Qed.
End proofs.
