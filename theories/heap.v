(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 * 
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
From stdpp Require Import strings.
From iris.base_logic.lib Require Import iprop own ghost_map.
From iris.algebra Require Import ofe cmra gmap_view.
From iris.proofmode Require Import tactics.

From shack Require Import lang.

Canonical Structure tagO : ofe := leibnizO tag.
Canonical Structure lang_tyO : ofe := leibnizO lang_ty.
Canonical Structure valueO : ofe := leibnizO value.


(* interpretation of types *)
Definition sem_typeO (Σ : gFunctors) : ofe := value -d> iPropO Σ.

Definition sem_typeOF (F: oFunctor) : oFunctor := value -d> F.

Class sem_heapGpreS (Σ : gFunctors) : Set := {
  sem_heap :> inG Σ (gmap_viewR loc (prodO tagO (gmapO string (laterO (sem_typeO Σ)))));
}.

Definition sem_heapΣ : gFunctors :=
  #[GFunctor (gmap_viewRF loc (tagO * (gmapOF string (laterOF (sem_typeOF ∙)))))].

Global Instance subG_sem_heapΣ {Σ}: subG sem_heapΣ Σ → sem_heapGpreS Σ.
Proof.  solve_inG. Qed.

Class sem_heapGS (Σ: gFunctors) := SemHeapGS {
  sem_heap_inG :> sem_heapGpreS Σ;
  sem_heap_name: gname;
}.

Section definitions.
  Context `{hG: !sem_heapGS Σ}.

  Definition loc_mapsto_def (ℓ: loc) (t: tag)
    (iFs: gmapO string (laterO (sem_typeO Σ))) :=
    (gmap_view_frag ℓ DfracDiscarded (t, iFs)).

  Definition mapsto_def (ℓ: loc) (t: tag)
    (iFs: gmapO string (laterO (sem_typeO Σ))) :=
    own (@sem_heap_name _ hG) (loc_mapsto_def ℓ t iFs).

  Definition loc_mapsto_aux : seal (@loc_mapsto_def). Proof. by eexists. Qed.
  Definition loc_mapsto := loc_mapsto_aux.(unseal).
  Definition loc_mapsto_eq : @loc_mapsto = @loc_mapsto_def := loc_mapsto_aux.(seal_eq).

  Definition mapsto_aux : seal (@mapsto_def). Proof. by eexists. Qed.
  Definition mapsto := mapsto_aux.(unseal).
  Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).
End definitions.

Notation "l  ↪ '(' t ',' iFs ')'" := (loc_mapsto l t iFs)
  (at level 20, format "l  ↪ '(' t ',' iFs ')'") : bi_scope.

Notation "l ↦ '(' t ',' iFs ')'" := (mapsto l t iFs)
  (at level 20, format "l ↦ '(' t ',' iFs ')'") : bi_scope.

Section sem_heap.
  Context `{hG: !sem_heapGS Σ}.
  Notation γ := sem_heap_name.

	Lemma mapsto_contractive
    (l: loc)
    (t: tag)
    (f: (lang_ty -d> sem_typeO Σ) → gmapO string (laterO (sem_typeO Σ )))
    `{hf: Contractive f}:
  Contractive (λ i, mapsto l t (f i)).
  Proof.
    move => n i1 i2 hdist.
    rewrite mapsto_eq /mapsto_def /loc_mapsto_def.
    do 3 f_equiv.
    by apply hf.
  Qed.

  Global Instance mapsto_persistent l t iFs: Persistent (mapsto l t iFs).
  Proof.
    rewrite mapsto_eq /mapsto_def /loc_mapsto_def.
    by apply _.
  Qed.

  Lemma sem_heap_own_valid_2 sh l t iFs:
    own γ (gmap_view_auth (DfracOwn 1) sh) -∗
    l ↦ (t, iFs) -∗
    sh !! l ≡ Some (t, iFs).
  Proof.
    rewrite mapsto_eq /mapsto_def /loc_mapsto_def.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as "#Hv".
    rewrite gmap_view_both_validI.
    by iDestruct "Hv" as "[_ HΦ]".
  Qed.

  Lemma sem_heap_own_update new sh t iFs:
    sh !! new = None →
    (gmap_view_auth (DfracOwn 1) sh ~~>
      gmap_view_auth (DfracOwn 1) (<[new:=(t, iFs)]> sh) ⋅ (new ↪ (t, iFs))%I) →
    own γ (gmap_view_auth (DfracOwn 1) sh) -∗
    |==> own γ ((gmap_view_auth (DfracOwn 1) (<[new:=(t, iFs)]> sh)) ⋅
           (new  ↪ (t, iFs))%I).
  Proof.
    rewrite loc_mapsto_eq /loc_mapsto_def  => hnew h.
    iIntros "H●".
    iMod (own_update with "H●") as "H";
      first by apply (gmap_view_alloc _ new DfracDiscarded (t, iFs)).
    by iModIntro.
  Qed.
End sem_heap.
