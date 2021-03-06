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
Definition sem_typeO (Θ : gFunctors) : ofe := value -d> iPropO Θ.

Definition sem_typeOF (F: oFunctor) : oFunctor := value -d> F.

(* The semantic heap is a map from locations to:
 * - a runtime tag
 * - the (gated by Next) interpretation of fields for this tag
 *)
Class sem_heapGpreS (Θ : gFunctors) : Set := {
  sem_heap :> inG Θ (gmap_viewR loc (prodO tagO (laterO (gmapO string (sem_typeO Θ)))));
}.

Definition sem_heapΘ : gFunctors :=
  #[GFunctor (gmap_viewRF loc (tagO * (laterOF (gmapOF string (sem_typeOF ∙)))))].

Global Instance subG_sem_heapΘ {Θ}: subG sem_heapΘ Θ → sem_heapGpreS Θ.
Proof.  solve_inG. Qed.

Class sem_heapGS (Θ: gFunctors) := SemHeapGS {
  sem_heap_inG :> sem_heapGpreS Θ;
  sem_heap_name: gname;
}.

Section definitions.
  Context `{hG: !sem_heapGS Θ}.

  Definition loc_mapsto_def (ℓ: loc) (t: tag)
    (iFs: gmapO string (sem_typeO Θ)) :=
    (gmap_view_frag ℓ DfracDiscarded (t, Next iFs)).

  Definition mapsto_def (ℓ: loc) (t: tag)
    (iFs: gmapO string (sem_typeO Θ)) :=
    own (@sem_heap_name _ hG) (loc_mapsto_def ℓ t iFs).

  Definition loc_mapsto_aux : seal (@loc_mapsto_def). Proof. by eexists. Qed.
  Definition loc_mapsto := loc_mapsto_aux.(unseal).
  Definition loc_mapsto_eq : @loc_mapsto = @loc_mapsto_def := loc_mapsto_aux.(seal_eq).

  Definition mapsto_aux : seal (@mapsto_def). Proof. by eexists. Qed.
  Definition mapsto := mapsto_aux.(unseal).
  Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).
End definitions.

Notation "l ↪ '(' t ',' iFs ')'" := (loc_mapsto l t iFs)
  (at level 20, format "l  ↪ '(' t ',' iFs ')'") : bi_scope.

Notation "l ↦ '(' t ',' iFs ')'" := (mapsto l t iFs)
  (at level 20, format "l ↦ '(' t ',' iFs ')'") : bi_scope.

Section sem_heap.
  Context `{hG: !sem_heapGS Θ}.
  Notation γ := sem_heap_name.

  Global Instance mapsto_persistent l t iFs: Persistent (mapsto l t iFs).
  Proof.
    rewrite mapsto_eq /mapsto_def /loc_mapsto_def.
    by apply _.
  Qed.

  Lemma mapsto_proper l t iFs0 iFs1 :
    iFs0 ≡ iFs1 →
    mapsto l t iFs0 ≡ mapsto l t iFs1.
  Proof.
    move => heq.
    rewrite mapsto_eq /mapsto_def /loc_mapsto_def.
    rewrite gmap_view_frag_proper; first done.
    by f_equiv.
  Qed.

  Lemma sem_heap_own_valid_2 sh l t iFs:
    own γ (gmap_view_auth (DfracOwn 1) sh) -∗
    l ↦ (t, iFs) -∗
    sh !! l ≡ Some (t, Next iFs).
  Proof.
    rewrite mapsto_eq /mapsto_def /loc_mapsto_def.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as "#Hv".
    rewrite gmap_view_both_validI.
    by iDestruct "Hv" as "[_ HΦ]".
  Qed.

  Lemma sem_heap_view_alloc sh new t iFs:
    sh !! new = None →
    gmap_view_auth (DfracOwn 1) sh ~~>
    gmap_view_auth (DfracOwn 1) (<[new:=(t, Next iFs)]> sh) ⋅ (@loc_mapsto Θ new t iFs).
  Proof.
    move => hnew.
    rewrite loc_mapsto_eq /loc_mapsto_def.
    by apply gmap_view_alloc.
  Qed.

  Lemma sem_heap_own_update new sh t iFs:
    sh !! new = None →
    (gmap_view_auth (DfracOwn 1) sh ~~>
      gmap_view_auth (DfracOwn 1) (<[new:=(t, Next iFs)]> sh) ⋅ (new ↪ (t, iFs))%I) →
    own γ (gmap_view_auth (DfracOwn 1) sh) -∗
    |==> (own γ (gmap_view_auth (DfracOwn 1) (<[new:=(t, Next iFs)]> sh))) ∗
         (new ↦ (t, iFs))%I.
  Proof.
    rewrite loc_mapsto_eq /loc_mapsto_def  => hnew h.
    iIntros "H●".
    iMod (own_update with "H●") as "[? ?]";
      first by apply (gmap_view_alloc _ new DfracDiscarded (t, Next iFs)).
    iModIntro.
    iSplit; first done.
    by rewrite mapsto_eq /mapsto_def /loc_mapsto_def.
  Qed.
End sem_heap.
