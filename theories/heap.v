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
