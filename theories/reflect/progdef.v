(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
From stdpp Require Import base strings gmap stringmap fin_maps.
(* Not using iris but importing their ssreflect dependencies *)
From iris.proofmode Require Import tactics.
From shack Require Import lang progdef.

Section Reflect.
  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.

  Definition extendsb A B : bool :=
    if pdefs !! A is Some adef then
    if adef.(superclass) is Some (t, _) then String.eqb B t else false
    else false
  .

  Lemma extendsb_correct A B : extendsb A B ↔ extends A B.
  Proof.
    rewrite /extendsb; split.
    - destruct (pdefs !! A) as [adef | ] eqn:hadef; last done.
      destruct (adef.(superclass)) as [(t, ?) | ] eqn:hsuper; last done.
      move => heq.
      destruct (B =? t) eqn:h; last done.
      apply String.eqb_eq in h; subst.
      by econstructor.
    - move => h; destruct h as [A B adef σ hadef hsuper].
      rewrite hadef hsuper.
      destruct (B =? B) eqn:h; first done.
      by rewrite eqb_neq in h.
  Qed.

  Lemma pacc_helper (P: tag → Prop) (xdefs: stringmap classDef):
    Forall P (map fst (map_to_list xdefs)) →
    Forall (uncurry (λ c _, P c)) (map_to_list xdefs).
  Proof.
    rewrite Forall_lookup => h.
  rewrite Forall_lookup => k [c ?] hk /=.
  apply h with k.
  by rewrite list_lookup_fmap hk.
  Qed.
End Reflect.
