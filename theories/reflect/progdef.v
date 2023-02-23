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

Section Extends.
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
End Extends.

Lemma pacc_helper (P: tag → Prop) (xdefs: stringmap classDef):
  Forall P (map fst (map_to_list xdefs)) →
  Forall (uncurry (λ c _, P c)) (map_to_list xdefs).
Proof.
  rewrite Forall_lookup => h.
  rewrite Forall_lookup => k [c ?] hk /=.
  apply h with k.
  by rewrite list_lookup_fmap hk.
Qed.

(* Helper tactics to deal with the `Acc` goal in progdef.v *)
Lemma string_eqb_correct (s t: string) : (s =? t)%string ↔ s = t.
Proof.
  destruct String.eqb eqn:h.
  - by apply String.eqb_eq in h as ->.
  - apply String.eqb_neq in h.
    by split.
Qed.

(* Do one step of Accessibility *)
Ltac simpl_acc0 :=
  constructor => ? /extendsb_correct;
  rewrite /extendsb /=;
  simpl_map => /=.

(* If the previous tactic didn't solve the goal,
 * rewrite.
 *)
Ltac simpl_acc1 := move/string_eqb_correct => ->.

(* Gluing both tactics into an automated one *)
Ltac simpl_acc_match :=
  match goal with
  | |- False → _ => done
  | |- _ => (simpl_acc1; simpl_acc0)
  end.

Ltac simpl_acc := simpl_acc0; repeat simpl_acc_match.

Ltac step_pacc :=
  match goal with
  | |- None = Some ?t → _ => done
  | H : nat |- _ => destruct H; first (case => <-; simpl_acc)
  end.

Definition pacc_uncurry_def `{PDC: ProgDefContext} :=
  Forall (uncurry (λ c _, Acc (λ x y : tag, extends y x) c))
         (map_to_list pdefs).

Lemma pacc `{PDC: ProgDefContext}:
  pacc_uncurry_def → ∀ c, Acc (λ x y : tag, extends y x) c.
Proof.
  move => hacc.
  assert (pacc_ : map_Forall (λ c _, Acc (λ x y, extends y x) c) pdefs).
  { rewrite map_Forall_to_list /=.
    by apply hacc.
  }
  move => c.
  destruct (pdefs !! c) as [cdef | ] eqn:hcdef.
  - move : pacc_ => /map_Forall_lookup h.
    by eapply h.
  - constructor => t hext; exfalso.
    inv hext.
    by simplify_eq.
Qed.
