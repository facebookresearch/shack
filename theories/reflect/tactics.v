(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
From stdpp Require Import base strings gmap stringmap fin_maps.
(* Not using iris but importing their ssreflect dependencies *)
From iris.proofmode Require Import tactics.

From shack Require Import reflect.progdef.

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
