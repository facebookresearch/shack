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

Section SolveAcc.
  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.

  Fixpoint check_acc_def n c : bool :=
    if n is S p then
      if pdefs !! c is Some cdef then
        if cdef.(superclass) is Some (parent, _) then
          if pdefs !! parent is Some pdef then
            check_acc_def p parent
          else false
        else true
      else false
    else false
.

  Lemma check_acc_def_correct n:
    ∀ c, check_acc_def n c → Acc (λ x y, extends y x) c.
  Proof.
    elim: n => [ // | p ] /= hi c.
    destruct (pdefs !! c) as [cdef | ] eqn:hcdef; last done.
    destruct (cdef.(superclass)) as [ [parent ?] | ] eqn:hsuper; last first.
    { move => _; constructor => ? h.
      destruct h as [A B adef σ hadef' hsuper'].
      by simplify_eq.
    }
    destruct (pdefs !! parent); last done.
    move/hi => hacc.
    constructor => ? h.
    destruct h as [A B adef σ hadef' hsuper'].
    by simplify_eq.
  Qed.

  Definition check_acc_defs n : bool :=
    forallb (λ kv, check_acc_def n kv.1) (map_to_list pdefs).

  Lemma check_acc_defs_correct n:
    check_acc_defs n →
    ∀ c, Acc (λ x y, extends y x) c.
  Proof.
    assert (hForall:
      check_acc_defs n → map_Forall (λ c _, Acc (λ x y, extends y x) c) pdefs).
    { rewrite map_Forall_to_list /check_acc_defs forallb_True Forall_lookup.
      rewrite Forall_lookup => h k [c cdef] hcdef /=.
      apply check_acc_def_correct with n.
      by apply h in hcdef.
    }
    move => h.
    move: {hForall h} (hForall h).
    rewrite map_Forall_lookup => h c.
    destruct (pdefs !! c) as [cdef | ] eqn:hcdef; last first.
    { constructor => ? hext.
      destruct hext as [].
      by simplify_eq.
    }
    by apply h in hcdef.
  Qed.
End SolveAcc.
