(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
From stdpp Require Import base strings gmap stringmap fin_maps.

From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import iprop own wsat.
From iris.algebra.lib Require Import gmap_view.

From shack Require Import lang progdef subtype ok typing.
From shack Require Import eval heap modality interp soundness.

From shack.reflect Require Import lang progdef subtype.

(* Generated from test.lang *)

Definition arraykey := UnionT IntT BoolT.

Definition ROBox_get := {|
  methodargs := ∅;
  methodrettype := GenT 0;
  methodbody := GetC "$ret" (ThisE) "data";
  methodret := VarE "$ret";
  methodvisibility := Public;
|}.

Definition ROBox := {|
  superclass := None;
  generics := [Covariant];
  constraints := [];
  classfields := {["data" := (Private, GenT 0)]};
  classmethods := {["get" := ROBox_get]};
|}.

Definition Box_get := {|
  methodargs := ∅;
  methodrettype := GenT 0;
  methodbody := GetC "$ret" (ThisE) "data";
  methodret := VarE "$ret";
  methodvisibility := Public;
|}.

Definition Box_set := {|
  methodargs := {["$x" := GenT 0]};
  methodrettype := NullT;
  methodbody := SetC (ThisE) "data" (VarE "$x");
  methodret := NullE;
  methodvisibility := Public;
|}.

Definition Box := {|
  superclass := None;
  generics := [Invariant];
  constraints := [(GenT 0, arraykey)];
  classfields := {["data" := (Public, GenT 0)]};
  classmethods := {["get" := Box_get
                  ; "set" := Box_set]};
|}.

Definition IntBoxS_set := {|
  methodargs := {["$data" := IntT]};
  methodrettype := NullT;
  methodbody := SetC (ThisE) "data" (BinOpE PlusO (VarE "$data") (IntE 1));
  methodret := NullE;
  methodvisibility := Public;
|}.

Definition IntBoxS := {|
  superclass := Some("Box", [IntT]);
  generics := [];
  constraints := [];
  classfields := ∅;
  classmethods := {["set" := IntBoxS_set]};
|}.

Definition Main_main := {|
  methodargs := ∅;
  methodrettype := BoolT;
  methodbody :=
  SeqC
    (NewC "$robox" "ROBox" None {["$data" := IntE 42]})
    (SeqC
       (CallC "$init" (VarE "$robox") "get" ∅)
       (SeqC
          (NewC "$box" "IntBoxS" None {["$data" := VarE "$init"]})
          (SeqC
             (CallC "$tmp" (VarE "$box") "get" ∅)
             (SeqC
                (LetC "$tmp" (BinOpE PlusO (VarE "$tmp") (IntE 20)))
                (SeqC
                   (CallC "$tmp0" (VarE "$box") "set"
                    {["$x" := BinOpE MinusO (VarE "$tmp") (IntE 10)]})
                   (GetC "$tmp" (VarE "$box") "data"))))));
  methodret := BinOpE EqO (VarE "$tmp") (IntE 43);
  methodvisibility := Public;
|}.

Definition Main := {|
  superclass := None;
  generics := [];
  constraints := [];
  classfields := ∅;
  classmethods := {["main" := Main_main]};
|}.

Definition pdefs0 : stringmap classDef :=

  {[ "ROBox" := ROBox; "Box" := Box; "IntBoxS" := IntBoxS; "Main" := Main ]}.

Local Instance PDC : ProgDefContext := { pdefs := pdefs0 }.

Lemma pacc : ∀ c, Acc (λ x y, extends y x) c.
Proof.
  apply check_acc_defs_correct with (n := 100).
  by exact (I <: True).
Qed.

Local Instance PDA : ProgDefAcc  := { pacc := pacc }.

Lemma wf_fields_bounded : map_Forall (λ _cname, wf_cdef_fields_bounded) pdefs.
Proof.
  apply wf_cdef_fields_bounded_context_correct.
  by exact (I <: True).
Qed.

Lemma wf_methods_bounded : map_Forall (λ _cname, cdef_methods_bounded) pdefs.
Proof.
  apply cdef_methods_bounded_context_correct.
  by exact (I <: True).
Qed.

Lemma wf_constraints_bounded : map_Forall (λ _cname, wf_cdef_constraints_bounded) pdefs.
Proof.
  apply wf_cdef_constraints_bounded_context_correct.
  by exact (I <: True).
Qed.

Lemma wf_fields_wf  : map_Forall (λ _cname, wf_cdef_fields_wf) pdefs.
Proof.
  apply: wf_cdef_fields_wf_context_correct.
  exact (I <: True).
Qed.

Lemma wf_constraints_wf : map_Forall (λ _cname, wf_cdef_constraints_wf) pdefs.
Proof.
  apply: wf_cdef_constraints_wf_context_correct.
  exact (I <: True).
Qed.

Lemma wf_methods_wf : map_Forall (λ _cname, wf_cdef_methods_wf) pdefs.
Proof.
  apply: wf_cdef_methods_wf_context_correct.
  exact (I <: True).
Qed.

Lemma wf_fields_mono : map_Forall (λ _cname, wf_field_mono) pdefs.
Proof.
  apply wf_fields_mono_correct.
  exact (I <: True).
Qed.

Lemma wf_methods_mono : map_Forall (λ _cname, wf_cdef_methods_mono) pdefs.
Proof.
  apply wf_methods_mono_correct.
  exact (I <: True).
Qed.

Lemma wf_mono : map_Forall (λ _cname, wf_cdef_mono) pdefs.
Proof.
  apply wf_mono_correct.
  exact (I <: True).
Qed.

Lemma wf_constraints_no_this: map_Forall (λ _ : string, wf_cdef_constraints_no_this) pdefs.
Proof.
 apply wf_constraints_no_this_correct.
  by exact (I <: True).
Qed.

Lemma wf_fields : map_Forall (λ _cname, wf_cdef_fields) pdefs.
Proof.
  apply (wf_fields_correct _ 100).
  by exact (I <: True).
Qed.
