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
  classfields := {["data" := (Public, GenT 0)]};
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
