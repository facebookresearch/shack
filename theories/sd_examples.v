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

From shack Require Import lang progdef subtype typing eval heap modality interp soundness.

(* Will be updated soon with

  <SDT where T = Dynamic>
  class Box<T> {
    private T $x;
    <SDT when T <: dynamic >
   public get(): T { return $this->x; }

    <SDT when T:>dynamic>
   public set(T $y): void { $this->x = $y; }
   }

<SDT when T<:dynamic>
   class ROBox<+T> extends Box<T> {
     <SDT>
     public set(mixed $y): void { throw new Exception; }
   }

 *)
