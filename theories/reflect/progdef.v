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
From shack.reflect Require Import lang.

Fixpoint check_wf_ty (G : ProgDefContext) (ty : lang_ty) :=
  match ty with
  | BoolT
  | DynamicT
  | GenT _
  | IntT
  | MixedT
  | NonNullT
  | NothingT
  | NullT
  | SupportDynT
  | ThisT => true
  | ClassT _ t s =>
      if pdefs !! t is Some cdef then
      (length s =? length (generics cdef))%nat
      && forallb (check_wf_ty G) s
      else false
  | UnionT ty1 ty2 | InterT ty1 ty2 =>
      check_wf_ty G ty1 && check_wf_ty G ty2
  end.

Lemma wf_ty_correct (G : ProgDefContext) (ty : lang_ty) :
  check_wf_ty G ty -> wf_ty ty.
Proof.
  elim/lang_ty_ind: ty => //=.
  - move=> ? tag s ih; case E: (_ !! _) => [cdef|] //.
    case/andb_prop_elim=> hlen hwf; econstructor => //.
    (* sigh... *)
    + by rewrite -Nat.eqb_eq -Is_true_true.
    + by move: hwf; rewrite forallb_True => /Forall_impl_in; apply.
  - by move=> ty1 ty2 ih1 ih2 /andb_prop_elim[] {}/ih1 ih1 {}/ih2 ih2; constructor.
  - by move=> ty1 ty2 ih1 ih2 /andb_prop_elim[] {}/ih1 ih1 {}/ih2 ih2; constructor.
Qed.

Definition check_wf_cdef_parent (G : ProgDefContext) (c : classDef) :=
  if superclass c is Some (parent, σ) then
       check_wf_ty G (ClassT true parent σ)
    && forallb (check_generic_bounded (length (generics c))) σ
    && forallb no_this σ
  else true.

Lemma wf_cdef_parent_correct (G : ProgDefContext) (c : classDef) :
  check_wf_cdef_parent G c -> wf_cdef_parent c.
Proof.
  rewrite /check_wf_cdef_parent /wf_cdef_parent.
  case: superclass => [[tag σ]|] //.
  case/andb_prop_elim => /andb_prop_elim[] wfty wfs no_this; do! split.
  - by apply: wf_ty_correct.
  - by move/forallb_True/Forall_impl: wfs; apply; apply/generic_bounded_correct.  
  - by move/forallb_True/Forall_impl: no_this; apply.
Qed.

Definition check_wf_cdef_parent_context (G : ProgDefContext) :=
  forallb (fun kv => check_wf_cdef_parent G kv.2) (map_to_list pdefs).

Lemma wf_cdef_parent_context_correct (G : ProgDefContext) :
  check_wf_cdef_parent_context G -> map_Forall (λ _, wf_cdef_parent) pdefs.
Proof.
  rewrite /check_wf_cdef_parent_context map_Forall_to_list forallb_True.
  by move/Forall_impl; apply => -[??] /=; apply/wf_cdef_parent_correct.
Qed.

Fixpoint check_acc_def (G: ProgDefContext) n c : bool :=
  if n is S p then
    if pdefs !! c is Some cdef then
      if cdef.(superclass) is Some (parent, _) then
        if pdefs !! parent is Some pdef then
          check_acc_def G p parent
        else false
      else true
    else false
  else false
.

Lemma check_acc_def_correct (G: ProgDefContext) n:
  ∀ c, check_acc_def G n c → Acc (λ x y, extends y x) c.
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

Definition check_acc_defs (G: ProgDefContext) n : bool :=
  forallb (λ kv, check_acc_def G n kv.1) (map_to_list pdefs).

Lemma check_acc_defs_correct (G: ProgDefContext) n:
  check_acc_defs G n →
  ∀ c, Acc (λ x y, extends y x) c.
Proof.
  assert (hForall:
    check_acc_defs G n → map_Forall (λ c _, Acc (λ x y, extends y x) c) pdefs).
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
