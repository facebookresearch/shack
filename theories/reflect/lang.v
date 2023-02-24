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

Lemma Forall_impl_in {T : Type} (P Q : T → Prop) (l : list T) :
  Forall P l → Forall (fun x => P x → Q x) l → Forall Q l.
Proof.
  elim: l => //= x l ih; rewrite !Forall_cons.
  move=> [] Px Pl [] PQx /[dup] PQl /ih - /(_ Pl) Ql.
  by split=> //; apply/PQx.
Qed.

Fixpoint check_generic_bounded (n : nat) (ty : lang_ty) :=
  match ty with
  | GenT k => (k <? n)%nat
  | ClassT _ _ σ => forallb (check_generic_bounded n) σ
  | UnionT s t
  | InterT s t => check_generic_bounded n s && check_generic_bounded n t
  | _ => true
  end.

Lemma generic_bounded_correct (n : nat) (ty : lang_ty) :
  check_generic_bounded n ty → bounded n ty.
Proof.
  elim: ty => //=.
  - move => ?? σ hi /forallb_True hb; constructor.
    by apply: Forall_impl_in.
  - move => s t hs ht /andb_prop_elim [h0 h1]; constructor; by firstorder.
  - move => s t hs ht /andb_prop_elim [h0 h1]; constructor; by firstorder.
  - move=> k lt_kn; constructor.
    by rewrite -Nat.ltb_lt -Is_true_true.
Qed.

Fixpoint check_generic_bounded_expr n e :=
  match e with
  | BinOpE _ e1 e2 => check_generic_bounded_expr n e1 &&
      check_generic_bounded_expr n e2
  | UniOpE _ e => check_generic_bounded_expr n e
  | UpcastE e ty => check_generic_bounded_expr n e &&
      check_generic_bounded n ty
  | _ => true
  end.

Lemma generic_bounded_expr_correct n e:
  check_generic_bounded_expr n e →
  expr_bounded n e.
Proof.
  elim : e => //=; try (intros; by constructor).
  - move => ? e1 hi1 e2 hi2 /andb_prop_elim [h1 h2]; constructor; by firstorder.
  - move => ? e hi h; constructor; by firstorder.
  - move => e hi ty /andb_prop_elim [he hty]; constructor; first by firstorder.
    by apply generic_bounded_correct.
Qed.

Fixpoint check_generic_bounded_cmd n cmd :=
  match cmd with
  | RuntimeCheckC _ _ c0 c1
  | SeqC c0 c1 => check_generic_bounded_cmd n c0 &&
      check_generic_bounded_cmd n c1
  | GetC _ e _
  | LetC _ e => check_generic_bounded_expr n e
  | IfC cond c0 c1 => check_generic_bounded_expr n cond &&
      check_generic_bounded_cmd n c0 &&
      check_generic_bounded_cmd n c1
  | CallC _ recv _ args =>
      check_generic_bounded_expr n recv &&
      forallb (λ kv, check_generic_bounded_expr n kv.2) (map_to_list args)
  | NewC _ _ targs args =>
      (if targs is Some σ then forallb (check_generic_bounded n) σ else true) &&
      forallb (λ kv, check_generic_bounded_expr n kv.2) (map_to_list args)
  | SetC recv _ rhs =>
      check_generic_bounded_expr n recv &&
      check_generic_bounded_expr n rhs
  | SkipC
  | ErrorC => true
  end.

Lemma generic_bounded_cmd_correct n cmd:
  check_generic_bounded_cmd n cmd →
  cmd_bounded n cmd.
Proof.
  elim : cmd => /=.
  - move => _; by constructor.
  - move => c0 hi0 c1 hi1 /andb_prop_elim [h0 h1]; constructor; by firstorder.
  - move => ? e he; constructor; by apply generic_bounded_expr_correct.
  - move => cond c0 hi0 c1 hi1 /andb_prop_elim [/andb_prop_elim [h0 h1]] h2.
    constructor; try by firstorder.
    by apply generic_bounded_expr_correct.
  - move => ? e ? args /andb_prop_elim [he /forallb_True hargs]; constructor; first by apply generic_bounded_expr_correct.
    rewrite map_Forall_to_list; apply: Forall_impl_in => //.
    rewrite Forall_lookup => [? [? a]] /= h; by apply generic_bounded_expr_correct.
  - move => ?? targs args /andb_prop_elim [h0 /forallb_True h1]; constructor.
    + case: targs h0 => [σ | //] /forallb_True h; apply: Forall_impl_in => //.
      rewrite Forall_lookup => k ty hk; by apply generic_bounded_correct.
    + rewrite map_Forall_to_list; apply: Forall_impl_in => //.
      rewrite Forall_lookup => [? [? a]] /= h; by apply generic_bounded_expr_correct.
  - move => ? e ? he; constructor; by apply generic_bounded_expr_correct.
  - move => recv ? rhs /andb_prop_elim [h0 h1]; constructor; by apply generic_bounded_expr_correct.
  - move => ?? c0 hi0 c1 hi1 /andb_prop_elim [h0 h1]; constructor; by firstorder.
  - move => _; by constructor.
Qed.

Definition check_wf_cdef_fields_bounded cdef :=
  let n := length cdef.(generics) in
  forallb (fun kv => check_generic_bounded n kv.2.2) (map_to_list cdef.(classfields)).

Lemma wf_cdef_fields_bounded_correct cdef:
  check_wf_cdef_fields_bounded cdef → wf_cdef_fields_bounded cdef.
Proof.
  rewrite /check_wf_cdef_fields_bounded /wf_cdef_fields_bounded /=.
  move/forallb_True => hF; rewrite map_Forall_to_list; apply: Forall_impl_in => //.
  rewrite Forall_lookup => ? [? [? ty]] /= ?; by apply generic_bounded_correct.
Qed.

Definition check_wf_cdef_fields_bounded_context (G: ProgDefContext) :=
  forallb (fun kv => check_wf_cdef_fields_bounded kv.2) (map_to_list pdefs).

Lemma wf_cdef_fields_bounded_context_correct (G: ProgDefContext):
  check_wf_cdef_fields_bounded_context G →
  map_Forall (λ _cname, wf_cdef_fields_bounded) pdefs.
Proof.
  rewrite /check_wf_cdef_fields_bounded_context forallb_True => hF.
  rewrite map_Forall_to_list; apply: Forall_impl_in => //.
  rewrite Forall_lookup => ? [? c] ? /=; by apply wf_cdef_fields_bounded_correct.
Qed.

Definition check_generic_bounded_mdef n mdef : bool :=
  forallb (λ kv, check_generic_bounded n kv.2) (map_to_list mdef.(methodargs)) &&
  check_generic_bounded n mdef.(methodrettype) &&
  check_generic_bounded_cmd n mdef.(methodbody) &&
  check_generic_bounded_expr n mdef.(methodret).

Lemma generic_bounded_mdef_correct n mdef:
  check_generic_bounded_mdef n mdef →
  mdef_bounded n mdef.
Proof.
  rewrite /check_generic_bounded_mdef /mdef_bounded.
  case/andb_prop_elim.
  case/andb_prop_elim.
  case/andb_prop_elim => /forallb_True h0 h1 h2 h3.
  split.
  { rewrite map_Forall_to_list; apply: Forall_impl_in => //=.
    rewrite Forall_lookup => ? [? ty] /= ?; by apply generic_bounded_correct.
  }
  split; first by apply generic_bounded_correct.
  split; first by apply generic_bounded_cmd_correct.
  by apply generic_bounded_expr_correct.
Qed.

Definition check_cdef_methods_bounded cdef :=
  let n := length cdef.(generics) in
  forallb (fun kv => check_generic_bounded_mdef n kv.2) (map_to_list cdef.(classmethods)).

Lemma cdef_methods_bounded_correct cdef:
  check_cdef_methods_bounded cdef → cdef_methods_bounded cdef.
Proof.
  rewrite /check_cdef_methods_bounded /cdef_methods_bounded /=.
  move/forallb_True => hF; rewrite map_Forall_to_list; apply: Forall_impl_in => //.
  rewrite Forall_lookup => ? [? mdef] /= ?; by apply generic_bounded_mdef_correct.
Qed.

Definition check_cdef_methods_bounded_context (G: ProgDefContext) :=
  forallb (fun kv => check_cdef_methods_bounded kv.2) (map_to_list pdefs).

Lemma cdef_methods_bounded_context_correct (G: ProgDefContext):
  check_cdef_methods_bounded_context G →
  map_Forall (λ _cname, cdef_methods_bounded) pdefs.
Proof.
  rewrite /check_cdef_methods_bounded_context forallb_True => hF.
  rewrite map_Forall_to_list; apply: Forall_impl_in => //.
  rewrite Forall_lookup => ? [? c] ? /=; by apply cdef_methods_bounded_correct.
Qed.

Definition check_wf_cdef_constraints_bounded cdef : bool :=
  let n := length cdef.(generics) in
  forallb (λ c, check_generic_bounded n c.1 && check_generic_bounded n c.2) cdef.(constraints).

Lemma wf_cdef_constraints_bounded_correct cdef:
  check_wf_cdef_constraints_bounded cdef →
  wf_cdef_constraints_bounded cdef.
Proof.
  rewrite /check_wf_cdef_constraints_bounded /wf_cdef_constraints_bounded forallb_True => hF.
  apply: Forall_impl_in => //.
  rewrite Forall_lookup => [? c1] ? /andb_prop_elim [h0 h1].
  split; by apply generic_bounded_correct.
Qed.

Definition check_wf_cdef_constraints_bounded_context (G: ProgDefContext) : bool :=
  forallb (fun kv => check_wf_cdef_constraints_bounded kv.2) (map_to_list pdefs).

Lemma wf_cdef_constraints_bounded_context_correct (G: ProgDefContext) :
  check_wf_cdef_constraints_bounded_context G →
  map_Forall (λ _cname, wf_cdef_constraints_bounded) pdefs.
Proof.
  rewrite /check_wf_cdef_constraints_bounded_context forallb_True => hF.
  rewrite map_Forall_to_list; apply: Forall_impl_in => //.
  rewrite Forall_lookup => ? [? c] ? /=; by apply wf_cdef_constraints_bounded_correct.
Qed.
