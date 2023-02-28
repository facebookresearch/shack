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

Definition check_wf_cdef_fields_wf (G: ProgDefContext) cdef :=
  forallb (fun kv => check_wf_ty G kv.2.2) (map_to_list cdef.(classfields)).

Lemma wf_cdef_fields_wf_correct (G: ProgDefContext) cdef:
  check_wf_cdef_fields_wf G cdef → wf_cdef_fields_wf cdef.
Proof.
  rewrite /check_wf_cdef_fields_wf /wf_cdef_fields_wf /=.
  move/forallb_True => hF; rewrite map_Forall_to_list; apply: Forall_impl_in => //.
  rewrite Forall_lookup => ? [? [? ty]] /= ?; by apply wf_ty_correct.
Qed.

Definition check_wf_cdef_fields_wf_context (G: ProgDefContext) :=
  forallb (fun kv => check_wf_cdef_fields_wf G kv.2) (map_to_list pdefs).

Lemma wf_cdef_fields_wf_context_correct (G: ProgDefContext):
  check_wf_cdef_fields_wf_context G →
  map_Forall (λ _cname, wf_cdef_fields_wf) pdefs.
Proof.
  rewrite /check_wf_cdef_fields_wf_context forallb_True => hF.
  rewrite map_Forall_to_list; apply: Forall_impl_in => //.
  rewrite Forall_lookup => ? [? c] ? /=; by apply wf_cdef_fields_wf_correct.
Qed.

Definition check_wf_ty_mdef (G: ProgDefContext) mdef : bool :=
  forallb (λ kv, check_wf_ty G kv.2) (map_to_list mdef.(methodargs)) &&
  check_wf_ty G mdef.(methodrettype).

Lemma wf_ty_mdef_correct (G: ProgDefContext) mdef:
  check_wf_ty_mdef G mdef → mdef_wf mdef.
Proof.
  rewrite /check_wf_ty_mdef /mdef_wf.
  case/andb_prop_elim => /forallb_True h0 h1.
  split.
  { rewrite map_Forall_to_list; apply: Forall_impl_in => //=.
    rewrite Forall_lookup => ? [? ty] /= ?; by apply wf_ty_correct.
  }
  by apply wf_ty_correct.
Qed.

Definition check_wf_cdef_methods_wf (G: ProgDefContext) cdef :=
  forallb (fun kv => check_wf_ty_mdef G kv.2) (map_to_list cdef.(classmethods)).

Lemma wf_cdef_methods_wf_correct (G: ProgDefContext) cdef:
  check_wf_cdef_methods_wf G cdef → wf_cdef_methods_wf cdef.
Proof.
  rewrite /check_wf_cdef_methods_wf /wf_cdef_methods_wf /=.
  move/forallb_True => hF; rewrite map_Forall_to_list; apply: Forall_impl_in => //.
  rewrite Forall_lookup => ? [? mdef] /= ?; by apply wf_ty_mdef_correct.
Qed.

Definition check_wf_cdef_methods_wf_context (G: ProgDefContext) :=
  forallb (fun kv => check_wf_cdef_methods_wf G kv.2) (map_to_list pdefs).

Lemma wf_cdef_methods_wf_context_correct (G: ProgDefContext):
  check_wf_cdef_methods_wf_context G →
  map_Forall (λ _cname, wf_cdef_methods_wf) pdefs.
Proof.
  rewrite /check_wf_cdef_methods_wf_context forallb_True => hF.
  rewrite map_Forall_to_list; apply: Forall_impl_in => //.
  rewrite Forall_lookup => ? [? c] ? /=; by apply wf_cdef_methods_wf_correct.
Qed.

Definition check_wf_cdef_constraints_wf (G: ProgDefContext) cdef: bool :=
  forallb (λ c, check_wf_ty G c.1 && check_wf_ty G c.2) cdef.(constraints).

Lemma wf_cdef_constraints_wf_correct (G: ProgDefContext) cdef:
  check_wf_cdef_constraints_wf G cdef →
  wf_cdef_constraints_wf cdef.
Proof.
  rewrite /check_wf_cdef_constraints_wf /wf_cdef_constraints_wf forallb_True => hF.
  apply: Forall_impl_in => //.
  rewrite Forall_lookup => [? c1] ? /andb_prop_elim [h0 h1].
  split; by apply wf_ty_correct.
Qed.

Definition check_wf_cdef_constraints_wf_context (G: ProgDefContext) : bool :=
  forallb (fun kv => check_wf_cdef_constraints_wf G kv.2) (map_to_list pdefs).

Lemma wf_cdef_constraints_wf_context_correct (G: ProgDefContext) :
  check_wf_cdef_constraints_wf_context G →
  map_Forall (λ _cname, wf_cdef_constraints_wf) pdefs.
Proof.
  rewrite /check_wf_cdef_constraints_wf_context forallb_True => hF.
  rewrite map_Forall_to_list; apply: Forall_impl_in => //.
  rewrite Forall_lookup => ? [? c] ? /=; by apply wf_cdef_constraints_wf_correct.
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

Definition check_constaints_no_this cdef : bool :=
  forallb (λ c, no_this c.1 && no_this c.2) cdef.(constraints).

Lemma wf_cdef_constraints_no_this_correct cdef:
  check_constaints_no_this cdef →
  wf_cdef_constraints_no_this cdef.
Proof.
  rewrite /check_constaints_no_this /wf_cdef_constraints_no_this forallb_True => hF.
  apply: Forall_impl_in => //.
  rewrite Forall_lookup => k [c0 c1] /= ?.
  by case/andb_prop_elim => h0 h1.
Qed.

Definition check_wf_constraints_no_this (G: ProgDefContext) : bool :=
  forallb (λ kv, check_constaints_no_this kv.2) (map_to_list pdefs).

Lemma wf_constraints_no_this_correct (G: ProgDefContext):
  check_wf_constraints_no_this G →
  map_Forall (λ _ : string, wf_cdef_constraints_no_this) pdefs.
Proof.
  rewrite /check_wf_constraints_no_this map_Forall_to_list forallb_True.
  by move/Forall_impl; apply => -[??] /=; apply/wf_cdef_constraints_no_this_correct.
Qed.

(* has_field *)
Definition get_local_fields (G: ProgDefContext) c : list string :=
  if pdefs !! c is Some cdef then
    List.map fst (map_to_list cdef.(classfields))
    else []
.

Lemma map_to_list_has_field_Some cdef k f:
  map fst (map_to_list cdef.(classfields)) !! k = Some f →
  is_Some(cdef.(classfields) !! f).
Proof.
  destruct (cdef.(classfields) !! f) eqn:hf; first done.
  rewrite list_lookup_fmap.
  destruct ((map_to_list cdef.(classfields)) !! k) as [ [k' v] | ] eqn:hf'; last done.
  simpl.
  case => ?; simplify_eq.
  assert (h: (f, v) ∈ map_to_list cdef.(classfields)).
  { by apply elem_of_list_lookup_2 in hf'. }
  apply elem_of_map_to_list in h.
  by rewrite hf in h.
Qed.

Lemma get_local_fields_Some_0 (G: ProgDefContext) c cdef k f:
  pdefs !! c = Some cdef →
  (get_local_fields G c) !! k = Some f →
  ∃ vfty, cdef.(classfields) !! f = Some vfty.
Proof.
  by rewrite /get_local_fields => -> /map_to_list_has_field_Some h.
Qed.

Lemma get_local_fields_Some_1 (G: ProgDefContext) c cdef f vfty:
  pdefs !! c = Some cdef →
  cdef.(classfields) !! f = Some vfty →
  ∃ k, (get_local_fields G c) !! k = Some f.
Proof.
  rewrite /get_local_fields => -> hf.
  assert (h: (f, vfty) ∈ map_to_list cdef.(classfields)) by by apply elem_of_map_to_list.
  apply elem_of_list_lookup_1 in h as [k hk].
  exists k; by rewrite list_lookup_fmap hk.
Qed.

Lemma get_local_fields_None (G: ProgDefContext) c cdef f:
  pdefs !! c = Some cdef →
  cdef.(classfields) !! f = None →
  ∀ k f', (get_local_fields G c) !! k = Some f' → f <> f'.
Proof.
  rewrite /get_local_fields => -> hf k f'.
  move/map_to_list_has_field_Some => [? hf'] ?; by simplify_eq.
Qed.

Lemma get_local_fields_correct (G: ProgDefContext) c:
  Forall (λ f, ∃ vis fty orig, has_field f c vis fty orig) (get_local_fields G c).
Proof.
  rewrite Forall_lookup /get_local_fields => k f /=.
  destruct (pdefs !! c) as [cdef | ] eqn:hcdef => //; rewrite hcdef; last done.
  move/map_to_list_has_field_Some => [[vis fty] hf].
  exists (vis, fty).1, fty, c.
  by apply HasField with cdef.
Qed.

(* has_fields *)

Fixpoint get_fields (G:ProgDefContext) n c : option (list string) :=
  if n is S p then
    if pdefs !! c is Some cdef then
      let fields := get_local_fields G c in
      if cdef.(superclass) is Some (parent, _) then
        if get_fields G p parent is Some pfields then Some (fields ++ pfields)
        else None
      else Some fields
    else None
  else None
.

Lemma has_fields_correct_0 (G: ProgDefContext) n c:
  match get_fields G n c with
  | Some fields => 
      ∀ k f, fields !! k = Some f → ∃ vis fty orig, has_field f c vis fty orig
  | None => True
  end.
Proof.
  elim: n c => [ // | p hi ] /= c.
  destruct (pdefs !! c) as [cdef | ] eqn:hcdef => //=.
  destruct cdef.(superclass) as [[parent σ] | ] eqn:hp; last first.
  { move => k f hf.
    move : (get_local_fields_correct G c).
    move/Forall_lookup => h; apply h in hf as (vis & fty & orig & hf); clear h.
    by eexists _, _ ,_.
  }
  destruct (get_fields G p parent) as [pfields | ] eqn:hgp => //=.
  specialize hi with parent.
  rewrite hgp in hi.
  move => k f.
  rewrite lookup_app.
  destruct (get_local_fields G c !! k) eqn:hg0.
  { case => ?; simplify_eq.
    move : (get_local_fields_correct G c).
    move/Forall_lookup => h; apply h in hg0 as (vis & fty & orig & hf); clear h.
    by eexists _, _, _.
  }
  move => hpfields.
  destruct (cdef.(classfields) !! f) as [ [vis fty] | ] eqn:hf.
  - exists (vis, fty).1, fty, c.
    by apply HasField with cdef.
  - apply hi in hpfields as (vis & fty & orig & ?).
    exists vis, (subst_ty σ fty), orig.
    by eapply InheritsField.
Qed.

Lemma has_fields_correct_1 (G: ProgDefContext) n c:
  match get_fields G n c with
  | Some fields => 
      ∀ f vis fty orig, has_field f c vis fty orig → ∃ k, fields !! k = Some f
  | None => True
  end.
Proof.
  elim: n c => [ // | p hi ] /= c.
  destruct (pdefs !! c) as [cdef | ] eqn:hcdef => //=.
  destruct cdef.(superclass) as [[parent σ] | ] eqn:hp; last first.
  { move => f vis fty orig hf.
    inv hf.
    + by eapply get_local_fields_Some_1.
    + by rewrite H in hcdef; simplify_eq.
  }
  destruct (get_fields G p parent) as [pfields | ] eqn:hgp => //=.
  specialize hi with parent.
  rewrite hgp in hi.
  move => f vis fty orig hf.
  inv hf.
  + eapply get_local_fields_Some_1 in H0 as [k hk] => //.
    exists k; by rewrite lookup_app hk.
  + rewrite hcdef in H; case: H => ?; simplify_eq.
    apply hi in H2 as [k hk].
    exists (length (get_local_fields G c) + k).
    rewrite lookup_app_r; last by lia.
    by rewrite Nat.sub_add'.
Qed.

Definition has_local_field cdef f : bool :=
  if cdef.(classfields) !! f is Some _ then true else false
.

Definition check_wf_cdef_fields (G: ProgDefContext) n cdef :=
  if cdef.(superclass) is Some (super, _) then
    if get_fields G n super is Some fields then
      forallb (λ f, (negb (has_local_field cdef f))) fields
    else false
  else true.

Lemma wf_cdef_fields_correct (G: ProgDefContext) n cdef:
  check_wf_cdef_fields G n cdef →
  ∀ f vis fty orig super σ,
    cdef.(superclass) = Some (super, σ) →
    has_field f super vis fty orig →
    cdef.(classfields) !! f = None.
Proof.
  rewrite /check_wf_cdef_fields.
  destruct cdef.(superclass) as [[parent σ] | ] eqn:hp => //=.
  destruct (get_fields G n parent) as [ fields | ] eqn:hfields => //=.
  rewrite forallb_True Forall_lookup => hF f vis fty orig p' σ'.
  case => ??; simplify_eq => hf'.
  move: (has_fields_correct_1 G n p').
  rewrite hfields => h.
  apply h in hf' as [k hk].
  apply hF in hk; move : hk.
  rewrite /has_local_field.
  by case: (cdef.(classfields) !! f).
Qed.

Definition check_wf_fields (G: ProgDefContext) n : bool :=
  forallb (λ kv, check_wf_cdef_fields G n kv.2) (map_to_list pdefs).

Lemma wf_fields_correct (G: ProgDefContext) n :
  check_wf_fields G n →
  map_Forall (λ _cname, wf_cdef_fields) pdefs.
Proof.
  rewrite /check_wf_fields map_Forall_to_list forallb_True.
  by move/Forall_impl; apply => -[??] /=; apply/wf_cdef_fields_correct.
Qed.
