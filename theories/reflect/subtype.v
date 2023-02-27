(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
From stdpp Require Import base strings gmap stringmap fin_maps.
(* Not using iris but importing their ssreflect dependencies *)
From iris.proofmode Require Import tactics.
From shack Require Import lang progdef subtype.
From shack.reflect Require Import lang.

Fixpoint forallb2 {A B: Type} (f: A → B → bool)
  (la: list A) (lb: list B) : bool :=
  match la, lb with
  | [], [] => true
  | a :: la, b :: lb => f a b && forallb2 f la lb
  | _, _ => false
  end.

Lemma forallb2_True:
  ∀ {A B : Type} (f : A → B → bool) (la : list A) (lb : list B),
    forallb2 f la lb ↔ Forall2 (λ x y, f x y) la lb.
Proof.
  move => A B f.
  elim => [ | a la hi] [ | b lb] /=.
  - by split => //.
  - split => // h; by inv h.
  - split => // h; by inv h.
  - split.
    + case/andb_prop_elim => h0 h1; constructor; by firstorder.
    + move => h.
      apply Forall2_cons_1 in h as [? h].
      apply andb_prop_intro; split; by firstorder.
Qed.

Lemma unroll_forallb2 {A B: Type} (f: A → B → bool) la lb:
  forallb2 f la lb =
      (fix rec0 la lb { struct la } :=
      match la, lb with
      | [], [] => true
      | a :: la, b :: lb => f a b && rec0 la lb
      | _, _ => false
      end) la lb.
Proof.
  elim: la lb => [ | a la hi] [ | b lb] //=.
  by case: (f a b) => //=.
Qed.

Fixpoint check_mono (G: ProgDefContext) (vs: list variance) ty { struct ty } : bool :=
  match ty with
  | UnionT s t
  | InterT s t => check_mono G vs s && check_mono G vs t
  | GenT n =>
      match vs !! n with
      | Some Invariant | Some Covariant => true
      | Some Contravariant | None => false
      end
  | ClassT exact c targs =>
      if pdefs !! c is Some cdef then
      ((fix rec0 (la: list lang_ty) lb { struct la } :=
      match la, lb with
      | [], [] => true
      | a :: la, b :: lb =>
          (implb (not_contra b || exact) (check_mono G vs a)) && rec0 la lb
      | _, _ => false
      end) targs cdef.(generics)) &&
      ((fix rec0 (la: list lang_ty) lb { struct la } :=
      match la, lb with
      | [], [] => true
      | a :: la, b :: lb =>
          (implb (not_cov b || exact) (check_mono G (neg_variance <$> vs) a)) && rec0 la lb
      | _, _ => false
      end) targs cdef.(generics))
      else false
  | _ => true
  end.

Lemma check_mono_class G vs exact c σ:
  check_mono G vs (ClassT exact c σ) =
  if pdefs !! c is Some cdef then
  forallb2 (λ ty w, (implb (not_contra w || exact) (check_mono G vs ty))) σ cdef.(generics) &&
  forallb2 (λ ty w, (implb (not_cov w || exact) (check_mono G (neg_variance <$> vs) ty))) σ cdef.(generics)
  else false.
Proof.
  rewrite /=.
  case: (pdefs !! c) => //= cdef.
  by rewrite !unroll_forallb2.
Qed.

Lemma option_Forall2_inv {A B: Type} (f: A → B → Prop) (a : A) (b : B):
  option_Forall2 f (Some a) (Some b) → f a b.
Proof. by move => h; inv h.  Qed.

Lemma mono_correct (G: ProgDefContext) vs ty:
  check_mono G vs ty → mono vs ty.
Proof.
  elim: ty vs; try (intros; by constructor).
  - move => exact c σ /Forall_lookup hF vs.
    rewrite check_mono_class.
    destruct (pdefs !! c) as [cdef | ] eqn:hcdef => //=.
    case/andb_prop_elim.
    rewrite forallb2_True Forall2_lookup => h0.
    rewrite forallb2_True Forall2_lookup => h1.
    eapply MonoClass => //.
    + move => k wk tk hwk htk.
      case => [hno | hex].
      * apply hF with k => //.
        move: {h0} (h0 k); rewrite htk hwk /= => h.
        apply option_Forall2_inv in h.
        rewrite Is_true_true in hno.
        by rewrite hno /= in h.
      * apply hF with k => //.
        move: {h0} (h0 k); rewrite htk hwk /= => h.
        apply option_Forall2_inv in h.
        by rewrite hex orb_true_r /= in h.
    + move => k wk tk hwk htk.
      case => [hno | hex].
      * apply hF with k => //.
        move: {h1} (h1 k); rewrite htk hwk /= => h.
        apply option_Forall2_inv in h.
        rewrite Is_true_true in hno.
        by rewrite hno /= in h.
      * apply hF with k => //.
        move: {h1} (h1 k); rewrite htk hwk /= => h.
        apply option_Forall2_inv in h.
        by rewrite hex orb_true_r /= in h.
  - move => /= s t hs ht vs /andb_prop_elim [h0 h1]; constructor; by firstorder.
  - move => /= s t hs ht vs /andb_prop_elim [h0 h1]; constructor; by firstorder.
  - move => /= n vs.
    destruct (vs !! n) as [[] | ] eqn:var => // _; by constructor.
Qed.

Definition check_wf_cdef_mono (G: ProgDefContext) cdef : bool :=
  if cdef.(superclass) is Some(parent, σ) then
  check_mono G cdef.(generics) (ClassT false parent σ)
  else true
.

Lemma wf_cdef_mono_correct (G: ProgDefContext) cdef :
  check_wf_cdef_mono G cdef → wf_cdef_mono cdef.
Proof.
  rewrite /check_wf_cdef_mono /wf_cdef_mono.
  case : cdef => ?? superclass ??.
  simpl lang.superclass.
  case: superclass => //.
  simpl generics => [[p σ]].
  rewrite check_mono_class => /=.
  destruct (pdefs !! p) as [pdef | ] eqn:hpdef; last done.
  case/andb_prop_elim => /forallb2_True /Forall2_lookup h0
    /forallb2_True /Forall2_lookup h1.
  apply MonoClass with pdef; first done.
  - move => i wi ti hwi hti [h | //].
    move : {h0} (h0 i); rewrite hti hwi => h0.
    apply option_Forall2_inv in h0.
    rewrite Is_true_true in h.
    rewrite h /= in h0.
    by apply mono_correct.
  - move => i wi ti hwi hti [h | //].
    move : {h1} (h1 i); rewrite hti hwi => h1.
    apply option_Forall2_inv in h1.
    rewrite Is_true_true in h.
    rewrite h /= in h1.
    by apply mono_correct.
Qed.

Definition check_wf_mono (G: ProgDefContext): bool :=
  forallb (λ kv, check_wf_cdef_mono G kv.2) (map_to_list pdefs).

Lemma wf_mono_correct (G: ProgDefContext):
  check_wf_mono G → map_Forall (λ _cname, wf_cdef_mono) pdefs.
Proof.
  rewrite /check_wf_mono.
  move/forallb_True => hF.
  rewrite map_Forall_to_list.
  apply: Forall_impl_in => //.
  rewrite Forall_lookup => ? [? ty] /= ? h.
  by apply wf_cdef_mono_correct.
Qed.

Definition check_wf_mdef_mono (G: ProgDefContext) vs mdef : bool :=
  if mdef.(methodvisibility) is Public then
    forallb (λ kv, check_mono G (neg_variance <$> vs) kv.2) (map_to_list mdef.(methodargs)) &&
    check_mono G vs mdef.(methodrettype)
  else true
.

Lemma wf_mdef_mono_correct (G: ProgDefContext) vs mdef:
  check_wf_mdef_mono G vs mdef → wf_mdef_mono vs mdef.
Proof.
  rewrite /check_wf_mdef_mono /wf_mdef_mono.
  case: mdef => [[ | //]] args rettype ?? /=.
  case/andb_prop_elim => /forallb_True hF hm.
  split; last by apply mono_correct.
  rewrite map_Forall_to_list.
  apply: Forall_impl_in => //.
  rewrite Forall_lookup => ? [? ty] /= ? h.
  by apply mono_correct.
Qed.

Definition check_wf_cdef_methods_mono (G: ProgDefContext) cdef : bool :=
  forallb (λ kv, check_wf_mdef_mono G cdef.(generics) kv.2) (map_to_list cdef.(classmethods)).

Lemma wf_cdef_methods_mono_correct (G: ProgDefContext) cdef:
  check_wf_cdef_methods_mono G cdef → wf_cdef_methods_mono cdef.
Proof.
  rewrite /check_wf_cdef_methods_mono /wf_cdef_methods_mono.
  move/forallb_True => hF.
  rewrite map_Forall_to_list.
  apply: Forall_impl_in => //.
  rewrite Forall_lookup => ? [? ty] /= ? h.
  by apply wf_mdef_mono_correct.
Qed.

Definition check_invariant (G: ProgDefContext) vs ty : bool :=
  check_mono G vs ty && check_mono G (neg_variance <$> vs) ty.

Lemma invariant_correct (G: ProgDefContext) vs ty:
  check_invariant G vs ty → invariant vs ty.
Proof. case/andb_prop_elim => h0 h1; split; by apply mono_correct. Qed.

Definition check_field_mono (G: ProgDefContext) vs (vfty: visibility * lang_ty) : bool :=
  let (vis, fty) := vfty in
  if vis is Public then check_invariant G vs fty else true.

Lemma field_mono_correct (G: ProgDefContext) vs vfty:
  check_field_mono G vs vfty → field_mono vs vfty.
Proof.
    rewrite /check_field_mono /field_mono.
    case: vfty => [[ | //]] fty h.
    by apply invariant_correct.
Qed.

Definition check_wf_field_mono (G: ProgDefContext) cdef : bool :=
  forallb (λ kv, check_field_mono G cdef.(generics) kv.2) (map_to_list cdef.(classfields)).

Lemma wf_field_mono_correct (G: ProgDefContext) cdef:
  check_wf_field_mono G cdef → wf_field_mono cdef.
Proof.
  rewrite /check_wf_field_mono /wf_field_mono.
  move/forallb_True => hF.
  rewrite map_Forall_to_list.
  apply: Forall_impl_in => //.
  rewrite Forall_lookup => ? [? ty] /= ? h.
  by apply field_mono_correct.
Qed.

Definition check_wf_methods_mono (G: ProgDefContext): bool :=
  forallb (λ kv, check_wf_cdef_methods_mono G kv.2) (map_to_list pdefs).

Lemma wf_methods_mono_correct (G: ProgDefContext):
  check_wf_methods_mono G → map_Forall (λ _cname, wf_cdef_methods_mono) pdefs.
Proof.
  rewrite /check_wf_methods_mono.
  move/forallb_True => hF.
  rewrite map_Forall_to_list.
  apply: Forall_impl_in => //.
  rewrite Forall_lookup => ? [? ty] /= ? h.
  by apply wf_cdef_methods_mono_correct.
Qed.

Definition check_wf_fields_mono (G: ProgDefContext) : bool :=
  forallb (λ kv, check_wf_field_mono G kv.2) (map_to_list pdefs).

Lemma wf_fields_mono_correct (G: ProgDefContext):
  check_wf_fields_mono G → map_Forall (λ _cname, wf_field_mono) pdefs.
Proof.
  rewrite /check_wf_fields_mono.
  move/forallb_True => hF.
  rewrite map_Forall_to_list.
  apply: Forall_impl_in => //.
  rewrite Forall_lookup => ? [? ty] /= ? h.
  by apply wf_field_mono_correct.
Qed.
