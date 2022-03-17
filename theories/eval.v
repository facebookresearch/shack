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

Section Evaluation.
  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.

  (* Big step reduction *)
  Definition primop_eval (op: primop) : Z → Z → value :=
    match op with
    | PlusO => fun x y => IntV (x + y)
    | MinusO => fun x y => IntV (x - y)
    | TimesO => fun x y => IntV (x * y)
    | DivO => fun x y => IntV (x / y)
    | LeqO => fun x y => BoolV (Z.leb x y)
    | GeqO => fun x y => BoolV (Z.geb x y)
    | EqO => fun x y => BoolV (Z.eqb x y)
    end
  .

  Record local_env := {
    vthis : loc;
    lenv : gmap var value
  }.

  Global Instance local_env_insert : Insert string value local_env :=
    λ x v le, 
    {| vthis := le.(vthis);
      lenv := <[x := v]>le.(lenv);
    |}.

  Fixpoint expr_eval (le : local_env) (e: expr) : option value :=
    match e with
    | IntE z => Some (IntV z)
    | BoolE b => Some (BoolV b)
    | NullE => Some NullV
    | OpE op e1 e2 =>
        match expr_eval le e1, expr_eval le e2 with 
        | Some (IntV z1), Some (IntV z2) => Some (primop_eval op z1 z2)
        | _, _ => None
        end
    | VarE v => le.(lenv) !! v
    | ThisE => Some (LocV le.(vthis))
    end
  .

  (* concrete heaps *)
  Definition heap : Type := gmap loc (tag * stringmap value).

  Definition map_args {A B: Type} (f: A → option  B) (m: stringmap A) :
    option (stringmap B) :=
    guard (map_Forall (λ _ x, is_Some (f x)) m); Some (omap f m)
  .

  Lemma dom_map_args: ∀ A B (f: A → option B)
    (m: stringmap A) (n: stringmap B),
    map_args f m = Some n → 
    dom stringset n = dom _ m.
  Proof.
    rewrite /map_args => A B f m n h.
    case_option_guard; last done.
    injection h; intros <-; clear h.
    apply set_eq => x; split; move/elem_of_dom => hx; apply elem_of_dom.
    - rewrite lookup_omap in hx.
      destruct hx as [v hv]; by apply bind_Some in hv as [a [-> ha]].
    - destruct hx as [v hv].
      rewrite lookup_omap hv.
      by apply H in hv.
  Qed.

  Lemma map_args_lookup: ∀ A B (f: A → option B) (m: stringmap A) n,
    map_args f m = Some n →
    ∀ k, n !! k = (m !! k) ≫= f.
  Proof.
    rewrite /map_args => A B f m n h k.
    case_option_guard; last done.
    injection h; intros <-; clear h.
    by rewrite lookup_omap.
  Qed.

  Lemma map_args_empty: ∀ A B (f: A → option B),
    map_args f ∅ = Some ∅.
  Proof.
    rewrite /map_args => A B f /=.
    case_option_guard; first by rewrite omap_empty.
    elim: H.
    apply map_Forall_lookup => i x h; discriminate h.
  Qed.

  Lemma map_args_update: ∀ A B (f: A → option B) k a m n,
    map_args f m = Some n →
    map_args f (<[ k := a]> m) =
    match f a with
    | Some b => Some (<[ k := b]> n)
    | None => None
    end.
  Proof.
    rewrite /map_args => A B f k a m n h /=.
    case_option_guard; last done.
    injection h; intros <-; clear h.
    case_option_guard.
    - rewrite map_Forall_lookup in H0.
      specialize H0 with k a.
      rewrite lookup_insert in H0.
      destruct H0 as [ b hb ]; first by done.
      rewrite hb.
      f_equal.
      by apply omap_insert_Some.
    - destruct (f a) as [b | ] eqn:hb; last done.
      elim: H0 => i x h.
      rewrite lookup_insert_Some in h.
      destruct h as [[<- <-] | [hne hin]]; first by rewrite hb.
      now apply H in hin.
  Qed.

  Definition tag_match (st : local_env * heap) (v: string) (t: tag) :=
    ∃ l, st.1.(lenv) !! v = Some (LocV l) ∧
    ∃ t' (fields: stringmap value), st.2 !! l = Some (t', fields) ∧
    inherits t' t
  .

  Inductive cmd_eval:
    (local_env * heap) → cmd →
    (local_env * heap) → nat → Prop :=
    | SkipEv : ∀ st, cmd_eval st SkipC st 0
    | LetEv: ∀ le h v e val,
        expr_eval le e = Some val →
        cmd_eval (le, h) (LetC v e) (<[v := val]> le, h) 0
    | NewEv: ∀ le h lhs new t args vargs,
        (* targs are not stored in the heap: erased generics *)
        h !! new = None →
        map_args (expr_eval le) args = Some vargs →
        cmd_eval (le, h) (NewC lhs t args) (<[lhs := LocV new]>le, <[new := (t, vargs)]>h) 1
    | GetEv: ∀ le h lhs recv name l t vs v,
        expr_eval le recv = Some (LocV l) →
        h !! l = Some (t, vs) →
        vs !! name = Some v →
        cmd_eval (le, h) (GetC lhs recv name) (<[lhs := v]>le, h) 1
    | SetEv: ∀ le h recv fld rhs l v t vs vs',
        expr_eval le recv = Some (LocV l) →
        expr_eval le rhs = Some v →
        h !! l = Some (t, vs) →
        vs' = <[ fld := v ]>vs →
        cmd_eval (le, h) (SetC recv fld rhs) (le, <[l := (t, vs')]> h) 0
    | SeqEv: ∀ st1 st2 st3 fstc sndc n1 n2,
        cmd_eval st1 fstc st2 n1 →
        cmd_eval st2 sndc st3 n2 →
        cmd_eval st1 (SeqC fstc sndc) st3 (n1 + n2)
    | IfTrueEv: ∀ st1 st2 cond thn els n,
        expr_eval st1.1 cond = Some (BoolV true) →
        cmd_eval st1 thn st2 n →
        cmd_eval st1 (IfC cond thn els) st2 n
    | IfFalseEv: ∀ st1 st2 cond thn els n,
        expr_eval st1.1 cond = Some (BoolV false) →
        cmd_eval st1 els st2 n →
        cmd_eval st1 (IfC cond thn els) st2 n
    | CallEv: ∀ le h h' lhs recv l t vs name args vargs orig mdef
        run_env run_env' ret n,
        expr_eval le recv = Some (LocV l) →
        map_args (expr_eval le) args = Some vargs →
        h !! l = Some (t, vs) →
        has_method name t orig mdef →
        {| vthis := l; lenv := vargs|} = run_env →
        cmd_eval (run_env, h) mdef.(methodbody) (run_env', h') n →
        expr_eval run_env' mdef.(methodret) = Some ret →
        cmd_eval (le, h) (CallC lhs recv name args) (<[lhs := ret]>le, h') (S n)
    | CondTag1Ev n st1 st2 v t cmd :
        (* tag in heap must <: requested tag to move forward *)
        tag_match st1 v t →
        cmd_eval st1 cmd st2 n →
        cmd_eval st1 (CondTagC v t cmd) st2 n
    | CondTag2Ev st v t cmd :
        ¬tag_match st v t →
        cmd_eval st (CondTagC v t cmd) st 0
.

End Evaluation.
