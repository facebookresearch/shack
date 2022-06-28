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
  Definition binop_eval (op: binop) : Z → Z → value :=
    match op with
    | PlusO => fun x y => IntV (x + y)
    | MinusO => fun x y => IntV (x - y)
    | TimesO => fun x y => IntV (x * y)
    | DivO => fun x y => IntV (x / y)
    | LtO => fun x y => BoolV (Z.ltb x y)
    | GtO => fun x y => BoolV (Z.gtb x y)
    | EqO => fun x y => BoolV (Z.eqb x y)
    end
  .

  Record local_env := {
    vthis : loc;
    lenv : gmap var value
  }.

  Global Instance local_env_insert : Insert string value local_env :=
    λ x v Ω,
    {| vthis := Ω.(vthis);
      lenv := <[x := v]>Ω.(lenv);
    |}.

  Fixpoint expr_eval (Ω : local_env) (e: expr) : option value :=
    match e with
    | IntE z => Some (IntV z)
    | BoolE b => Some (BoolV b)
    | NullE => Some NullV
    | BinOpE op e1 e2 =>
        match expr_eval Ω e1, expr_eval Ω e2 with
        | Some (IntV z1), Some (IntV z2) => Some (binop_eval op z1 z2)
        | Some (BoolV b1), Some (BoolV b2) =>
            match op with
            | EqO => Some (BoolV (eqb b1 b2))
            | _ => None
            end
        | _, _ => None
        end
    | UniOpE op e =>
        match op, expr_eval Ω e with
        | NotO, Some (BoolV b) => Some (BoolV (negb b))
        | _, _ => None
        end
    | VarE v => Ω.(lenv) !! v
    | ThisE => Some (LocV Ω.(vthis))
    | UpcastE e _ => expr_eval Ω e
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
    dom n = dom m.
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

  Definition rc_match (st : local_env * heap) (v: string) (rc: runtime_check) :=
    match rc with
    | RCTag t =>
        ∃ l, st.1.(lenv) !! v = Some (LocV l) ∧
        ∃ t' (fields: stringmap value), st.2 !! l = Some (t', fields) ∧
        inherits t' t
    | RCInt => ∃ z, st.1.(lenv) !! v = Some (IntV z)
    | RCBool => ∃ b, st.1.(lenv) !! v = Some (BoolV b)
    | RCNull => st.1.(lenv) !! v = Some NullV
    | RCNonNull =>
        match st.1.(lenv) !! v with
        | None => False
        | Some (IntV z) => True
        | Some (BoolV b) => True
        | Some (LocV l) =>
            ∃ t' (fields: stringmap value), st.2 !! l = Some (t', fields)
        | Some NullV => False
        end
    end.

  (* We keep track of the tag of the current class, to correctly implement
   * the runtime check for visibility:
   *)
  Definition visibility_check (C t: tag) (recv: expr) name :=
    ∃ vis fty orig,
    has_field name t vis fty orig ∧
    (match (vis, recv) with
     | (Public, _) => True
     | (Private, ThisE) => orig = C
     | (Private, _) => False
     end)
  .

  Inductive cmd_eval:
    tag →
    (local_env * heap) → cmd →
    (local_env * heap) → nat → Prop :=
    | SkipEv : ∀ C st, cmd_eval C st SkipC st 0
    | LetEv: ∀ C Ω h v e val,
        expr_eval Ω e = Some val →
        cmd_eval C (Ω, h) (LetC v e) (<[v := val]> Ω, h) 0
    | NewEv: ∀ C Ω h lhs new t targs args vargs,
        (* targs are not stored in the heap: erased generics *)
        h !! new = None →
        map_args (expr_eval Ω) args = Some vargs →
        cmd_eval C (Ω, h) (NewC lhs t targs args) (<[lhs := LocV new]>Ω, <[new := (t, vargs)]>h) 1
    | GetEv: ∀ C Ω h lhs recv name l t vs v,
        expr_eval Ω recv = Some (LocV l) →
        h !! l = Some (t, vs) →
        vs !! name = Some v →
        visibility_check C t recv name →
        cmd_eval C (Ω, h) (GetC lhs recv name) (<[lhs := v]>Ω, h) 1
    | SetEv: ∀ C Ω h recv fld rhs l v t vs vs',
        expr_eval Ω recv = Some (LocV l) →
        expr_eval Ω rhs = Some v →
        h !! l = Some (t, vs) →
        vs' = <[ fld := v ]>vs →
        visibility_check C t recv fld →
        cmd_eval C (Ω, h) (SetC recv fld rhs) (Ω, <[l := (t, vs')]> h) 0
    | SeqEv: ∀ C st1 st2 st3 fstc sndc n1 n2,
        cmd_eval C st1 fstc st2 n1 →
        cmd_eval C st2 sndc st3 n2 →
        cmd_eval C st1 (SeqC fstc sndc) st3 (n1 + n2)
    | IfTrueEv: ∀ C st1 st2 cond thn els n,
        expr_eval st1.1 cond = Some (BoolV true) →
        cmd_eval C st1 thn st2 n →
        cmd_eval C st1 (IfC cond thn els) st2 n
    | IfFalseEv: ∀ C st1 st2 cond thn els n,
        expr_eval st1.1 cond = Some (BoolV false) →
        cmd_eval C st1 els st2 n →
        cmd_eval C st1 (IfC cond thn els) st2 n
    | CallEv: ∀ C Ω h h' lhs recv l t vs name args vargs orig mdef
        run_env run_env' ret n,
        expr_eval Ω recv = Some (LocV l) →
        map_args (expr_eval Ω) args = Some vargs →
        h !! l = Some (t, vs) →
        has_method name t orig mdef →
        dom mdef.(methodargs) = dom args →
        {| vthis := l; lenv := vargs|} = run_env →
        cmd_eval orig (run_env, h) mdef.(methodbody) (run_env', h') n →
        expr_eval run_env' mdef.(methodret) = Some ret →
        cmd_eval C (Ω, h) (CallC lhs recv name args) (<[lhs := ret]>Ω, h') (S n)
    | RuntimeCheck1Ev C n st1 st2 v rc thn els:
        rc_match st1 v rc →
        cmd_eval C st1 thn st2 n →
        cmd_eval C st1 (RuntimeCheckC v rc thn els) st2 n
    | RuntimeCheck2Ev C n st1 st2 v rc thn els:
        ¬rc_match st1 v rc →
        cmd_eval C st1 els st2 n →
        cmd_eval C st1 (RuntimeCheckC v rc thn els) st2 n
.
End Evaluation.
