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

Section Typing.
  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.

  (* Helping the inference with this notation that hides pdefs *)
  Local Notation "Δ ⊢ s <: t" := (@subtype _ Δ Plain s t) (at level 70, s at next level, no associativity).
  Local Notation "Δ ⊢ s <D: t" := (@subtype _ Δ Aware s t) (at level 70, s at next level, no associativity).

  (* At class + substitution is `ok` w.r.t. to a set of constraints `Δ` if
   * - all the types in the substitution are ok
   * - all the constraints of that class are satisfied.
   *)
  Inductive ok_ty (Δ: list constraint) : lang_ty → Prop :=
    | OkInt: ok_ty Δ IntT
    | OkBool: ok_ty Δ BoolT
    | OkNothing: ok_ty Δ NothingT
    | OkMixed: ok_ty Δ MixedT
    | OkClass t σ def:
        (∀ i ty, σ !! i = Some ty → ok_ty Δ ty) →
        pdefs !! t = Some def →
        (∀ i c, def.(constraints) !! i = Some c → Δ ⊢ (subst_ty σ c.1) <D: (subst_ty σ c.2)) →
        ok_ty Δ (ClassT t σ)
    | OkNull: ok_ty Δ NullT
    | OkNonNull: ok_ty Δ NonNullT
    | OkUnion s t: ok_ty Δ s → ok_ty Δ t → ok_ty Δ (UnionT s t)
    | OkInter s t: ok_ty Δ s → ok_ty Δ t → ok_ty Δ (InterT s t)
    | OkGen n: ok_ty Δ (GenT n)
    | OkDynamic : ok_ty Δ DynamicT
    | OkSupportDyn : ok_ty Δ SupportDynT
  .

  Lemma ok_ty_weaken Δ t: ok_ty Δ t → ∀ Δ', Δ ⊆ Δ' → ok_ty Δ' t.
  Proof.
    induction 1 as [ | | | | t σ def hσ hi hdef hconstr
    | | | s t hs hi ht hit | s t hs hi ht hit | n | | ] => Δ' hincl; try by constructor.
    - apply OkClass with def => //.
      + move => i ty h; by apply hi with i.
      + move => i c h.
        apply subtype_weaken with Δ; by eauto.
    - constructor; by eauto.
    - constructor; by eauto.
  Qed.

  Lemma ok_ty_class_inv Δ t σ: ok_ty Δ (ClassT t σ) → Forall (ok_ty Δ) σ.
  Proof.
    move => h; inv h.
    apply Forall_lookup => ? x hin.
    by eauto.
  Qed.

  Lemma ok_ty_subst Δ t:
    map_Forall (λ _, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _, wf_cdef_constraints_bounded) pdefs →
    ok_ty Δ t →
    wf_ty t →
    ∀ Δ' σ, Forall wf_ty σ →
         Forall (ok_ty Δ') σ →
         ok_ty (Δ' ++ (subst_constraints σ Δ)) (subst_ty σ t).
  Proof.
    move => hwp hcb.
    induction 1 as [ | | | | t σt def hσt hi hdef hconstr
    | | | s t hs his ht hit | s t hs his ht hit | n | | ]
    => hwf Δ' σ hwfσ hokσ /=; try (constructor; by eauto).
    - apply OkClass with def => //.
      + move => i ty h.
        apply list_lookup_fmap_inv in h as [ty' [-> h]].
        apply wf_ty_class_inv in hwf.
        apply hi with i => //.
        rewrite Forall_lookup in hwf.
        by apply hwf in h.
      + move => i c h.
        assert (hdef' := hdef).
        apply hcb in hdef'.
        rewrite /wf_cdef_constraints_bounded Forall_lookup in hdef'.
        assert (h' := h).
        apply hdef' in h as [].
        apply subtype_weaken with (subst_constraints σ Δ); last by set_solver.
        rewrite -!subst_ty_subst.
        * apply subtype_subst => //.
          by apply hconstr with i.
        * inv hwf; simplify_eq.
          by rewrite H4.
        * inv hwf; simplify_eq.
          by rewrite H4.
    - inv hwf.
      constructor; by eauto.
    - inv hwf.
      constructor; by eauto.
    - destruct (σ !! n) as [ ty | ] eqn:hty; last by constructor.
      simpl.
      rewrite Forall_lookup in hokσ.
      apply hokσ in hty.
      apply ok_ty_weaken with Δ'; first by apply hty.
      by set_solver.
  Qed.

  Definition ok_constraint Δ (c: constraint) :=
    ok_ty Δ c.1 ∧ ok_ty Δ c.2.

  Definition ok_constraints Δ G := Forall (ok_constraint Δ) G.

  Definition wf_cdef_parent_ok cdef :=
    match cdef.(superclass) with
    | None => True
    | Some (parent, σ) =>
        ok_ty cdef.(constraints) (ClassT parent σ)
    end
  .

  Lemma extends_using_ok A B σ:
    map_Forall (λ _cname, wf_cdef_parent_ok) pdefs →
    extends_using A B σ →
    ∃ adef,
    pdefs !! A = Some adef ∧
    ok_ty adef.(constraints) (ClassT B σ).
  Proof.
    move => hok h.
    destruct h as [A B adef σ hpdefs hsuper].
    exists adef; split => //.
    apply hok in hpdefs.
    by rewrite /wf_cdef_parent_ok hsuper in hpdefs.
  Qed.

  Lemma gen_targs_ok Δ n:
    ∀ i ty, gen_targs n !! i = Some ty →
    ok_ty Δ ty.
  Proof.
    move => i ty /lookup_gen_targs ->.
    by constructor.
  Qed.

  Lemma ok_ty_trans Δ ty:
    ok_ty Δ ty →
    ∀ Δ',
    (∀ i c, Δ !! i = Some c → Δ' ⊢ c.1 <D: c.2) →
    ok_ty Δ' ty.
  Proof.
    induction 1 as [ | | | | t σ def hσ hi hdef hconstr
    | | | s t hs hi ht hit | s t hs hi ht hit | n | | ] => Δ' hΔ; try by constructor.
    - econstructor => //.
      + move => k ty hk; by eauto.
      + move => k c' hc'.
        apply hconstr in hc'.
        apply subtype_constraint_trans with Δ; by eauto.
    - constructor; by eauto.
    - constructor; by eauto.
  Qed.

  Lemma inherits_using_ok A B σ:
    map_Forall (λ _ : string, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _cname, wf_cdef_parent_ok) pdefs →
    map_Forall (λ _ : string, wf_cdef_constraints_bounded) pdefs →
    inherits_using A B σ →
    ∃ adef,
    pdefs !! A = Some adef ∧
    ok_ty adef.(constraints) (ClassT B σ).
  Proof.
    move => hp hok hcb.
    induction 1 as [ A adef hpdefs | A B σ hext | A B σ C σC hext h hi ].
    - exists adef; split => //.
      econstructor => //.
      + by apply gen_targs_ok.
      + move => i c hc.
        rewrite !subst_ty_id.
        * constructor.
          apply elem_of_list_lookup.
          exists i; by rewrite hc {1}(surjective_pairing c).
        * apply hcb in hpdefs.
          rewrite /wf_cdef_constraints_bounded Forall_lookup in hpdefs.
          by apply hpdefs in hc as [].
        * apply hcb in hpdefs.
          rewrite /wf_cdef_constraints_bounded Forall_lookup in hpdefs.
          by apply hpdefs in hc as [].
    - by apply extends_using_ok in hext.
    - destruct hi as (bdef & hB & hokB).
      assert (hwfB: wf_ty (ClassT B σ)).
      { apply extends_using_wf in hext => //.
        by repeat destruct hext as [? hext].
      }
      assert (hwfC: wf_ty (ClassT C σC)).
      { apply inherits_using_wf in h => //.
        by repeat destruct h as [? h].
      }
      inv hwfC.
      destruct hext as [A B adef σ hpdefs hsuper].
      exists adef; split => //.
      econstructor => //.
      { move => i ty hi.
        apply list_lookup_fmap_inv in hi as [ty' [-> hi]].
        eapply ok_ty_trans.
        + eapply ok_ty_subst => //.
          { inv hokB; by eauto. }
          { by eauto. }
          { by apply wf_ty_class_inv in hwfB. }
          apply hok in hpdefs.
          rewrite /wf_cdef_parent_ok hsuper in hpdefs.
          by apply ok_ty_class_inv in hpdefs.
        + move => j c.
          rewrite lookup_app_Some.
          case => [hc | [? ]].
          * apply SubConstraint.
            apply elem_of_list_lookup_2 in hc.
            by rewrite -surjective_pairing.
          * rewrite /subst_constraints => hc.
            apply list_lookup_fmap_inv in hc as [c' [-> hc]].
            rewrite /subst_constraint /=.
            apply hok in hpdefs.
            rewrite /wf_cdef_parent_ok hsuper in hpdefs.
            inv hpdefs; simplify_eq.
            by eauto.
      }
      move => i c hc.
      rewrite -!subst_ty_subst.
      + eapply subtype_constraint_trans.
        * apply subtype_subst => //; last by apply wf_ty_class_inv in hwfB.
          inv hokB; simplify_eq; by eauto.
        * move => j c'.
          rewrite /subst_constraints => hc'.
          apply list_lookup_fmap_inv in hc' as [c'' [-> hc']].
          rewrite /subst_constraint /=.
          apply hok in hpdefs.
          rewrite /wf_cdef_parent_ok hsuper in hpdefs.
          inv hpdefs; simplify_eq.
          by eauto.
      + assert (hC := H1).
        apply hcb in hC.
        rewrite /wf_cdef_constraints_bounded Forall_lookup in hC.
        apply hC in hc as [].
        apply inherits_using_wf in h as (? & ? & ? & hwf)=> //.
        inv hwf; simplify_eq.
        by rewrite H9.
      + assert (hC := H1).
        apply hcb in hC.
        rewrite /wf_cdef_constraints_bounded Forall_lookup in hC.
        apply hC in hc as [].
        apply inherits_using_wf in h as (? & ? & ? & hwf)=> //.
        inv hwf; simplify_eq.
        by rewrite H9.
  Qed.

  Definition wf_cdef_constraints_ok cdef :=
    ok_constraints cdef.(constraints) cdef.(constraints).

  Definition mdef_ok Δ mdef : Prop :=
    map_Forall (λ _argname, ok_ty Δ) mdef.(methodargs) ∧ ok_ty Δ mdef.(methodrettype).

  Definition cdef_methods_ok cdef :=
    map_Forall (λ _mname, mdef_ok cdef.(constraints)) cdef.(classmethods).

  (* Typing Judgements *)
  Definition is_bool_op op : bool :=
    match op with
    | LtO | GtO | EqO => true
    | PlusO | MinusO | TimesO | DivO => false
    end
  .

  Inductive expr_has_ty Δ (Γ : local_tys) (rigid: nat):
    subtype_kind → expr → lang_ty → Prop :=
    | IntTy : ∀ kd z, expr_has_ty Δ Γ rigid kd (IntE z) IntT
    | BoolTy: ∀ kd b, expr_has_ty Δ Γ rigid kd (BoolE b) BoolT
    | NullTy kd: expr_has_ty Δ Γ rigid kd NullE NullT
    | BinOpIntTy: ∀ kd op e1 e2,
        is_bool_op op = false →
        expr_has_ty Δ Γ rigid kd e1 IntT →
        expr_has_ty Δ Γ rigid kd e2 IntT →
        expr_has_ty Δ Γ rigid kd (BinOpE op e1 e2) IntT
    | BinOpBoolTy: ∀ kd op e1 e2,
        is_bool_op op = true →
        expr_has_ty Δ Γ rigid kd e1 IntT →
        expr_has_ty Δ Γ rigid kd e2 IntT →
        expr_has_ty Δ Γ rigid kd (BinOpE op e1 e2) BoolT
    | EqBoolTy: ∀ kd e1 e2,
        expr_has_ty Δ Γ rigid kd e1 BoolT →
        expr_has_ty Δ Γ rigid kd e2 BoolT →
        expr_has_ty Δ Γ rigid kd (BinOpE EqO e1 e2) BoolT
    | UniOpTy: ∀ kd e,
        expr_has_ty Δ Γ rigid kd e BoolT →
        expr_has_ty Δ Γ rigid kd (UniOpE NotO e) BoolT
    | GenTy: ∀ kd v ty,
        Γ.(ctxt) !! v = Some ty →
        expr_has_ty Δ Γ rigid kd (VarE v) ty
    | ThisTy kd: expr_has_ty Δ Γ rigid kd ThisE (this_type Γ)
    | ESubTy: ∀ kd e s t,
        expr_has_ty Δ Γ rigid kd e s →
        wf_ty t →
        bounded rigid t →
        ok_ty Δ t →
        subtype Δ kd s t →
        expr_has_ty Δ Γ rigid kd e t
    (* SD.V3 <D: is only available using explicit UpcastE *)
    | UpcastTy: ∀ kd e s t,
        expr_has_ty Δ Γ rigid kd e s →
        wf_ty t →
        bounded rigid t →
        ok_ty Δ t →
        Δ ⊢ s <D: t →
        expr_has_ty Δ Γ rigid kd (UpcastE e t) t
  .

  Definition wf_lty Γ :=
    wf_ty (this_type Γ) ∧
    map_Forall (λ _, wf_ty) Γ.(ctxt)
  .

  Lemma insert_wf_lty x ty Γ :
    wf_ty ty → wf_lty Γ → wf_lty (<[x := ty]>Γ).
  Proof.
    destruct Γ as [[lt lσ] Γ].
    rewrite /wf_lty /this_type /= => h [h0 hl]; split => //.
    rewrite map_Forall_lookup => k tk.
    rewrite lookup_insert_Some.
    case => [[? <-] | [? hk]]; first done.
    by apply hl in hk.
  Qed.

  Lemma expr_has_ty_wf Δ Γ rigid kd e ty:
    wf_lty Γ →
    expr_has_ty Δ Γ rigid kd e ty →
    wf_ty ty.
  Proof.
    move => hwf.
    induction 1 as [ | | | kd op e1 e2 hop h1 hi1 h2 hi2 |
      kd op e1 e2 hop h1 hi1 h2 hi2 | kd e1 e2 h1 hi1 h2 hi2 | kd e h hi | kd v ty h | |
      kd e s t h hi ? hb hok hsub | kd e s t h hi ? hb hok hsub]
      => //=; subst; try (by constructor).
    - by apply hwf in h.
    - by apply hwf.
  Qed.

  Definition bounded_lty n Γ :=
    bounded n (this_type Γ) ∧
    map_Forall (λ _, bounded n) Γ.(ctxt)
  .

  Lemma insert_bounded_lty n x ty Γ :
    bounded n ty → bounded_lty n Γ → bounded_lty n (<[x := ty]>Γ).
  Proof.
    destruct Γ as [[lt lσ] Γ].
    rewrite /bounded_lty /this_type /= => h [h0 hl]; split => //.
    rewrite map_Forall_lookup => k tk.
    rewrite lookup_insert_Some.
    case => [[? <-] | [? hk]]; first done.
    by apply hl in hk.
  Qed.

  Lemma bounded_lty_ge Γ n m:
    bounded_lty n Γ → m ≥ n → bounded_lty m Γ.
  Proof.
    move => [h0 /map_Forall_lookup h1] hge; split.
    - by eapply bounded_ge.
    - rewrite map_Forall_lookup => k ty h.
      apply h1 in h.
      by eapply bounded_ge.
  Qed.

  Lemma expr_has_ty_bounded Δ Γ n kd e ty:
    bounded_lty n Γ →
    expr_has_ty Δ Γ n kd e ty →
    bounded n ty.
  Proof.
    move => hb.
    induction 1 as [ | | | kd op e1 e2 hop h1 hi1 h2 hi2 |
      kd op e1 e2 hop h1 hi1 h2 hi2 | kd e1 e2 h1 hi1 h2 hi2 | kd e h hi | kd v ty h | |
      kd e s t h hi ? ? hok hsub | kd e s t h hi ? ? hok hsub]
      => //=; subst; try (by constructor).
    - by apply hb in h.
    - by apply hb.
  Qed.

  (* For runtime check, we want to introduce fresh new generic types,
   * and keep their constraints around. To this purpose, we need
   * to 'lift' constraints deBruijn to match the right indexes.
   *)
  Fixpoint lift_ty n (ty: lang_ty) : lang_ty :=
    match ty with
    | ClassT t σ => ClassT t (lift_ty n <$> σ)
    | UnionT s t => UnionT (lift_ty n s) (lift_ty n t)
    | InterT s t => InterT (lift_ty n s) (lift_ty n t)
    | GenT k => GenT (k + n)
    | IntT | BoolT | NothingT | MixedT | NullT |
      NonNullT | DynamicT | SupportDynT => ty
    end.

  Lemma lift_ty_wf ty: ∀ n, wf_ty ty → wf_ty (lift_ty n ty).
  Proof.
    induction ty as [ | | | | t σ hi | | | s t hs ht |
        s t hs ht | k | | ] => n h //=.
    - inv h.
      econstructor => //.
      + by rewrite map_length.
      + move => k ty h.
        apply list_lookup_fmap_inv in h as [ty' [-> h]].
        rewrite Forall_lookup in hi.
        by eauto.
    - inv h; constructor; by eauto.
    - inv h; constructor; by eauto.
  Qed.

  Lemma lift_ty_bounded ty: ∀ n m, bounded m ty → bounded (n + m) (lift_ty n ty).
  Proof.
    induction ty as [ | | | | t σ hi | | | s t hs ht |
        s t hs ht | k | | ] => n m h //=.
    - inv h.
      constructor => //.
      rewrite Forall_lookup => k ty h.
      apply list_lookup_fmap_inv in h as [ty' [-> h]].
      rewrite Forall_lookup in hi.
      rewrite Forall_lookup in H0.
      by eauto.
    - inv h; constructor; by eauto.
    - inv h; constructor; by eauto.
    - inv h; constructor.
      by lia.
  Qed.

  Definition lift_constraint n c := (lift_ty n c.1, lift_ty n c.2).

  Definition lift_constraints n (Δ : list constraint) :=
    lift_constraint n <$> Δ.

  Lemma lift_constraints_wf n Δ:
    Forall wf_constraint Δ → Forall wf_constraint (lift_constraints n Δ).
  Proof.
    move => /Forall_lookup h.
    rewrite Forall_lookup => k ty hty.
    apply list_lookup_fmap_inv in hty as [ty' [-> hty]].
    apply h in hty as [].
    split; by apply lift_ty_wf.
  Qed.

  Lemma lift_constraints_bounded m n Δ:
    Forall (bounded_constraint m) Δ →
    Forall (bounded_constraint (n + m)) (lift_constraints n Δ).
  Proof.
    move => /Forall_lookup h.
    rewrite Forall_lookup => k ty hty.
    apply list_lookup_fmap_inv in hty as [ty' [-> hty]].
    apply h in hty as [].
    split; by apply lift_ty_bounded.
  Qed.

  (* continuation-based typing for commands.
   * Δ is the set of constraints S <: T of the current class
   * and C is the tag of the current class (for `private` related checks)
   *
   * Note on Getter/Setter visibility check:
   * if `e` has type `C<σ>` and we are typing `e->x`.
   *
   * For private access, we must make sure the current enclosing class
   * is where the member is defined, and the member can only be accessed
   * via `This`
   *)
  Inductive cmd_has_ty (C : tag) : list constraint → subtype_kind → nat → local_tys → cmd → local_tys → Prop :=
    | SkipTy: ∀ Γ Δ kd rigid, cmd_has_ty C Δ kd rigid Γ SkipC Γ
    | ErrorTy: ∀ Δ kd rigid Γ0 Γ1,
        wf_lty Γ1 → bounded_lty rigid Γ1 → cmd_has_ty C Δ kd rigid Γ0 ErrorC Γ1
    | SeqTy: ∀ Δ kd rigid Γ1 Γ2 Γ3 fstc sndc,
        cmd_has_ty C Δ kd rigid Γ1 fstc Γ2 →
        cmd_has_ty C Δ kd rigid Γ2 sndc Γ3 →
        cmd_has_ty C Δ kd rigid Γ1 (SeqC fstc sndc) Γ3
    | LetTy: ∀ Δ kd rigid Γ lhs e ty,
        expr_has_ty Δ Γ rigid kd e ty →
        cmd_has_ty C Δ kd rigid Γ (LetC lhs e) (<[lhs := ty]>Γ)
    | IfTy: ∀ Δ kd rigid Γ1 Γ2 cond thn els,
        expr_has_ty Δ Γ1 rigid kd cond BoolT →
        cmd_has_ty C Δ kd rigid Γ1 thn Γ2 →
        cmd_has_ty C Δ kd rigid Γ1 els Γ2 →
        cmd_has_ty C Δ kd rigid Γ1 (IfC cond thn els) Γ2
    | GetPrivTy: ∀ Δ kd rigid Γ lhs t σ name fty,
        type_of_this Γ = (t, σ) →
        has_field name t Private fty C →
        cmd_has_ty C Δ kd rigid Γ (GetC lhs ThisE name) (<[lhs := subst_ty σ fty]>Γ)
    | GetPubTy: ∀ Δ kd rigid Γ lhs recv t σ name fty orig,
        expr_has_ty Δ Γ rigid kd recv (ClassT t σ) →
        has_field name t Public fty orig →
        cmd_has_ty C Δ kd rigid Γ (GetC lhs recv name) (<[lhs := subst_ty σ fty]>Γ)
    | SetPrivTy: ∀ Δ kd rigid Γ fld rhs fty t σ,
        type_of_this Γ = (t, σ) →
        has_field fld t Private fty C →
        expr_has_ty Δ Γ rigid kd rhs (subst_ty σ fty) →
        cmd_has_ty C Δ kd rigid Γ (SetC ThisE fld rhs) Γ
    | SetPubTy: ∀ Δ kd rigid Γ recv fld rhs fty orig t σ,
        expr_has_ty Δ Γ rigid kd recv (ClassT t σ) →
        has_field fld t Public fty orig →
        expr_has_ty Δ Γ rigid kd rhs (subst_ty σ fty) →
        cmd_has_ty C Δ kd rigid Γ (SetC recv fld rhs) Γ
    | NewTy: ∀ Δ kd rigid Γ lhs t targs args fields,
        wf_ty (ClassT t targs) →
        bounded rigid (ClassT t targs) →
        ok_ty Δ (ClassT t targs) →
        has_fields t fields →
        dom fields = dom args →
        (∀ f fty arg,
        fields !! f = Some fty →
        args !! f = Some arg →
        expr_has_ty Δ Γ rigid kd arg (subst_ty targs fty.1.2)) →
        cmd_has_ty C Δ kd rigid Γ (NewC lhs t targs args) (<[lhs := ClassT t targs]>Γ)
    | CallTy: ∀ Δ kd rigid Γ lhs recv t targs name orig mdef args,
        expr_has_ty Δ Γ rigid kd recv (ClassT t targs) →
        has_method name t orig mdef →
        dom mdef.(methodargs) = dom args →
        (∀ x ty arg,
        mdef.(methodargs) !! x = Some ty →
        args !! x = Some arg →
        expr_has_ty Δ Γ rigid kd arg (subst_ty targs ty)) →
        cmd_has_ty C Δ kd rigid Γ (CallC lhs recv name args) (<[lhs := subst_ty targs mdef.(methodrettype)]>Γ)
    | SubTy: ∀ Δ kd rigid Γ c Γ0 Γ1,
        lty_sub Δ kd Γ1 Γ0 →
        bounded_lty rigid Γ0 →
        cmd_has_ty C Δ kd rigid Γ c Γ1 →
        cmd_has_ty C Δ kd rigid Γ c Γ0
    | TagCheckTy Δ kd rigid Γ0 Γ1 v tv t def thn els:
        Γ0.(ctxt) !! v = Some tv →
        pdefs !! t = Some def →
        cmd_has_ty C (lift_constraints rigid def.(constraints) ++ Δ) kd (rigid + length def.(generics))
          (<[v:=InterT tv (ClassT t (map GenT (seq rigid (length def.(generics)))))]> Γ0) thn Γ1 →
        (* Important note:
         * we use to have the following condition:
         *
         * ∀ k ty, Γ1.(ctxt)!! k = Some ty → bounded rigid ty
         *
         * but because of the else branch, if Γ0 is bounded by
         * rigid, then Γ1 must be bounded by rigid too. Which means the
         * then branch has too prune/weaken its type to remove all occurrences
         * of the fresh types from Γ1
         *)
        cmd_has_ty C Δ kd rigid Γ0 els Γ1 →
        cmd_has_ty C Δ kd rigid Γ0 (RuntimeCheckC v (RCTag t) thn els) Γ1
    | IntCheckTy Δ kd rigid Γ0 Γ1 v tv thn els:
        Γ0.(ctxt) !! v = Some tv →
        cmd_has_ty C Δ kd rigid (<[v:=InterT tv IntT]> Γ0) thn Γ1 →
        cmd_has_ty C Δ kd rigid Γ0 els Γ1 →
        cmd_has_ty C Δ kd rigid Γ0 (RuntimeCheckC v RCInt thn els) Γ1
    | BoolCheckTy Δ kd rigid Γ0 Γ1 v tv thn els:
        Γ0.(ctxt) !! v = Some tv →
        cmd_has_ty C Δ kd rigid (<[v:=InterT tv BoolT]> Γ0) thn Γ1 →
        cmd_has_ty C Δ kd rigid Γ0 els Γ1 →
        cmd_has_ty C Δ kd rigid Γ0 (RuntimeCheckC v RCBool thn els) Γ1
    | NullCheckTy Δ kd rigid Γ0 Γ1 v tv thn els:
        Γ0.(ctxt) !! v = Some tv →
        cmd_has_ty C Δ kd rigid (<[v:=InterT tv NullT]> Γ0) thn Γ1 →
        cmd_has_ty C Δ kd rigid Γ0 els Γ1 →
        cmd_has_ty C Δ kd rigid Γ0 (RuntimeCheckC v RCNull thn els) Γ1
    | NonNullCheckTy Δ kd rigid Γ0 Γ1 v tv thn els:
        Γ0.(ctxt) !! v = Some tv →
        cmd_has_ty C Δ kd rigid (<[v:=InterT tv NonNullT]> Γ0) thn Γ1 →
        cmd_has_ty C Δ kd rigid Γ0 els Γ1 →
        cmd_has_ty C Δ kd rigid Γ0 (RuntimeCheckC v RCNonNull thn els) Γ1
    (* Dynamic related typing rules *)
    | DynIfTy: ∀ Δ kd rigid Γ1 Γ2 cond thn els,
        expr_has_ty Δ Γ1 rigid kd cond DynamicT →
        cmd_has_ty C Δ kd rigid Γ1 thn Γ2 →
        cmd_has_ty C Δ kd rigid Γ1 els Γ2 →
        cmd_has_ty C Δ kd rigid Γ1 (IfC cond thn els) Γ2
    | DynGetTy : ∀ Δ kd rigid Γ lhs recv name,
        expr_has_ty Δ Γ rigid kd recv DynamicT →
        (match recv with
         | ThisE => False
         | _ => True
         end
        ) →
        cmd_has_ty C Δ kd rigid Γ (GetC lhs recv name) (<[lhs := DynamicT]>Γ)
    | DynSetTy : ∀ Δ kd rigid Γ recv fld rhs,
        expr_has_ty Δ Γ rigid kd recv DynamicT →
        expr_has_ty Δ Γ rigid kd rhs DynamicT →
        (match recv with
         | ThisE => False
         | _ => True
         end) →
        cmd_has_ty C Δ kd rigid Γ (SetC recv fld rhs) Γ
    | DynCallTy: ∀ Δ kd rigid Γ lhs recv name (args: stringmap expr),
        expr_has_ty Δ Γ rigid kd recv DynamicT →
        (∀ x arg, args !! x = Some arg →
          expr_has_ty Δ Γ rigid kd arg DynamicT) →
        (match recv with
         | ThisE => False
         | _ => True
         end) →
        cmd_has_ty C Δ kd rigid Γ (CallC lhs recv name args) (<[lhs := DynamicT]>Γ)
  .

  Lemma cmd_has_ty_wf C Δ kd rigid Γ0 cmd Γ1:
    map_Forall (λ _ : string, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _ : string, wf_cdef_fields_wf) pdefs →
    map_Forall (λ _ : string, wf_cdef_methods_wf) pdefs →
    Forall wf_constraint Δ →
    wf_lty Γ0 →
    cmd_has_ty C Δ kd rigid Γ0 cmd Γ1 →
    wf_lty Γ1.
  Proof.
    move => hp hfields hmethods hΔ [hthis hwf].
    induction 1 as [ | ?????? | ???????? h1 hi1 h2 hi2 | ??????? he |
      ???????? he h1 hi1 h2 hi2 | ????????? he hf | ??????????? he hf |
      ????????? he hf hr | ??????????? he hf hr | ????????? ht hb hok hf hdom hargs |
      ???????????? he hm hdom hargs |
      ??????? hsub hb h hi | ??????????? hin hdef hthn hi0 hels hi1 |
      ????????? hin hthn hi0 hels hi1 | ????????? hin hthn hi0 hels hi1 |
      ????????? hin hthn hi0 hels hi1 | ????????? hin hthn hi0 helse hi1 |
      ???????? hcond hthn hi1 hels hi2 | ??????? he hnotthis |
      ??????? hrecv hrhs hnotthis | ???????? he hargs hnotthis
      ] => //=; try (by eauto).
    - apply hi2 => //.
      + by apply hi1.
      + by apply hi1.
    - apply insert_wf_lty => //.
      by apply expr_has_ty_wf in he.
    - apply insert_wf_lty => //.
      apply wf_ty_subst; last by apply has_field_wf in hf.
      destruct Γ as [[? ?] Γ].
      rewrite /this_type /= in hthis, he.
      simplify_eq.
      by apply wf_ty_class_inv in hthis.
    - apply insert_wf_lty => //.
      apply wf_ty_subst; last by apply has_field_wf in hf.
      apply expr_has_ty_wf in he => //.
      by apply wf_ty_class_inv in he.
    - split; first by apply hthis.
      by apply map_Forall_insert_2.
    - split; first by apply hthis.
      apply map_Forall_insert_2 => //.
      apply has_method_wf in hm => //.
      destruct hm as [hargs' hret'].
      apply wf_ty_subst => //.
      apply expr_has_ty_wf in he => //.
      by apply wf_ty_class_inv in he.
    - apply hi in hwf as [hthis' hwf] => //; clear hi h.
      destruct hsub as [h0 h1].
      split; first by rewrite -h0.
      rewrite map_Forall_lookup => k ty hty.
      apply h1 in hty.
      destruct hty as [ty' [ hty' hsub']].
      apply hwf in hty'.
      by eapply subtype_wf.
    - by apply insert_wf_lty.
    - by apply insert_wf_lty.
  Qed.

  Lemma cmd_has_ty_bounded C Δ kd rigid Γ0 cmd Γ1:
    map_Forall (λ _ : string, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _ : string, wf_cdef_fields_wf) pdefs →
    map_Forall (λ _ : string, wf_cdef_methods_wf) pdefs →
    map_Forall (λ _ : string, wf_cdef_fields_bounded) pdefs →
    map_Forall (λ _ : string, cdef_methods_bounded) pdefs →
    Forall wf_constraint Δ →
    wf_lty Γ0 →
    bounded_lty rigid Γ0 →
    cmd_has_ty C Δ kd rigid Γ0 cmd Γ1 →
    bounded_lty rigid Γ1.
  Proof.
    move => hp ?? hfields hmethods hΔ hwf [hthis hb].
    induction 1 as [ | ?????? | ???????? h1 hi1 h2 hi2 | ??????? he |
      ???????? he h1 hi1 h2 hi2 | ????????? he hf | ??????????? he hf |
      ????????? he hf hr | ??????????? he hf hr | ????????? ht htb hok hf hdom hargs |
      ???????????? he hm hdom hargs |
      ??????? hsub hΓb h hi | ??????????? hin hdef hthn hi0 hels hi1 |
      ????????? hin hthn hi0 hels hi1 | ????????? hin hthn hi0 hels hi1 |
      ????????? hin hthn hi0 hels hi1 | ????????? hin hthn hi0 helse hi1 |
      ???????? hcond hthn hi1 hels hi2 | ??????? he hnotthis |
      ??????? hrecv hrhs hnotthis | ???????? he hargs hnotthis
      ] => //=; try (by eauto).
    - apply hi2 => //.
      + by apply cmd_has_ty_wf in h1.
      + by apply hi1.
      + by apply hi1.
    - apply insert_bounded_lty => //.
      by apply expr_has_ty_bounded in he.
    - apply insert_bounded_lty => //.
      apply has_field_bounded in hf => //.
      destruct hf as (def & hdef & hbfty).
      destruct Γ as [[tt σt] Γ].
      injection he; intros; subst; clear he.
      apply bounded_subst with (length def.(generics)) => //.
      + destruct hwf as [hwf ?].
        rewrite /this_type /= in hwf.
        inv hwf.
        by simplify_eq.
      + rewrite /this_type /= in hthis.
        by inv hthis.
    - apply insert_bounded_lty => //.
      apply has_field_bounded in hf => //.
      destruct hf as (def & hdef & hbfty).
      apply bounded_subst with (length def.(generics)) => //.
      + apply expr_has_ty_wf in he => //.
        inv he.
        by simplify_eq.
      + apply expr_has_ty_bounded in he => //.
        inv he.
        by simplify_eq.
    - by apply insert_bounded_lty.
    - split; first by apply hthis.
      apply map_Forall_insert_2 => //.
      apply has_method_from_def in hm => //.
      destruct hm as (odef & m & hodef & hmdef & hm & [σ [hin ->]]).
      assert (he' := he).
      apply expr_has_ty_wf in he' => //.
      inv he'.
      rewrite /subst_mdef /=.
      apply bounded_subst with (length def.(generics)) => //.
      + apply bounded_subst with (length odef.(generics)) => //.
        * apply hmethods in hodef.
          apply hodef in hmdef.
          by apply hmdef.
        * apply inherits_using_wf in hin => //.
          destruct hin as (? & ? & ? & h); simplify_eq.
          inv h; by simplify_eq.
        * apply inherits_using_wf in hin => //.
          by destruct hin as (? & ? & h & ?); simplify_eq.
      + apply expr_has_ty_bounded in he => //.
        by inv he.
    - by apply insert_bounded_lty.
    - by apply insert_bounded_lty.
  Qed.

  (* Consider a class C<T0, ..., Tn>,
   * method bodies must be well-formed under a generic substitution mapping
   * Ti -> Ti.
   *)
  Definition wf_mdef_ty tag Δ rigid σ mdef :=
    ∃ Γ',
    wf_lty Γ' ∧
    cmd_has_ty tag Δ Plain rigid
      {| type_of_this := (tag, σ); ctxt := mdef.(methodargs) |}
      mdef.(methodbody) Γ' ∧
    expr_has_ty Δ Γ' rigid Plain mdef.(methodret) mdef.(methodrettype)
  .

  Definition cdef_wf_mdef_ty cname cdef :=
    let n := length cdef.(generics) in
    let σ := gen_targs n in
    map_Forall (λ _mname mdef, wf_mdef_ty cname cdef.(constraints) n σ mdef) cdef.(classmethods)
  .

  (* Checks related to support dynamic *)
  Definition to_dyn (ty: lang_ty) : lang_ty := DynamicT.

  Definition wf_mdef_dyn_ty tag Δ rigid σ mdef :=
    ∃ Γ',
    wf_lty Γ' ∧
    cmd_has_ty tag Δ Aware rigid
      {| type_of_this := (tag, σ); ctxt := to_dyn <$> mdef.(methodargs) |}
      mdef.(methodbody) Γ' ∧
    expr_has_ty Δ Γ' rigid Aware mdef.(methodret) (to_dyn mdef.(methodrettype))
  .

  Definition wf_cdef_methods_dyn_wf cname cdef :=
    if cdef.(support_dynamic) then
    ∀ mname orig mdef,
    has_method mname cname orig mdef → mdef.(method_support_dynamic) = true
    else True
  .

  Definition cdef_wf_mdef_dyn_ty cname cdef :=
    let n := length cdef.(generics) in
    let σ := gen_targs n in 
    map_Forall (λ _ mdef,
      if mdef.(method_support_dynamic) then
        wf_mdef_dyn_ty cname cdef.(constraints) n σ mdef
      else True) cdef.(classmethods)
  .

  Definition wf_field_dyn_wf Δ (vfty: ((visibility * lang_ty) * tag)) :=
    match vfty.1 with
    | (Private, _) => True
    | (Public, fty) =>
        Δ ⊢ fty <D: DynamicT ∧ Δ ⊢ DynamicT <D: fty
    end.

  Definition wf_cdef_fields_dyn_wf cname cdef :=
    if cdef.(support_dynamic) then
    ∀ fields, has_fields cname fields →
    map_Forall (λ _fname vfty, wf_field_dyn_wf cdef.(constraints) vfty) fields
    else True.

  Definition wf_cdef_dyn_parent cdef :=
    match cdef.(superclass) with
    | Some (parent, _) =>
        ∀ def, pdefs !! parent = Some def →
        def.(support_dynamic) = true →
        cdef.(support_dynamic) = true
    | None => True
    end.

  Lemma extends_using_dyn_parent A B σ:
    map_Forall (λ _, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _, wf_cdef_dyn_parent) pdefs →
    extends_using A B σ →
    ∃ adef bdef,
      pdefs !! A = Some adef ∧
      pdefs !! B = Some bdef ∧
      (bdef.(support_dynamic) = true → adef.(support_dynamic) = true).
  Proof.
    move => hp hwf hext.
    assert (h0 := hext).
    apply extends_using_wf in h0 => //.
    destruct h0 as (adef & hadef & _ & h).
    inv h.
    destruct hext as [A B adef' σ hadef' hsuper]; simplify_eq.
    exists adef', def; repeat split => //.
    apply hwf in hadef'.
    rewrite /wf_cdef_dyn_parent hsuper in hadef'.
    by apply hadef'.
  Qed.

  Lemma inherits_using_dyn_parent A B σ:
    map_Forall (λ _, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _, wf_cdef_dyn_parent) pdefs →
    inherits_using A B σ →
    ∃ adef bdef,
      pdefs !! A = Some adef ∧
      pdefs !! B = Some bdef ∧
      (bdef.(support_dynamic) = true → adef.(support_dynamic) = true).
  Proof.
    move => hp hwf.
    induction 1 as [ A adef hpdefs | A B σ hext | A B σ C σC hext h hi ].
    - exists adef, adef.
      by repeat split => //.
    - by apply extends_using_dyn_parent in hext.
    - apply extends_using_dyn_parent in hext as (adef & bdef & ? & ? & h0) => //.
      destruct hi as (bdef' & cdef & ? & ? & h1); simplify_eq.
      exists adef, cdef; repeat split => //.
      move => ?; by eauto.
  Qed.

  (* Collection of all program invariant (at the source level):
   * - no cycle (we have a forest)
   * - every type is well-formed/bounded
   * - every substitution's domain/codomain is valid
   * - variance is checked
   *)
  Record wf_cdefs (prog: stringmap classDef) := {
    wf_extends_wf : wf_no_cycle prog;
    wf_parent : map_Forall (λ _cname, wf_cdef_parent prog) prog;
    wf_parent_ok : map_Forall (λ _cname, wf_cdef_parent_ok) prog;
    wf_constraints_wf : map_Forall (λ _cname, wf_cdef_constraints_wf) prog;
    wf_constraints_ok : map_Forall (λ _cname, wf_cdef_constraints_ok) prog;
    wf_constraints_bounded : map_Forall (λ _cname, wf_cdef_constraints_bounded) prog;
    wf_override : wf_method_override prog;
    wf_fields : map_Forall (λ _cname, wf_cdef_fields) prog;
    wf_fields_bounded : map_Forall (λ _cname, wf_cdef_fields_bounded) prog;
    wf_fields_wf  : map_Forall (λ _cname, wf_cdef_fields_wf) prog;
    (* because all public fields are mutable *)
    wf_fields_mono : map_Forall (λ _cname, wf_field_mono) prog;
    wf_methods_bounded : map_Forall (λ _cname, cdef_methods_bounded) prog;
    wf_methods_wf : map_Forall (λ _cname, wf_cdef_methods_wf) prog;
    wf_methods_mono : map_Forall (λ _cname, wf_cdef_methods_mono) prog;
    wf_methods_ok : map_Forall (λ _cname, cdef_methods_ok) prog;
    wf_mdefs : map_Forall cdef_wf_mdef_ty prog;
    wf_mono : map_Forall (λ _cname, wf_cdef_mono) prog;
    (* Dynamic related invariant *)
    wf_fields_dyn : map_Forall wf_cdef_fields_dyn_wf prog;
    wf_dyn_parent: map_Forall (λ _cname, wf_cdef_dyn_parent) prog;
    wf_methods_dyn : map_Forall wf_cdef_methods_dyn_wf prog;
    wf_mdefs_dyn : map_Forall cdef_wf_mdef_dyn_ty prog;
  }
  .
End Typing.
