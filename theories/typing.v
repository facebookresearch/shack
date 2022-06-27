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

  (* Helping the inference with this notation that hides Δ *)
  Local Notation "Γ ⊢ s <: t" := (@subtype _ Γ Plain s t) (at level 70, s at next level, no associativity).
  Local Notation "Γ ⊢ s <D: t" := (@subtype _ Γ Aware s t) (at level 70, s at next level, no associativity).

  (* At class + substitution is `ok` w.r.t. to a set of constraints `Γ` if
   * - all the types in the substitution are ok
   * - all the constraints of that class are satisfied.
   *)
  Inductive ok_ty (Γ: list constraint) : lang_ty → Prop :=
    | OkInt: ok_ty Γ IntT
    | OkBool: ok_ty Γ BoolT
    | OkNothing: ok_ty Γ NothingT
    | OkMixed: ok_ty Γ MixedT
    | OkClass t σ def:
        (∀ i ty, σ !! i = Some ty → ok_ty Γ ty) →
        Δ !! t = Some def →
        (∀ i c, def.(constraints) !! i = Some c → Γ ⊢ (subst_ty σ c.1) <D: (subst_ty σ c.2)) →
        ok_ty Γ (ClassT t σ)
    | OkNull: ok_ty Γ NullT
    | OkNonNull: ok_ty Γ NonNullT
    | OkUnion s t: ok_ty Γ s → ok_ty Γ t → ok_ty Γ (UnionT s t)
    | OkInter s t: ok_ty Γ s → ok_ty Γ t → ok_ty Γ (InterT s t)
    | OkGen n: ok_ty Γ (GenT n)
    | OkEx t: ok_ty Γ (ExT t)
    | OkDynamic : ok_ty Γ DynamicT
    | OkSupportDyn : ok_ty Γ SupportDynT
  .

  Lemma ok_ty_constraint_elim_ G T:
    ok_ty G T →
    ∀ Γ Γ', G = Γ ++ Γ' →
    (∀ i c, Γ' !! i = Some c → Γ ⊢ c.1 <D: c.2) →
    ok_ty Γ T.
  Proof.
    induction 1 as [ | | | | t σ def hσ hi hdef hconstr
    | | | s t hs hi ht hit | s t hs hi ht hit | | | | ] => Γ Γ' heq hΓ; subst; try by constructor.
    - apply OkClass with def => //.
      + move => i ty h; by eapply hi.
      + move => i c h.
        apply subtype_constraint_elim with Γ'; by eauto.
    - constructor; by eauto.
    - constructor; by eauto.
  Qed.

  Lemma ok_ty_constraint_elim Γ Γ' T:
    ok_ty (Γ ++ Γ') T →
    (∀ i c, Γ' !! i = Some c → Γ ⊢ c.1 <D: c.2) →
    ok_ty Γ T.
  Proof. intros; by eapply ok_ty_constraint_elim_. Qed.

  Lemma ok_ty_weaken Γ t: ok_ty Γ t → ∀ Γ', Γ ⊆ Γ' → ok_ty Γ' t.
  Proof.
    induction 1 as [ | | | | t σ def hσ hi hdef hconstr
    | | | s t hs hi ht hit | s t hs hi ht hit | n | t | | ] => Γ' hincl; try by constructor.
    - apply OkClass with def => //.
      + move => i ty h; by apply hi with i.
      + move => i c h.
        apply subtype_weaken with Γ; by eauto.
    - constructor; by eauto.
    - constructor; by eauto.
  Qed.

  Lemma ok_ty_class_inv Γ t σ: ok_ty Γ (ClassT t σ) → Forall (ok_ty Γ) σ.
  Proof.
    move => h; inv h.
    apply Forall_forall => x hin.
    apply elem_of_list_lookup_1 in hin as [i hin].
    by eauto.
  Qed.

  Lemma ok_ty_subst Γ t:
    map_Forall (λ _, wf_cdef_parent Δ) Δ →
    map_Forall (λ _, wf_cdef_constraints_bounded) Δ →
    ok_ty Γ t →
    wf_ty t →
    ∀ Γ' σ, Forall wf_ty σ →
         Forall (ok_ty Γ') σ →
         ok_ty (Γ' ++ (subst_constraints σ Γ)) (subst_ty σ t).
  Proof.
    move => hwp hcb.
    induction 1 as [ | | | | t σt def hσt hi hdef hconstr
    | | | s t hs his ht hit | s t hs his ht hit | n | t | | ]
    => hwf Γ' σ hwfσ hokσ /=; try (constructor; by eauto).
    - apply OkClass with def => //.
      + move => i ty h.
        apply list_lookup_fmap_inv in h as [ty' [-> h]].
        apply wf_ty_class_inv in hwf.
        apply hi with i => //.
        rewrite Forall_forall in hwf.
        apply elem_of_list_lookup_2 in h.
        by apply hwf in h.
      + move => i c h.
        assert (hdef' := hdef).
        apply hcb in hdef'.
        rewrite /wf_cdef_constraints_bounded Forall_forall in hdef'.
        assert (h' := h).
        apply elem_of_list_lookup_2 in h.
        apply hdef' in h as [].
        apply subtype_weaken with (subst_constraints σ Γ); last by set_solver.
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
      rewrite Forall_forall in hokσ.
      apply elem_of_list_lookup_2 in hty.
      apply ok_ty_weaken with Γ'; first by apply hokσ.
      by set_solver.
  Qed.

  Definition ok_constraint Γ (c: constraint) :=
    ok_ty Γ c.1 ∧ ok_ty Γ c.2.

  Definition ok_constraints Γ G := Forall (ok_constraint Γ) G.

  Definition wf_cdef_parent_ok cdef :=
    match cdef.(superclass) with
    | None => True
    | Some (parent, σ) =>
        ok_ty cdef.(constraints) (ClassT parent σ)
    end
  .

  Lemma extends_using_ok A B σ:
    map_Forall (λ _cname, wf_cdef_parent_ok) Δ →
    extends_using A B σ →
    ∃ adef,
    Δ !! A = Some adef ∧
    ok_ty adef.(constraints) (ClassT B σ).
  Proof.
    move => hok h.
    destruct h as [A B adef σ hΔ hsuper].
    exists adef; split => //.
    apply hok in hΔ.
    by rewrite /wf_cdef_parent_ok hsuper in hΔ.
  Qed.

  Lemma gen_targs_ok Γ n:
    ∀ i ty, gen_targs n !! i = Some ty →
    ok_ty Γ ty.
  Proof.
    move => i ty /lookup_gen_targs ->.
    by constructor.
  Qed.

  Lemma ok_ty_trans Γ ty:
    ok_ty Γ ty →
    ∀ Γ',
    (∀ i c, Γ !! i = Some c → Γ' ⊢ c.1 <D: c.2) →
    ok_ty Γ' ty.
  Proof.
    induction 1 as [ | | | | t σ def hσ hi hdef hconstr
    | | | s t hs hi ht hit | s t hs hi ht hit | n | t | | ] => Γ' hΓ; try by constructor.
    - econstructor => //.
      + move => k ty hk; by eauto.
      + move => k c' hc'.
        apply hconstr in hc'.
        apply subtype_constraint_trans with Γ; by eauto.
    - constructor; by eauto.
    - constructor; by eauto.
  Qed.

  Lemma inherits_using_ok A B σ:
    map_Forall (λ _ : string, wf_cdef_parent Δ) Δ →
    map_Forall (λ _cname, wf_cdef_parent_ok) Δ →
    map_Forall (λ _ : string, wf_cdef_constraints_bounded) Δ →
    inherits_using A B σ →
    ∃ adef,
    Δ !! A = Some adef ∧
    ok_ty adef.(constraints) (ClassT B σ).
  Proof.
    move => hp hok hcb.
    induction 1 as [ A adef hΔ | A B σ hext | A B σ C σC hext h hi ].
    - exists adef; split => //.
      econstructor => //.
      + by apply gen_targs_ok.
      + move => i c hc.
        rewrite !subst_ty_id.
        * constructor.
          apply elem_of_list_lookup.
          exists i; by rewrite hc {1}(surjective_pairing c).
        * apply hcb in hΔ.
          rewrite /wf_cdef_constraints_bounded Forall_forall in hΔ.
          apply elem_of_list_lookup_2 in hc.
          by apply hΔ in hc as [].
        * apply hcb in hΔ.
          rewrite /wf_cdef_constraints_bounded Forall_forall in hΔ.
          apply elem_of_list_lookup_2 in hc.
          by apply hΔ in hc as [].
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
      destruct hext as [A B adef σ hΔ hsuper].
      exists adef; split => //.
      econstructor => //.
      { move => i ty hi.
        apply list_lookup_fmap_inv in hi as [ty' [-> hi]].
        eapply ok_ty_trans.
        + eapply ok_ty_subst => //.
          { inv hokB; by eauto. }
          { by eauto. }
          { by apply wf_ty_class_inv in hwfB. }
          apply hok in hΔ.
          rewrite /wf_cdef_parent_ok hsuper in hΔ.
          by apply ok_ty_class_inv in hΔ.
        + move => j c.
          rewrite lookup_app_Some.
          case => [hc | [? ]].
          * apply SubConstraint.
            apply elem_of_list_lookup_2 in hc.
            by rewrite -surjective_pairing.
          * rewrite /subst_constraints => hc.
            apply list_lookup_fmap_inv in hc as [c' [-> hc]].
            rewrite /subst_constraint /=.
            apply hok in hΔ.
            rewrite /wf_cdef_parent_ok hsuper in hΔ.
            inv hΔ; simplify_eq.
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
          apply hok in hΔ.
          rewrite /wf_cdef_parent_ok hsuper in hΔ.
          inv hΔ; simplify_eq.
          by eauto.
      + assert (hC := H1).
        apply hcb in hC.
        rewrite /wf_cdef_constraints_bounded Forall_forall in hC.
        apply elem_of_list_lookup_2 in hc.
        apply hC in hc as [].
        apply inherits_using_wf in h as (? & ? & ? & hwf)=> //.
        inv hwf; simplify_eq.
        by rewrite H9.
      + assert (hC := H1).
        apply hcb in hC.
        rewrite /wf_cdef_constraints_bounded Forall_forall in hC.
        apply elem_of_list_lookup_2 in hc.
        apply hC in hc as [].
        apply inherits_using_wf in h as (? & ? & ? & hwf)=> //.
        inv hwf; simplify_eq.
        by rewrite H9.
  Qed.

  Definition wf_cdef_constraints_ok cdef :=
    ok_constraints cdef.(constraints) cdef.(constraints).

  Definition mdef_ok Γ mdef : Prop :=
    map_Forall (λ _argname, ok_ty Γ) mdef.(methodargs) ∧ ok_ty Γ mdef.(methodrettype).

  Definition cdef_methods_ok cdef :=
    map_Forall (λ _mname, mdef_ok cdef.(constraints)) cdef.(classmethods).

  (* Typing Judgements *)
  Definition is_bool_op op : bool :=
    match op with
    | LtO | GtO | EqO => true
    | PlusO | MinusO | TimesO | DivO => false
    end
  .

  Inductive expr_has_ty Γ (lty : local_tys):
    subtype_kind → expr → lang_ty → Prop :=
    | IntTy : ∀ kd z, expr_has_ty Γ lty kd (IntE z) IntT
    | BoolTy: ∀ kd b, expr_has_ty Γ lty kd (BoolE b) BoolT
    | NullTy kd: expr_has_ty Γ lty kd NullE NullT
    | BinOpIntTy: ∀ kd op e1 e2,
        is_bool_op op = false →
        expr_has_ty Γ lty kd e1 IntT →
        expr_has_ty Γ lty kd e2 IntT →
        expr_has_ty Γ lty kd (BinOpE op e1 e2) IntT
    | BinOpBoolTy: ∀ kd op e1 e2,
        is_bool_op op = true →
        expr_has_ty Γ lty kd e1 IntT →
        expr_has_ty Γ lty kd e2 IntT →
        expr_has_ty Γ lty kd (BinOpE op e1 e2) BoolT
    | EqBoolTy: ∀ kd e1 e2,
        expr_has_ty Γ lty kd e1 BoolT →
        expr_has_ty Γ lty kd e2 BoolT →
        expr_has_ty Γ lty kd (BinOpE EqO e1 e2) BoolT
    | UniOpTy: ∀ kd e,
        expr_has_ty Γ lty kd e BoolT →
        expr_has_ty Γ lty kd (UniOpE NotO e) BoolT
    | GenTy: ∀ kd v ty,
        lty.(ctxt) !! v = Some ty →
        expr_has_ty Γ lty kd (VarE v) ty
    | ThisTy kd: expr_has_ty Γ lty kd ThisE (this_type lty)
    | ESubTy: ∀ kd e s t,
        expr_has_ty Γ lty kd e s →
        wf_ty t →
        ok_ty Γ t →
        subtype Γ kd s t →
        expr_has_ty Γ lty kd e t
    (* SD.V3 <D: is only available using explicit UpcastE *)
    | UpcastTy: ∀ kd e s t,
        expr_has_ty Γ lty kd e s →
        wf_ty t →
        ok_ty Γ t →
        Γ ⊢ s <D: t →
        expr_has_ty Γ lty kd (UpcastE e t) t
  .

  Lemma expr_has_ty_constraint_elim_ G kd lty e ty:
    expr_has_ty G lty kd e ty →
    ∀ Γ Γ', G = Γ ++ Γ' →
    (∀ i c, Γ' !! i = Some c → Γ ⊢ c.1 <D: c.2) →
    expr_has_ty Γ lty kd e ty.
  Proof.
    induction 1 as [ | | | kd op e1 e2 hop h1 hi1 h2 hi2 |
      kd op e1 e2 hop h1 hi1 h2 hi2 | kd e1 e2 h1 hi1 h2 hi2 | kd e h hi | kd v ty h | |
      kd e s t h hi hok hsub | kd e s t h hi hok hsub] => Γ Γ' heq hΓ; subst; try (by constructor).
    - constructor; by eauto.
    - constructor; by eauto.
    - constructor; by eauto.
    - constructor; by eauto.
    - eapply ESubTy.
      + by eapply hi.
      + done.
      + by eapply ok_ty_constraint_elim.
      + by eapply subtype_constraint_elim.
    - eapply UpcastTy.
      + by eapply hi.
      + done.
      + by eapply ok_ty_constraint_elim.
      + by eapply subtype_constraint_elim.
  Qed.

  Lemma expr_has_ty_constraint_elim Γ Γ' kd lty e ty:
    expr_has_ty (Γ ++ Γ') lty kd e ty →
    (∀ i c, Γ' !! i = Some c → Γ ⊢ c.1 <D: c.2) →
    expr_has_ty Γ lty kd e ty.
  Proof. intros; by eapply expr_has_ty_constraint_elim_. Qed.

  Lemma expr_has_ty_subst Γ' Γ kd σ lty e ty:
    map_Forall (λ _ : string, wf_cdef_parent Δ) Δ →
    map_Forall (λ _ : string, wf_cdef_constraints_bounded) Δ →
    Forall wf_ty σ →
    Forall (ok_ty Γ') σ →
    expr_has_ty Γ lty kd e ty →
    expr_has_ty (Γ' ++ (subst_constraints σ Γ)) (subst_lty σ lty) kd (subst_expr σ e) (subst_ty σ ty).
  Proof.
    move => hp hb hσwf hσok.
    induction 1 as [ | | | kd op e1 e2 hop h1 hi1 h2 hi2 |
      kd op e1 e2 hop h1 hi1 h2 hi2 | kd e1 e2 h1 hi1 h2 hi2 | kd e h hi |
      kd v ty h | | kd e s t h hi hok hsub | kd e s t h hi hok hsub ] => //=; try (econstructor; by eauto).
    - constructor.
      rewrite /subst_lty /=.
      by rewrite lookup_fmap h.
    - econstructor; first by apply hi.
      + by apply wf_ty_subst.
      + by apply ok_ty_subst.
      + apply subtype_weaken with (subst_constraints σ Γ); first by apply subtype_subst.
        by set_solver.
    - eapply UpcastTy; first by apply hi.
      + by apply wf_ty_subst.
      + by apply ok_ty_subst.
      + apply subtype_weaken with (subst_constraints σ Γ); first by apply subtype_subst.
        by set_solver.
  Qed.

  Definition wf_lty lty :=
    wf_ty (this_type lty) ∧
    map_Forall (λ _, wf_ty) lty.(ctxt)
  .

  Lemma insert_wf_lty x ty lty :
    wf_ty ty → wf_lty lty → wf_lty (<[x := ty]>lty).
  Proof.
    destruct lty as [[lt lσ] lty].
    rewrite /wf_lty /this_type /= => h [h0 hl]; split => //.
    rewrite map_Forall_lookup => k tk.
    rewrite lookup_insert_Some.
    case => [[? <-] | [? hk]]; first done.
    by apply hl in hk.
  Qed.

  Lemma subst_wf_lty σ lty :
    Forall wf_ty σ → wf_lty lty → wf_lty (subst_lty σ lty).
  Proof.
    destruct lty as [[lt lσ] lty].
    rewrite /wf_lty /this_type /= => hσ [h0 hl]; split.
    - inv h0.
      econstructor => //.
      + by rewrite map_length H2.
      + move => k tk hk.
        apply list_lookup_fmap_inv in hk.
        destruct hk as [tk' [-> hk]].
        apply wf_ty_subst => //.
        by apply H3 in hk.
    - rewrite map_Forall_lookup => k tk.
      rewrite lookup_fmap_Some.
      case => t [<- hk].
      apply wf_ty_subst => //.
      by apply hl in hk.
  Qed.

  Lemma expr_has_ty_wf Γ kd lty e ty:
    wf_lty lty →
    expr_has_ty Γ lty kd e ty →
    wf_ty ty.
  Proof.
    move => hwf.
    induction 1 as [ | | | kd op e1 e2 hop h1 hi1 h2 hi2 |
      kd op e1 e2 hop h1 hi1 h2 hi2 | kd e1 e2 h1 hi1 h2 hi2 | kd e h hi |
      kd v ty h | | kd e s t h hi hsub | kd e s t h hi hsub] => //=; try (by constructor).
    - by apply hwf in h.
    - by apply hwf.
  Qed.

  (* continuation-based typing for commands.
   * Γ is the set of constraints S <: T of the current class
   * and C is the tag of the current class (for `private` related checks)
   *
   * Note on Getter/Setter visibility check:
   * if `e` has type `C<σ>` and we are typing `e->x`.
   *
   * For private access, we must make sure the current enclosing class
   * is where the member is defined, and the member can only be accessed
   * via `This`
   *)
  Inductive cmd_has_ty Γ (C : tag) : subtype_kind → local_tys → cmd → local_tys → Prop :=
    | SkipTy: ∀ lty kd, cmd_has_ty Γ C kd lty SkipC lty
    | ErrorTy: ∀ kd lty rty,
        wf_lty rty → cmd_has_ty Γ C kd lty ErrorC rty
    | SeqTy: ∀ kd lty1 lty2 lty3 fstc sndc,
        cmd_has_ty Γ C kd lty1 fstc lty2 →
        cmd_has_ty Γ C kd lty2 sndc lty3 →
        cmd_has_ty Γ C kd lty1 (SeqC fstc sndc) lty3
    | LetTy: ∀ kd lty lhs e ty,
        expr_has_ty Γ lty kd e ty →
        cmd_has_ty Γ C kd lty (LetC lhs e) (<[lhs := ty]>lty)
    | IfTy: ∀ kd lty1 lty2 cond thn els,
        expr_has_ty Γ lty1 kd cond BoolT →
        cmd_has_ty Γ C kd lty1 thn lty2 →
        cmd_has_ty Γ C kd lty1 els lty2 →
        cmd_has_ty Γ C kd lty1 (IfC cond thn els) lty2
    | GetPrivTy: ∀ kd lty lhs t σ name fty,
        type_of_this lty = (t, σ) →
        has_field name t Private fty C →
        cmd_has_ty Γ C kd lty (GetC lhs ThisE name) (<[lhs := subst_ty σ fty]>lty)
    | GetPubTy: ∀ kd lty lhs recv t σ name fty orig,
        expr_has_ty Γ lty kd recv (ClassT t σ) →
        has_field name t Public fty orig →
        cmd_has_ty Γ C kd lty (GetC lhs recv name) (<[lhs := subst_ty σ fty]>lty)
    | SetPrivTy: ∀ kd lty fld rhs fty t σ,
        type_of_this lty = (t, σ) →
        has_field fld t Private fty C →
        expr_has_ty Γ lty kd rhs (subst_ty σ fty) →
        cmd_has_ty Γ C kd lty (SetC ThisE fld rhs) lty
    | SetPubTy: ∀ kd lty recv fld rhs fty orig t σ,
        expr_has_ty Γ lty kd recv (ClassT t σ) →
        has_field fld t Public fty orig →
        expr_has_ty Γ lty kd rhs (subst_ty σ fty) →
        cmd_has_ty Γ C kd lty (SetC recv fld rhs) lty
    | NewTy: ∀ kd lty lhs t targs args fields,
        wf_ty (ClassT t targs) →
        ok_ty Γ (ClassT t targs) →
        has_fields t fields →
        dom fields = dom args →
        (∀ f fty arg,
        fields !! f = Some fty →
        args !! f = Some arg →
        expr_has_ty Γ lty kd arg (subst_ty targs fty.1.2)) →
        cmd_has_ty Γ C kd lty (NewC lhs t targs args) (<[lhs := ClassT t targs]>lty)
    | CallTy: ∀ kd lty lhs recv t targs name orig mdef args,
        expr_has_ty Γ lty kd recv (ClassT t targs) →
        has_method name t orig mdef →
        dom mdef.(methodargs) = dom args →
        (∀ x ty arg,
        mdef.(methodargs) !! x = Some ty →
        args !! x = Some arg →
        expr_has_ty Γ lty kd arg (subst_ty targs ty)) →
        cmd_has_ty Γ C kd lty (CallC lhs recv name args) (<[lhs := subst_ty targs mdef.(methodrettype)]>lty)
    | SubTy: ∀ kd lty c rty rty',
        lty_sub Γ kd rty' rty →
        cmd_has_ty Γ C kd lty c rty' →
        cmd_has_ty Γ C kd lty c rty
    | TagCheckTy kd lty rty v tv t thn els:
        lty.(ctxt) !! v = Some tv →
        cmd_has_ty Γ C kd (<[v:=InterT tv (ExT t)]> lty) thn rty →
        cmd_has_ty Γ C kd lty els rty →
        cmd_has_ty Γ C kd lty (RuntimeCheckC v (RCTag t) thn els) rty
    | IntCheckTy kd lty rty v tv thn els:
        lty.(ctxt) !! v = Some tv →
        cmd_has_ty Γ C kd (<[v:=InterT tv IntT]> lty) thn rty →
        cmd_has_ty Γ C kd lty els rty →
        cmd_has_ty Γ C kd lty (RuntimeCheckC v RCInt thn els) rty
    | BoolCheckTy kd lty rty v tv thn els:
        lty.(ctxt) !! v = Some tv →
        cmd_has_ty Γ C kd (<[v:=InterT tv BoolT]> lty) thn rty →
        cmd_has_ty Γ C kd lty els rty →
        cmd_has_ty Γ C kd lty (RuntimeCheckC v RCBool thn els) rty
    | NullCheckTy kd lty rty v tv thn els:
        lty.(ctxt) !! v = Some tv →
        cmd_has_ty Γ C kd (<[v:=InterT tv NullT]> lty) thn rty →
        cmd_has_ty Γ C kd lty els rty →
        cmd_has_ty Γ C kd lty (RuntimeCheckC v RCNull thn els) rty
    | NonNullCheckTy kd lty rty v tv thn els:
        lty.(ctxt) !! v = Some tv →
        cmd_has_ty Γ C kd (<[v:=InterT tv NonNullT]> lty) thn rty →
        cmd_has_ty Γ C kd lty els rty →
        cmd_has_ty Γ C kd lty (RuntimeCheckC v RCNonNull thn els) rty
    (* Dynamic related typing rules *)
    | DynIfTy: ∀ kd lty1 lty2 cond thn els,
        expr_has_ty Γ lty1 kd cond DynamicT →
        cmd_has_ty Γ C kd lty1 thn lty2 →
        cmd_has_ty Γ C kd lty1 els lty2 →
        cmd_has_ty Γ C kd lty1 (IfC cond thn els) lty2
    | DynGetTy : ∀ kd lty lhs recv name,
        expr_has_ty Γ lty kd recv DynamicT →
        (match recv with
         | ThisE => False
         | _ => True
         end
        ) →
        cmd_has_ty Γ C kd lty (GetC lhs recv name) (<[lhs := DynamicT]>lty)
    | DynSetTy : ∀ kd lty recv fld rhs,
        expr_has_ty Γ lty kd recv DynamicT →
        expr_has_ty Γ lty kd rhs DynamicT →
        (match recv with
         | ThisE => False
         | _ => True
         end) →
        cmd_has_ty Γ C kd lty (SetC recv fld rhs) lty
    | DynCallTy: ∀ kd lty lhs recv name (args: stringmap expr),
        expr_has_ty Γ lty kd recv DynamicT →
        (∀ x arg, args !! x = Some arg →
          expr_has_ty Γ lty kd arg DynamicT) →
        (match recv with
         | ThisE => False
         | _ => True
         end) →
        cmd_has_ty Γ C kd lty (CallC lhs recv name args) (<[lhs := DynamicT]>lty)
  .

  Lemma cmd_has_ty_constraint_elim_ G C kd lty cmd rty:
    cmd_has_ty G C kd lty cmd rty →
    ∀ Γ Γ', G = Γ ++ Γ' →
    (∀ i c, Γ' !! i = Some c → Γ ⊢ c.1 <D: c.2) →
    cmd_has_ty Γ C kd lty cmd rty.
  Proof.
    induction 1 as [ | ???? | ?????? h1 hi1 h2 hi2 | ????? he |
      ?????? he h1 hi1 h2 hi2 | ??????? he hf | ????????? he hf |
      ??????? he hf hr | ????????? he hf hr | ??????? ht hok hf hdom hargs |
      ?????????? he hm hdom hargs |
      ????? hsub h hi | ???????? hin hthn hi0 hels hi1 |
      ??????? hin hthn hi0 hels hi1 | ??????? hin hthn hi0 hels hi1 |
      ??????? hin hthn hi0 hels hi1 | ??????? hin hthn hi0 helse hi1 |
      ?????? hcond hthn hi1 hels hi2 | ????? he hnotthis |
      ????? hrecv hrhs hnotthis | ?????? he hargs hnotthis
      ] => Γ Γ' heq hΓ; subst.
    - by econstructor.
    - by eapply ErrorTy.
    - econstructor; by eauto.
    - econstructor => //.
      by eapply expr_has_ty_constraint_elim.
    - econstructor => //.
      + by eapply expr_has_ty_constraint_elim.
      + by eauto.
      + by eauto.
    - econstructor; by eauto.
    - econstructor => //.
      by eapply expr_has_ty_constraint_elim.
    - econstructor => //.
      by eapply expr_has_ty_constraint_elim.
    - econstructor => //.
      + by eapply expr_has_ty_constraint_elim.
      + by eapply expr_has_ty_constraint_elim.
    - econstructor => //.
      + by eapply ok_ty_constraint_elim.
      + move => ?????.
        eapply expr_has_ty_constraint_elim; by eauto.
    - econstructor => //.
      + by eapply expr_has_ty_constraint_elim.
      + move => ?????.
        eapply expr_has_ty_constraint_elim; by eauto.
    - econstructor => //.
      + eapply lty_sub_constraint_elim => //.
      + by eauto.
    - eapply TagCheckTy => //; by eauto.
    - eapply IntCheckTy => //; by eauto.
    - eapply BoolCheckTy => //; by eauto.
    - eapply NullCheckTy => //; by eauto.
    - eapply NonNullCheckTy => //; by eauto.
    - eapply DynIfTy.
      + by eapply expr_has_ty_constraint_elim.
      + by eapply hi1.
      + by eapply hi2.
    - eapply DynGetTy => //.
      by eapply expr_has_ty_constraint_elim.
    - eapply DynSetTy => //.
      + by eapply expr_has_ty_constraint_elim.
      + by eapply expr_has_ty_constraint_elim.
    - eapply DynCallTy => //.
      + by eapply expr_has_ty_constraint_elim.
      + move => ???; eapply expr_has_ty_constraint_elim => //.
        by eapply hargs.
  Qed.

  Lemma cmd_has_ty_constraint_elim Γ Γ' C kd lty cmd rty:
    cmd_has_ty (Γ ++ Γ') C kd lty cmd rty →
    (∀ i c, Γ' !! i = Some c → Γ ⊢ c.1 <D: c.2) →
    cmd_has_ty Γ C kd lty cmd rty.
  Proof. intros; by eapply cmd_has_ty_constraint_elim_. Qed.

  Lemma cmd_has_ty_wf Γ C kd lty cmd lty' :
    map_Forall (λ _ : string, wf_cdef_parent Δ) Δ →
    map_Forall (λ _ : string, wf_cdef_fields_wf) Δ →
    map_Forall (λ _ : string, wf_cdef_methods_wf) Δ →
    Forall wf_constraint Γ →
    wf_lty lty →
    cmd_has_ty Γ C kd lty cmd lty' →
    wf_lty lty'.
  Proof.
    move => hp hfields hmethods hΓ [hthis hwf].
    induction 1 as [ | ???? | ?????? h1 hi1 h2 hi2 | ????? he |
      ?????? he h1 hi1 h2 hi2 | ??????? he hf | ????????? he hf |
      ??????? he hf hr | ????????? he hf hr | ??????? ht hok hf hdom hargs |
      ?????????? he hm hdom hargs |
      ????? hsub h hi | ???????? hin hthn hi0 hels hi1 |
      ??????? hin hthn hi0 hels hi1 | ??????? hin hthn hi0 hels hi1 |
      ??????? hin hthn hi0 hels hi1 | ??????? hin hthn hi0 helse hi1 |
      ?????? hcond hthn hi1 hels hi2 | ????? he hnotthis |
      ????? hrecv hrhs hnotthis | ?????? he hargs hnotthis
      ] => //=; try (by eauto).
    - apply hi2.
      + by apply hi1.
      + by apply hi1.
    - apply insert_wf_lty => //.
      by apply expr_has_ty_wf in he.
    - apply insert_wf_lty => //.
      apply wf_ty_subst; last by apply has_field_wf in hf.
      destruct lty as [[? ?] lty].
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

  Lemma cmd_has_ty_subst Γ' Γ C kd σ lty cmd lty':
    map_Forall (λ _ : string, wf_cdef_parent Δ) Δ →
    map_Forall (λ _ : string, wf_cdef_fields_wf) Δ →
    map_Forall (λ _ : string, wf_cdef_methods_wf) Δ →
    map_Forall (λ _ : string, wf_cdef_fields_bounded) Δ →
    map_Forall (λ _ : string, cdef_methods_bounded) Δ →
    map_Forall (λ _ : string, wf_cdef_constraints_bounded) Δ →
    Forall wf_constraint Γ →
    wf_lty lty →
    Forall wf_ty σ →
    Forall (ok_ty Γ') σ →
    cmd_has_ty Γ C kd lty cmd lty' →
    cmd_has_ty (Γ' ++ (subst_constraints σ Γ)) C kd (subst_lty σ lty) (subst_cmd σ cmd) (subst_lty σ lty').
  Proof.
    move => hp hfields hmethods hfb hmb hcb hΓ hwf0 hwf1 hwf2.
    induction 1 as [ | ???? | ?????? h1 hi1 h2 hi2 | ????? he |
      ?????? he h1 hi1 h2 hi2 | ??????? he hf | ????????? he hf |
      ??????? he hf hr | ????????? he hf hr | ??????? hwf hok hf hdom hargs |
      ?????????? he hm hdom hargs |
      ????? hsub h hi | ???????? hin hthn hi0 hels hi1 |
      ??????? hin hthn hi0 hels hi1 | ??????? hin hthn hi0 hels hi1 |
      ??????? hin hthn hi0 hels hi1 | ??????? hin hthn hi0 helse hi1 |
      ?????? hcond hthn hi1 hels hi2 | ????? he hnotthis |
      ????? hrecv hrhs hnotthis | ?????? he hargs hnotthis
      ] => //=.
    - by constructor.
    - apply ErrorTy.
      by apply subst_wf_lty.
    - econstructor.
      + by eapply hi1.
      + eapply hi2 => //.
        by apply cmd_has_ty_wf in h1.
    - rewrite /subst_lty fmap_insert.
      eapply LetTy.
      by eapply expr_has_ty_subst.
    - eapply IfTy => //.
      + change BoolT with (subst_ty σ BoolT).
        by eapply expr_has_ty_subst.
      + by apply hi1.
      + by apply hi2.
    - destruct lty as [[this σt] lty].
      destruct hwf0 as [hthis hwf].
      simpl in *.
      rewrite /this_type /= in hthis, he.
      injection he; intros; subst; clear he.
      rewrite /subst_lty fmap_insert subst_ty_subst; last first.
      { apply has_field_bounded in hf => //.
        destruct hf as (hdef & ht & hfty).
        inv hthis; simplify_eq.
        by rewrite H2.
      }
      simpl in *.
      by eapply GetPrivTy.
    - rewrite /subst_lty fmap_insert subst_ty_subst; last first.
      { apply has_field_bounded in hf => //.
        destruct hf as (hdef & ht & hfty).
        apply expr_has_ty_wf in he => //.
        inv he; simplify_eq.
        by rewrite H2.
      }
      eapply GetPubTy => //.
      change (ClassT t (subst_ty σ <$> σ0)) with (subst_ty σ (ClassT t σ0)).
      by eapply expr_has_ty_subst.
    - apply SetPrivTy with (fty := fty) (t := t) (σ := subst_ty σ <$> σ0) => //; last first.
      + rewrite -subst_ty_subst; first by eapply expr_has_ty_subst.
        apply has_field_bounded in hf => //.
        destruct hf as (hdef & ht & hfty).
        destruct lty as [this lty]; simpl in he.
        rewrite he in hwf0; destruct hwf0 as [hwf _].
        rewrite /this_type /= in hwf.
        inv hwf; simplify_eq.
        by rewrite H2.
      + by rewrite /subst_lty /= he.
    - apply SetPubTy with (orig := orig) (fty := fty) (t := t) (σ := subst_ty σ <$> σ0) => //; last first.
      + rewrite -subst_ty_subst; first by eapply expr_has_ty_subst.
        apply has_field_bounded in hf => //.
        destruct hf as (hdef & ht & hfty).
        apply expr_has_ty_wf in he => //.
        inv he; simplify_eq.
        by rewrite H2.
      + change (ClassT t (subst_ty σ <$> σ0)) with (subst_ty σ (ClassT t σ0)).
        by eapply expr_has_ty_subst.
    - rewrite /subst_lty fmap_insert /=.
      eapply NewTy => //.
      { inv hwf.
        econstructor => //; first by rewrite map_length.
        move => k ty.
        rewrite list_lookup_fmap.
        destruct (targs !! k) as [ ty' | ] eqn:hty' => //=.
        case => <-.
        apply wf_ty_subst => //.
        by apply H3 in hty'.
      }
      { change (ClassT t (subst_ty σ <$> targs)) with (subst_ty σ (ClassT t targs)).
        by apply ok_ty_subst.
      }
      { by rewrite dom_fmap_L. }
      { move => f [[vis fty] orig] arg hfty ha.
        apply lookup_fmap_Some in ha as [e [<- he]].
        rewrite -subst_ty_subst.
        + eapply expr_has_ty_subst => //.
          by eapply hargs.
        + apply hf in hfty.
          apply has_field_bounded in hfty => //.
          destruct hfty as (hdef & ht & hfty).
          inv hwf; simplify_eq.
          by rewrite H2.
      }
    - rewrite /subst_lty fmap_insert /=.
      rewrite subst_ty_subst; last first.
      { apply has_method_from_def in hm => //.
        destruct hm as (odef & mo & ho & hmo & _ & [σo [hin ->]]).
        rewrite /subst_mdef /=.
        apply inherits_using_wf in hin => //.
        destruct hin as (tdef & htdef & hF& hwfo); inv hwfo; simplify_eq.
        assert (ho' := ho).
        apply hmb in ho.
        apply ho in hmo.
        destruct hmo as [_ [hret hbody]].
        apply bounded_subst with (n := length (generics odef)) => //.
        + apply expr_has_ty_wf in he => //.
          inv he; simplify_eq.
          by rewrite H4.
      }
      eapply CallTy => //.
      + change (ClassT t (subst_ty σ <$> targs)) with (subst_ty σ (ClassT t targs)).
        by eapply expr_has_ty_subst.
      + by rewrite hdom dom_fmap_L.
      + move => x ty arg hty ha.
        apply lookup_fmap_Some in ha as [e [<- ha]].
        rewrite -subst_ty_subst.
        { eapply expr_has_ty_subst => //.
          by eapply hargs.
        }
        apply has_method_from_def in hm => //.
        destruct hm as (odef & mo & ho & hmo & _ & [σo [hin ->]]).
        apply inherits_using_wf in hin => //.
        destruct hin as (tdef & htdef & hF & hwfo); inv hwfo; simplify_eq.
        assert (ho' := ho).
        apply hmb in ho.
        apply ho in hmo.
        destruct hmo as [hargs' _].
        rewrite /subst_mdef /= in hty.
        rewrite lookup_fmap_Some in hty.
        destruct hty as [ty' [ <- hty]].
        apply hargs' in hty.
        apply bounded_subst with (n := length (generics odef)) => //.
        apply expr_has_ty_wf in he => //.
        inv he; simplify_eq.
        by rewrite H4.
    - econstructor; last by apply hi.
      apply lty_sub_weaken with (subst_constraints σ Γ); last by set_solver.
      by apply lty_sub_subst.
    - eapply TagCheckTy.
      + by rewrite lookup_fmap hin /=.
      + rewrite /subst_lty fmap_insert /= in hi0.
        apply hi0 => //.
        destruct lty as [[lt lσ] lty].
        split.
        * rewrite /this_type /=.
          by apply hwf0.
        * apply map_Forall_insert_2 => //; last by apply hwf0.
          constructor; last by constructor.
          by apply hwf0 in hin.
      + by apply hi1.
    - eapply IntCheckTy.
      + by rewrite lookup_fmap hin /=.
      + rewrite /subst_lty fmap_insert /= in hi0.
        apply hi0 => //.
        destruct lty as [[lt lσ] lty].
        split.
        * rewrite /this_type /=.
          by apply hwf0.
        * apply map_Forall_insert_2 => //; last by apply hwf0.
          constructor; last by constructor.
          by apply hwf0 in hin.
      + by apply hi1.
    - eapply BoolCheckTy.
      + by rewrite lookup_fmap hin /=.
      + rewrite /subst_lty fmap_insert /= in hi0.
        apply hi0 => //.
        destruct lty as [[lt lσ] lty].
        split.
        * rewrite /this_type /=.
          by apply hwf0.
        * apply map_Forall_insert_2 => //; last by apply hwf0.
          constructor; last by constructor.
          by apply hwf0 in hin.
      + by apply hi1.
    - eapply NullCheckTy.
      + by rewrite lookup_fmap hin /=.
      + rewrite /subst_lty fmap_insert /= in hi0.
        apply hi0 => //.
        destruct lty as [[lt lσ] lty].
        split.
        * rewrite /this_type /=.
          by apply hwf0.
        * apply map_Forall_insert_2 => //; last by apply hwf0.
          constructor; last by constructor.
          by apply hwf0 in hin.
      + by apply hi1.
    - eapply NonNullCheckTy.
      + by rewrite lookup_fmap hin /=.
      + rewrite /subst_lty fmap_insert /= in hi0.
        apply hi0 => //.
        destruct lty as [[lt lσ] lty].
        split.
        * rewrite /this_type /=.
          by apply hwf0.
        * apply map_Forall_insert_2 => //; last by apply hwf0.
          constructor; last by constructor.
          by apply hwf0 in hin.
      + by apply hi1.
    - eapply DynIfTy.
      + change DynamicT with (subst_ty σ DynamicT).
        by eapply expr_has_ty_subst.
      + by apply hi1.
      + by apply hi2.
    - replace (subst_lty σ (<[lhs:=DynamicT]> lty)) with
             (<[lhs := DynamicT]>(subst_lty σ lty)); last first.
      { rewrite /subst_lty /= /insert /local_tys_insert /=.
        f_equal.
        by rewrite fmap_insert.
      }
      eapply DynGetTy.
      + change DynamicT with (subst_ty σ DynamicT).
        by eapply expr_has_ty_subst.
      + by destruct recv.
    - eapply DynSetTy.
      + change DynamicT with (subst_ty σ DynamicT).
        by eapply expr_has_ty_subst.
      + change DynamicT with (subst_ty σ DynamicT).
        by eapply expr_has_ty_subst.
      + by destruct recv.
    - replace (subst_lty σ (<[lhs:=DynamicT]> lty)) with
             (<[lhs := DynamicT]>(subst_lty σ lty)); last first.
      { rewrite /subst_lty /= /insert /local_tys_insert /=.
        f_equal.
        by rewrite fmap_insert.
      }
      eapply DynCallTy.
      + change DynamicT with (subst_ty σ DynamicT).
        by eapply expr_has_ty_subst.
      + move => ?? ha.
        rewrite lookup_fmap_Some in ha.
        destruct ha as [a [<- ha]].
        change DynamicT with (subst_ty σ DynamicT).
        eapply expr_has_ty_subst => //.
        by eapply hargs.
      + by destruct recv.
  Qed.

  (* Consider a class C<T0, ..., Tn>,
   * method bodies must be well-formed under a generic substitution mapping
   * Ti -> Ti.
   *)
  Definition wf_mdef_ty Γ tag σ mdef :=
    ∃ rty,
    wf_lty rty ∧
    cmd_has_ty Γ tag Plain
      {| type_of_this := (tag, σ); ctxt := subst_ty σ <$> mdef.(methodargs) |}
      mdef.(methodbody) rty ∧
    expr_has_ty Γ rty Plain mdef.(methodret) (subst_ty σ mdef.(methodrettype))
  .

  Definition cdef_wf_mdef_ty cname cdef :=
    let σ := gen_targs (length cdef.(generics)) in
    map_Forall (λ _mname mdef, wf_mdef_ty cdef.(constraints) cname σ mdef) cdef.(classmethods)
  .

  (* Checks related to support dynamic *)
  Definition to_dyn (ty: lang_ty) : lang_ty := DynamicT.

  Definition wf_mdef_dyn_ty Γ tag σ mdef :=
    ∃ rty,
    wf_lty rty ∧
    cmd_has_ty Γ tag Aware
      {| type_of_this := (tag, σ); ctxt := to_dyn <$> mdef.(methodargs) |}
      mdef.(methodbody) rty ∧
    expr_has_ty Γ rty Aware mdef.(methodret) (to_dyn mdef.(methodrettype))
  .

  Definition wf_cdef_methods_dyn_wf cname cdef :=
    if cdef.(support_dynamic) then
    ∀ mname orig mdef,
    has_method mname cname orig mdef → mdef.(method_support_dynamic) = true
    else True
  .

  Definition cdef_wf_mdef_dyn_ty cname cdef :=
    let σ := gen_targs (length cdef.(generics)) in
    map_Forall (λ _ mdef,
      if mdef.(method_support_dynamic) then
        wf_mdef_dyn_ty cdef.(constraints) cname σ mdef
      else True) cdef.(classmethods)
  .

  Definition wf_field_dyn_wf Σc (vfty: ((visibility * lang_ty) * tag)) :=
    match vfty.1 with
    | (Private, _) => True
    | (Public, fty) =>
        Σc ⊢ fty <D: DynamicT ∧ Σc ⊢ DynamicT <D: fty
    end.

  Definition wf_cdef_fields_dyn_wf cname cdef :=
    if cdef.(support_dynamic) then
    ∀ fields, has_fields cname fields →
    map_Forall (λ _fname vfty, wf_field_dyn_wf cdef.(constraints) vfty) fields
    else True.

  Definition wf_cdef_dyn_parent cdef :=
    match cdef.(superclass) with
    | Some (parent, _) =>
        ∀ def, Δ !! parent = Some def →
        def.(support_dynamic) = true →
        cdef.(support_dynamic) = true
    | None => True
    end.

  Lemma extends_using_dyn_parent A B σ:
    map_Forall (λ _, wf_cdef_parent Δ) Δ →
    map_Forall (λ _, wf_cdef_dyn_parent) Δ →
    extends_using A B σ →
    ∃ adef bdef,
      Δ !! A = Some adef ∧
      Δ !! B = Some bdef ∧
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
    map_Forall (λ _, wf_cdef_parent Δ) Δ →
    map_Forall (λ _, wf_cdef_dyn_parent) Δ →
    inherits_using A B σ →
    ∃ adef bdef,
      Δ !! A = Some adef ∧
      Δ !! B = Some bdef ∧
      (bdef.(support_dynamic) = true → adef.(support_dynamic) = true).
  Proof.
    move => hp hwf.
    induction 1 as [ A adef hΔ | A B σ hext | A B σ C σC hext h hi ].
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

(* With wf_mdefs, we have a global invariant for every method: they are
 * correctly typed in the class they are defined, with a generic(symbolic)
 * environment.
 * In practice, we want to get them for some instantiated class, and
 * inheritance / override might make things more complex.
 * Let's bundle this into a helper lemma to get that a method is correctly
 * typed in any suitable context.
 *)
Section MethodTyping.
  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.

  (* Helping the inference with this notation that hides Δ *)
  Local Notation "Γ ⊢ s <: t" := (@subtype _ Γ Plain s t) (at level 70, s at next level, no associativity).
  Local Notation "Γ ⊢ s <D: t" := (@subtype _ Γ Aware s t) (at level 70, s at next level, no associativity).

  (* Let's consider that class C0 has/inherits a method m from class C1
   * where it is declared. Then m is correctly typed in C0 for any valid
   * instantiation of the class.
   *)
  Lemma wf_mdef_ty_gen Σc C m σ def mdef:
    wf_cdefs Δ →
    Δ !! C = Some def →
    def.(classmethods) !! m = Some mdef →
    wf_ty (ClassT C σ) → ok_ty Σc (ClassT C σ) →
    ∃ rty, wf_lty rty ∧
      cmd_has_ty Σc C Plain {| type_of_this := (C, σ); ctxt := subst_ty σ <$> mdef.(methodargs) |}
                (subst_cmd σ mdef.(methodbody)) rty ∧
      expr_has_ty Σc rty Plain (subst_expr σ mdef.(methodret)) (subst_ty σ mdef.(methodrettype)).
  Proof.
    move => hΔ hdef hmdef hwf hok.
    destruct hΔ.
    (* Let's assert a bunch of helper statements *)
    assert (hwfσ : Forall wf_ty σ) by (by apply wf_ty_class_inv in hwf).
    assert (hokσ : Forall (ok_ty Σc) σ) by (by apply ok_ty_class_inv in hok).
    (* Let's use the general substitution lemma to make the instantiation *)
    assert (hgen : ∃ rty, wf_lty rty ∧
      cmd_has_ty (Σc ++ subst_constraints σ def.(constraints)) C Plain
                 (subst_lty σ {| type_of_this := (C, gen_targs (length def.(generics))); ctxt := mdef.(methodargs) |})
                 (subst_cmd σ mdef.(methodbody)) rty ∧
      expr_has_ty (Σc ++ subst_constraints σ def.(constraints))
                  rty Plain (subst_expr σ mdef.(methodret)) (subst_ty σ mdef.(methodrettype))).
    { assert (hd := hdef).
      assert (hm := hmdef).
      apply wf_mdefs0 in hd.
      apply hd in hm as [rty [wf_rty [hbody hret]]].
      exists (subst_lty σ rty); split; last split.
      - by apply subst_wf_lty.
      - apply cmd_has_ty_subst => //.
        { assert (hd1 := hdef).
          apply wf_constraints_wf0 in hd1.
          rewrite /wf_cdef_constraints_wf Forall_forall in hd1.
          rewrite Forall_forall /subst_constraints => c hc.
          by apply hd1.
        }
        { split => /=.
          - rewrite /this_type /=.
            econstructor => //; first by rewrite length_gen_targs.
            by apply gen_targs_wf.
          - rewrite map_Forall_lookup => k tk hk.
            apply wf_methods_wf0 in hdef.
            apply hdef in hmdef.
            by apply hmdef in hk.
        }
        rewrite fmap_subst_tys_id // in hbody.
        apply wf_methods_bounded0 in hdef.
        apply hdef in hmdef.
        by apply hmdef.
      - apply expr_has_ty_subst => //.
        rewrite subst_ty_id // in hret.
        apply wf_methods_bounded0 in hdef.
        apply hdef in hmdef.
        by apply hmdef.
    }
    destruct hgen as (rty & hwf_rty & hbody & hret).
    (* Now, because everything is correctly typed, let's discharge
     * some redundant constraints.
     *)
    assert (hconstraints: ∀ i c,
      (subst_constraints σ (constraints def)) !! i = Some c →
      Σc ⊢ c.1 <D: c.2).
    { move => i c hin.
      apply list_lookup_fmap_inv in hin as [c' [-> hin]].
      inv hok; simplify_eq.
      rewrite /subst_constraint /=.
      by eauto.
    }
    exists rty; split; first done.
    split.
    - eapply cmd_has_ty_constraint_elim => //.
      rewrite /subst_lty subst_ty_gen_targs //= in hbody.
      inv hwf; by simplify_eq.
    - by eapply expr_has_ty_constraint_elim.
  Qed.
End MethodTyping.
