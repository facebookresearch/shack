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
  Local Notation "Γ ⊢ s <: t" := (@subtype _ Γ s t) (at level 70, s at next level, no associativity).
  Local Notation "Γ ⊢ lty <:< rty" := (@lty_sub _ Γ lty rty) (lty at next level, at level 70, no associativity).

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
        (∀ i c, def.(constraints) !! i = Some c → Γ ⊢ (subst_ty σ c.1) <: (subst_ty σ c.2)) →
        ok_ty Γ (ClassT t σ)
    | OkNull: ok_ty Γ NullT
    | OkNonNull: ok_ty Γ NonNullT
    | OkUnion s t: ok_ty Γ s → ok_ty Γ t → ok_ty Γ (UnionT s t)
    | OkInter s t: ok_ty Γ s → ok_ty Γ t → ok_ty Γ (InterT s t)
    | OkGen n: ok_ty Γ (GenT n)
    | OkEx t: ok_ty Γ (ExT t)
  .

  Lemma ok_ty_constraint_elim_ G T:
    ok_ty G T →
    ∀ Γ Γ', G = Γ ++ Γ' →
    (∀ i c, Γ' !! i = Some c → Γ ⊢ c.1 <: c.2) →
    ok_ty Γ T.
  Proof.
    induction 1 as [ | | | | t σ def hσ hi hdef hconstr
    | | | s t hs hi ht hit | s t hs hi ht hit | n | t] => Γ Γ' heq hΓ; subst; try by constructor.
    - apply OkClass with def => //.
      + move => i ty h; by eapply hi.
      + move => i c h.
        apply subtype_constraint_elim with Γ'; by eauto.
    - constructor; by eauto.
    - constructor; by eauto.
  Qed.

  Lemma ok_ty_constraint_elim Γ Γ' T:
    ok_ty (Γ ++ Γ') T →
    (∀ i c, Γ' !! i = Some c → Γ ⊢ c.1 <: c.2) →
    ok_ty Γ T.
  Proof. intros; by eapply ok_ty_constraint_elim_. Qed.

  Lemma ok_ty_weaken Γ t: ok_ty Γ t → ∀ Γ', Γ ⊆ Γ' → ok_ty Γ' t.
  Proof.
    induction 1 as [ | | | | t σ def hσ hi hdef hconstr
    | | | s t hs hi ht hit | s t hs hi ht hit | n | t] => Γ' hincl; try by constructor.
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
    | | | s t hs his ht hit | s t hs his ht hit | n | t ]
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
    (∀ i c, Γ !! i = Some c → Γ' ⊢ c.1 <: c.2) →
    ok_ty Γ' ty.
  Proof.
    induction 1 as [ | | | | t σ def hσ hi hdef hconstr
    | | | s t hs hi ht hit | s t hs hi ht hit | n | t] => Γ' hΓ; try by constructor.
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
      destruct hext as [A B adef σ hΔ hsuper].
      assert (hσ: Forall wf_ty σ).
      { apply hp in hΔ.
        rewrite /wf_cdef_parent hsuper in hΔ.
        by repeat destruct hΔ as [? hΔ].
      }
      exists adef; split => //.
      assert (hA := hΔ).
      apply hok in hΔ.
      rewrite /wf_cdef_parent_ok hsuper in hΔ.
      inv hΔ; inv hokB; simplify_eq.
      rename def0 into cdef.
      rename H5 into hC.
      econstructor => //.
      { move => i ty hi.
        apply list_lookup_fmap_inv in hi as [ty' [-> hi]].
        eapply ok_ty_trans.
        + eapply ok_ty_subst => //.
          { by eauto. }
          { apply inherits_using_wf in h as (? & ? & ? & ? & ? & ? & hF)=> //.
            rewrite Forall_forall in hF.
            apply hF.
            by apply elem_of_list_lookup_2 in hi.
          }
          apply hok in hA.
          rewrite /wf_cdef_parent_ok hsuper in hA.
          apply ok_ty_class_inv in hA.
          exact hA.
        + move => j c.
          rewrite lookup_app_Some.
          case => [hc | [? ]].
          * apply SubConstraint.
            apply elem_of_list_lookup_2 in hc.
            by rewrite -surjective_pairing.
          * rewrite /subst_constraints => hc.
            apply list_lookup_fmap_inv in hc as [c' [-> hc]].
            rewrite /subst_constraint /=.
            apply hok in hA.
            rewrite /wf_cdef_parent_ok hsuper in hA.
            inv hA; simplify_eq.
            by eauto.
      }
      move => i c hc.
      simplify_eq.
      rewrite -!subst_ty_subst.
      + eapply subtype_constraint_trans.
        * apply subtype_subst => //.
          by eauto.
        * move => j c'.
          rewrite /subst_constraints => hc'.
          apply list_lookup_fmap_inv in hc' as [c'' [-> hc']].
          rewrite /subst_constraint /=.
          by eauto.
      + assert (hC' := hC).
        apply hcb in hC.
        rewrite /wf_cdef_constraints_bounded Forall_forall in hC.
        apply elem_of_list_lookup_2 in hc.
        apply hC in hc as [].
        apply inherits_using_wf in h as (? & ? & ? & ? & ? & hL & ?)=> //.
        simplify_eq.
        by rewrite hL.
      + assert (hC' := hC).
        apply hcb in hC.
        rewrite /wf_cdef_constraints_bounded Forall_forall in hC.
        apply elem_of_list_lookup_2 in hc.
        apply hC in hc as [].
        apply inherits_using_wf in h as (? & ? & ? & ? & ? & hL & ?)=> //.
        simplify_eq.
        by rewrite hL.
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
    | LeqO | GeqO | EqO => true
    | PlusO | MinusO | TimesO | DivO => false
    end
  .

  Inductive expr_has_ty Γ (lty : local_tys) :
    expr → lang_ty → Prop :=
    | IntTy : ∀ z, expr_has_ty Γ lty (IntE z) IntT
    | BoolTy: ∀ b, expr_has_ty Γ lty (BoolE b) BoolT
    | NullTy: expr_has_ty Γ lty NullE NullT
    | OpIntTy: ∀ op e1 e2,
        is_bool_op op = false →
        expr_has_ty Γ lty e1 IntT →
        expr_has_ty Γ lty e2 IntT →
        expr_has_ty Γ lty (OpE op e1 e2) IntT
    | OpBoolTy: ∀ op e1 e2,
        is_bool_op op = true →
        expr_has_ty Γ lty e1 IntT →
        expr_has_ty Γ lty e2 IntT →
        expr_has_ty Γ lty (OpE op e1 e2) BoolT
    | GenTy: ∀ v ty,
        lty.(ctxt) !! v = Some ty →
        expr_has_ty Γ lty (VarE v) ty
    | ThisTy : expr_has_ty Γ lty ThisE (this_type lty)
    | ESubTy: ∀ e s t,
        expr_has_ty Γ lty e s →
        wf_ty t →
        ok_ty Γ t →
        Γ ⊢ s <: t →
        expr_has_ty Γ lty e t
  .

  Lemma expr_has_ty_constraint_elim_ G lty e ty:
    expr_has_ty G lty e ty →
    ∀ Γ Γ', G = Γ ++ Γ' →
    (∀ i c, Γ' !! i = Some c → Γ ⊢ c.1 <: c.2) →
    expr_has_ty Γ lty e ty.
  Proof.
    induction 1 as [ z | b | | op e1 e2 hop h1 hi1 h2 hi2 |
      op e1 e2 hop h1 hi1 h2 hi2 | v ty h | | e s t h hi hok hsub ] => Γ Γ' heq hΓ; subst; try (by constructor).
    - constructor; by eauto.
    - constructor; by eauto.
    - econstructor.
      + by eauto.
      + done.
      + by eapply ok_ty_constraint_elim.
      + by eapply subtype_constraint_elim.
  Qed.

  Lemma expr_has_ty_constraint_elim Γ Γ' lty e ty:
    expr_has_ty (Γ ++ Γ') lty e ty →
    (∀ i c, Γ' !! i = Some c → Γ ⊢ c.1 <: c.2) →
    expr_has_ty Γ lty e ty.
  Proof. intros; by eapply expr_has_ty_constraint_elim_. Qed.

  Lemma expr_has_ty_subst Γ' Γ σ lty e ty:
    map_Forall (λ _ : string, wf_cdef_parent Δ) Δ →
    map_Forall (λ _ : string, wf_cdef_constraints_bounded) Δ →
    Forall wf_ty σ →
    Forall (ok_ty Γ') σ →
    expr_has_ty Γ lty e ty →
    expr_has_ty (Γ' ++ (subst_constraints σ Γ)) (subst_lty σ lty) e (subst_ty σ ty).
  Proof.
    move => hp hb hσwf hσok.
    induction 1 as [ z | b | | op e1 e2 hop h1 hi1 h2 hi2 |
      op e1 e2 hop h1 hi1 h2 hi2 | v ty h | | e s t h hi hok hsub ] => //=; try (by constructor).
    - constructor.
      rewrite /subst_lty /=.
      by rewrite lookup_fmap h.
    - econstructor; first by apply hi.
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

  Lemma expr_has_ty_wf Γ lty e ty:
    wf_lty lty →
    expr_has_ty Γ lty e ty →
    wf_ty ty.
  Proof.
    move => hwf.
    induction 1 as [ z | b | | op e1 e2 hop h1 hi1 h2 hi2 |
      op e1 e2 hop h1 hi1 h2 hi2 | v ty h | | e s t h hi hsub ] => //=; try (by constructor).
    - by apply hwf in h.
    - by apply hwf.
  Qed.

  (* continuation-based typing for commands *)
  Inductive cmd_has_ty Γ : local_tys → cmd → local_tys → Prop :=
    | SkipTy: ∀ lty, cmd_has_ty Γ lty SkipC lty
    | SeqTy: ∀ lty1 lty2 lty3 fstc sndc,
        cmd_has_ty Γ lty1 fstc lty2 →
        cmd_has_ty Γ lty2 sndc lty3 →
        cmd_has_ty Γ lty1 (SeqC fstc sndc) lty3
    | LetTy: ∀ lty lhs e ty,
        expr_has_ty Γ lty e ty →
        cmd_has_ty Γ lty (LetC lhs e) (<[lhs := ty]>lty)
    | IfTy: ∀ lty1 lty2 cond thn els,
        expr_has_ty Γ lty1 cond BoolT →
        cmd_has_ty Γ lty1 thn lty2 →
        cmd_has_ty Γ lty1 els lty2 →
        cmd_has_ty Γ lty1 (IfC cond thn els) lty2
    | GetPrivTy: ∀ lty lhs t σ name fty,
        type_of_this lty = (t, σ) →
        has_field name t Private fty t →
        cmd_has_ty Γ lty (GetC lhs ThisE name) (<[lhs := subst_ty σ fty]>lty)
    | GetPubTy: ∀ lty lhs recv t σ name fty orig,
        expr_has_ty Γ lty recv (ClassT t σ) →
        has_field name t Public fty orig →
        cmd_has_ty Γ lty (GetC lhs recv name) (<[lhs := subst_ty σ fty]>lty)
    | SetPrivTy: ∀ lty fld rhs fty t σ,
        type_of_this lty = (t, σ) →
        has_field fld t Private fty t →
        expr_has_ty Γ lty rhs (subst_ty σ fty) →
        cmd_has_ty Γ lty (SetC ThisE fld rhs) lty
    | SetPubTy: ∀ lty recv fld rhs fty orig t σ,
        expr_has_ty Γ lty recv (ClassT t σ) →
        has_field fld t Public fty orig →
        expr_has_ty Γ lty rhs (subst_ty σ fty) →
        cmd_has_ty Γ lty (SetC recv fld rhs) lty
    | NewTy: ∀ lty lhs t targs args fields,
        wf_ty (ClassT t targs) →
        ok_ty Γ (ClassT t targs) →
        has_fields t fields →
        dom (gset string) fields = dom _ args →
        (∀ f fty arg,
        fields !! f = Some fty →
        args !! f = Some arg →
        expr_has_ty Γ lty arg (subst_ty targs fty.1.2)) →
        cmd_has_ty Γ lty (NewC lhs t args) (<[lhs := ClassT t targs]>lty)
    | CallTy: ∀ lty lhs recv t targs name orig mdef args,
        expr_has_ty Γ lty recv (ClassT t targs) →
        has_method name t orig mdef →
        dom (gset string) mdef.(methodargs) = dom _ args →
        (∀ x ty arg,
        mdef.(methodargs) !! x = Some ty →
        args !! x = Some arg →
        expr_has_ty Γ lty arg (subst_ty targs ty)) →
        cmd_has_ty Γ lty (CallC lhs recv name args) (<[lhs := subst_ty targs mdef.(methodrettype)]>lty)
    | SubTy: ∀ lty c rty rty',
        Γ ⊢ rty' <:< rty →
        cmd_has_ty Γ lty c rty' →
        cmd_has_ty Γ lty c rty
    | CondTagTy lty rty v tv t cmd :
        lty.(ctxt) !! v = Some tv →
        Γ ⊢ lty <:< rty →
        cmd_has_ty Γ (<[v:=InterT tv (ExT t)]> lty) cmd rty →
        cmd_has_ty Γ lty (CondTagC v t cmd) rty
  .

  Lemma cmd_has_ty_constraint_elim_ G lty cmd rty:
    cmd_has_ty G lty cmd rty →
    ∀ Γ Γ', G = Γ ++ Γ' →
    (∀ i c, Γ' !! i = Some c → Γ ⊢ c.1 <: c.2) →
    cmd_has_ty Γ lty cmd rty.
  Proof.
    induction 1 as [ lty | ????? h1 hi1 h2 hi2 | ???? he |
      ????? he h1 hi1 h2 hi2 | ?????? he hf | ???????? he hf |
      ?????? he hf hr | ???????? he hf hr | ?????? ht hok hf hdom hargs |
      ????????? he hm hdom hargs |
      ???? hsub h hi | ?????? hin hr h hi ] => Γ Γ' heq hΓ; subst.
    - by econstructor.
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
      + by eapply lty_sub_constraint_elim.
      + by eauto.
    - eapply CondTagTy => //.
      + by eapply lty_sub_constraint_elim.
      + by eauto.
  Qed.

  Lemma cmd_has_ty_constraint_elim Γ Γ' lty cmd rty:
    cmd_has_ty (Γ ++ Γ') lty cmd rty →
    (∀ i c, Γ' !! i = Some c → Γ ⊢ c.1 <: c.2) →
    cmd_has_ty Γ lty cmd rty.
  Proof. intros; by eapply cmd_has_ty_constraint_elim_. Qed.

  Lemma cmd_has_ty_wf Γ lty cmd lty' :
    map_Forall (λ _ : string, wf_cdef_parent Δ) Δ →
    map_Forall (λ _ : string, wf_cdef_fields_wf) Δ →
    map_Forall (λ _ : string, wf_cdef_methods_wf) Δ →
    Forall wf_constraint Γ →
    wf_lty lty →
    cmd_has_ty Γ lty cmd lty' →
    wf_lty lty'.
  Proof.
    move => hp hfields hmethods hΓ [hthis hwf].
    induction 1 as [ lty | ????? h1 hi1 h2 hi2 | ???? he |
      ????? he h1 hi1 h2 hi2 | ?????? he hf | ???????? he hf |
      ?????? he hf hr | ???????? he hf hr | ?????? ht hok hf hdom hargs |
      ????????? he hm hdom hargs |
      ???? hsub h hi | ?????? hin hr h hi ] => //=; try (by eauto).
    - apply hi2.
      + by apply hi1.
      + by apply hi1.
    - split; first by apply hthis.
      apply map_Forall_insert_2 => //.
      by apply expr_has_ty_wf in he.
    - destruct lty as [[? ?] lty].
      rewrite /this_type /= in hthis, he.
      simplify_eq.
      simpl in *.
      split; first by apply hthis.
      apply map_Forall_insert_2 => //.
      apply wf_ty_subst; first by apply wf_ty_class_inv in hthis.
      by apply has_field_wf in hf.
    - split; first by apply hthis.
      apply map_Forall_insert_2 => //.
      apply wf_ty_subst.
      + apply expr_has_ty_wf in he => //.
        by apply wf_ty_class_inv in he.
      + by apply has_field_wf in hf.
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
    - apply hi; clear hi.
      + destruct lty as [[lt lσ] ?]; rewrite /this_type /=.
        by apply hthis.
      + rewrite map_Forall_lookup => k ty.
        rewrite lookup_insert_Some.
        case => [[heq <-] | [hne hk]].
        { constructor; last by constructor.
          by apply hwf in hin.
        }
        by apply hwf in hk.
  Qed.

  Lemma cmd_has_ty_subst Γ' Γ σ lty cmd lty':
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
    cmd_has_ty Γ lty cmd lty' →
    cmd_has_ty (Γ' ++ (subst_constraints σ Γ)) (subst_lty σ lty) cmd (subst_lty σ lty').
  Proof.
    move => hp hfields hmethods hfb hmb hcb hΓ hwf0 hwf1 hwf2.
    induction 1 as [ lty | ????? h1 hi1 h2 hi2 | ???? he |
      ????? he h1 hi1 h2 hi2 | ?????? he hf | ???????? he hf |
      ?????? he hf hr | ???????? he hf hr | ?????? hwf hok hf hdom hargs |
      ????????? he hm hdom hargs |
      ???? hsub h hi | ?????? hin hr h hi ] => //=.
    - by constructor.
    - econstructor.
      + by eapply hi1.
      + eapply hi2.
        by apply cmd_has_ty_wf in h1.
    - rewrite /subst_lty fmap_insert.
      eapply LetTy.
      by eapply expr_has_ty_subst.
    - eapply IfTy => //.
      + change BoolT with (subst_ty σ BoolT).
        by eapply expr_has_ty_subst.
      + by apply hi1.
      + apply hi2.
        by apply cmd_has_ty_wf in h1.
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
      move => f [[vis fty] orig] arg hfty ha.
      rewrite -subst_ty_subst.
      + eapply expr_has_ty_subst => //.
        by eapply hargs.
      + apply hf in hfty.
        apply has_field_bounded in hfty => //.
        destruct hfty as (hdef & ht & hfty).
        inv hwf; simplify_eq.
        by rewrite H2.
    - rewrite /subst_lty fmap_insert /=.
      rewrite subst_ty_subst; last first.
      { apply has_method_from_def in hm => //.
        destruct hm as (odef & mo & ho & hmo & _ & [σo [hin ->]]).
        rewrite /subst_mdef /=.
        apply inherits_using_wf in hin => //.
        destruct hin as (tdef & ? & ht & ho' & hfo & hlo & htyo); simplify_eq.
        assert (ho' := ho).
        apply hmb in ho.
        apply ho in hmo.
        destruct hmo as [_ hret].
        apply bounded_subst with (n := length (generics odef)) => //.
        apply expr_has_ty_wf in he => //.
        inv he; simplify_eq.
        by rewrite H2.
      }
      eapply CallTy => //.
      + change (ClassT t (subst_ty σ <$> targs)) with (subst_ty σ (ClassT t targs)).
        by eapply expr_has_ty_subst.
      + move => x ty arg hty ha.
        rewrite -subst_ty_subst.
        { eapply expr_has_ty_subst => //.
          by eapply hargs.
        }
        apply has_method_from_def in hm => //.
        destruct hm as (odef & mo & ho & hmo & _ & [σo [hin ->]]).
        apply inherits_using_wf in hin => //.
        destruct hin as (tdef & ? & ht & ho' & hfo & hlo & htyo); simplify_eq.
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
        by rewrite H2.
    - econstructor; last by apply hi.
      apply lty_sub_weaken with (subst_constraints σ Γ); last by set_solver.
      by apply lty_sub_subst.
    - eapply CondTagTy.
      + by rewrite lookup_fmap hin /=.
      + apply lty_sub_weaken with (subst_constraints σ Γ); last by set_solver.
        by apply lty_sub_subst.
      + rewrite /subst_lty fmap_insert /= in hi.
        apply hi.
        destruct lty as [[lt lσ] lty].
        split.
        * rewrite /this_type /=.
          by apply hwf0.
        * apply map_Forall_insert_2 => //; last by apply hwf0.
          constructor; last by constructor.
          by apply hwf0 in hin.
  Qed.

  (* Consider a class C<T0, ..., Tn>,
   * method bodies must be well-formed under a generic substitution mapping
   * Ti -> Ti.
   *)
  Definition wf_mdef_ty Γ tag σ σ' mdef :=
    ∃ rty,
    wf_lty rty ∧
    cmd_has_ty Γ
      {| type_of_this := (tag, σ); ctxt := subst_ty σ' <$> mdef.(methodargs) |}
      mdef.(methodbody) rty ∧
    expr_has_ty Γ rty mdef.(methodret) (subst_ty σ' mdef.(methodrettype))
  .

  Definition cdef_wf_mdef_ty cname cdef :=
    let σ := gen_targs (length cdef.(generics)) in
    map_Forall (λ _mname mdef, wf_mdef_ty cdef.(constraints) cname σ σ mdef) cdef.(classmethods)
  .

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
  }
  .
End Typing.
