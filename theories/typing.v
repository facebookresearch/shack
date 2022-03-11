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
  Local Notation "s <: t" := (@subtype _ s t) (at level 70, no associativity).
  Local Notation "lty <:< rty" := (@lty_sub _ lty rty) (at level 70, no associativity).
  Local Notation "lts <: vs :> rts" := (@subtype_targs _ vs lts rts) (at level 70, vs at next level).

  (* Typing Judgements *)
  Definition is_bool_op op : bool :=
    match op with
    | LeqO | GeqO | EqO => true
    | PlusO | MinusO | TimesO | DivO => false
    end
  .

  Inductive expr_has_ty (lty : local_tys) :
    expr → lang_ty → Prop :=
    | IntTy : ∀ z, expr_has_ty lty (IntE z) IntT
    | BoolTy: ∀ b, expr_has_ty lty (BoolE b) BoolT
    | NullTy: expr_has_ty lty NullE NullT
    | OpIntTy: ∀ op e1 e2,
        is_bool_op op = false →
        expr_has_ty lty e1 IntT →
        expr_has_ty lty e2 IntT →
        expr_has_ty lty (OpE op e1 e2) IntT
    | OpBoolTy: ∀ op e1 e2,
        is_bool_op op = true →
        expr_has_ty lty e1 IntT →
        expr_has_ty lty e2 IntT →
        expr_has_ty lty (OpE op e1 e2) BoolT
    | GenTy: ∀ v ty,
        lty.(ctxt) !! v = Some ty →
        expr_has_ty lty (VarE v) ty
    | ThisTy : expr_has_ty lty ThisE (this_type lty)
    | ESubTy: ∀ e s t,
        expr_has_ty lty e s →
        wf_ty t →
        s <: t →
        expr_has_ty lty e t
  .

  Lemma expr_has_ty_subst σ lty e ty:
    map_Forall (λ _ : string, wf_cdef_parent Δ) Δ →
    Forall wf_ty σ →
    expr_has_ty lty e ty →
    expr_has_ty (subst_lty σ lty) e (subst_ty σ ty).
  Proof.
    move => hp hwf.
    induction 1 as [ z | b | | op e1 e2 hop h1 hi1 h2 hi2 |
      op e1 e2 hop h1 hi1 h2 hi2 | v ty h | | e s t h hi hsub ] => //=; try (by constructor).
    - constructor.
      rewrite /subst_lty /=.
      by rewrite lookup_fmap h.
    - econstructor; first by apply hi.
      + by apply wf_ty_subst.
      + by apply subtype_subst.
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

  Lemma expr_has_ty_wf lty e ty:
    wf_lty lty →
    expr_has_ty lty e ty →
    wf_ty ty.
  Proof.
    move => hwf.
    induction 1 as [ z | b | | op e1 e2 hop h1 hi1 h2 hi2 |
      op e1 e2 hop h1 hi1 h2 hi2 | v ty h | | e s t h hi hsub ] => //=; try (by constructor).
    - by apply hwf in h.
    - by apply hwf.
  Qed.

  (* continuation-based typing for commands *)
  Inductive cmd_has_ty :
    local_tys → cmd → local_tys → Prop :=
    | SkipTy: ∀ lty, cmd_has_ty lty SkipC lty
    | SeqTy: ∀ lty1 lty2 lty3 fstc sndc,
        cmd_has_ty lty1 fstc lty2 →
        cmd_has_ty lty2 sndc lty3 →
        cmd_has_ty lty1 (SeqC fstc sndc) lty3
    | LetTy: ∀ lty lhs e ty,
        expr_has_ty lty e ty →
        cmd_has_ty lty (LetC lhs e) (<[lhs := ty]>lty)
    | IfTy: ∀ lty1 lty2 cond thn els,
        expr_has_ty lty1 cond BoolT →
        cmd_has_ty lty1 thn lty2 →
        cmd_has_ty lty1 els lty2 →
        cmd_has_ty lty1 (IfC cond thn els) lty2
    | GetPrivTy: ∀ lty lhs t σ name fty,
        type_of_this lty = (t, σ) →
        has_field name t Private fty t →
        cmd_has_ty lty (GetC lhs ThisE name) (<[lhs := subst_ty σ fty]>lty)
    | GetPubTy: ∀ lty lhs recv t σ name fty orig,
        expr_has_ty lty recv (ClassT t σ) →
        has_field name t Public fty orig →
        cmd_has_ty lty (GetC lhs recv name) (<[lhs := subst_ty σ fty]>lty)
    | SetPrivTy: ∀ lty fld rhs fty t σ,
        type_of_this lty = (t, σ) →
        has_field fld t Private fty t →
        expr_has_ty lty rhs (subst_ty σ fty) →
        cmd_has_ty lty (SetC ThisE fld rhs) lty
    | SetPubTy: ∀ lty recv fld rhs fty orig t σ,
        expr_has_ty lty recv (ClassT t σ) →
        has_field fld t Public fty orig →
        expr_has_ty lty rhs (subst_ty σ fty) →
        cmd_has_ty lty (SetC recv fld rhs) lty
    | NewTy: ∀ lty lhs t targs args fields (*cdef*),
        wf_ty (ClassT t targs) →
        has_fields t fields →
        dom (gset string) fields = dom _ args →
        (∀ f fty arg,
        fields !! f = Some fty →
        args !! f = Some arg →
        expr_has_ty lty arg (subst_ty targs fty.1.2)) →
        cmd_has_ty lty (NewC lhs t args) (<[lhs := ClassT t targs]>lty)
    | CallTy: ∀ lty lhs recv t targs name orig mdef args,
        expr_has_ty lty recv (ClassT t targs) →
        has_method name t orig mdef →
        dom (gset string) mdef.(methodargs) = dom _ args →
        (∀ x ty arg,
        mdef.(methodargs) !! x = Some ty →
        args !! x = Some arg →
        expr_has_ty lty arg (subst_ty targs ty)) →
        cmd_has_ty lty (CallC lhs recv name args) (<[lhs := subst_ty targs mdef.(methodrettype)]>lty)
    | SubTy: ∀ lty c rty rty',
        rty' <:< rty →
        cmd_has_ty lty c rty' →
        cmd_has_ty lty c rty
    | CondTagTy lty rty v tv t cmd :
        lty.(ctxt) !! v = Some tv →
        lty <:< rty →
        cmd_has_ty (<[v:=InterT tv (ExT t)]> lty) cmd rty →
        cmd_has_ty lty (CondTagC v t cmd) rty
  .

  Lemma cmd_has_ty_wf lty cmd lty' :
    map_Forall (λ _ : string, wf_cdef_parent Δ) Δ →
    map_Forall (λ _ : string, wf_cdef_fields_wf) Δ →
    map_Forall (λ _ : string, wf_cdef_methods_wf) Δ →
    wf_lty lty →
    cmd_has_ty lty cmd lty' →
    wf_lty lty'.
  Proof.
    move => hp hfields hmethods [hthis hwf].
    induction 1 as [ lty | ????? h1 hi1 h2 hi2 | ???? he |
      ????? he h1 hi1 h2 hi2 | ?????? he hf | ???????? he hf |
      ?????? he hf hr | ???????? he hf hr | ?????? ht hf hdom hargs |
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

  Lemma cmd_has_ty_subst σ lty cmd lty':
    map_Forall (λ _ : string, wf_cdef_parent Δ) Δ →
    map_Forall (λ _ : string, wf_cdef_fields_wf) Δ →
    map_Forall (λ _ : string, wf_cdef_methods_wf) Δ →
    map_Forall (λ _ : string, wf_cdef_fields_bounded) Δ →
    map_Forall (λ _ : string, cdef_methods_bounded) Δ →
    wf_lty lty →
    Forall wf_ty σ →
    cmd_has_ty lty cmd lty' →
    cmd_has_ty (subst_lty σ lty) cmd (subst_lty σ lty').
  Proof.
    move => hp hfields hmethods hfb hmb hwf0 hwf1.
    induction 1 as [ lty | ????? h1 hi1 h2 hi2 | ???? he |
      ????? he h1 hi1 h2 hi2 | ?????? he hf | ???????? he hf |
      ?????? he hf hr | ???????? he hf hr | ?????? hwf hf hdom hargs |
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
    - econstructor; first by apply lty_sub_subst.
      by apply hi.
    - eapply CondTagTy.
      + by rewrite lookup_fmap hin /=.
      + by apply lty_sub_subst.
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
  Definition wf_mdef_ty tag σ σ' mdef :=
    ∃ rty,
    wf_lty rty ∧
    cmd_has_ty
      {| type_of_this := (tag, σ); ctxt := subst_ty σ' <$> mdef.(methodargs) |}
      mdef.(methodbody) rty ∧
    expr_has_ty rty mdef.(methodret) (subst_ty σ' mdef.(methodrettype))
  .

  Definition cdef_wf_mdef_ty cname cdef :=
    let σ := gen_targs (length cdef.(generics)) in
    map_Forall (λ _mname mdef, wf_mdef_ty cname σ σ mdef) cdef.(classmethods)
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
    wf_override : wf_method_override prog;
    wf_fields : map_Forall (λ _cname, wf_cdef_fields) prog;
    wf_fields_bounded : map_Forall (λ _cname, wf_cdef_fields_bounded) prog;
    wf_fields_wf  : map_Forall (λ _cname, wf_cdef_fields_wf) prog;
    (* because all public fields are mutable *)
    wf_fields_mono : map_Forall (λ _cname, wf_field_mono) prog;
    wf_methods_bounded : map_Forall (λ _cname, cdef_methods_bounded) prog;
    wf_methods_wf : map_Forall (λ _cname, wf_cdef_methods_wf) prog;
    wf_methods_mono : map_Forall (λ _cname, wf_cdef_methods_mono) prog;
    wf_mdefs : map_Forall cdef_wf_mdef_ty prog;
    wf_mono : map_Forall (λ _cname, wf_cdef_mono) prog;
  }
  .
End Typing.
