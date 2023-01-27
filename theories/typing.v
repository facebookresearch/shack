(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
From stdpp Require Import base strings gmap stringmap fin_maps.
(* Not using iris but importing their ssreflect dependencies *)
From iris.proofmode Require Import tactics.
From shack Require Import lang progdef subtype ok.

Section Typing.
  (* assume a given set of class definitions and their SDT annotations. *)
  Context `{SDTCS: SDTClassSpec}.

  (* Helping the inference with this notation that hides pdefs *)
  Local Notation "Δ ⊢ s <D: t" := (@subtype _ _ Δ Aware s t) (at level 70, s at next level, no associativity).

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
    | VarTy: ∀ kd v ty,
        Γ !! v = Some ty →
        expr_has_ty Δ Γ rigid kd (VarE v) ty
    | ThisTy kd: expr_has_ty Δ Γ rigid kd ThisE ThisT
    | ESubTy: ∀ kd e s t,
        expr_has_ty Δ Γ rigid kd e s →
        wf_ty t →
        bounded rigid t →
        ok_ty Δ t →
        subtype Δ kd s t →
        expr_has_ty Δ Γ rigid kd e t
    | UpcastTy: ∀ kd e s t,
        expr_has_ty Δ Γ rigid kd e s →
        wf_ty t →
        bounded rigid t →
        ok_ty Δ t →
        Δ ⊢ s <D: t →
        expr_has_ty Δ Γ rigid kd (UpcastE e t) t
    | FalseTy: ∀ kd e t,
        wf_ty t →
        bounded rigid t →
        subtype Δ kd IntT BoolT →
        expr_has_ty Δ Γ rigid kd e t
  .

  Lemma expr_has_ty_wf Δ Γ rigid kd e ty:
    wf_lty Γ →
    expr_has_ty Δ Γ rigid kd e ty →
    wf_ty ty.
  Proof.
    move => hwf.
    induction 1 as [ | | | kd op e1 e2 hop h1 hi1 h2 hi2 |
      kd op e1 e2 hop h1 hi1 h2 hi2 | kd e1 e2 h1 hi1 h2 hi2 | kd e h hi | kd v ty h | |
      kd e s t h hi ? hb hok hsub | kd e s t h hi ? hb hok hsub |
      kd ????? ]
      => //=; subst; try (by constructor).
    - by apply hwf in h.
  Qed.

  Lemma expr_has_ty_bounded Δ Γ n kd e ty:
    bounded_lty n Γ →
    expr_has_ty Δ Γ n kd e ty →
    bounded n ty.
  Proof.
    move => hb.
    induction 1 as [ | | | kd op e1 e2 hop h1 hi1 h2 hi2 |
      kd op e1 e2 hop h1 hi1 h2 hi2 | kd e1 e2 h1 hi1 h2 hi2 | kd e h hi | kd v ty h | |
      kd e s t h hi ? ? hok hsub | kd e s t h hi ? ? hok hsub |
      kd ?????]
      => //=; subst; try (by constructor).
    - by apply hb in h.
  Qed.


  Lemma var_has_ty_inv Δ Γ n kd x t:
    expr_has_ty Δ Γ n kd (VarE x) t →
    (match Γ !! x with
     | None => True
     | Some s => subtype Δ kd s t
     end).
  Proof.
    remember (VarE x) as vx.
    move => he.
    move : x Heqvx.
    induction he as [ | | | kd op e1 e2 hop h1 hi1 h2 hi2 |
      kd op e1 e2 hop h1 hi1 h2 hi2 | kd e1 e2 h1 hi1 h2 hi2 | kd e h hi | kd v ty h | |
      kd e s t h hi ? ? hok hsub | kd e s t h hi ? ? hok hsub |
      kd ?????] => //= x heq.
    - case: heq => <-.
      by rewrite h.
    - apply hi in heq.
      destruct (Γ !! x) as [s0 | ] => //.
      by eapply SubTrans.
    - destruct (Γ !! x) as [s0 | ] eqn:h0 => //.
      by econstructor.
  Qed.

  Definition subst_fty exact_ t σ fty :=
    subst_ty σ (subst_this (ClassT exact_ t (gen_targs (length σ))) fty)
  .

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
    | GetPrivTy: ∀ Δ kd rigid cdef Γ lhs name fty,
        pdefs !! C = Some cdef →
        cdef.(classfields) !! name = Some (Private, fty) →
        cmd_has_ty C Δ kd rigid Γ (GetC lhs ThisE name) (<[lhs := fty]>Γ)
    | GetPubTy: ∀ Δ kd rigid Γ lhs recv exact_ t σ name fty orig,
        expr_has_ty Δ Γ rigid kd recv (ClassT exact_ t σ) →
        has_field name t Public fty orig →
        (is_true exact_ ∨ no_this fty) →
        cmd_has_ty C Δ kd rigid Γ (GetC lhs recv name) (<[lhs := subst_fty exact_ t σ fty]>Γ)
    (* | SetPrivTy: ∀ Δ kd rigid Γ fld rhs fty, *)
    (*     has_field fld C Private fty C → *)
    (*     expr_has_ty Δ Γ rigid kd rhs fty → *)
    (*     cmd_has_ty C Δ kd rigid Γ (SetC ThisE fld rhs) Γ *)
    (* | SetPubTy: ∀ Δ kd rigid Γ recv fld rhs fty orig exact_ t σ, *)
    (*     expr_has_ty Δ Γ rigid kd recv (ClassT exact_ t σ) → *)
    (*     has_field fld t Public fty orig → *)
    (*     expr_has_ty Δ Γ rigid kd rhs (subst_fty exact_ t σ fty) → *)
    (*     cmd_has_ty C Δ kd rigid Γ (SetC recv fld rhs) Γ *)
    | NewTy: ∀ Δ kd rigid Γ lhs t otargs targs args fields,
        (match otargs with
         | Some σ => targs = σ
         | None => ∃ inferred_targs, targs = inferred_targs
         end) →
        wf_ty (ClassT true t targs) →
        bounded rigid (ClassT true t targs) →
        ok_ty Δ (ClassT true t targs) →
        has_fields t fields →
        dom fields = dom args →
        (∀ f fty arg,
        fields !! f = Some fty →
        args !! f = Some arg →
        expr_has_ty Δ Γ rigid kd arg (subst_fty true t targs fty.1.2)) →
        cmd_has_ty C Δ kd rigid Γ (NewC lhs t otargs args) (<[lhs := ClassT true t targs]>Γ)
        (* TODO: do we need a case for `this` too ? *)
    | CallPubTy: ∀ Δ kd rigid Γ lhs recv exact_ t σ name orig mdef args,
        expr_has_ty Δ Γ rigid kd recv (ClassT exact_ t σ) →
        has_method name t orig mdef →
        (is_true exact_ ∨ no_this_mdef mdef) →
        mdef.(methodvisibility) = Public →
        dom mdef.(methodargs) = dom args →
        (∀ x ty arg,
          mdef.(methodargs) !! x = Some ty →
          args !! x = Some arg →
          expr_has_ty Δ Γ rigid kd arg (subst_fty exact_ t σ ty)) →
        cmd_has_ty C Δ kd rigid Γ (CallC lhs recv name args) (<[lhs := subst_fty exact_ t σ mdef.(methodrettype)]>Γ)
    | CallPrivTy: ∀ cdef Δ kd rigid Γ lhs name mdef args,
        pdefs !! C = Some cdef →
        cdef.(classmethods) !! name = Some mdef →
        mdef.(methodvisibility) = Private →
        dom mdef.(methodargs) = dom args →
        (∀ x ty arg,
          mdef.(methodargs) !! x = Some ty →
          args !! x = Some arg →
          expr_has_ty Δ Γ rigid kd arg ty) →
        cmd_has_ty C Δ kd rigid Γ (CallC lhs ThisE name args) (<[lhs := mdef.(methodrettype)]>Γ)
    | SubTy: ∀ Δ kd rigid Γ c Γ0 Γ1,
        lty_sub Δ kd Γ1 Γ0 →
        bounded_lty rigid Γ0 →
        cmd_has_ty C Δ kd rigid Γ c Γ1 →
        cmd_has_ty C Δ kd rigid Γ c Γ0
        (*
    | TagCheckTy Δ kd rigid Γ0 Γ1 v tv t def thn els:
        Γ0.(ctxt) !! v = Some tv →
        pdefs !! t = Some def →
        cmd_has_ty C (lift_constraints rigid def.(constraints) ++ Δ) kd (rigid + length def.(generics))
          (<[v:=InterT tv (ClassT false t (map GenT (seq rigid (length def.(generics)))))]> Γ0) thn Γ1 →
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
    | FalseCmdTy: ∀ Δ kd rigid Γ0 cmd Γ1,
        wf_lty Γ1 →
        bounded_lty rigid Γ1 →
        subtype Δ kd IntT BoolT →
        cmd_has_ty C Δ kd rigid Γ0 cmd Γ1
   *)
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
    move => hp hfields hmethods hΔ hwf.
    induction 1 as [ | | ???????? h1 hi1 h2 hi2 | ??????? he |
      ???????? he h1 hi1 h2 hi2 | ???????? hcdef hf | ???????????? he hf hex |
      (* ??????? hf hr | ??????????? he hf hr | *)
      ?????????? _ ht hb hok hf hdom hargs |
      ????????????? he hm hex hvis hdom hargs |
      ????????? hcdef hm hvis hdom hargs |
      ??????? hsub hb h hi (* |
      ??????????? hin hdef hthn hi0 hels hi1 |
      ????????? hin hthn hi0 hels hi1 | ????????? hin hthn hi0 hels hi1 |
      ????????? hin hthn hi0 hels hi1 | ????????? hin hthn hi0 helse hi1 |
      ???????? hcond hthn hi1 hels hi2 | ??????? he hnotthis |
      ??????? hrecv hrhs hnotthis | ???????? he hargs hnotthis |
      ????????? *)
      ] => //=; try (by eauto).
    (* - apply hi2 => //. *)
    (*   + by apply hi1. *)
    (*   + by apply hi1. *)
    - apply insert_wf_lty => //.
      by apply expr_has_ty_wf in he.
    - apply insert_wf_lty => //.
      apply hfields in hcdef.
      by apply hcdef in hf.
    - apply expr_has_ty_wf in he => //.
      assert (he_ := he).
      apply wf_tyI in he_ as (? & ? & ? & ?).
      apply insert_wf_lty => //.
      apply wf_ty_subst; first by apply wf_ty_classI in he.
      apply wf_ty_subst_this.
      { econstructor => //; last by apply gen_targs_wf_2.
        by rewrite length_gen_targs.
      }
      by apply has_field_wf in hf.
    - by apply map_Forall_insert_2.
    - apply map_Forall_insert_2 => //.
      apply expr_has_ty_wf in he => //.
      apply wf_tyI in he as (? & ? & ? & ?).
      apply wf_ty_subst => //.
      apply wf_ty_subst_this.
      { econstructor => //; last by apply gen_targs_wf_2.
        by rewrite length_gen_targs.
      }
      apply has_method_wf in hm => //.
      by destruct hm as [hargs' hret'].
    - apply map_Forall_insert_2 => //.
      apply hmethods in hcdef.
      apply hcdef in hm.
      by apply hm.
    - apply hi in hwf => //; clear hi h.
      rewrite /wf_lty map_Forall_lookup => k ty hty.
      apply hsub in hty.
      destruct hty as [ty' [ hty' hsub']].
      apply hwf in hty'.
      by eapply subtype_wf.
    (* - by apply insert_wf_lty. *)
    (* - by apply insert_wf_lty. *)
  Qed.

  Lemma cmd_has_ty_bounded C cdef Δ kd rigid Γ0 cmd Γ1:
    map_Forall (λ _ : string, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _ : string, wf_cdef_fields_wf) pdefs →
    map_Forall (λ _ : string, wf_cdef_methods_wf) pdefs →
    map_Forall (λ _ : string, wf_cdef_fields_bounded) pdefs →
    map_Forall (λ _ : string, cdef_methods_bounded) pdefs →
    Forall wf_constraint Δ →
    wf_lty Γ0 →
    pdefs !! C = Some cdef →
    rigid ≥ length cdef.(generics) →
    bounded_lty rigid Γ0 →
    cmd_has_ty C Δ kd rigid Γ0 cmd Γ1 →
    bounded_lty rigid Γ1.
  Proof.
    move => hp ?? hfields hmethods hΔ hwf hcdef hge hb.
    induction 1 as [ | | ???????? h1 hi1 h2 hi2 | ??????? he |
      ???????? he h1 hi1 h2 hi2 | ????????? hf | ???????????? he hf hex |
      (* ??????? hf hr | ??????????? he hf hr | *)
      ?????????? _ ht htb hok hf hdom hargs |
      ????????????? he hm hex hvis hdom hargs |
      ?????????? hm hvis hdom hargs |
      ??????? hsub hΓb h hi (*| ??????????? hin hdef hthn hi0 hels hi1 |
      ????????? hin hthn hi0 hels hi1 | ????????? hin hthn hi0 hels hi1 |
      ????????? hin hthn hi0 hels hi1 | ????????? hin hthn hi0 helse hi1 |
      ???????? hcond hthn hi1 hels hi2 | ??????? he hnotthis |
      ??????? hrecv hrhs hnotthis | ???????? he hargs hnotthis |
      ?????????*)
      ] => //=; try (by eauto).
    - apply hi2 => //.
      + by apply cmd_has_ty_wf in h1.
      + by apply hi1.
    - apply insert_bounded_lty => //.
      by apply expr_has_ty_bounded in he.
    - apply insert_bounded_lty => //.
      simplify_eq.
      apply hfields in hcdef.
      apply hcdef in hf.
      by eapply bounded_ge.
    - apply insert_bounded_lty => //.
      apply has_field_bounded in hf => //.
      destruct hf as (def & hdef & hbfty).
      apply bounded_subst with (length def.(generics)) => //.
      + apply bounded_subst_this => //.
        constructor.
        apply expr_has_ty_wf in he => //.
        apply wf_tyI in he as (? & ? & hlen & ?); simplify_eq.
        rewrite hlen.
        by apply bounded_gen_targs.
      + apply expr_has_ty_wf in he => //.
        apply wf_tyI in he as (? & ? & ? & ?).
        by simplify_eq.
      + apply expr_has_ty_bounded in he => //.
        by apply boundedI in he.
    - by apply insert_bounded_lty.
    - apply map_Forall_insert_2 => //.
      apply has_method_from_def in hm => //.
      destruct hm as (odef & m & hodef & hmdef & hm & [? [hin ->]]).
      assert (he' := he).
      apply expr_has_ty_wf in he' => //.
      apply wf_tyI in he' as (tdef & ? & hlen & ?).
      rewrite /subst_mdef /=.
      apply bounded_subst with (length tdef.(generics)) => //.
      + apply bounded_subst_this.
        { apply bounded_subst with (length odef.(generics)) => //.
          * apply hmethods in hodef.
            apply hodef in hmdef.
            by apply hmdef.
          * apply inherits_using_wf in hin => //.
            destruct hin as (? & ? & ? & h & _); simplify_eq.
            apply wf_tyI in h as (? & ? & ? & ?); by simplify_eq.
          * apply inherits_using_wf in hin => //.
            by destruct hin as (? & ? & h & ?); simplify_eq.
        }
        { constructor.
          rewrite hlen.
          by apply bounded_gen_targs.
        }
      + apply expr_has_ty_bounded in he => //.
        by apply boundedI in he.
    - apply map_Forall_insert_2 => //.
      simplify_eq.
      apply hmethods in hcdef.
      apply hcdef in hm.
      eapply bounded_ge; first by apply hm.
      done.
    (* - by apply insert_bounded_lty. *)
    (* - by apply insert_bounded_lty. *)
  Qed.

  (* Consider a class C<T0, ..., Tn>,
   * method bodies must be well-formed under a generic substitution mapping
   * Ti -> Ti.
   *)
  Definition wf_mdef_ty tag Δ rigid mdef :=
    ∃ Γ',
    wf_lty Γ' ∧
    cmd_has_ty tag Δ Plain rigid mdef.(methodargs) mdef.(methodbody) Γ' ∧
    expr_has_ty Δ Γ' rigid Plain mdef.(methodret) mdef.(methodrettype)
  .

  Definition cdef_wf_mdef_ty cname cdef :=
    let n := length cdef.(generics) in
    let σ := gen_targs n in
    let Δ := (ThisT, ClassT false cname σ) :: cdef.(constraints) in
    map_Forall (λ _mname mdef, wf_mdef_ty cname Δ n mdef) cdef.(classmethods)
  .

  (* Checks related to support dynamic *)
  (* Note to the reader: I'll write Δ0 => Δ1 for `Δentails Δ0 Δ1`
   *
   * Each class and method can be annotated with a SDT statement, as
   * long as they verify some conditions.
   * Consider:
   * <<SDT: Δsdt D>> class D<S...> where Δd {
   *   <<SDT: Δsdt D f>> function f;
   * }
   * <<SDT: Δsdt C>> class C<T...> extends D<σ> where Δc {
   *   <<SDT: Δsdt C g>> function g;
   * }
   *
   * Normal type checking already requires that `Δc => Δd[σ]`
   * for the extends relation to be sound.
   * SD adds a couple more relations:
   * - Since C <: D, if D can be cast to dynamic, C must be too.
   *   Therefore, we require that `Δc ∧ Δsdt D[σ] => Δsdt C`
   *
   * - For all inherited methods, the same arguments apply, so we
   *   require that `Δc ∧ Δsdt C => Δsdt D f[σ]`
   *
   * - For all methods defined in C, we need them to be SD so we
   *   require that `Δc ∧ Δsdt C => Δsdt C g`
   *
   * Note that with our `has_method` predicates, we can factorize
   * these last two into
   * `has_method f C O mdef → ΔC ∧ Δsdt C => Δsdt O mdef
   *
   * The same reasoning applies to fields. We won't have a dedicated
   * Δsdt for each field, they will all use the class level one.
   *)
  Definition to_dyn (ty: lang_ty) : lang_ty := DynamicT.

  (* `Δc ∧ Δsdt D[σ] => Δsdt C` *)
  Definition wf_cdef_extends_dyn_targs t def tp σp :=
    Δentails Aware
      (def.(constraints) ++ subst_constraints σp (Δsdt tp))
      (Δsdt t)
    .

  Definition wf_cdef_extends_dyn t def :=
    match def.(superclass) with
    | None => True
    | Some (parent, σ) =>
        ∃ pdef, pdefs !! parent = Some pdef ∧
        wf_cdef_extends_dyn_targs t def parent σ
    end.

  Lemma extends_using_extends_dyn A B σ:
    map_Forall (λ _ : string, wf_cdef_parent pdefs) pdefs →
    map_Forall wf_cdef_extends_dyn pdefs →
    extends_using A B σ →
    ∃ adef,
      pdefs !! A = Some adef ∧
      wf_cdef_extends_dyn_targs A adef B σ.
  Proof.
    move => ? hwf hext.
    assert (hext0 := hext).
    apply extends_using_wf in hext0 => //.
    destruct hext0 as (adef & hadef & ? & hwfb & _).
    apply wf_tyI in hwfb as (? & ? & ? & ?).
    destruct hext as [A' B' adef' σ hadef' hsuper]; simplify_eq.
    exists adef'; repeat split => //.
    apply hwf in hadef'.
    rewrite /wf_cdef_extends_dyn hsuper in hadef'.
    destruct hadef' as (? & ? & ?); by simplify_eq.
  Qed.

  Lemma inherits_using_extends_dyn A B σ:
    map_Forall (λ _ : string, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _, wf_cdef_constraints_bounded) pdefs →
    map_Forall (λ _cname, wf_cdef_parent_ok) pdefs →
    map_Forall wf_cdef_extends_dyn pdefs →
    inherits_using A B σ →
    ∃ adef,
      pdefs !! A = Some adef ∧
      wf_cdef_extends_dyn_targs A adef B σ.
  Proof.
    move => ?? hok hwf.
    induction 1 as [ A adef hpdefs | A B σ hext | A B σ C σC hext h hi ].
    - exists adef; repeat split => //.
      move => k [??] heq.
      eapply subtype_weaken.
      + apply SubConstraint.
        by apply elem_of_list_lookup_2 with k.
      + rewrite subst_constraints_gen_targs; first by set_solver.
        rewrite Forall_lookup => ? ty.
        by apply Δsdt_bounded.
    - by apply extends_using_extends_dyn in hext.
    - destruct hi as (bdef & hbdef & h1).
      assert (hσ : Forall wf_ty σ ∧ length bdef.(generics) = length σ).
      { apply extends_using_wf in hext => //.
        destruct hext as (? & ? & ? & hh & _); simplify_eq.
        split; first by apply wf_ty_classI in hh.
        apply wf_tyI in hh as (? & ? & ? & ?); by simplify_eq.
      }
      destruct hσ as [hσ hl].
      assert (hext0 := hext).
      apply extends_using_extends_dyn in hext0 as (adef & hadef & h0) => //.
      simplify_eq.
      exists adef; repeat split => //.
      move => k c heq.
      rewrite /wf_cdef_extends_dyn_targs in h0, h1.
      apply h0 in heq.
      eapply subtype_constraint_trans; first by eapply heq.
      clear k c heq.
      move => k c heq.
      rewrite lookup_app in heq.
      destruct (adef.(constraints) !! k) as [[??] | ] eqn:hc0.
      { rewrite hc0 in heq.
        case : heq => <-.
        eapply subtype_weaken.
        - apply SubConstraint.
          apply elem_of_list_lookup_2 with k.
          by apply hc0.
        - by set_solver.
      }
      rewrite hc0 in heq.
      apply list_lookup_fmap_inv in heq as [c1 [-> hc1]].
      simpl.
      apply subtype_constraint_trans with
        ((subst_constraints σ bdef.(constraints)) ++ subst_constraints (subst_ty σ <$> σC) (Δsdt C));
        last first.
      { move => i c hc.
        rewrite lookup_app in hc.
        destruct (subst_constraints σ bdef.(constraints) !! i) as [cc0 | ] eqn:hcc0.
        - case: hc => <-.
          apply subtype_weaken with adef.(constraints); last by set_solver.
          apply extends_using_ok in hext => //.
          apply list_lookup_fmap_inv in hcc0 as [? [-> hcc]].
          rewrite /subst_constraint /=.
          destruct hext as (? & ? & hhok); simplify_eq.
          apply ok_tyI in hhok as (? & ? & ? & ?); simplify_eq.
          by eauto.
        - eapply subtype_weaken.
          + apply SubConstraint.
            eapply elem_of_list_lookup_2.
            destruct c; by apply hc.
          + by set_solver.
      }
      rewrite -subst_constraints_subst; last first.
      { apply inherits_using_wf in h => //.
        destruct h as (? & ? & ? & h & _).
        apply wf_tyI in h as (? & ? & hlen & ?); simplify_eq.
        rewrite hlen.
        rewrite Forall_lookup => ??.
        by apply Δsdt_bounded.
      }
      rewrite -subst_constraints_app.
      apply subtype_subst => //.
      by apply h1 in hc1.
  Qed.

  Definition wf_field_dyn_wf Δ (vfty: ((visibility * lang_ty) * tag)) :=
    match vfty.1 with
    | (Private, _) => True
    | (Public, fty) =>
        Δ ⊢ fty <D: DynamicT ∧ Δ ⊢ DynamicT <D: fty
    end.

  Definition wf_cdef_fields_dyn_wf cname cdef :=
    let Δ := cdef.(constraints) ++ Δsdt cname in
    ∀ fields, has_fields cname fields →
    map_Forall (λ _fname vfty, wf_field_dyn_wf Δ vfty) fields
    .

  Definition wf_mdef_dyn_ty tag Δ rigid mdef :=
    ∃ Γ',
    wf_lty Γ' ∧
    cmd_has_ty tag Δ Aware rigid (to_dyn <$> mdef.(methodargs)) mdef.(methodbody) Γ' ∧
    expr_has_ty Δ Γ' rigid Aware mdef.(methodret) (to_dyn mdef.(methodrettype))
  .

  (* `has_method f C O mdef → ΔC ∧ Δsdt C => Δsdt O mdef.  *)
  Definition wf_cdef_methods_dyn_wf cname cdef :=
    let Δ := cdef.(constraints) ++ Δsdt cname in
    ∀ mname orig mdef,
    has_method mname cname orig mdef →
    ∃ σ,
      inherits_using cname orig σ ∧
      Δentails Aware Δ (subst_constraints σ (Δsdt_m orig mname))
  .

  Definition cdef_wf_mdef_dyn_ty cname cdef :=
    let n := length cdef.(generics) in
    let σ := gen_targs n in
    let Δ0 := (ThisT, ClassT false cname σ) :: cdef.(constraints) in
    let Δ := λ mname, Δ0 ++ Δsdt_m cname mname in
    map_Forall (λ mname mdef, wf_mdef_dyn_ty cname (Δ mname) n mdef) cdef.(classmethods)
  .

  (* SDT class level constraints can't mention `this`, like normal
   * constraints. See SDTClassSpec.
   *)

  (* Collection of all program invariant (at the source level):
   * - no cycle (we have a forest)
   * - every type is well-formed/bounded
   * - every substitution's domain/codomain is valid
   * - variance is checked
   *)
  Record wf_cdefs (prog: stringmap classDef) := {
    wf_parent : map_Forall (λ _cname, wf_cdef_parent prog) prog;
    wf_parent_ok : map_Forall (λ _cname, wf_cdef_parent_ok) prog;
    wf_constraints_wf : map_Forall (λ _cname, wf_cdef_constraints_wf) prog;
    wf_constraints_ok : map_Forall (λ _cname, wf_cdef_constraints_ok) prog;
    wf_constraints_bounded : map_Forall (λ _cname, wf_cdef_constraints_bounded) prog;
    wf_constraints_no_this : map_Forall (λ _cname, wf_cdef_constraints_no_this) prog;
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
    wf_extends_dyn : map_Forall wf_cdef_extends_dyn prog;
    wf_methods_dyn : map_Forall wf_cdef_methods_dyn_wf prog;
    wf_fields_dyn : map_Forall wf_cdef_fields_dyn_wf prog;
    wf_mdefs_dyn : map_Forall cdef_wf_mdef_dyn_ty prog;
  }
  .
End Typing.
