(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 * 
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
From stdpp Require Import base strings gmap stringmap fin_maps.
(* Not using iris but importing their ssreflect dependencies *)
From iris.proofmode Require Import tactics.

(* Helper tactics *)
Ltac inv H := inversion H; subst; clear H.

Definition tag := string.

Local Instance tag_equiv : Equiv tag := fun s0 s1 => String.eqb s0 s1 = true.
Local Instance tag_equivalence : Equivalence (≡@{tag}).
Proof.
  split.
  - now move => x; apply String.eqb_refl.
  - move => x y hxy.
    now rewrite /equiv /tag_equiv String.eqb_sym.
  - move => x y z.
    move => /String.eqb_eq hxy /String.eqb_eq hyz.
    now apply String.eqb_eq; transitivity y.
Qed.

Definition loc := positive.
Global Instance loc_dec_eq (l l' : loc) : Decision (l = l') := _.

Inductive value : Set :=
  | IntV (z: Z)
  | BoolV (b: bool)
  | NullV
  | LocV (ℓ : loc).
Local Instance value_inhabited : Inhabited value := populate NullV.

Inductive lang_ty :=
  | IntT
  | BoolT
  | NothingT
  | MixedT
  | ClassT (cname: tag) (targs: list lang_ty)
  | NullT
  | NonNullT
  | UnionT (s t: lang_ty)
  | InterT (s t: lang_ty)
  | VarT (tvar: nat)
.

Section nested_ind.
  Variable P : lang_ty -> Prop.
  Hypothesis case_IntT : P IntT.
  Hypothesis case_BoolT : P BoolT.
  Hypothesis case_NothingT : P NothingT.
  Hypothesis case_MixedT : P MixedT.
  Hypothesis case_ClassT : ∀ cname targs, Forall P targs → P (ClassT cname targs).
  Hypothesis case_NullT : P NullT.
  Hypothesis case_NonNullT : P NonNullT.
  Hypothesis case_UnionT :  ∀ s t, P s → P t → P (UnionT s t).
  Hypothesis case_InterT :  ∀ s t, P s → P t → P (InterT s t).
  Hypothesis case_VarT: ∀ n, P (VarT n).

  Fixpoint lang_ty_ind' (t : lang_ty) :=
    match t with
    | IntT => case_IntT
    | BoolT => case_BoolT
    | NothingT => case_NothingT
    | MixedT => case_MixedT
    | ClassT cname targs =>
        let H := (fix fold (xs : list lang_ty) : Forall P xs :=
          match xs with
          | nil => List.Forall_nil _
          | x :: xs => List.Forall_cons _ x xs (lang_ty_ind' x) (fold xs)
          end) targs in
        case_ClassT cname targs H
    | NullT => case_NullT
    | NonNullT => case_NonNullT
    | UnionT s t => case_UnionT s t (lang_ty_ind' s) (lang_ty_ind' t)
    | InterT s t => case_InterT s t (lang_ty_ind' s) (lang_ty_ind' t)
    | VarT n => case_VarT n
    end.
End nested_ind.

Fixpoint subst (targs:list lang_ty) (ty: lang_ty): lang_ty :=
  match ty with
  | ClassT cname cargs => ClassT cname (List.map (subst targs) cargs)
  | UnionT s t => UnionT (subst targs s) (subst targs t)
  | InterT s t => InterT (subst targs s) (subst targs t)
  | VarT tvar => List.nth tvar targs ty
  | IntT | BoolT | NothingT | MixedT | NullT | NonNullT => ty
  end.

Definition var := string.
Global Instance var_dec_eq (l l' : var) : Decision (l = l') := _.

Inductive primop :=
  | PlusO | MinusO | TimesO | DivO | LeqO | GeqO | EqO
.

Inductive expr :=
  | IntE (z: Z)
  | BoolE (b: bool)
  | NullE
  | OpE (op: primop) (e1: expr) (e2: expr)
  | VarE (v: var)
.

Inductive cmd : Set :=
  | SkipC
  | SeqC (fstc: cmd) (sndc: cmd)
  | LetC (lhs: var) (e: expr)
  | IfC (cond: expr) (thn: cmd) (els: cmd)
  | CallC (lhs: var) (recv: expr) (name: string) (args: stringmap expr)
  | NewC (lhs: var) (class_name: tag) (targs: list lang_ty) (args: stringmap expr)
  | GetC (lhs: var) (recv: expr) (name: string)
  | SetC (recv: expr) (fld: string) (rhs: expr)
      (* tag test "if ($v is C) { ... }" *)
  | CondTagC (v : var) (t : tag) (body : cmd)
.

Record methodDef := {
  methodname: string;
  methodargs: stringmap lang_ty;
  methodrettype: lang_ty;
  methodbody: cmd;
  methodret: expr;
}.

Record classDef := {
  classname: tag;
  generics: nat; (* number of generics, no constraint for now *)
  superclass: option tag;
  classfields : stringmap lang_ty;
  classmethods : stringmap methodDef;
}.

Fixpoint gen_targs_ nleft n : list lang_ty :=
  match nleft with
  | O => []
  | S nleft => VarT n :: gen_targs_ nleft (S n)
  end.

Lemma lookup_gen_targs__lt :
  ∀ nleft n pos, pos < nleft →
  gen_targs_ nleft n !! pos = Some (VarT (n + pos)).
Proof.
  elim => [ | nleft hi] n pos //=; first by lia.
  case: pos hi => [ | pos] hi //=.
  { move => _; by rewrite plus_comm. }
  move/lt_S_n => hlt.
  apply (hi (S n)) in hlt.
  rewrite hlt.
  do 2 f_equal.
  by lia.
Qed.

Lemma lookup_gen_targs__ge:
  ∀ nleft n pos, pos >= nleft →
  gen_targs_ nleft n !! pos = None.
Proof.
  elim => [ | nleft hi] n pos //= hge.
  case: pos hge => [ | pos] hge; first by lia.
  simpl.
  rewrite (hi (S n)) //.
  by lia.
Qed.

Definition gen_targs n : list lang_ty := gen_targs_ n 0.

Corollary lookup_gen_targs_lt :
  ∀ n pos, pos < n → gen_targs n !! pos = Some (VarT pos).
Proof.
  rewrite /gen_targs => n pos h.
  by rewrite lookup_gen_targs__lt.
Qed.

Corollary lookup_gen_targs_ge :
  ∀ n pos, pos ≥ n → gen_targs n !! pos = None.
Proof.
  rewrite /gen_targs => n pos h.
  by rewrite lookup_gen_targs__ge.
Qed.

(* A program is a collection of classes *)
Class ProgDefContext := { Δ : stringmap classDef }.

Section ProgDef.

  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.

  (* class A extends B *)
  Definition extends (A B: tag) : Prop :=
    ∃ cdef,
    Δ !! A = Some cdef ∧
    cdef.(superclass) = Some B
  .

  (* Refl trans closure of extends *)
  Definition inherits := rtc extends.

  (* Not useful, just for sanity check: inherits are chains.
   * if A inherits B and C, then either B inherits C or C inherits B.
   *)
  Corollary inherits_is_chain:
    ∀ A B C,
    inherits A B → inherits A C →
    (inherits C B ∨ inherits B C).
  Proof.
    intros A B C h; revert C.
    induction h as [ t | x y z hxy hyz hi]; move => c hc; first by right.
    destruct hxy as (cdef & hin & hs).
    destruct hc as [ t | u v w huv hvw].
    - left; econstructor; first by exists cdef. done.
    - destruct huv as (? & hin' & hs').
      rewrite hin' in hin.
      injection hin; intros ->; clear hin hin'.
      rewrite hs' in hs.
      injection hs; intros ->; clear hs hs'.
      apply hi in hvw as [h | h]; first by left.
      by right.
  Qed.

  Inductive subtype : lang_ty → lang_ty → Prop :=
    | SubMixed : ∀ ty, subtype ty MixedT
    (* Generic class are invariant *)
    | SubClass : ∀ A B targs, inherits A B → subtype (ClassT A targs) (ClassT B targs)
    | SubMixed2: subtype MixedT (UnionT NonNullT NullT)
    | SubIntNonNull: subtype IntT NonNullT
    | SubBoolNonNull: subtype BoolT NonNullT
    | SubClassNonNull: ∀ A targs, subtype (ClassT A targs) NonNullT
    | SubUnionUpper1 : ∀ s t, subtype s (UnionT s t)
    | SubUnionUpper2 : ∀ s t, subtype t (UnionT s t)
        (* TODO: Do we need this one ? *)
    | SubUnionLeast : ∀ s t u, subtype s u → subtype t u → subtype (UnionT s t) u
    | SubInterLower1 : ∀ s t, subtype (InterT s t) s
    | SubInterLower2 : ∀ s t, subtype (InterT s t) t
    | SubInterGreatest: ∀ s t u, subtype u s → subtype u t → subtype u (InterT s t)
    | SubRefl: ∀ s, subtype s s
    | SubTrans : ∀ s t u, subtype s t → subtype t u → subtype s u
    .

    Hint Constructors subtype : core.

    Notation "s <: t" := (subtype s t) (at level 70, no associativity).

    (* Derived rules *)
    Lemma subtype_union_comm : ∀ A B, (UnionT A B) <: (UnionT B A).
    Proof. by auto.  Qed.

    Lemma subtype_inter_comm : ∀ A B, (InterT A B) <: (InterT B A).
    Proof. by auto.  Qed.

    Lemma subtype_union_assoc:
      ∀ A B C, (UnionT (UnionT A B) C) <: (UnionT A (UnionT B C)).
    Proof. by eauto.  Qed.

    Lemma subtype_inter_assoc:
      ∀ A B C, (InterT (InterT A B) C) <: (InterT A (InterT B C)).
    Proof. by eauto.  Qed.

    Definition local_tys := stringmap lang_ty.

    Definition lty_sub (lty rty: local_tys) :=
      ∀ k A, rty !! k = Some A → ∃ B, lty !! k = Some B ∧ B <: A.

    Notation "lty <:< rty" := (lty_sub lty rty) (at level 70, no associativity).

    Lemma lty_sub_reflexive: reflexive _ lty_sub.
    Proof.
      move => lty k A ->.
      by exists A.
    Qed.

    Lemma lty_sub_transitive: transitive _ lty_sub.
    Proof.
      move => lty rty zty hlr hrz k A hA.
      apply hrz in hA as (C & hC & hsub).
      apply hlr in hC as (B & -> & hsub').
      exists B; by eauto.
    Qed.

    (* has_field fname ty cname checks if the class cname has a field named
     * fname of type ty
     *)
    Inductive has_field (fname: string) (typ: lang_ty): tag → Prop :=
      | HasField current cdef:
          Δ !! current = Some cdef →
          cdef.(classfields) !! fname = Some typ →
          has_field fname typ current
      | InheritsField current parent cdef:
          Δ !! current = Some cdef →
          cdef.(classfields) !! fname = None →
          cdef.(superclass) = Some parent →
          has_field fname typ parent →
          has_field fname typ current.

    Hint Constructors has_field : core.

    (* Naive method lookup: methods are unique *)
    Inductive has_method (mname: string) (mdef: methodDef): tag → Prop :=
      | HasMethod current cdef:
          Δ !! current = Some cdef →
          cdef.(classmethods) !! mname = Some mdef →
          has_method mname mdef current
      | InheritsMethod current parent cdef:
          Δ !! current = Some cdef →
          cdef.(classmethods) !! mname = None →
          cdef.(superclass) = Some parent →
          has_method mname mdef parent →
          has_method mname mdef current
    .

    Hint Constructors has_method : code.

    Lemma has_method_from m mdef A:
      has_method m mdef A →
      ∃ B cdef,
      Δ !! B = Some cdef ∧
      cdef.(classmethods) !! m = Some mdef ∧
      inherits A B.
    Proof.
      induction 1 as [ current cdef hΔ hm | current parent cdef hΔ hm hs h hi];
          first by exists current, cdef.
      destruct hi as (B & cdef' & hΔ' & hm' & hinherits). 
      exists B, cdef'; repeat split => //.
      econstructor; last by apply hinherits.
      by exists cdef.
    Qed.

    (* A class cannot redeclare a field if it is present in
     * any of its parent definition.
     *)
    Definition wf_cdef_fields cdef : Prop :=
      ∀ f fty super,
      cdef.(superclass) = Some super →
      has_field f fty super →
      cdef.(classfields) !! f = None.

    (* We allow method override: children can redeclare a method if types
     * are compatible:
     * - return type must be a subtype
     * - argument types must be a supertype
     *)
    Definition mdef_incl sub super :=
      dom stringset sub.(methodargs) = dom _ super.(methodargs) ∧
      (∀ k A B, sub.(methodargs) !! k = Some A →
      super.(methodargs) !! k = Some B → B <: A) ∧
      sub.(methodrettype) <: super.(methodrettype).

    Lemma mdef_incl_reflexive: reflexive _ mdef_incl.
    Proof.
      move => mdef; split; first done.
      split; last done.
      by move => k A B -> [] ->.
    Qed.

    Lemma mdef_incl_transitive: transitive _ mdef_incl.
    Proof.
      move => m0 m1 m2 [hdom1 [h1 ?]] [hdom2 [h2 ?]]; split; first by etransitivity.
      split; last by eauto.
      move => k A B hA hB.
      destruct (methodargs m1 !! k) as [C | ] eqn:hC; last first.
      { apply mk_is_Some in hA.
        apply elem_of_dom in hA.
        rewrite hdom1 in hA.
        apply elem_of_dom in hA.
        rewrite hC in hA.
        by elim: hA.
      }
      apply SubTrans with C.
      - by eapply h2.
      - by eapply h1.
    Qed.

    Definition wf_cdef_methods cdef : Prop :=
      ∀ m mdef superdef super,
      cdef.(superclass) = Some super →
      has_method m superdef super →
      cdef.(classmethods) !! m = Some mdef →
      mdef_incl mdef superdef.

    (* all fields of class cname are in the fnames set *)
    Definition has_fields (cname: tag) (fnames: stringmap lang_ty) : Prop :=
      ∀ fname typ, has_field fname typ cname ↔ fnames !! fname = Some typ.

    Lemma has_fields_fun: ∀ c fs0 fs1,
      has_fields c fs0 → has_fields c fs1 → fs0 = fs1.
    Proof.
      move => c fs0 fs1 h0 h1.
      apply map_eq => k.
      destruct (fs0 !! k) as [ ty | ] eqn:hty.
      - destruct (h1 k ty) as [hl1 hr1].
        rewrite hl1 //=.
        by apply h0.
      - destruct (fs1 !! k) as [ ty | ] eqn:hty'; last done.
        destruct (h1 k ty) as [hl1 hr1].
        apply h0 in hr1; last done.
        by rewrite hty in hr1.
    Qed.

    Lemma has_method_fun: ∀ c name mdef0 mdef1,
      has_method name mdef0 c → has_method name mdef1 c → mdef0 = mdef1.
    Proof.
      move => c name mdef0 mdef1 h; move: mdef1.
      induction h as [ current cdef hΔ hm | current parent cdef hΔ hm hs hp hi ].
      - move => mdef1 h1; inv h1.
        + rewrite hΔ in H; injection H; intros; subst; clear hΔ H.
          rewrite hm in H0; by injection H0.
        + rewrite hΔ in H; injection H; intros; subst; clear hΔ H.
          rewrite hm in H0; discriminate H0.
      - move => mdef1 h1; inv h1.
        + rewrite hΔ in H; injection H; intros; subst; clear hΔ H.
          rewrite hm in H0; discriminate H0.
        + rewrite hΔ in H; injection H; intros; subst; clear hΔ H.
          rewrite hs in H1; injection H1; intros; subst; clear hs H1.
          by apply hi.
    Qed.

    Lemma has_field_inherits : map_Forall (fun _ => wf_cdef_fields) Δ →
      ∀ A B, inherits A B →
      ∀ f fty, has_field f fty B → has_field f fty A.
    Proof.
      move => wfΔ A B h.
      induction h as [ t | x y z hxy hyz hi]; move => f fty hf; first done.
      apply hi in hf.
      destruct hxy as (cdef & hΔ & hs).
      apply InheritsField with y cdef; move => //.
      apply wfΔ in hΔ.
      by eapply hΔ.
    Qed.

    Corollary has_fields_inherits_lookup:
      map_Forall (fun _ => wf_cdef_fields) Δ →
      ∀ A B name fty fields,
      has_field name fty B →
      inherits A B →
      has_fields A fields →
      fields !! name = Some fty.
    Proof.
      move => wfΔ A B name fty fields hfields hinherits hf.
      destruct (hf name fty) as [hl hr].
      apply hl.
      by eapply (has_field_inherits wfΔ).
    Qed.

    Lemma has_method_inherits (Hcdef: map_Forall (fun _ => wf_cdef_methods) Δ):
      ∀ A B, inherits A B →
      ∀ m mdef, has_method m mdef B →
      ∃ mdef', has_method m mdef' A ∧ mdef_incl mdef' mdef.
    Proof.
      move => A B h.
      induction h as [ t | x y z hxy hyz hi]; move => m mdef hf.
      { exists mdef; split => //.
        by apply mdef_incl_reflexive.
      }
      apply hi in hf as (mdef' & hm & hincl).
      destruct hxy as (cdef & hΔ & hs).
      destruct (cdef.(classmethods) !! m) as [ mdef'' | ] eqn:heq; last first.
      { exists mdef'; split; last done.
        by apply InheritsMethod with y cdef.
      }
      exists mdef''; split; first by apply HasMethod with cdef.
      apply mdef_incl_transitive with mdef'; last done.
      apply Hcdef in hΔ.
      by eapply hΔ.
    Qed.

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
      | VarTy: ∀ v ty,
          lty !! v = Some ty →
          expr_has_ty lty (VarE v) ty
      | ESubTy: ∀ e s t,
          expr_has_ty lty e s →
          s <: t →
          expr_has_ty lty e t
    .

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
      | GetTy: ∀ lty lhs recv t targs name fty,
          expr_has_ty lty recv (ClassT t targs) →
          has_field name fty t →
          cmd_has_ty lty (GetC lhs recv name) (<[lhs := subst targs fty]>lty)
      | SetTy: ∀ lty recv fld rhs fty t targs,
          expr_has_ty lty recv (ClassT t targs) →
          has_field fld fty t →
          expr_has_ty lty rhs (subst targs fty) →
          cmd_has_ty lty (SetC recv fld rhs) lty
      | NewTy: ∀ lty lhs t targs args fields,
          has_fields t fields →
          dom (gset string) fields = dom _ args →
          (∀ f fty arg,
          fields !! f = Some fty →
          args !! f = Some arg →
          expr_has_ty lty arg (subst targs fty)) →
          cmd_has_ty lty (NewC lhs t targs args) (<[ lhs := ClassT t targs]>lty)
      | CallTy: ∀ lty lhs recv t targs name mdef args,
          expr_has_ty lty recv (ClassT t targs) →
          has_method name mdef t →
          dom (gset string) mdef.(methodargs) = dom _ args →
          (∀ x ty arg,
          mdef.(methodargs) !! x = Some ty →
          args !! x = Some arg →
          expr_has_ty lty arg (subst targs ty)) →
          cmd_has_ty lty (CallC lhs recv name args) (<[lhs := subst targs mdef.(methodrettype)]>lty)
      | SubTy: ∀ lty c rty rty',
          rty' <:< rty →
          cmd_has_ty lty c rty' →
          cmd_has_ty lty c rty
      | CondTagTy lty v tv t targs cmd :
          lty !! v = Some tv →
          (* TODO pas correct, ils sortent du chapeau *)
          cmd_has_ty (<[v:=InterT tv (ClassT t targs)]> lty) cmd lty →
          cmd_has_ty lty (CondTagC v t cmd) lty
    .

    Corollary CallTy_: ∀ lty lhs recv t targs name mdef args,
      expr_has_ty lty recv (ClassT t targs) →
      has_method name mdef t →
      dom (gset string) mdef.(methodargs) = dom _ args →
      (∀ x ty arg,
      mdef.(methodargs) !! x = Some ty →
      args !! x = Some arg →
      ∃ ty', ty' <: subst targs ty ∧ expr_has_ty lty arg ty') →
      cmd_has_ty lty (CallC lhs recv name args) (<[lhs := subst targs mdef.(methodrettype)]>lty).
    Proof.
      move => lty lhs recv t targs name mdef args hrecv hmdef hdom hargs.
      econstructor; [done | done | done | ].
      move => k ty arg hk ha.
      destruct (hargs _ _ _ hk ha) as (ty' & hsub & he).
      by econstructor.
    Qed.

    Lemma CallTyGen: ∀ lty lhs recv t targs name mdef args ret,
      expr_has_ty lty recv (ClassT t targs) →
      has_method name mdef t →
      dom (gset string) mdef.(methodargs) = dom _ args →
      (∀ x ty arg,
      mdef.(methodargs) !! x = Some ty →
      args !! x = Some arg →
      ∃ ty', ty' <: subst targs ty ∧ expr_has_ty lty arg ty') →
      subst targs mdef.(methodrettype) <: ret →
      cmd_has_ty lty (CallC lhs recv name args) (<[lhs := ret]>lty).
    Proof.
      move =>lty lhs ?????? ret hrecv hm hdom hargs hret.
      eapply SubTy; last by eapply CallTy_.
      move => k A hA.
      rewrite lookup_insert_Some in hA.
      destruct hA as [[<- <-] | [hne heq]].
      - rewrite lookup_insert.
        by eexists.
      - rewrite lookup_insert_ne //.
        by exists A.
    Qed.

    Definition wf_mdef_ty t targs mdef :=
      ∃ lty,
      cmd_has_ty (<["$this" := ClassT t targs]>mdef.(methodargs)) mdef.(methodbody) lty ∧
      expr_has_ty lty mdef.(methodret) mdef.(methodrettype)
    .

    Record wf_cdefs (prog: stringmap classDef)  := {
      wf_fields : map_Forall (fun cname => wf_cdef_fields) prog;
      wf_methods : map_Forall (fun cname => wf_cdef_methods) prog;
      wf_mdefs :
      map_Forall (fun cname cdef =>
      map_Forall (fun mname mdef => wf_mdef_ty cname (gen_targs cdef.(generics)) mdef) cdef.(classmethods)) prog
    }
    .

    (* Big set reduction *)
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

    Definition local_env := gmap var value.

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
      | VarE v => le !! v
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
      rewrite -> map_Forall_lookup in H.
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
      rewrite -> map_Forall_lookup in H.
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
        rewrite map_Forall_lookup in H.
        now apply H in hin.
    Qed.

    Definition tag_match (st : local_env * heap) (v: string) (t: tag) :=
      ∃ l, st.1 !! v = Some (LocV l) ∧
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
      (* targs are not stored in the heap: erased generics *)
      | NewEv: ∀ le h lhs new t targs args vargs,
          h !! new = None →
          map_args (expr_eval le) args = Some vargs →
          cmd_eval (le, h) (NewC lhs t targs args) (<[lhs := LocV new]>le, <[new := (t, vargs)]>h) 1
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
      | CallEv: ∀ le h h' lhs recv l t vs name args vargs mdef
          run_env run_env' ret n,
          expr_eval le recv = Some (LocV l) →
          map_args (expr_eval le) args = Some vargs →
          h !! l = Some (t, vs) →
          has_method name mdef t →
          <["$this" := LocV l]>vargs = run_env →
          cmd_eval (run_env, h) mdef.(methodbody) (run_env', h') n →
          expr_eval run_env' mdef.(methodret) = Some ret →
          cmd_eval (le, h) (CallC lhs recv name args) (<[lhs := ret]>le, h') (S n)
      | CondTag1Ev n st1 st2 v t cmd :
          (* tag in heap must <: requested tag to move forward *)
          tag_match st1 v t →
          cmd_eval st1 cmd st2 n →
          cmd_eval st1 (CondTagC v t cmd) st2 n
      | CondTag2Ev n st v t cmd :
          ¬tag_match st v t →
          cmd_eval st (CondTagC v t cmd) st n
.
End ProgDef.

(* Hints and notations are local to the section. Re-exporting them *)
Global Hint Constructors subtype : core.
Global Hint Constructors has_field : core.
Global Hint Constructors has_method : code.
