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
Ltac rw_inj H0 H1 := rewrite H0 in H1; injection H1; intros; subst; clear H1.

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

Section nested_ind.
  Local Unset Elimination Schemes.

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
    | GenT (n: nat)
    | ExT (cname: tag) (* Ext C == ∃Ti, ClassT C Ti *) 
  .

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
  Hypothesis case_GenT: ∀ n, P (GenT n).
  Hypothesis case_ExT: ∀ cname, P (ExT cname).

  Fixpoint lang_ty_ind (t : lang_ty) :=
    match t with
    | IntT => case_IntT
    | BoolT => case_BoolT
    | NothingT => case_NothingT
    | MixedT => case_MixedT
    | ClassT cname targs =>
        let H := (fix fold (xs : list lang_ty) : Forall P xs :=
          match xs with
          | nil => List.Forall_nil _
          | x :: xs => List.Forall_cons _ x xs (lang_ty_ind x) (fold xs)
          end) targs in
        case_ClassT cname targs H
    | NullT => case_NullT
    | NonNullT => case_NonNullT
    | UnionT s t => case_UnionT s t (lang_ty_ind s) (lang_ty_ind t)
    | InterT s t => case_InterT s t (lang_ty_ind s) (lang_ty_ind t)
    | GenT n => case_GenT n
    | ExT cname => case_ExT cname
    end.
End nested_ind.

(* Not used yet *)
Inductive bounded (n: nat) : lang_ty → Prop :=
  | ClassIsBounded cname targs :
      Forall (bounded n) targs → bounded n (ClassT cname targs)
  | UnionIsBounded s t :
      bounded n s → bounded n t → bounded n (UnionT s t)
  | InterIsBounded s t :
      bounded n s → bounded n t → bounded n (InterT s t)
  | GenIsBounded k:
      k < n → bounded n (GenT k)
  | IntIsBounded : bounded n IntT
  | BoolIsBounded : bounded n BoolT
  | NothingIsBounded : bounded n NothingT
  | MixedIsBounded : bounded n MixedT
  | NullIsBounded : bounded n NullT
  | NonNullIsBounded : bounded n NonNullT
  | ExIsBounded cname : bounded n (ExT cname)
.

Global Hint Constructors bounded : core.

(* Generics must be always bound *)
Fixpoint subst_ty (targs:list lang_ty) (ty: lang_ty):  lang_ty :=
  match ty with
  | ClassT cname cargs => ClassT cname (subst_ty targs <$> cargs)
  | UnionT s t => UnionT (subst_ty targs s) (subst_ty targs t)
  | InterT s t => InterT (subst_ty targs s) (subst_ty targs t)
  | GenT n => default NothingT (targs !! n)
  | ExT _ | IntT | BoolT | NothingT | MixedT | NullT | NonNullT => ty
  end.

Lemma subst_ty_subst ty l k:
  subst_ty l (subst_ty k ty) = subst_ty (subst_ty l <$> k) ty.
Proof.
  induction ty as [ | | | | cname targs hi | | | s t hs ht |
      s t hs ht | n | cname ] => //=.
  - f_equal.
    rewrite -list_fmap_compose.
    rewrite Forall_forall in hi.
    apply map_ext_in => s /elem_of_list_In hin.
    by apply hi.
  - by f_equal.
  - by f_equal.
  - destruct (k !! n) as [ ty | ] eqn:hty.
    + by rewrite /= list_lookup_fmap hty.
    + by rewrite /= list_lookup_fmap hty.
Qed.

Lemma map_subst_ty_subst (j k l: list lang_ty):
  subst_ty j <$> (subst_ty k <$> l) =
  subst_ty (subst_ty j <$> k) <$> l.
Proof.
  induction l as [ | hd tl hi] => //=.
  rewrite subst_ty_subst.
  f_equal.
  by rewrite list_fmap_compose -/subst_ty list_fmap_id -/fmap hi.
Qed.

Lemma fmap_subst_ty_subst j k (l: stringmap lang_ty):
  subst_ty j <$> (subst_ty k <$> l) =
  subst_ty (subst_ty j <$> k) <$> l.
Proof.
  move: j k.
  induction l as [| s ty ftys Hs IH] using map_ind => j k;
    first by rewrite !fmap_empty.
  by rewrite !fmap_insert subst_ty_subst IH.
Qed.

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
  | NewC (lhs: var) (class_name: tag) (args: stringmap expr)
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

Definition subst_mdef targs mdef : methodDef := {|
    methodname := mdef.(methodname);
    methodargs := subst_ty targs <$> mdef.(methodargs);
    methodrettype := subst_ty targs mdef.(methodrettype);
    methodbody := mdef.(methodbody);
    methodret := mdef.(methodret);
  |}.

Lemma subst_mdef_mdef k l mdef :
  subst_mdef k (subst_mdef l mdef) = subst_mdef (subst_ty k <$> l) mdef.
Proof.
  rewrite /subst_mdef; destruct mdef as [? args ret ? ?]; f_equiv => //=.
  - by rewrite fmap_subst_ty_subst.
  - by rewrite subst_ty_subst.
Qed.


Record classDef := {
  classname: tag;
  generics: nat; (* number of generics, no constraint for now *)
  superclass: option (tag * list lang_ty);
  classfields : stringmap lang_ty;
  classmethods : stringmap methodDef;
}.

(* Wf defintions on the source *)
Definition mdef_bounded n mdef : Prop :=
  map_Forall (λ _argname, bounded n) mdef.(methodargs) ∧ bounded n mdef.(methodrettype).

Definition cdef_methods_bounded cdef : Prop :=
  map_Forall (λ _mname mdef, mdef_bounded cdef.(generics) mdef) cdef.(classmethods).

(* "Identity" substitution for n generics *)
Fixpoint gen_targs_ nleft n : list lang_ty :=
  match nleft with
  | O => []
  | S nleft => GenT n :: gen_targs_ nleft (S n)
  end.

Lemma length_gen_targs_: ∀ nleft n, length (gen_targs_ nleft n) = nleft.
Proof.
  elim => [ | nleft hi] n //=.
  by rewrite hi.
Qed.

Lemma lookup_gen_targs__lt :
  ∀ nleft n pos, pos < nleft →
  gen_targs_ nleft n !! pos = Some (GenT (n + pos)).
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
  ∀ n pos, pos < n → gen_targs n !! pos = Some (GenT pos).
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

Corollary length_gen_targs n : length (gen_targs n) = n.
Proof. by rewrite /gen_targs length_gen_targs_. Qed.

Corollary gen_targs_O : gen_targs 0 = [].
Proof. done. Qed.

Lemma subst_gen_targs_is_bounded n ty:
  bounded n ty →
  subst_ty (gen_targs n) ty = ty.
Proof.
  move => h.
  induction ty as [ | | | | cname targs hi | | | s t hs ht |
      s t hs ht | k | cname ] => //=.
  - f_equal.
    rewrite Forall_forall in hi.
    pattern targs at 2.
    replace targs with (map id targs) by apply map_id.
    apply map_ext_in => /= s /elem_of_list_In hin.
    apply hi => //.
    inv h.
    rewrite Forall_forall in H0.
    by apply H0.
  - inv h; f_equal; by eauto.
  - inv h; f_equal; by eauto.
  - inv h.
    by rewrite lookup_gen_targs_lt.
Qed.

Lemma subst_ty_gen_targs n targs :
  length targs = n →
  subst_ty targs <$> (gen_targs n) = targs.
Proof.
  move => hlen.
  apply nth_ext with NothingT NothingT.
  - by rewrite map_length length_gen_targs.
  - rewrite map_length length_gen_targs => k hk.
    rewrite !nth_lookup.
    f_equal.
    rewrite list_lookup_fmap lookup_gen_targs_lt => //=.
    rewrite -hlen in hk.
    apply lookup_lt_is_Some_2 in hk.
    destruct (targs !! k) => //=.
    by elim hk.
Qed.

Lemma subst_mdef_gen_targs_is_bounded n mdef :
  mdef_bounded n mdef →
  subst_mdef (gen_targs n) mdef = mdef.
Proof.
  rewrite /mdef_bounded /subst_mdef; move => [/map_Forall_lookup hargs hret].
  rewrite subst_gen_targs_is_bounded => //.
  replace (subst_ty (gen_targs n) <$> methodargs mdef) with (methodargs mdef);
    first by destruct mdef.
  apply map_eq => k.
  rewrite lookup_fmap.
  destruct (methodargs mdef !! k) as [ty | ] eqn:hty => //=.
  apply hargs in hty.
  by rewrite subst_gen_targs_is_bounded.
Qed.

(* A program is a collection of classes *)
Class ProgDefContext := { Δ : stringmap classDef }.

Section ProgDef.

  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.

  (* source relation `class A<...> extends B<...>` *)
  Inductive extends_using : tag → tag → list lang_ty → Prop :=
    | ExtendsUsing A B cdef σB:
        Δ !! A = Some cdef →
        cdef.(superclass) = Some (B, σB) →
        extends_using A B σB.

  Hint Constructors extends_using : core.

  Inductive extends: tag → tag → Prop :=
    | Extends A B cdef σB:
        Δ !! A = Some cdef →
        cdef.(superclass) = Some (B, σB) →
        extends A B.

  Hint Constructors extends : core.

  Inductive inherits_using : tag → tag → list lang_ty → Prop :=
    | InheritsExtends A B σ:
        extends_using A B σ →
        inherits_using A B σ
    | InheritsTrans A B σB C σC:
        inherits_using A B σB →
        inherits_using B C σC →
        inherits_using A C (subst_ty σB <$> σC)
  .

  Hint Constructors inherits_using : core.

  Definition inherits := rtc extends.

  Lemma inherits_to_using A B:
    inherits A B → (A = B) ∨ ∃ σ, inherits_using A B σ.
  Proof.
    induction 1 as [ x | x y z hxy hyz hi].
    - by left.
    - destruct hi as [-> | [σ hi]]; right.
      + inv hxy.
        exists σB; by eauto.
      + inv hxy.
        exists (subst_ty σB <$> σ); by eauto.
  Qed.

  Inductive subtype : lang_ty → lang_ty → Prop :=
    | SubMixed : ∀ ty, subtype ty MixedT
    | SubClass : ∀ A σA B σB, extends_using A B σB →
        subtype (ClassT A σA) (ClassT B (subst_ty σA <$> σB))
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
    | SubExT : ∀ cname targs, subtype (ClassT cname targs) (ExT cname)
  .
  (* TODO: add Nothing <: t ? *)

  Hint Constructors subtype : core.

  Notation "s <: t" := (subtype s t) (at level 70, no associativity).

  (* Not used yet *)
  Inductive is_class : lang_ty → Prop :=
    | IsClass A σA : is_class (ClassT A σA)
  .

  Lemma SubClassInherits A B σB:
    inherits_using A B σB →
    ∀ σA,
    (ClassT A σA) <: (ClassT B (subst_ty σA <$> σB)).
  Proof.
    induction 1 as [ A B σ hext | A B σB C σC hAB hiAB hBC hiBC ] => σA (*hσA*).
    - by econstructor.
    - eapply SubTrans.
      + by apply hiAB.
      + rewrite map_subst_ty_subst.
        by apply hiBC.
  Qed.

  Lemma subtype_subst A B:
    A <: B → ∀ targs, (subst_ty targs A) <: (subst_ty targs B).
  Proof.
    induction 1 as [ ty | A σA B σB hext | | | | A args | s t | s t
      | s t u hs his ht hit | s t | s t | s t u hs his ht hit | s
      | s t u hst hist htu hitu | cname args ] => targs //=.
    - rewrite map_subst_ty_subst.
      by constructor.
    - constructor; by eauto.
    - constructor; by eauto.
    - econstructor; by eauto.
  Qed.

  Corollary subtype_inst_class A B σA σB σ :
    (ClassT A σA) <: (ClassT B σB) →
    (ClassT A (subst_ty σ <$> σA)) <: (ClassT B (subst_ty σ <$> σB)).
  Proof.
    move => h.
    by apply subtype_subst with (targs := σ) in h.
  Qed.

  (* Derived rules *)
  Lemma subtype_union_comm : ∀ A B, (UnionT A B) <: (UnionT B A).
  Proof. by auto.  Qed.

  Lemma subtype_inter_comm : ∀ A B, (InterT A B) <: (InterT B A).
  Proof. by auto.  Qed.

  Lemma subtype_union_assoc:
    ∀ A B C, (UnionT (UnionT A B) C) <: (UnionT A (UnionT B C)).
  Proof. by eauto. Qed.

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

  Inductive has_field (fname: string) : tag -> lang_ty → list lang_ty → Prop :=
    | HasField tag cdef typ:
        Δ !! tag = Some cdef →
        cdef.(classfields) !! fname = Some typ →
        has_field fname tag typ (gen_targs cdef.(generics))
    | InheritsField tag targs parent inst cdef typ:
        Δ !! tag = Some cdef →
        cdef.(classfields) !! fname = None →
        cdef.(superclass) = Some (parent, targs) →
        has_field fname parent typ inst →
        has_field fname tag typ (subst_ty targs <$> inst)
  .

  Hint Constructors has_field : core.

  Lemma has_field_fun fname A typ σ:
    has_field fname A typ σ →
    ∀ typ' σ', has_field fname A typ' σ' →
    typ = typ' ∧ σ = σ'.
  Proof.
    induction 1 as [ tag cdef typ hΔ hf
      | tag targs parent inst cdef typ hΔ hf hs h hi ] => typ' σ' h'.
    - inv h'.
      + rw_inj hΔ H.
        rw_inj hf H0.
        done.
      + rw_inj hΔ H.
        rewrite hf in H0; discriminate.
    - inv h'.
      + rw_inj hΔ H.
        rewrite hf in H0; discriminate.
      + rw_inj hΔ H.
        rw_inj hs H1.
        by apply hi in H2 as [-> ->].
  Qed.

  (* A class cannot redeclare a field if it is present in
   * any of its parent definition.
   *)
  Definition wf_cdef_fields cdef : Prop :=
    ∀ f fty σ super inst,
    cdef.(superclass) = Some (super, inst) →
    has_field f super fty σ →
    cdef.(classfields) !! f = None.

  Definition wf_cdef_fields_bounded cdef : Prop :=
    map_Forall (λ _fname, bounded cdef.(generics)) cdef.(classfields).

  (*
  Lemma has_field_extends_using fname A typ finst:
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    has_field fname A typ finst →
    ∀ B σB typ' finst',
    extends_using A B σB →
    has_field fname B typ' finst' →
    (typ = typ' ∧ finst = subst_ty σB <$> finst').
  Proof.
    move => hwf.
    induction 1 as [ tag cdef typ hΔ hf
      | tag targs parent inst cdef typ hΔ hf hs h hi ] => B σB typ' finst' hext hB.
    - rewrite map_Forall_lookup in hwf.
      inv hext.
      rewrite hΔ in H; injection H; intros; subst; clear H.
      apply hwf in hΔ.
      by rewrite (hΔ _ _ _ _ _ H0 hB) in hf.
    - inv hext.
      rewrite hΔ in H; injection H; intros; subst; clear H.
      rewrite hs in H0; injection H0; intros; subst; clear H0.
      by apply (has_field_fun _ _ _ _ h) in hB as [-> ->].
  Qed.
  *)

  (* Naive method lookup: methods are unique. *)
  Inductive has_method (mname: string) : methodDef → tag → Prop :=
    | HasMethod tag cdef mdef:
        Δ !! tag = Some cdef →
        cdef.(classmethods) !! mname = Some mdef →
        has_method mname mdef tag
    | InheritsMethod tag parent σ cdef mdef:
        Δ !! tag = Some cdef →
        cdef.(classmethods) !! mname = None →
        cdef.(superclass) = Some (parent, σ) →
        has_method mname mdef parent →
        has_method mname mdef tag
  .

  Hint Constructors has_method : code.

  (*
  Lemma has_method_from n m mdef A:
    mdef_bounded n mdef →
    has_method m mdef A →
    ∃ B cdef orig inst,
    Δ !! B = Some cdef ∧
    cdef.(classmethods) !! m = Some orig ∧
    mdef = subst_mdef inst orig ∧
    inherits A B.
  Proof.
    move => hwf.
    induction 1 as [ tag cdef mdef hΔ hm 
      | tag parent inst cdef mdef hΔ hm hs h hi].
    - exists tag, cdef, mdef, (gen_targs n); repeat split => //.
      by rewrite subst_mdef_gen_targs_is_bounded.
    - destruct hi as (B & bdef & orig & Binst & hΔ' & horig & heq & hinherits). 
      exists B, bdef, orig, (subst_ty targs <$> Binst).
      split; first done.
      split; first done.
      split; first by rewrite heq subst_mdef_mdef.
      econstructor; last first.
      + change (ClassT B (subst_ty targs <$> Binst)) with
        (subst_ty targs (ClassT B Binst)).
        apply inherits_subst.
        exact hinherits.
      + by econstructor.
  Qed.
   *)


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
    ∀ m mdef superdef super σ,
    cdef.(superclass) = Some (super, σ) →
    has_method m superdef super →
    cdef.(classmethods) !! m = Some mdef →
    mdef_incl mdef superdef.

  Definition has_fields A (fields: stringmap (lang_ty * list lang_ty)) : Prop :=
    ∀ fname typ inst, has_field fname A typ inst ↔ fields !! fname = Some (typ, inst).

  Definition lift_fty (σ: list lang_ty) (fty: lang_ty * list lang_ty) :=
    (fty.1, subst_ty σ <$> fty.2).

  (*
  Lemma has_method_fun: ∀ A name mdef0 mdef1,
    has_method name mdef0 A → has_method name mdef1 A → mdef0 = mdef1.
  Proof.
    move => A name mdef0 mdef1 h; move: mdef1.
    induction h as [ current cdef mdef hΔ hm 
      | current parent inst cdef mdef hΔ hm hs hp hi ] => mdef1 h1.
    - inv h1.
      + rewrite hΔ in H; injection H; intros; subst; clear hΔ H.
        rewrite hm in H0; injection H0; intros; by subst.
      + rewrite hΔ in H; injection H; intros; subst; clear hΔ H.
        rewrite hm in H0; discriminate H0.
    - inv h1.
      + rewrite hΔ in H; injection H; intros; subst; clear hΔ H.
        rewrite hm in H0; discriminate H0.
      + rewrite hΔ in H; injection H; intros; subst; clear hΔ H.
        rewrite hs in H1; injection H1; intros; subst; clear hs H1.
        apply hi in H2; by subst.
  Qed.
   *)

  Lemma has_field_inherits :
    map_Forall (fun _ => wf_cdef_fields) Δ →
    ∀ A B σ, inherits_using A B σ → 
    ∀ f fty σf, has_field f B fty σf → has_field f A fty (subst_ty σ <$> σf).
  Proof.
    move => wfΔ A B σ h.
    induction h as [ A B σ hext | A B σB C σC hAB hiAB hBC hiBC]; move => f fty σf hf.
    - inv hext.
      econstructor => //.
      apply wfΔ in H.
      by eapply H.
    - apply hiBC in hf.
      apply hiAB in hf.
      by rewrite -map_subst_ty_subst.
  Qed.

  Lemma has_fields_inherits :
    map_Forall (fun _ => wf_cdef_fields) Δ →
    ∀ A B σ, inherits_using A B σ → 
    ∀ Afields Bfields, has_fields A Afields → has_fields B Bfields →
    ∀ k fty σf, Bfields !! k = Some (fty, σf) →
    Afields !! k = Some (fty, subst_ty σ <$> σf).
  Proof.
    move => wfΔ A B σ hin Afields Bfields hA hB k fty σf hk.
    apply hB in hk.
    apply has_field_inherits with (A := A) (σ := σ) in hk => //.
    by apply hA.
  Qed.

  (*

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
   *)

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
    | GetTy: ∀ lty lhs recv t σ σf name fty,
        expr_has_ty lty recv (ClassT t σ) →
        has_field name t fty σf →
        cmd_has_ty lty (GetC lhs recv name) (<[lhs := subst_ty σ (subst_ty σf fty)]>lty)
    | SetTy: ∀ lty recv fld rhs fty σf t σ,
        expr_has_ty lty recv (ClassT t σ) →
        has_field fld t fty σf →
        expr_has_ty lty rhs (subst_ty σ (subst_ty σf fty)) →
        cmd_has_ty lty (SetC recv fld rhs) lty
        (*
    | NewTy: ∀ lty lhs t targs args fields (*cdef*),
        (* Δ !! t = Some cdef → *)
        (* length targs = cdef.(generics) → (1* check constraints *1) *)
        has_fields t fields →
        dom (gset string) fields = dom _ args →
        (∀ f fty arg,
        fields !! f = Some fty →
        args !! f = Some arg →
        expr_has_ty lty arg (subst_ty targs fty)) →
        cmd_has_ty lty (NewC lhs t args) (<[lhs := ClassT t targs]>lty)
    | CallTy: ∀ lty lhs recv t targs name mdef args (*cdef*),
        (* Δ !! t = Some cdef → *)
        (* length targs = cdef.(generics) → *)
        expr_has_ty lty recv (ClassT t targs) →
        has_method name mdef t →
        dom (gset string) mdef.(methodargs) = dom _ args →
        (∀ x ty arg,
        mdef.(methodargs) !! x = Some ty →
        args !! x = Some arg →
        expr_has_ty lty arg (subst_ty targs ty)) →
        cmd_has_ty lty (CallC lhs recv name args) (<[lhs := subst_ty targs mdef.(methodrettype)]>lty)
         *)
    | SubTy: ∀ lty c rty rty',
        rty' <:< rty →
        cmd_has_ty lty c rty' →
        cmd_has_ty lty c rty
    | CondTagTy lty v tv t cmd :
        lty !! v = Some tv →
        cmd_has_ty (<[v:=InterT tv (ExT t)]> lty) cmd lty →
        cmd_has_ty lty (CondTagC v t cmd) lty
  .

  (* TODO: update
  Corollary CallTy_: ∀ lty lhs recv t targs name mdef args,
    expr_has_ty lty recv (ClassT t targs) →
    has_method name mdef t →
    dom (gset string) mdef.(methodargs) = dom _ args →
    (∀ x ty arg,
    mdef.(methodargs) !! x = Some ty →
    args !! x = Some arg →
    ∃ ty', ty' <: subst_ty targs ty ∧ expr_has_ty lty arg ty') →
    cmd_has_ty lty (CallC lhs recv name args) (<[lhs := subst_ty targs mdef.(methodrettype)]>lty).
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
    ∃ ty', ty' <: subst_ty targs ty ∧ expr_has_ty lty arg ty') →
    subst_ty targs mdef.(methodrettype) <: ret →
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
   *)

  Definition subst_local_tys targs (lty: local_tys) : local_tys :=
    (subst_ty targs) <$> lty.

  Lemma dom_subst_local_tys targs lty :
    dom stringset (subst_local_tys targs lty) = dom _ lty.
  Proof. by rewrite /subst_local_tys dom_fmap_L. Qed.

  Lemma lookup_subst_local_tys targs lty k:
    (subst_local_tys targs lty) !! k = subst_ty targs <$> lty !! k.
  Proof. by rewrite /subst_local_tys lookup_fmap. Qed.

  Lemma lookup_subst_local_tys_Some targs lty k ty:
    (subst_local_tys targs lty) !! k = Some ty →
    ∃ ty', lty !! k = Some ty' ∧ ty = subst_ty targs ty'.
  Proof.
    rewrite lookup_subst_local_tys.
    destruct (lty !! k) as [ ty' | ] eqn:h => //=.
    case => <-.
    by exists ty'.
  Qed.

  Lemma insert_subst_local_tys targs lhs ty lty:
    subst_local_tys targs (<[lhs:=ty]> lty) =
    <[lhs := subst_ty targs ty]>(subst_local_tys targs lty).
  Proof. by rewrite /subst_local_tys fmap_insert. Qed.

  Lemma subst_local_tys_gen_targs_is_bounded n lty:
    map_Forall (λ _ ty, bounded n ty) lty →
    subst_local_tys (gen_targs n) lty = lty.
  Proof.
    move => h.
    apply map_eq => k.
    rewrite lookup_subst_local_tys.
    rewrite map_Forall_lookup in h.
    destruct (lty !! k) as [ty | ] eqn:hty => //=.
    rewrite hty.
    apply h in hty.
    by rewrite subst_gen_targs_is_bounded.
  Qed.

  Lemma lty_sub_subst lty rty:
    lty <:< rty →
    ∀ targs, (subst_local_tys targs lty) <:< (subst_local_tys targs rty).
  Proof.
    rewrite /lty_sub => h targs k A.
    rewrite !lookup_subst_local_tys.
    destruct (rty !! k) as [ty | ] eqn:hty; last done.
    move => /= [<-].
    apply h in hty as [B [-> hsub]].
    exists (subst_ty targs B); split; first done.
    by apply subtype_subst.
  Qed.

  Lemma expr_has_ty_subst lty e ty:
    expr_has_ty lty e ty →
    ∀ targs,
    expr_has_ty (subst_local_tys targs lty) e (subst_ty targs ty).
  Proof.
    induction 1 as [ z | b | | op e1 e2 hop h1 hi1 h2 hi2
      | op e1 e2 hop h1 hi1 h2 hi2 | v ty hv
      | e s t hs hi hsub ] => targs; try by constructor.
    - simpl in *; by constructor.
    - simpl in *; by constructor.
    - constructor.
      by rewrite /subst_local_tys lookup_fmap hv.
    - econstructor; first by apply hi.
      by apply subtype_subst.
  Qed.

  (* Consider a class C<T0, ..., Tn>,
     method bodies are checked under a generic env = [| T0, .., Tn |]
   *)
  Definition wf_mdef_ty t n mdef :=
    let targs := gen_targs n in
    ∃ lty,
    cmd_has_ty (<["$this" := ClassT t targs]>(subst_local_tys targs mdef.(methodargs))) mdef.(methodbody) lty ∧
    expr_has_ty lty mdef.(methodret) (subst_ty targs mdef.(methodrettype))
  .

  Record wf_cdefs (prog: stringmap classDef) := {
    wf_fields : map_Forall (λ _cname, wf_cdef_fields) prog;
    wf_fields_bounded : map_Forall (λ _cname, wf_cdef_fields_bounded) prog;
    wf_methods : map_Forall (λ _cname, wf_cdef_methods) prog;
    wf_methods_bounded : map_Forall (λ _cname, cdef_methods_bounded) prog;
    wf_mdefs :
      map_Forall (λ cname cdef,
        map_Forall (λ _mname mdef,
           wf_mdef_ty cname cdef.(generics) mdef)
        cdef.(classmethods)) prog
  }
  .

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
    | NewEv: ∀ le h lhs new t args vargs,
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
Global Hint Constructors has_method : core.
