(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 * 
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
From stdpp Require Import base strings gmap stringmap fin_maps.
(* Not using iris but importing their ssreflect dependencies *)
From iris.proofmode Require Import tactics.

(* TODO:
 * - maybe update definitions of bounded and gen_targs to take
 *   a variance list or a class definition as input, and some
 *   of the details away.
 *)

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

(* A type is bounded by n if any generic that might be
 * present in it is < n
 *)
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

(* To be used with `bounded`: Generics must be always bound *)
Fixpoint subst_ty (targs:list lang_ty) (ty: lang_ty):  lang_ty :=
  match ty with
  | ClassT cname cargs => ClassT cname (subst_ty targs <$> cargs)
  | UnionT s t => UnionT (subst_ty targs s) (subst_ty targs t)
  | InterT s t => InterT (subst_ty targs s) (subst_ty targs t)
  | GenT n => default ty (targs !! n)
  | ExT _ | IntT | BoolT | NothingT | MixedT | NullT | NonNullT => ty
  end.

Corollary subst_ty_nil ty : subst_ty [] ty = ty.
Proof.
  induction ty as [ | | | | cname targs hi | | | s t hs ht |
      s t hs ht | n | cname ] => //=.
  - f_equal.
    rewrite Forall_forall in hi.
    pattern targs at 2.
    replace targs with (map id targs) by apply map_id.
    apply map_ext_in => s /elem_of_list_In hin.
    by apply hi.
  - by rewrite hs ht.
  - by rewrite hs ht.
Qed.

Corollary map_subst_ty_nil (σ: list lang_ty) : subst_ty [] <$> σ = σ.
Proof.
  induction σ as [ | hd tl hi] => //=.
  f_equal; first by rewrite subst_ty_nil.
  by apply hi.
Qed.

Corollary fmap_subst_ty_nil (σ: stringmap lang_ty) : subst_ty [] <$> σ = σ.
Proof.
  induction σ as [| s ty ftys Hs IH] using map_ind => //=.
  - by rewrite fmap_empty.
  - by rewrite fmap_insert IH subst_ty_nil.
Qed.

Lemma subst_ty_subst ty l k:
  bounded (length k) ty →
  subst_ty l (subst_ty k ty) = subst_ty (subst_ty l <$> k) ty.
Proof.
  move => hbounded.
  induction ty as [ | | | | cname targs hi | | | s t hs ht |
      s t hs ht | n | cname ] => //=.
  - f_equal.
    rewrite -list_fmap_compose.
    rewrite Forall_forall in hi.
    apply map_ext_in => s /elem_of_list_In hin.
    apply hi => //.
    inv hbounded.
    rewrite Forall_forall in H0.
    by apply H0.
  - inv hbounded.
    f_equal; by eauto.
  - inv hbounded.
    f_equal; by eauto.
  - rewrite list_lookup_fmap.
    destruct (k !! n) as [ ty | ] eqn:hty => //=.
    inv hbounded.
    apply lookup_lt_is_Some_2 in H0.
    rewrite hty in H0.
    by elim H0.
Qed.

Lemma map_subst_ty_subst (j k l: list lang_ty):
  Forall (bounded (length k)) l →
  subst_ty j <$> (subst_ty k <$> l) =
  subst_ty (subst_ty j <$> k) <$> l.
Proof.
  move => hwf.
  induction l as [ | hd tl hi] => //=.
  inv hwf.
  rewrite subst_ty_subst => //.
  f_equal.
  by rewrite list_fmap_compose -/subst_ty list_fmap_id -/fmap hi.
Qed.

Lemma fmap_subst_ty_subst j k (l: stringmap lang_ty):
  map_Forall (λ _, bounded (length k)) l →
  subst_ty j <$> (subst_ty k <$> l) =
  subst_ty (subst_ty j <$> k) <$> l.
Proof.
  move => hwf.
  move: j k hwf.
  induction l as [| s ty ftys Hs IH] using map_ind => j k hwf;
    first by rewrite !fmap_empty.
  rewrite map_Forall_insert // in hwf.
  destruct hwf as [hhd htl].
  by rewrite !fmap_insert subst_ty_subst // IH.
Qed.

Lemma bounded_subst n ty:
  bounded n ty →
  ∀ m targs, length targs = n →
  Forall (bounded m) targs →
  bounded m (subst_ty targs ty).
Proof.
  induction ty as [ | | | | cname targs hi | | | s t hs ht |
      s t hs ht | k | cname ] => //= hb m σ hlen hσ.
  - constructor.
    rewrite Forall_forall => ty /elem_of_list_fmap hin.
    destruct hin as [ty' [-> hin]].
    rewrite Forall_forall in hi.
    apply hi with (m := m) (targs := σ) in hin => //.
    inv hb.
    rewrite Forall_forall in H0.
    by apply H0.
  - inv hb.
    constructor; by eauto.
  - inv hb.
    constructor; by eauto.
  - inv hb.
    rewrite Forall_forall in hσ.
    apply hσ.
    apply lookup_lt_is_Some_2 in H0.
    destruct (σ !! k) as [ ty | ] eqn:hty; last by elim H0.
    by apply elem_of_list_lookup_2 in hty.
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
  | ThisE (* $this *)
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
      (* tag test "if ($v is C<_>) { ... }" *)
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

Lemma subst_mdef_nil mdef : subst_mdef [] mdef = mdef.
Proof.
  rewrite /subst_mdef subst_ty_nil fmap_subst_ty_nil.
  by destruct mdef.
Qed.

Lemma subst_mdef_body mdef σ: methodbody (subst_mdef σ mdef) = methodbody mdef.
Proof. by []. Qed.

Lemma subst_mdef_ret mdef σ: methodret (subst_mdef σ mdef) = methodret mdef.
Proof. by []. Qed.

Definition mdef_bounded n mdef : Prop :=
  map_Forall (λ _argname, bounded n) mdef.(methodargs) ∧ bounded n mdef.(methodrettype).

Lemma subst_mdef_mdef k l mdef :
  mdef_bounded (length l) mdef →
  subst_mdef k (subst_mdef l mdef) = subst_mdef (subst_ty k <$> l) mdef.
Proof.
  rewrite /mdef_bounded map_Forall_lookup.
  case => hargs hret.
  rewrite /subst_mdef; destruct mdef as [? args ret ? ?]; f_equiv => //=.
  - by rewrite fmap_subst_ty_subst.
  - by rewrite subst_ty_subst.
Qed.

Lemma bounded_subst_mdef n mdef:
  mdef_bounded n mdef →
  ∀ m targs, length targs = n →
  Forall (bounded m) targs →
  mdef_bounded m (subst_mdef targs mdef).
Proof.
  move => [/map_Forall_lookup hargs hret] m σ hl hf.
  rewrite /mdef_bounded /subst_mdef /=; split; last by apply bounded_subst with n.
  rewrite map_Forall_lookup => k ty hty.
  apply lookup_fmap_Some in hty as [ty' [ <- hm]].
  apply bounded_subst with n => //.
  by eapply hargs.
Qed.

Inductive variance : Set :=
  | Invariant
  | Covariant
  | Contravariant
.

Definition neg_variance v :=
  match v with
  | Invariant => Invariant
  | Covariant => Contravariant
  | Contravariant => Covariant
  end
.

Lemma neg_variance_idem v : neg_variance (neg_variance v) = v.
Proof. by destruct v. Qed.

Lemma neg_variance_fmap_idem (vs: list variance) : neg_variance <$> (neg_variance <$> vs) = vs.
Proof.
  induction vs as [ | v vs hi] => //.
  by rewrite !fmap_cons neg_variance_idem hi.
Qed.

Definition not_cov v :=
  match v with
  | Invariant | Contravariant => true
  | Covariant => false
  end
.

Definition not_contra v :=
  match v with
  | Invariant | Covariant => true
  | Contravariant => false
  end
.

Inductive visibility := Public | Private.

Record classDef := {
  classname: tag;
  generics: list variance; (* variance of the generics *)
  superclass: option (tag * list lang_ty);
  classfields : stringmap (visibility * lang_ty);
  classmethods : stringmap methodDef;
}.

(* "Identity" substitution for n generics *)
Definition gen_targs n : list lang_ty := map GenT (seq 0 n).

Lemma lookup_gen_targs_lt :
  ∀ n pos, pos < n → gen_targs n !! pos = Some (GenT pos).
Proof.
  move => n pos h.
  by rewrite /gen_targs list_lookup_fmap lookup_seq_lt.
Qed.

Lemma lookup_gen_targs:
  ∀ n pos ty, gen_targs n !! pos = Some ty -> ty = GenT pos.
Proof.
  move => n pos ty.
  rewrite /gen_targs => h.
  apply list_lookup_fmap_inv in h.
  destruct h as [? [-> h]].
  rewrite lookup_seq in h.
  by destruct h as [-> ?].
Qed.

Lemma length_gen_targs n : length (gen_targs n) = n.
Proof. by rewrite /gen_targs map_length seq_length. Qed.

Lemma subst_ty_id n ty:
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

Lemma subst_tys_id n σ:
  Forall (bounded n) σ →
  subst_ty (gen_targs n) <$> σ = σ.
Proof.
  revert n.
  induction σ as [ | hd tl hi] => σ //= hf.
  f_equal.
  - apply subst_ty_id.
    apply Forall_inv in hf.
    by apply hf.
  - apply hi.
    by apply Forall_inv_tail in hf.
Qed.

Lemma fmap_subst_tys_id n (m: stringmap lang_ty):
  map_Forall (λ _, bounded n) m →
  subst_ty (gen_targs n) <$> m = m.
Proof.
  revert n.
  induction m as [| s ty ftys Hs IH] using map_ind => n hm; first by rewrite fmap_empty.
  rewrite fmap_insert; f_equal.
  - apply subst_ty_id.
    apply hm with s.
    by rewrite lookup_insert.
  - apply IH.
    rewrite map_Forall_lookup => k tk hk.
    apply hm with k.
    rewrite lookup_insert_ne // => heq; subst.
    by rewrite Hs in hk.
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

Lemma subst_mdef_gen_targs n mdef :
  mdef_bounded n mdef →
  subst_mdef (gen_targs n) mdef = mdef.
Proof.
  rewrite /mdef_bounded /subst_mdef; move => [/map_Forall_lookup hargs hret].
  rewrite subst_ty_id => //.
  replace (subst_ty (gen_targs n) <$> methodargs mdef) with (methodargs mdef);
    first by destruct mdef.
  apply map_eq => k.
  rewrite lookup_fmap.
  destruct (methodargs mdef !! k) as [ty | ] eqn:hty => //=.
  apply hargs in hty.
  by rewrite subst_ty_id.
Qed.

Lemma bounded_gen_targs n: Forall (bounded n) (gen_targs n).
Proof.
  rewrite Forall_forall => ty.
  rewrite /gen_targs => h.
  apply elem_of_list_fmap_2 in h as [ k [-> hk]].
  constructor.
  rewrite elem_of_seq /= in hk.
  by destruct hk.
Qed.

(* A program is a collection of classes *)
Class ProgDefContext := { Δ : stringmap classDef }.

Section ProgDef.
  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.

  (* A type is well-formed w.r.t. Δ if all classes are
   * defined in Δ, substitution applied to classes have the
   * correct length, and they are all made of well-formed types.
   *)
  Inductive wf_ty : lang_ty → Prop :=
    | WfInt : wf_ty IntT
    | WfBool : wf_ty BoolT
    | WfNothing : wf_ty NothingT
    | WfMixed : wf_ty MixedT
    | WfClassT t σ def:
        Δ !! t = Some def →
        length σ = length def.(generics) →
        (∀ k ty, σ !! k = Some ty → wf_ty ty) →
        wf_ty (ClassT t σ)
    | WfNull : wf_ty NullT
    | WfNonNull : wf_ty NonNullT
    | WfUnion s t : wf_ty s → wf_ty t → wf_ty (UnionT s t)
    | WfInter s t : wf_ty s → wf_ty t → wf_ty (InterT s t)
    | WfGen k: wf_ty (GenT k)
    | WfEx t : wf_ty (ExT t)
  .

  Hint Constructors wf_ty : core.

  Lemma wf_ty_class t σ def:
    Δ !! t = Some def →
    length σ = length def.(generics) →
    Forall wf_ty σ →
    wf_ty (ClassT t σ).
  Proof.
    move => h hl hσ.
    econstructor => //.
    rewrite Forall_forall in hσ => k ty hk.
    apply elem_of_list_lookup_2 in hk.
    by apply hσ in hk.
  Qed.

  Lemma wf_ty_class_inv t σ:
    wf_ty (ClassT t σ) →
    Forall wf_ty σ.
  Proof.
    move => h.
    inv h.
    apply Forall_forall => ty hin.
    apply elem_of_list_lookup_1 in hin.
    destruct hin as [k hk].
    by apply H3 in hk.
  Qed.

  Lemma wf_ty_subst σ ty :
    Forall wf_ty σ →
    wf_ty ty → wf_ty (subst_ty σ ty).
  Proof.
    move => hwf.
    induction 1 as [ | | | | t targs def hdef hl h hi | | |
        s t hs his ht hit | s t hs his ht hit | | ] => //=; try (by constructor).
    - econstructor; [ done | by rewrite map_length | ].
      move => k ty.
      rewrite list_lookup_fmap.
      destruct (targs !! k) as [ tk | ] eqn:htk => //=.
      case => <-.
      by eapply hi.
    - destruct (σ !! k) as [ ty | ] eqn:hty => /=; last by constructor.
      rewrite Forall_forall in hwf; apply hwf.
      by apply elem_of_list_lookup_2 in hty.
  Qed.

  Lemma wf_ty_subst_map σ σ':
    Forall wf_ty σ →
    Forall wf_ty σ' →
    Forall wf_ty (subst_ty σ <$> σ').
  Proof.
    move => h h'.
    induction σ' as [ | hd tl hi ] => //=.
    constructor.
    - apply Forall_inv in h'.
      by apply wf_ty_subst.
    - apply hi.
      by apply Forall_inv_tail in h'.
  Qed.

  Lemma gen_targs_wf n k ty: gen_targs n !! k = Some ty → wf_ty ty.
  Proof.
    rewrite /gen_targs -/fmap => hx.
    apply list_lookup_fmap_inv in hx.
    destruct hx as [ty' [ -> h]].
    by constructor.
  Qed.

  (* A class definition 'parent' information is valid
   * if the parent class actually exists, and the subsitution is:
   * - of the right length (must capture all generics of the parent class)
   * - bounded by the current class (must only mention generics of the current class)
   * - be well-formed.
   * - respect variance (see wf_cdef_mono)
   *)
  Definition wf_cdef_parent (prog: stringmap classDef) cdef : Prop :=
    match cdef.(superclass) with
    | None => True
    | Some (parent, σ) =>
        ∃ pdef, prog !! parent = Some pdef ∧
        length σ = length pdef.(generics) ∧
        Forall wf_ty σ ∧
        Forall (bounded (length cdef.(generics))) σ
    end
  .
  
  Definition cdef_methods_bounded cdef : Prop :=
    map_Forall (λ _mname mdef, mdef_bounded (length cdef.(generics)) mdef) cdef.(classmethods).

  (* source relation `class A<...> extends B<...>` *)
  Inductive extends_using : tag → tag → list lang_ty → Prop :=
    | ExtendsUsing A B cdef σB:
        Δ !! A = Some cdef →
        cdef.(superclass) = Some (B, σB) →
        extends_using A B σB.

  Hint Constructors extends_using : core.

  Lemma extends_using_wf A B σ:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    extends_using A B σ →
    ∃ adef bdef,
    Δ !! A = Some adef ∧
    Δ !! B = Some bdef ∧
    Forall (bounded (length adef.(generics))) σ ∧
    length σ = length bdef.(generics) ∧
    Forall wf_ty σ.
  Proof.
    move => /map_Forall_lookup hwf hext.
    inv hext.
    assert (H' := H).
    apply hwf in H.
    rewrite /wf_cdef_parent H0 in H.
    destruct H as (pdef & h & hlen & hσ & hf).
    by exists cdef, pdef.
  Qed.
   
  Inductive inherits_using : tag → tag → list lang_ty → Prop :=
    | InheritsRefl A adef:
        Δ !! A = Some adef →
        inherits_using A A (gen_targs (length (adef.(generics))))
    | InheritsExtends A B σ:
        extends_using A B σ →
        inherits_using A B σ
    | InheritsTrans A B σB C σC:
        extends_using A B σB →
        inherits_using B C σC →
        inherits_using A C (subst_ty σB <$> σC)
  .

  Hint Constructors inherits_using : core.

  Lemma inherits_using_wf A B σ:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    inherits_using A B σ →
    ∃ adef bdef,
    Δ !! A = Some adef ∧
    Δ !! B = Some bdef ∧
    Forall (bounded (length adef.(generics))) σ ∧
    length σ = length bdef.(generics) ∧
    Forall wf_ty σ.
  Proof.
    move => hwf.
    induction 1 as [ A adef hΔ | A B σ hext | A B σ C σC hext h hi ].
    - exists adef, adef; repeat split => //.
      + by apply bounded_gen_targs.
      + by rewrite length_gen_targs.
      + rewrite Forall_forall => x hx.
        apply elem_of_list_lookup_1 in hx.
        destruct hx as [i hi].
        by apply gen_targs_wf in hi.
    - by apply extends_using_wf.
    - apply extends_using_wf in hext => //.
      destruct hext as [adef [bdef [ha0 [hb0 [hf0 [hl0 hσ]]]]]].
      destruct hi as [? [cdef [hb1 [hc1 [hf1 [hl1 hσC]]]]]].
      simplify_eq.
      exists adef, cdef; repeat split => //.
      + rewrite Forall_forall => ty hin.
        apply elem_of_list_fmap_2 in hin as [ty' [-> hin]].
        rewrite Forall_forall in hf1; apply hf1 in hin.
        by eapply bounded_subst.
      + by rewrite map_length.
      + apply Forall_forall => x hx.
        apply elem_of_list_fmap_2 in hx as [ty [ -> hty]].
        apply wf_ty_subst => //.
        rewrite Forall_forall in hσC.
        by apply hσC in hty.
  Qed.

  Lemma inherits_using_trans A B C σB σC:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    inherits_using A B σB →
    inherits_using B C σC →
    inherits_using A C (subst_ty σB <$> σC).
  Proof.
    move => hwf h;
    move : h C σC.
    induction 1 as [ A cdef hΔ | A B s hext | A B s C t hext h hi] => Z σ' hin.
    - rewrite subst_tys_id //.
      apply inherits_using_wf in hin => //.
      destruct hin as (? & ? & ? & ? & hF & _ ).
      by simplify_eq.
    - by econstructor.
    - assert (hCZ := hin).
      apply hi in hin; clear hi.
      rewrite -map_subst_ty_subst; first by eapply InheritsTrans.
      apply inherits_using_wf in h => //.
      apply inherits_using_wf in hCZ => //.
      destruct h as [bdef [cdef [hB [hC [hF0 [hlen0 _]]]]]].
      destruct hCZ as [? [zdef [hC' [hZ [hF1 [hlen1 _]]]]]].
      simplify_eq.
      by rewrite hlen0.
  Qed.

  (* Stripped version of extends_using/inherits_using, mostly for
   * evaluation when we don't care about the generics.
   *) 
  Inductive extends: tag → tag → Prop :=
    | Extends A B cdef σB:
        Δ !! A = Some cdef →
        cdef.(superclass) = Some (B, σB) →
        extends A B.

  Hint Constructors extends : core.
  Definition inherits := rtc extends.

  Lemma extends_using_erase t t' σ: extends_using t t' σ → extends t t'.
  Proof.
    move => h; inv h.
    by econstructor.
  Qed.

  Lemma inherits_using_erase t t' σ: inherits_using t t' σ → inherits t t'.
  Proof.
    induction 1 as [ A adef hΔ | A B σ hext | A B σ C σC hext h hi ].
    - by constructor.
    - apply extends_using_erase in hext.
      by econstructor.
    - apply extends_using_erase in hext.
      by econstructor.
  Qed.

  (* Our class inheritance tree/forest doesn't have cycles. Which means
   * inherits A B → inherits B A → A = B.
   *)
  Definition wf_no_cycle (prog: stringmap classDef) :=
    ∀ A B σ σ', inherits_using A B σ → inherits_using B A σ' → A = B ∧ σ = σ'.

  (* if A inherits B and A inherits C,
   * then either B inherits C or C inherits B *)
  Lemma inherits_using_chain A B σ:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    inherits_using A B σ →
    ∀ C σ', inherits_using A C σ' →
    (∃ σ'', (subst_ty σ <$> σ'' = σ' ∧ inherits_using B C σ'') ∨
            (subst_ty σ' <$> σ'' = σ ∧ inherits_using C B σ'')).
  Proof.
    move => hwf.
    induction 1 as [ A adef hΔ | A B s hext | A B s C t hext h hi] => Z σ' hz.
    - exists σ'; left; split => //.
      apply subst_tys_id.
      apply inherits_using_wf in hz => //.
      destruct hz as (? & ? & ? & ? & hF & _ ).
      by simplify_eq.
    - inv hext; inv hz.
      + simplify_eq.
        exists s; right; split; last by econstructor; econstructor.
        apply subst_tys_id.
        apply hwf in H.
        rewrite /wf_cdef_parent H0 in H.
        by destruct H as (? & ? & _ & _ & hF).
      + inv H1.
        simplify_eq.
        apply hwf in H.
        rewrite /wf_cdef_parent H0 in H.
        destruct H as (bdef & hB & hL & _ & hF).
        exists (gen_targs (length bdef.(generics))); left; split; last by econstructor.
        by rewrite subst_ty_gen_targs.
      + inv H1.
        simplify_eq.
        exists σC; by left.
    - destruct (inherits_using_wf _ _ _ hwf hz) as (adef & zdef & hA & hZ & hF0 & hL0 & _).
      inv hext; inv hz.
      + simplify_eq.
        exists (subst_ty s <$> t); right; split; last first.
        { eapply InheritsTrans => //.
          by econstructor.
        }
        rewrite subst_tys_id // Forall_forall => ty hty.
        apply elem_of_list_fmap_2 in hty as [ ty' [ -> hty']].
        apply hwf in hA.
        rewrite /wf_cdef_parent H0 in hA.
        destruct hA as (bdef & hB & hL & _ & hF).
        apply bounded_subst with (length (generics bdef)) => //.
        apply inherits_using_wf in h => //.
        destruct h as (? & cdef & ? & hC & hF' & hL' & _); simplify_eq.
        by rewrite Forall_forall in hF'; apply hF'.
      + inv H1.
        simplify_eq.
        exists t; by right.
      + inv H1.
        simplify_eq.
        apply hi in H2 as [σ'' [ [<- hx] | [<- hx]]]; clear hi.
        * exists σ''; left; split; last done.
          rewrite map_subst_ty_subst //.
          apply inherits_using_wf in h => //.
          apply inherits_using_wf in hx => //.
          destruct h as (bdef & Cdef & ? & ? & hf0 & hl0 & _).
          destruct hx as (? & zdef' & ? & ? & hf1 & hl1 & _).
          simplify_eq.
          by rewrite hl0.
        * exists σ''; right; split; last done.
          rewrite map_subst_ty_subst //.
          apply inherits_using_wf in h => //.
          apply inherits_using_wf in hx => //.
          destruct h as (bdef & Cdef & ? & ? & hf0 & hl0 & _).
          destruct hx as (zdef' & ? & ? & ? & hf1 & hl1 & _).
          simplify_eq.
          rewrite map_length in hL0.
          by rewrite hL0.
  Qed.

  Lemma inherits_using_refl A σ:
    wf_no_cycle Δ →
    inherits_using A A σ →
    ∃ adef, Δ !! A = Some adef ∧ σ = gen_targs (length adef.(generics)).
  Proof.
    move => hwf hA.
    assert (h: ∃ adef, Δ !! A = Some adef).
    { inv hA.
      - by exists adef.
      - inv H.
        by exists cdef.
      - inv H.
        by exists cdef.
    }
    destruct h as [adef hΔ].
    exists adef; split => //.
    eapply hwf; first by apply hA.
    by constructor.
  Qed.

  Lemma inherits_using_fun A B σ:
    wf_no_cycle Δ →
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    inherits_using A B σ →
    ∀ σ', inherits_using A B σ' → σ = σ'.
  Proof.
    move => hwf hp.
    induction 1 as [ A adef hΔ | A B s hext | A B s C t hext h hi ] => σ' hother.
    - apply inherits_using_refl in hother as [? [h ->]] => //.
      by simplify_eq.
    - inv hext; inv hother.
      + simplify_eq.
        destruct (inherits_using_refl B s) as [? [h ->]] => //; last by simplify_eq.
        eapply InheritsExtends.
        by econstructor.
      + inv H1; by simplify_eq.
      + inv H1; simplify_eq.
        apply inherits_using_refl in H2 as [bdef [hb ->]] => //.
        rewrite subst_ty_gen_targs //.
        apply hp in H.
        rewrite /wf_cdef_parent H0 in H.
        destruct H as [? [? [ -> _ ]]].
        by simplify_eq.
    - inv hext; inv hother.
      + simplify_eq.
        eapply hwf; last by constructor.
        eapply InheritsTrans; last done.
        by econstructor.
      + inv H1; simplify_eq.
        apply inherits_using_refl in h => //.
        destruct h as [bdef [hB ->]].
        rewrite subst_ty_gen_targs //.
        apply hp in H.
        rewrite /wf_cdef_parent H0 in H.
        destruct H as [? [? [ -> _ ]]].
        by simplify_eq.
      + inv H1; simplify_eq.
        apply hi in H2; by subst.
  Qed.

  (* Type well-formdness is mostly introduced to be able to define
   * subtyping rule correctly, like unions.
   *)
  Inductive subtype : lang_ty → lang_ty → Prop :=
    | SubMixed : ∀ ty, subtype ty MixedT
    | SubNothing : ∀ ty, wf_ty ty → subtype NothingT ty
    | SubClass : ∀ A σA B σB adef,
        Δ !! A = Some adef →
        length σA = length (adef.(generics)) →
        extends_using A B σB →
        subtype (ClassT A σA) (ClassT B (subst_ty σA <$> σB))
    | SubVariance : ∀ A adef σ0 σ1,
        Δ !! A = Some adef →
        Forall wf_ty σ1 →
        subtype_targs adef.(generics) σ0 σ1 →
        subtype (ClassT A σ0) (ClassT A σ1)
    | SubMixed2: subtype MixedT (UnionT NonNullT NullT)
    | SubIntNonNull: subtype IntT NonNullT
    | SubBoolNonNull: subtype BoolT NonNullT
    | SubClassNonNull: ∀ A targs, subtype (ClassT A targs) NonNullT
    | SubUnionUpper1 : ∀ s t, wf_ty t → subtype s (UnionT s t)
    | SubUnionUpper2 : ∀ s t, wf_ty s → subtype t (UnionT s t)
        (* TODO: Do we need this one ? *)
    | SubUnionLeast : ∀ s t u, subtype s u → subtype t u → subtype (UnionT s t) u
    | SubInterLower1 : ∀ s t, subtype (InterT s t) s
    | SubInterLower2 : ∀ s t, subtype (InterT s t) t
    | SubInterGreatest: ∀ s t u, subtype u s → subtype u t → subtype u (InterT s t)
    | SubRefl: ∀ s, subtype s s
    | SubTrans : ∀ s t u, subtype s t → subtype t u → subtype s u
 with subtype_targs : list variance → list lang_ty → list lang_ty → Prop :=
    | subtype_targs_nil : subtype_targs [] [] []
    | subtype_targs_invariant : ∀ ty0 ty1 vs ty0s ty1s,
        subtype ty0 ty1 →
        subtype ty1 ty0 →
        subtype_targs vs ty0s ty1s →
        subtype_targs (Invariant :: vs) (ty0 :: ty0s) ( ty1 :: ty1s)
    | subtype_targs_covariant : ∀ ty0 ty1 vs ty0s ty1s,
        subtype ty0 ty1 →
        subtype_targs vs ty0s ty1s →
        subtype_targs (Covariant :: vs) (ty0 :: ty0s) ( ty1 :: ty1s)
    | subtype_targs_contravariant : ∀ ty0 ty1 vs ty0s ty1s,
        subtype ty1 ty0 →
        subtype_targs vs ty0s ty1s →
        subtype_targs (Contravariant :: vs) (ty0 :: ty0s) ( ty1 :: ty1s)
  .
 
  Corollary length_subtype_targs_v0: ∀ vs ty0s ty1s,
    subtype_targs vs ty0s ty1s → length vs = length ty0s.
  Proof.
    induction 1 as [ | ??????? h hi | ?????? h hi | ?????? h hi] => //=; by rewrite hi.
  Qed.

  Corollary length_subtype_targs_v1: ∀ vs ty0s ty1s,
    subtype_targs vs ty0s ty1s → length vs = length ty1s.
  Proof.
    induction 1 as [ | ??????? h hi | ?????? h hi | ?????? h hi] => //=; by rewrite hi.
  Qed.

  Corollary length_subtype_targs_01: ∀ vs ty0s ty1s,
    subtype_targs vs ty0s ty1s → length ty0s = length ty1s.
  Proof.
    induction 1 as [ | ??????? h hi | ?????? h hi | ?????? h hi] => //=; by rewrite hi.
  Qed.

  Hint Constructors subtype : core.
  Hint Constructors subtype_targs : core.

  Notation "s <: t" := (subtype s t) (at level 70, no associativity).
  Notation "lts <: vs :> rts" := (subtype_targs vs lts rts) (at level 70, vs at next level).

  Lemma subtype_targs_refl vs: ∀ σ,
    length vs = length σ → σ <:vs:> σ.
  Proof.
    induction vs as [ | v vs hi] => σ hLen.
    - by rewrite (nil_length_inv σ).
    - destruct σ as [ | ty σ]; first by discriminate hLen.
      case : hLen => hLen.
      apply hi in hLen.
      destruct v; by constructor.
  Qed.

  Lemma neg_subtype_targs vs σ0 σ1 :
    σ0 <:vs:> σ1 → σ1 <:(neg_variance <$> vs):> σ0.
  Proof.
    induction 1 as [ | ??????? h hi | ?????? h hi | ?????? h hi] => //=.
    - by constructor.
    - by constructor.
    - by constructor.
  Qed.

  (* See Andrew Kennedy's paper:
     Variance and Generalized Constraints for C♯ Generics
  *)
  Inductive mono : list variance → lang_ty → Prop :=
    | MonoInt vs : mono vs IntT
    | MonoBool vs : mono vs BoolT
    | MonoNothing vs : mono vs NothingT
    | MonoMixed vs : mono vs MixedT
    | MonoNull vs : mono vs NullT
    | MonoNonNull vs : mono vs NonNullT
    | MonoUnion vs s t : mono vs s → mono vs t → mono vs (UnionT s t)
    | MonoInter vs s t : mono vs s → mono vs t → mono vs (InterT s t)
    | MonoVInvGen vs n: vs !! n = Some Invariant → mono vs (GenT n)
    | MonoVCoGen vs n: vs !! n = Some Covariant → mono vs (GenT n)
    | MonoGen vs n: vs !! n = None → mono vs (GenT n)
    | MonoEx vs cname: mono vs (ExT cname)
    | MonoClass vs cname cdef targs:
        Δ !! cname = Some cdef →
        (∀ i wi ti, cdef.(generics) !! i = Some wi →
                    targs !! i = Some ti →
                    not_contra wi →
                    mono vs ti) →
        (∀ i wi ti, cdef.(generics) !! i = Some wi →
                    targs !! i = Some ti →
                    not_cov wi →
                    mono (neg_variance <$> vs) ti) →
        mono vs (ClassT cname targs)
  .

  Definition wf_cdef_mono cdef : Prop :=
    match cdef.(superclass) with
    | None => True
    | Some (parent, σ) =>
        mono cdef.(generics) (ClassT parent σ)
    end
  .

  Definition wf_mdef_mono vs mdef : Prop :=
    map_Forall (λ _argname, mono (neg_variance <$> vs)) mdef.(methodargs) ∧
    mono vs mdef.(methodrettype).

  Definition wf_cdef_methods_mono cdef : Prop :=
    map_Forall (λ _mname, wf_mdef_mono cdef.(generics)) cdef.(classmethods)
  .

  Definition invariant vs ty :=
    mono vs ty ∧ mono (neg_variance <$> vs) ty.

  Definition field_mono vs (vfty: visibility * lang_ty) :=
    let (vis, fty) := vfty in
    match vis with
    | Public => invariant vs fty
    | Private => True
    end.

  Definition wf_field_mono cdef :=
    map_Forall (λ _fname, field_mono cdef.(generics)) cdef.(classfields).

  Lemma mono_subst vs ty:
    mono vs ty →
    bounded (length vs) ty →
    ∀ ws σ,
    length vs = length σ →
    (∀ i vi ti, vs !! i = Some vi → σ !! i = Some ti →
      not_cov vi → mono (neg_variance <$> ws) ti) →
    (∀ i vi ti, vs !! i = Some vi → σ !! i = Some ti →
      not_contra vi → mono ws ti) →
    mono ws (subst_ty σ ty).
  Proof.
    induction 1 as [ vs | vs | vs | vs | vs | vs | vs s t hs his ht hit
      | vs s t hs his ht hit | vs n hinv | vs n hco | vs n hnone
      | vs cname | vs cname cdef targs hΔ hcov hicov hcontra hicontra ]
      => hb ws σ hlen h0 h1 //=; try by constructor.
    - inv hb.
      constructor.
      + eapply his; by eauto.
      + eapply hit; by eauto.
    - inv hb.
      constructor.
      + eapply his; by eauto.
      + eapply hit; by eauto.
    - destruct (σ !! n) as [ty | ] eqn:hty => //=.
      + by eapply h1.
      + apply lookup_lt_Some in hinv.
        rewrite hlen in hinv.
        apply lookup_lt_is_Some_2 in hinv.
        rewrite hty in hinv.
        by elim hinv.
    - destruct (σ !! n) as [ty | ] eqn:hty => //=.
      + by eapply h1.
      + apply lookup_lt_Some in hco.
        rewrite hlen in hco.
        apply lookup_lt_is_Some_2 in hco.
        rewrite hty in hco.
        by elim hco.
    - inv hb.
      apply lookup_lt_is_Some_2 in H0.
      rewrite hnone in H0.
      by elim H0.
    - inv hb.
      econstructor; first done.
      + move => i ci ti hci hi hc.
        apply list_lookup_fmap_inv in hi as [ty [-> hi]].
        eapply hicov => //.
        rewrite Forall_forall in H0.
        apply H0.
        by apply elem_of_list_lookup_2 in hi.
      + move => i ci ti hci hi hc.
        apply list_lookup_fmap_inv in hi as [ty [-> hi]].
        eapply hicontra => //.
        * rewrite Forall_forall in H0.
          rewrite map_length.
          apply H0.
          by apply elem_of_list_lookup_2 in hi.
        * by rewrite map_length.
        * move => j vj tj hj htj hcj.
          apply list_lookup_fmap_inv in hj as [vj' [-> hj]].
          rewrite neg_variance_fmap_idem.
          eapply h1 => //.
          by destruct vj'.
        * move => j vj tj hj htj hcj.
          apply list_lookup_fmap_inv in hj as [vj' [-> hj]].
          eapply h0 => //.
          by destruct vj'.
  Qed.

  Lemma extends_using_mono A B σ :
    map_Forall (λ _cname, wf_cdef_mono) Δ →
    extends_using A B σ →
    ∀ def, Δ !! A = Some def →
    mono def.(generics) (ClassT B σ).
  Proof.
    move => hmono h def hdef.
    inv h; simplify_eq.
    apply hmono in hdef.
    by rewrite /wf_cdef_mono H0 in hdef.
  Qed.

  Lemma inherits_using_mono A B σ :
    map_Forall (λ _ : string, wf_cdef_parent Δ) Δ →
    map_Forall (λ _cname, wf_cdef_mono) Δ →
    inherits_using A B σ →
    ∀ def, Δ !! A = Some def →
    mono def.(generics) (ClassT B σ).
  Proof.
    move => ? hmono.
    induction 1 as [A adef h | A B σ h | A B σ C σC hext h hi ] => def hdef.
    - simplify_eq.
      econstructor => //.
      + move => i wi ti hgi /lookup_gen_targs -> hc.
        destruct wi; by constructor.
      + move => i wi ti hgi /lookup_gen_targs -> hc.
        destruct wi => //.
        * apply MonoVInvGen.
          by rewrite list_lookup_fmap hgi.
        * apply MonoVCoGen.
          by rewrite list_lookup_fmap hgi.
    - by apply extends_using_mono with (def := def) in h.
    - apply inherits_using_wf in h => //.
      destruct h as (bdef & cdef & hb & hc & hF & hL & hwf).
      assert (hb' := hb).
      assert (hext' := hext).
      apply hi in hb'.
      apply extends_using_mono with (def := def) in hext' => //.
      inv hext'.
      simplify_eq.
      change (ClassT C (subst_ty σ <$> σC)) with (subst_ty σ (ClassT C σC)).
      apply mono_subst with (generics bdef) => //.
      + by constructor.
      + apply extends_using_wf in hext => //.
        repeat destruct hext as [? hext].
        by simplify_eq.
  Qed.

  Definition check_variance v ty0 ty1 :=
    match v with
    | Invariant => (ty0 <: ty1) ∧ (ty1 <: ty0)
    | Covariant => ty0 <: ty1
    | Contravariant => ty1 <: ty0
    end.

  Lemma subtype_targs_lookup_0 vs σ0 σ1:
    σ0 <:vs:> σ1 →
    ∀ k ty0, σ0 !! k = Some ty0 →
    ∃ v ty1, vs !! k = Some v ∧ σ1 !! k = Some ty1 ∧
    check_variance v ty0 ty1.
  Proof.
    induction 1 as [ | ????? h0 h1 h hi | ????? h0 h hi | ????? h0 h hi] => k tk.
    - by rewrite lookup_nil.
    - destruct k as [ | k] => //=.
      + case => <-; clear tk.
        exists Invariant, ty1; by repeat split.
      + move => hk.
        apply hi in hk as (v & t2 & -> & -> & hv).
        exists v, t2; by repeat split.
    - destruct k as [ | k] => //=.
      + case => <-; clear tk.
        exists Covariant, ty1; by repeat split.
      + move => hk.
        apply hi in hk as (v & t2 & -> & -> & hv).
        exists v, t2; by repeat split.
    - destruct k as [ | k] => //=.
      + case => <-; clear tk.
        exists Contravariant, ty1; by repeat split.
      + move => hk.
        apply hi in hk as (v & t2 & -> & -> & hv).
        exists v, t2; by repeat split.
  Qed.

  Lemma subtype_targs_lookup_1 vs σ0 σ1:
    σ0 <:vs:> σ1 →
    ∀ k ty1, σ1 !! k = Some ty1 →
    ∃ v ty0, vs !! k = Some v ∧ σ0 !! k = Some ty0 ∧
    check_variance v ty0 ty1.
  Proof.
    move => hsub k ty1 h1.
    destruct (σ0 !! k) as [ty0 | ] eqn:h0; last first.
    { apply length_subtype_targs_01 in hsub.
      apply mk_is_Some in h1.
      apply lookup_lt_is_Some_1 in h1.
      rewrite -hsub in h1.
      apply lookup_lt_is_Some_2 in h1.
      rewrite h0 in h1.
      by elim h1.
    }
    apply subtype_targs_lookup_0 with (k := k) (ty0 := ty0) in hsub => //.
    destruct hsub as (v & ty1' & hv & ? & h); simplify_eq.
    exists v, ty0.
    by repeat split.
  Qed.

  Lemma subtype_targs_lookup_v vs σ0 σ1:
    σ0 <:vs:> σ1 →
    ∀ k v, vs !! k = Some v →
    ∃ ty0 ty1, σ0 !! k = Some ty0 ∧ σ1 !! k = Some ty1 ∧
    check_variance v ty0 ty1.
  Proof.
    move => hsub k v hv.
    destruct (σ0 !! k) as [ty0 | ] eqn:h0; last first.
    { apply length_subtype_targs_v0 in hsub.
      apply mk_is_Some in hv.
      apply lookup_lt_is_Some_1 in hv.
      rewrite hsub in hv.
      apply lookup_lt_is_Some_2 in hv.
      rewrite h0 in hv.
      by elim hv.
    }
    apply subtype_targs_lookup_0 with (k := k) (ty0 := ty0) in hsub => //.
    destruct hsub as (v' & ty1 & ? & ? & h); simplify_eq.
    exists ty0, ty1.
    by repeat split.
  Qed.
      
  Lemma subtype_targs_forall vs σ0 σ1:
    length σ0 = length vs →
    length σ1 = length vs →
    (∀ k v ty0 ty1,
         vs !! k = Some v → σ0 !! k = Some ty0 → σ1 !! k = Some ty1 → 
         check_variance v ty0 ty1) →
    σ0 <:vs:> σ1.
  Proof.
    move : σ0 σ1.
    induction vs as [ | v vs hi] => σ0 σ1 h0 h1 h.
    - apply nil_length_inv in h0.
      apply nil_length_inv in h1.
      by rewrite h0 h1.
    - destruct σ0 as [ | ty0 σ0]; first by discriminate h0.
      destruct σ1 as [ | ty1 σ1]; first by discriminate h1.
      case : h0 => h0.
      case : h1 => h1.
      destruct v.
      + constructor.
        * by apply (h 0 Invariant ty0 ty1).
        * by apply (h 0 Invariant ty0 ty1).
        * apply hi => //.
          move => k v ty2 ty3 hv h2 h3.
          by apply (h (S k) v ty2 ty3).
      + constructor.
        * by apply (h 0 Covariant ty0 ty1).
        * apply hi => //.
          move => k v ty2 ty3 hv h2 h3.
          by apply (h (S k) v ty2 ty3).
      + constructor.
        * by apply (h 0 Contravariant ty0 ty1).
        * apply hi => //.
          move => k v ty2 ty3 hv h2 h3.
          by apply (h (S k) v ty2 ty3).
  Qed.

  Lemma subtype_targs_cons v t0 t1 vs σ0 σ1:
    check_variance v t0 t1 →
    σ0 <:vs:> σ1 →
    (t0::σ0) <:(v::vs):> (t1::σ1).
  Proof.
    rewrite /check_variance => hc hs.
    destruct v; constructor => //.
    - by destruct hc.
    - by destruct hc.
  Qed.

  Lemma subtype_wf A B:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    wf_ty A → A <: B → wf_ty B.
  Proof.
    move => hp hwf.
    induction 1 as [ ty | ty h | A σA B σB adef hΔ hA hext
      | A adef σ0 σ1 hΔ hwfσ hσ | | | | A args | s t h
      | s t h | s t u hs his ht hit | s t | s t | s t u hs his ht hit | s
      | s t u hst hist htu hitu ] => //=; try (by constructor).
    - inv hext; simplify_eq.
      rewrite /map_Forall_lookup in hp.
      apply hp in hΔ.
      rewrite /wf_cdef_parent H0 in hΔ.
      destruct hΔ as (bdef & hB & hL & hσB & hb).
      econstructor; first done.
      + by rewrite map_length.
      + move => k ty.
        rewrite list_lookup_fmap.
        destruct (σB !! k) as [ tyk | ] eqn:hty => //=.
        case => <-.
        apply wf_ty_subst; first by apply wf_ty_class_inv in hwf.
        rewrite Forall_forall in hσB.
        apply elem_of_list_lookup_2 in hty.
        by apply hσB in hty.
    - apply length_subtype_targs_v1 in hσ.
      inv hwf; simplify_eq; econstructor.
      + exact hΔ.
      + by rewrite hσ.
      + rewrite Forall_forall in hwfσ => k ty hty.
        apply elem_of_list_lookup_2 in hty.
        by apply hwfσ in hty.
    - inv hwf; by eauto.
    - inv hwf; by eauto.
    - inv hwf; by eauto.
    - constructor; by eauto.
    - by eauto.
  Qed.

  Lemma subtype_subst A B:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    A <: B → ∀ σ,
    Forall wf_ty σ →
    (subst_ty σ A) <: (subst_ty σ B)
  with subtype_targs_subst vs As Bs:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    As <:vs:> Bs → ∀ σ,
    Forall wf_ty σ →
    (subst_ty σ <$> As) <:vs:> (subst_ty σ <$> Bs).
  Proof.
    - move => hp.
      destruct 1 as [ ty | ty h | A σA B σB adef hΔ hA hext
      | A adef σ0 σ1 hΔ hwfσ hσ01 | | | | A args
      | s t h | s t h | s t u hs ht | s t | s t | s t u hs ht | s
      | s t u hst htu ] => σ hσ => /=; try (by constructor).
      + constructor.
        by apply wf_ty_subst.
      + rewrite map_subst_ty_subst.
        * econstructor; [exact hΔ | | by assumption].
          by rewrite map_length.
        * apply extends_using_wf in hext; last done.
          destruct hext as (? & bdef & ? & hB & hF & hL).
          simplify_eq.
          by rewrite hA.
      + eapply SubVariance.
        * exact hΔ.
        * rewrite Forall_forall => ty /elem_of_list_fmap [ty' [-> hin]].
          apply wf_ty_subst => //.
          rewrite Forall_forall in hwfσ; by apply hwfσ in hin.
        * apply subtype_targs_subst; by assumption.
      + constructor.
        by apply wf_ty_subst.
      + constructor.
        by apply wf_ty_subst.
      + constructor; by apply subtype_subst.
      + constructor; by apply subtype_subst.
      + econstructor; by apply subtype_subst.
    - move => hp.
      destruct 1 as [ | ????? h0 h1 h | ????? h0 h | ????? h0 h] => σ hσ /=.
      + by constructor.
      + constructor.
        * by apply subtype_subst.
        * by apply subtype_subst.
        * by apply subtype_targs_subst.
      + constructor.
        * by apply subtype_subst.
        * by apply subtype_targs_subst.
      + constructor.
        * by apply subtype_subst.
        * by apply subtype_targs_subst.
  Qed.

  Lemma subtype_subst_class A B σA σB:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    ClassT A σA <: ClassT B σB → ∀ σ,
    Forall wf_ty σ →
    ClassT A (subst_ty σ <$> σA) <: ClassT B (subst_ty σ <$> σB).
  Proof.
    move => ? hsub σ h.
    by apply subtype_subst with (σ := σ) in hsub.
  Qed.

  Lemma subtype_lift vs ty :
    mono vs ty →
    ∀ σ0 σ1,
    wf_ty ty →
    Forall wf_ty σ0 →
    Forall wf_ty σ1 →
    σ0 <:vs:> σ1 →
    subst_ty σ0 ty <: subst_ty σ1 ty.
  Proof.
    induction 1 as [ vs | vs | vs | vs | vs | vs
      | vs s t hs his ht hit
      | vs s t hs his ht hit
      | vs n hinv | vs n hco | vs n hnone | vs cname
      | vs cname cdef targs hΔ hcov hicov hcontra hicontra ] => σ0 σ1 hwf hwf0 hwf1 hsub //=.
    - inv hwf.
      constructor.
      + econstructor; first by eapply his.
        econstructor.
        by apply wf_ty_subst.
      + econstructor; first by eapply hit.
        econstructor.
        by apply wf_ty_subst.
    - inv hwf.
      constructor.
      + eapply SubTrans with (subst_ty σ0 s); last by eapply his.
        by constructor.
      + eapply SubTrans with (subst_ty σ0 t); last by eapply hit.
        by constructor.
    - apply subtype_targs_lookup_v with (k := n) (v := Invariant) in hsub => //.
      by destruct hsub as (ty0 & ty1 & -> & -> & h0 & h1).
    - apply subtype_targs_lookup_v with (k := n) (v := Covariant) in hsub => //.
      by destruct hsub as (ty0 & ty1 & -> & -> & h).
    - destruct (σ0 !! n) as [? | ] eqn:h0.
      { apply length_subtype_targs_v0 in hsub.
        apply mk_is_Some in h0.
        apply lookup_lt_is_Some_1 in h0.
        rewrite -hsub in h0.
        apply lookup_lt_is_Some_2 in h0.
        rewrite hnone in h0.
        by elim h0.
      }
      destruct (σ1 !! n) as [? | ] eqn:h1.
      { apply length_subtype_targs_v1 in hsub.
        apply mk_is_Some in h1.
        apply lookup_lt_is_Some_1 in h1.
        rewrite -hsub in h1.
        apply lookup_lt_is_Some_2 in h1.
        rewrite hnone in h1.
        by elim h1.
      }
      done.
    - assert (hwftargs : Forall wf_ty targs) by (by apply wf_ty_class_inv in hwf).
      apply SubVariance with cdef => //; first by apply wf_ty_subst_map.
      apply subtype_targs_forall.
      + rewrite map_length.
        inv hwf; by simplify_eq.
      + rewrite map_length.
        inv hwf; by simplify_eq.
      + move => k v ty0 ty1 hk h0 h1.
        apply list_lookup_fmap_inv in h0.
        destruct h0 as [t0' [-> h0]].
        apply list_lookup_fmap_inv in h1.
        destruct h1 as [t1' [-> h1]].
        simplify_eq.
        destruct v; first split.
        * eapply hicov => //.
          rewrite Forall_forall in hwftargs.
          apply hwftargs.
          by apply elem_of_list_lookup_2 in h0.
        * eapply hicontra => //.
          rewrite Forall_forall in hwftargs.
          apply hwftargs.
          by apply elem_of_list_lookup_2 in h0.
          by apply neg_subtype_targs.
        * eapply hicov => //.
          rewrite Forall_forall in hwftargs.
          apply hwftargs.
          by apply elem_of_list_lookup_2 in h0.
        * eapply hicontra => //.
          rewrite Forall_forall in hwftargs.
          apply hwftargs.
          by apply elem_of_list_lookup_2 in h0.
          by apply neg_subtype_targs.
  Qed.

  Lemma subtype_targs_lift σ:
    ∀ vs σ0 σ1 ws,
    Forall wf_ty σ →
    Forall wf_ty σ0 →
    Forall wf_ty σ1 →
    σ0 <:vs:> σ1 →
    length σ = length ws →
    (∀ i wi ti, ws !! i = Some wi →
                σ !! i = Some ti →
                not_contra wi →
                mono vs ti) →
    (∀ i wi ti, ws !! i = Some wi →
                σ !! i = Some ti →
                not_cov wi →
                mono (neg_variance <$> vs) ti) →
    (subst_ty σ0 <$> σ) <:ws:> (subst_ty σ1 <$> σ)
    .
  Proof.
    induction σ as [ | ty σ hi] => vs σ0 σ1 ws hwf hwf0 hwf1 h hlen hcov hcontra;
      first by rewrite (nil_length_inv ws).
    destruct ws as [ | w ws]; first by discriminate hlen.
    case: hlen => hlen /=.
    apply Forall_cons_1 in hwf as [hty hwf].
    apply subtype_targs_cons.
    { destruct w => /=.
      - split.
        + apply subtype_lift with vs => //.
          by apply (hcov 0 Invariant).
        + apply subtype_lift with (neg_variance <$> vs) => //; last by apply neg_subtype_targs.
          by apply (hcontra 0 Invariant).
      - apply subtype_lift with vs => //.
        by apply (hcov 0 Covariant).
      - apply subtype_lift with (neg_variance <$> vs) => //; last by apply neg_subtype_targs.
        by apply (hcontra 0 Contravariant).
    }
    apply hi with vs => //.
    - move => i wi ti hwi hti hc.
      by apply (hcov (S i) wi ti).
    - move => i wi ti hwi hti hc.
      by apply (hcontra (S i) wi ti).
  Qed.

  Lemma subtype_targs_inv_0 vs σ ty0 σ0:
    (ty0 :: σ0) <:vs:> σ →
    ∃ w ws ty1 σ1,
    vs = w :: ws ∧
    σ = ty1 :: σ1 ∧
    check_variance w ty0 ty1 ∧
    σ0 <:ws:> σ1.
  Proof.
    move => h; inv h.
    - by exists Invariant, vs0, ty2, ty1s.
    - by exists Covariant, vs0, ty2, ty1s.
    - by exists Contravariant, vs0, ty2, ty1s.
  Qed.

  Lemma subtype_targs_inv_1 vs σ ty1 σ1:
    σ <:vs:> (ty1 :: σ1) →
    ∃ w ws ty0 σ0,
    vs = w :: ws ∧
    σ = ty0 :: σ0 ∧
    check_variance w ty0 ty1 ∧
    σ0 <:ws:> σ1.
  Proof.
    move => h; inv h.
    - by exists Invariant, vs0, ty0, ty0s.
    - by exists Covariant, vs0, ty0, ty0s.
    - by exists Contravariant, vs0, ty0, ty0s.
  Qed.

  Lemma subtype_targs_trans σ:
    ∀ vs σ0 σ1,
    σ0 <:vs:> σ1 →
    σ <:vs:> σ0 →
    σ <:vs:> σ1.
  Proof.
    induction σ as [ | ty σ hi] => vs σ0 σ1 h01 h0.
    - inv h0.
      by inv h01.
    - apply subtype_targs_inv_0 in h0.
      destruct h0 as (w & ws & ty0 & ty0s & -> & -> & hc & hsub).
      apply subtype_targs_inv_0 in h01.
      destruct h01 as (? & ? & ty1 & ty1s & heq & -> & hc' & hsub').
      case : heq.
      intros <- <-.
      apply subtype_targs_cons; last by eapply hi.
      move : hc hc'; destruct w => /=.
      + move => [??] [??]; split; by eauto.
      + move => ? ?; by eauto.
      + move => ? ?; by eauto.
  Qed.

  (* Sanity checks: Some derived rules *)
  Lemma subtype_union_comm : ∀ A B,
    wf_ty A → wf_ty B →
    (UnionT A B) <: (UnionT B A).
  Proof. by auto. Qed.

  Lemma subtype_inter_comm : ∀ A B,
    wf_ty A → wf_ty B →
    (InterT A B) <: (InterT B A).
  Proof. by auto. Qed.

  Lemma subtype_union_assoc:
    ∀ A B C,
    wf_ty A → wf_ty B → wf_ty C →
    (UnionT (UnionT A B) C) <: (UnionT A (UnionT B C)).
  Proof.
    move => A B C wfA wfB wfC.
    apply SubUnionLeast; last by eauto.
    apply SubUnionLeast; last by eauto.
    apply SubUnionUpper1.
    constructor; by eauto.
  Qed.

  Lemma subtype_inter_assoc:
    ∀ A B C, 
    wf_ty A → wf_ty B → wf_ty C →
    (InterT (InterT A B) C) <: (InterT A (InterT B C)).
  Proof. by eauto. Qed.

  (* Generalized version of SubClass to any inheritance sequence *)
  Lemma subtype_inherits_using A B σ σA adef:
    map_Forall (λ _ : string, wf_cdef_parent Δ) Δ →
    Δ !! A = Some adef →
    length σA = length (adef.(generics)) →
    inherits_using A B σ →
    ClassT A σA <: ClassT B (subst_ty σA <$> σ).
  Proof.
    move => hp hA hl h.
    move : h σA adef hA hl.
    induction 1 as [ A ? h | A B σ0 hext | A B σ0 C σC hext h hi ] => σA ? hA hl.
    - simplify_eq.
      by rewrite subst_ty_gen_targs.
    - by econstructor.
    - eapply SubTrans; first by eapply SubClass.
      apply extends_using_wf in hext => //.
      destruct hext as (? & bdef & hadef' & hbdef & hF0 & hL0 & _).
      apply inherits_using_wf in h => //.
      destruct h as (? & cdef & hbdef' & hcdef & hF1 & hL1 & _).
      simplify_eq.
      rewrite map_subst_ty_subst; last by rewrite hL0.
      apply hi with bdef => //.
      by rewrite map_length.
  Qed.

  (* Typing contexts *)
  Record local_tys := {
    type_of_this: tag * list lang_ty;
    ctxt: stringmap lang_ty;
  }.

  Definition this_type lty :=
    ClassT lty.(type_of_this).1 lty.(type_of_this).2.

  (* Subtype / Inclusion of typing contexts *)
  Definition lty_sub (lty rty: local_tys) :=
    this_type lty = this_type rty ∧
    ∀ k A, rty.(ctxt) !! k = Some A → ∃ B, lty.(ctxt) !! k = Some B ∧ B <: A.

  Notation "lty <:< rty" := (lty_sub lty rty) (at level 70, no associativity).

  Lemma lty_sub_reflexive: reflexive _ lty_sub.
  Proof.
    move => [this lty]; split => // k A ->.
    by exists A.
  Qed.

  Lemma lty_sub_transitive: transitive _ lty_sub.
  Proof.
    move => [[t0 σ0] lty] [[t1 σ1] rty] [[t2 σ2] zty] [h0 hlr] [h1 hrz].
    move : h0 h1.
    rewrite /this_type /=.
    case => -> ->.
    case => -> ->.
    split; first by eauto.
    move => k A hA.
    apply hrz in hA as (C & hC & hsub).
    apply hlr in hC as (B & hB & hsub').
    exists B; by eauto.
  Qed.

  Global Instance local_tys_insert : Insert string lang_ty local_tys :=
    λ x ty lty, 
    {| type_of_this := lty.(type_of_this);
      ctxt := <[x := ty]>lty.(ctxt);
    |}.

  Definition subst_lty σ lty :=
    {| type_of_this := (lty.(type_of_this).1, subst_ty σ <$> lty.(type_of_this).2);
        ctxt := subst_ty σ <$> lty.(ctxt);
    |}.

  Lemma lty_sub_insert_1 lhs ty lty0 lty1:
    lty0 <:< lty1 →
    <[lhs:=ty]> lty0 <:< <[lhs:=ty]> lty1.
  Proof.
    move => [hthis h]; split => // x xty.
    rewrite lookup_insert_Some.
    case => [[<- <-] | [hne hin]].
    - rewrite lookup_insert; by exists ty.
    - rewrite lookup_insert_ne //.
      apply h in hin.
      destruct hin as [B [hin hsub]].
      by exists B.
  Qed.

  Lemma lty_sub_insert_2 ty0 ty1 lhs lty:
    ty0 <: ty1 →
    <[lhs := ty0]>lty <:< <[lhs := ty1]> lty.
  Proof.
    move => hsub; split => // k ty.
    rewrite lookup_insert_Some.
    case => [[<- <-] | [hne hin]].
    - exists ty0; by rewrite lookup_insert.
    - exists ty; by rewrite lookup_insert_ne.
  Qed.

  Lemma lty_sub_subst σ lty rty:
    map_Forall (λ _ : string, wf_cdef_parent Δ) Δ →
    Forall wf_ty σ →
    lty <:< rty → (subst_lty σ lty) <:< (subst_lty σ rty).
  Proof.
    destruct lty as [[lt lσ] lty].
    destruct rty as [[rt rσ] rty].
    rewrite /subst_lty => hp hσ [].
    rewrite /this_type /=.
    case => -> -> hsub.
    split => //.
    move => k A.
    rewrite lookup_fmap_Some.
    case => B [<- hk].
    apply hsub in hk as [ B' [HB' hsub']].
    exists (subst_ty σ B').
    rewrite lookup_fmap HB'; split; first done.
    by apply subtype_subst.
  Qed.

  (* has_field f C vis fty orig means that class C defines or inherits a field f
   * of type fty. Its visibility is vis in the class orig.
   * The type fty is substituted accordingly so it can be
   * interpreted in C directly.
   *)
  Inductive has_field (fname: string) : tag → visibility → lang_ty → tag → Prop :=
    | HasField tag cdef vtyp:
        Δ !! tag = Some cdef →
        cdef.(classfields) !! fname = Some vtyp →
        has_field fname tag vtyp.1 vtyp.2 tag
    | InheritsField tag targs parent cdef vis typ orig:
        Δ !! tag = Some cdef →
        cdef.(classfields) !! fname = None →
        cdef.(superclass) = Some (parent, targs) →
        has_field fname parent vis typ orig →
        has_field fname tag vis (subst_ty targs typ) orig
  .

  Hint Constructors has_field : core.

  (* has_field is a functional relation *)
  Lemma has_field_fun fname A vis typ orig:
    has_field fname A vis typ orig →
    ∀ vis' typ' orig', has_field fname A vis' typ' orig' →
    vis = vis' ∧ typ = typ' ∧ orig = orig'.
  Proof.
    induction 1 as [ tag cdef [vis typ] hΔ hf
      | tag targs parent cdef vis typ orig hΔ hf hs h hi ] => vis' typ' orig' h'.
    - inv h'; by simplify_eq.
    - inv h'.
      + by simplify_eq.
      + simplify_eq.
        by destruct (hi _ _ _ H2) as [-> [-> ->]].
  Qed.

  (* A class cannot redeclare a field if it is already present in
   * any of its parent definition.
   * (No field override)
   * Note: we can probably restrict this to public fields, but to avoid
   * confusion in the source code, we restrict it to all fields.
   *)
  Definition wf_cdef_fields cdef : Prop :=
    ∀ f vis fty orig super inst,
    cdef.(superclass) = Some (super, inst) →
    has_field f super vis fty orig →
    cdef.(classfields) !! f = None.

  (* All field types in a class must be bounded by the class generics *)
  Definition wf_cdef_fields_bounded cdef : Prop :=
    map_Forall (λ _fname vfty, bounded (length cdef.(generics)) vfty.2) cdef.(classfields).

  (* All field types in a class must be well-formed *)
  Definition wf_cdef_fields_wf cdef : Prop :=
    map_Forall (λ _fname vfty, wf_ty vfty.2) cdef.(classfields). 

  Lemma has_field_wf f t vis fty orig:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _, wf_cdef_fields_wf) Δ →
    has_field f t vis fty orig →
    wf_ty fty.
  Proof.
    move => hp hwf.
    induction 1 as [ tag cdef [? typ] hΔ hf
      | tag targs parent cdef vis typ orig hΔ hf hs h hi ].
    - apply hwf in hΔ.
      by apply hΔ in hf.
    - apply wf_ty_subst => //.
      apply hp in hΔ.
      rewrite /wf_cdef_parent hs in hΔ.
      by destruct hΔ as (pdef & ? & ? & htargs & _).
  Qed.

  (* If a class has a field f, then any subclass will inherit it,
   * with the right substituted type.
   *)
  Lemma has_field_extends_using f B vis typ orig:
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    has_field f B vis typ orig →
    ∀ A σB,
    extends_using A B σB →
    has_field f A vis (subst_ty σB typ) orig.
  Proof.
    move => hwf hf A σB hext.
    inv hext.
    eapply InheritsField => //.
    by eapply hwf.
  Qed.

  Lemma has_field_bounded f t vis fty orig:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
    has_field f t vis fty orig →
    ∃ def, Δ !! t = Some def ∧ bounded (length def.(generics)) fty.
  Proof.
    move => hwfparent hwfb.
    induction 1 as [ tag cdef [? typ] hΔ hf
      | tag targs parent cdef vis typ orig hΔ hf hs h hi ].
    - exists cdef; split => //.
      apply hwfb in hΔ.
      by apply hΔ in hf.
    - exists cdef; split => //.
      destruct hi as [pdef [ hp hb]].
      apply hwfparent in hΔ.
      rewrite /wf_cdef_parent hs hp in hΔ.
      destruct hΔ as (? & [= <-] & h0 & _ & h1).
      by eapply bounded_subst.
  Qed.

  (* like has_field_extends_using, for any chain of inheritance. *)
  Lemma has_field_inherits_using f B vis typ orig:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
    has_field f B vis typ orig →
    ∀ A σB,
    inherits_using A B σB →
    has_field f A vis (subst_ty σB typ) orig.
  Proof.
    move => hp hfs hfb hf A σB hin.
    induction hin as [ A adef | A B σ hext | A B σ C σC hext h hi].
    - rewrite subst_ty_id //.
      apply has_field_bounded in hf => //.
      destruct hf as [? [? h]].
      by simplify_eq.
    - by eapply has_field_extends_using.
    - destruct (has_field_bounded _ _ _ _ _ hp hfb hf) as (cdef & hcdef & hc).
      apply hi in hf; clear hi.
      apply has_field_extends_using with (A := A) (σB := σ) in hf => //.
      rewrite -subst_ty_subst //.
      apply inherits_using_wf in h => //.
      destruct h as (? & ? & ? & ? & ? & h & _).
      simplify_eq.
      by rewrite h.
  Qed.

  Lemma has_field_mono f t vis ty orig:
    map_Forall (λ _cname, wf_field_mono) Δ →
    map_Forall (λ _cname, wf_cdef_mono) Δ →
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
    has_field f t vis ty orig →
    ∃ def, Δ !! t = Some def ∧
    match vis with
    | Public => invariant def.(generics) ty
    | Private => True
    end.
  Proof.
    move => hwfΔ hmono hp hfb.
    induction 1 as [ tag cdef [vis typ] hΔ hf
      | tag targs parent cdef vis typ orig hΔ hf hs h hi ].
      - exists cdef; split => //.
        apply hwfΔ in hΔ.
        by apply hΔ in hf.
      - destruct hi as [def [hdef hvis]].
        exists cdef; split => //.
        destruct vis; last done.
        destruct hvis as [h0 h1].
        assert (htag := hΔ).
        apply hp in htag.
        rewrite /wf_cdef_parent hs in htag.
        destruct htag as (? & ? & hlen & hwf & hb); simplify_eq.
        apply has_field_bounded in h => //.
        destruct h as (? & ? & hbt).
        assert (htag := hΔ).
        apply hmono in htag.
        rewrite /wf_cdef_mono hs in htag.
        inv htag.
        simplify_eq.
        split.
        + by apply mono_subst with (generics x).
        + apply mono_subst with (neg_variance <$> generics x) => //.
          * by rewrite map_length.
          * by rewrite map_length.
          * rewrite !neg_variance_fmap_idem.
            move => i vi ti hvi hti hc.
            apply list_lookup_fmap_inv in hvi.
            destruct hvi as [wi [-> hwi]].
            eapply H4 => //.
            by destruct wi.
          * move => i vi ti hvi hti hc.
            apply list_lookup_fmap_inv in hvi.
            destruct hvi as [wi [-> hwi]].
            eapply H5 => //.
            by destruct wi.
  Qed.

  Lemma has_field_pub_mono f t ty orig:
    map_Forall (λ _cname, wf_field_mono) Δ →
    map_Forall (λ _cname, wf_cdef_mono) Δ →
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
    has_field f t Public ty orig →
    ∃ def, Δ !! t = Some def ∧
    invariant def.(generics) ty.
  Proof.
    move => hwfΔ hmono hp hfb hf.
    by apply has_field_mono in hf.
  Qed.

  (* Helper predicate to collect all fields of a given class, as a map.
   * We collect both public and private fields, and their origins.
   *)
  Definition has_fields A (fields: stringmap ((visibility * lang_ty) * tag)) : Prop :=
    ∀ fname vis typ orig, has_field fname A vis typ orig ↔ fields !! fname = Some (vis, typ, orig).

  (* has_method m C orig mdef means that class C inherits a method m,
   * described by the methodDef mdef.
   *
   * The method is declared in class orig (which can be C).
   * mdef is substituted accordingly to be interpreted in the class C.
   * 
   * Note that we do support method override (see mdef_incl below).
   *)
  Inductive has_method (mname: string) : tag → tag → methodDef → Prop :=
    | HasMethod tag cdef mdef:
        Δ !! tag = Some cdef →
        cdef.(classmethods) !! mname = Some mdef →
        has_method mname tag tag mdef
    | InheritsMethod tag parent orig σ cdef mdef:
        Δ !! tag = Some cdef →
        cdef.(classmethods) !! mname = None →
        cdef.(superclass) = Some (parent, σ) →
        has_method mname parent orig mdef →
        has_method mname tag orig (subst_mdef σ mdef)
  .

  Hint Constructors has_method : code.

  (* a method is well-formed if the type of all its arguments, and its
   * return type are well-formed.
   *)
  Definition mdef_wf mdef : Prop :=
    map_Forall (λ _mname, wf_ty) mdef.(methodargs) ∧
    wf_ty mdef.(methodrettype).

  (* all method of a class are well-formed *)
  Definition wf_cdef_methods_wf cdef : Prop :=
    map_Forall (λ _mname, mdef_wf) cdef.(classmethods).

  Lemma has_method_wf m t orig mdef:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _, wf_cdef_methods_wf) Δ →
    has_method m t orig mdef →
    map_Forall (λ _mname, wf_ty) mdef.(methodargs) ∧
    wf_ty mdef.(methodrettype).
  Proof.
    move => hp hm.
    induction 1 as [ tag cdef mdef ht hin |
        tag parent orig σ cdef mdef ht hin hs h [hia hir] ].
    - apply hm in ht.
      by apply ht in hin.
    - assert (hσ : Forall wf_ty σ).
      { apply hp in ht.
        rewrite /wf_cdef_parent hs in ht.
        by destruct ht as (? & ? & ? & ? & ?).
      }
      split.
      + apply map_Forall_lookup => k ty.
        rewrite lookup_fmap_Some.
        case => ty' [<- hk].
        apply wf_ty_subst => //.
        by apply hia in hk.
      + rewrite /subst_mdef /=.
        by apply wf_ty_subst.
  Qed.

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

  Lemma mdef_incl_subst mdef0 mdef1 σ :
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    Forall wf_ty σ →
    mdef_incl mdef0 mdef1 →
    mdef_incl (subst_mdef σ mdef0) (subst_mdef σ mdef1).
  Proof.
    move => hp hσ.
    rewrite /mdef_incl /subst_mdef /=.
    case => [hdom [hargs hret]]; split; first by rewrite !dom_fmap_L.
    split; last by apply subtype_subst.
    move => k A B.
    rewrite !lookup_fmap_Some.
    case => tyA [<- hA].
    case => tyB [<- hB].
    apply subtype_subst => //.
    by eapply hargs.
  Qed.

  (* has_method is a functional relation *)
  Lemma has_method_fun: ∀ A name mdef0 mdef1 orig0 orig1,
    has_method name A orig0 mdef0 → has_method name A orig1 mdef1 →
    orig0 = orig1 ∧ mdef0 = mdef1.
  Proof.
    move => A name mdef0 mdef1 orig0 orig1 h; move: mdef1.
    induction h as [ current cdef mdef hΔ hm 
      | current parent orig inst cdef mdef hΔ hm hs hp hi ] => mdef1 h1.
    - inv h1; by simplify_eq.
    - inv h1.
      + by simplify_eq.
      + simplify_eq.
        apply hi in H2 as []; by subst.
  Qed.

  (* any redeclared method must correctly override its parent methods *)
  Definition wf_method_override (prog: stringmap classDef) :=
    ∀ A B adef bdef m σ mA mB,
    prog !! A = Some adef →
    prog !! B = Some bdef →
    inherits_using A B σ →
    adef.(classmethods) !! m = Some mA →
    bdef.(classmethods) !! m = Some mB →
    mdef_incl mA (subst_mdef σ mB).

  (* Helper lemma that gives all the relevant info from a has_method
   * statement:
   * - the class where it was originall defined
   * - the substitutions needed to interpret it in A, or in its original
   *   location.
   *)
  Lemma has_method_from_def A m orig mdef:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _cname, cdef_methods_bounded) Δ →
    has_method m A orig mdef →
    ∃ cdef mdef_orig,
      Δ !! orig = Some cdef ∧
      cdef.(classmethods) !! m = Some mdef_orig ∧
      has_method m orig orig mdef_orig ∧
      ∃ σ, inherits_using A orig σ ∧ mdef = subst_mdef σ mdef_orig.
  Proof.
    move => hp hmb.
    induction 1 as [ A adef mdef hΔ hm | A parent orig σ cdef mdef hΔ hm hs h hi ].
    - exists adef, mdef; repeat split => //; first by econstructor.
      exists (gen_targs (length adef.(generics))); split; first by constructor.
      rewrite subst_mdef_gen_targs //.
      apply hmb in hΔ.
      by apply hΔ in hm.
    - destruct hi as (odef & omdef & ho & hom & hdef & [σo [hin ->]]).
      exists odef, omdef; repeat split => //.
      exists (subst_ty σ <$> σo); split.
      { econstructor; last done.
        by econstructor.
      }
      rewrite subst_mdef_mdef //.
      assert (ho' := ho).
      apply hmb in ho.
      apply ho in hom.
      apply inherits_using_wf in hin as (? & ? & ? & ? & ? & hlen & _) => //.
      simplify_eq.
      by rewrite hlen.
  Qed.

  (* Helper lemma: If A inherits a method m from class orig, and
   * A <: B <: orig, then B must also inherits method m from orig.
   *)
  Lemma has_method_below_orig A m orig mdef:
    wf_no_cycle Δ →
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _cname, cdef_methods_bounded) Δ →
    has_method m A orig mdef →
    ∀ B σ σ', inherits_using A B σ → inherits_using B orig σ' →
    ∃ odef mdefo mdefB,
    Δ !! orig = Some odef ∧
    odef.(classmethods) !! m = Some mdefo ∧
    has_method m B orig mdefB ∧
    mdefB = subst_mdef σ' mdefo.
  Proof.
    move => hc hp hb.
    induction 1 as [ A cdef mdef hΔ hm | A parent orig σ cdef mdef hΔ hm hs h hi ] =>
          B σA σB hAB hBO.
    - destruct (hc _ _ _ _ hAB hBO) as [-> ->].
      apply inherits_using_refl in hAB as [ ? [? ->]] => // ; simplify_eq.
      exists cdef, mdef, mdef; repeat split => //.
      + by econstructor.
      + rewrite subst_mdef_gen_targs //.
        apply hb in hΔ.
        by apply hΔ in hm.
    - inv hAB.
      + simplify_eq.
        destruct (has_method_from_def _ _ _ _ hp hb h) as (odef & modef & ? & hmo & _ & [σo [hin ->]]).
        exists odef, modef, (subst_mdef σ (subst_mdef σo modef)); repeat split => //.
        * by econstructor.
        * assert (hσ: subst_ty σ <$> σo = σB).
          { eapply inherits_using_fun => //.
            eapply InheritsTrans; last done.
            by econstructor.
          }
          rewrite subst_mdef_mdef; first by rewrite hσ.
          apply inherits_using_wf in hBO as (? & ? & ? & ? & hF & hL & _) => //; simplify_eq.
          apply hb in H1.
          apply H1 in hmo.
          rewrite map_length in hL.
          by rewrite hL.
      + inv H; simplify_eq; clear hi.
        destruct (has_method_from_def _ _ _ _ hp hb h) as (odef & modef & ? & hmo & _ & [σo [hin ->]]).
        exists odef, modef, (subst_mdef σo modef); repeat split => //.
        replace σB with σo; first done.
        by eapply inherits_using_fun.
      + inv H; simplify_eq.
        destruct (hi _ _ _ H0 hBO) as (odef & mdefo & mdefB & ? & ? & ? & ->).
        by exists odef, mdefo, (subst_mdef σB mdefo).
  Qed.

  (* Key lemma for adequacy of method call:
   * if A <: B and they both have a method m (from resp. origA, origB), then
   * the origins must be ordered in the same way, meaning origA <: origB.
   * This implies some relations on all the inheritance substitution.
   *)
  Lemma has_method_ordered A B σ m origA mdefA origB mdefB:
    wf_no_cycle Δ →
    wf_method_override Δ →
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _cname, cdef_methods_bounded) Δ →
    inherits_using A B σ →
    has_method m A origA mdefA →
    has_method m B origB mdefB →
    ∃ σin σA σB oA oB mA mB,
      subst_ty σ <$> σB = subst_ty σA <$> σin ∧
      Δ !! origA = Some oA ∧
      Δ !! origB = Some oB ∧
      oA.(classmethods) !! m = Some mA ∧
      oB.(classmethods) !! m = Some mB ∧
      inherits_using origA origB σin ∧
      inherits_using A origA σA ∧
      inherits_using B origB σB ∧
      mdefA = subst_mdef σA mA ∧
      mdefB = subst_mdef σB mB ∧
      mdef_incl mA (subst_mdef σin mB) ∧
      mdef_incl mdefA (subst_mdef σ mdefB).
  Proof.
    move => hc ho hp hm hin hA hB.
    assert (hhA := hA).
    assert (hhB := hB).
    apply has_method_from_def in hA => //.
    apply has_method_from_def in hB => //.
    destruct hA as (oadef & oaorig & hoA & hmA & hmoA & [σA [hiA ->]]).
    destruct hB as (obdef & oborig & hoB & hmB & hmoB & [σB [hiB ->]]).
    destruct (inherits_using_chain _ _ _ hp hin _ _ hiA) as [σ'' [ [<- h] | [<- h]]].
    - destruct (has_method_below_orig _ _ _ _ hc hp hm hhA _ _ _ hin h) as
        (? & ? & mbdef & ? & ? & hbm & ->); simplify_eq.
      destruct (has_method_fun _ _ _ _ _ _ hhB hbm) as [-> ->].
      simplify_eq.
      exists (gen_targs (length oadef.(generics))),
             (subst_ty σ <$> σ''),
             σ'',
             oadef, oadef,
             oaorig, oaorig.
      split.
      { rewrite subst_ty_gen_targs //.
        apply inherits_using_wf in hiA => //.
        repeat destruct hiA as [? hiA]; by simplify_eq.
      }
      do 4 (split => //).
      split; first by econstructor.
      do 4 (split => //).
      split.
      + repeat split.
        * by rewrite /subst_mdef /= dom_fmap_L.
        * move => k X Y hX.
          rewrite /subst_mdef /= lookup_fmap hX /= subst_ty_id.
          { by case => ->. }
          apply hm in hoA.
          apply hoA in hmA.
          by apply hmA in hX.
        * rewrite /subst_mdef /= subst_ty_id //.
          apply hm in hoA.
          by apply hoA in hmA as [].
      + rewrite subst_mdef_mdef; first by apply mdef_incl_reflexive.
        assert (hoA' := hoA).
        apply hm in hoA'.
        apply hoA' in hmA.
        apply inherits_using_wf in h => //.
        repeat destruct h as [? h]; simplify_eq.
        by rewrite H2.
    - exists (subst_ty σ'' <$> σB), σA, σB, oadef, obdef, oaorig, oborig.
      split.
      { rewrite map_subst_ty_subst //.
        apply inherits_using_wf in hiB => //.
        repeat destruct hiB as [? hiB].
        apply inherits_using_wf in h => //.
        repeat destruct h as [? h].
        simplify_eq.
        by rewrite H6.
      }
      assert (hh: inherits_using origA origB (subst_ty σ'' <$> σB))
        by (by eapply inherits_using_trans).
      assert (hincl : mdef_incl oaorig (subst_mdef (subst_ty σ'' <$> σB) oborig))
        by (by eapply (ho origA origB) in hh).
      do 10 (split => //).
      rewrite -subst_mdef_mdef; last first.
      { assert (hoB' := hoB).
        apply hm in hoB'.
        apply hoB' in hmB.
        apply inherits_using_wf in hiB => //.
        repeat destruct hiB as [? hiB].
        simplify_eq.
        apply bounded_subst_mdef with (length (generics obdef)) => //.
        apply inherits_using_wf in h => //.
        repeat destruct h as [? h].
        simplify_eq.
        rewrite Forall_forall => ty hty.
        rewrite H5.
        rewrite Forall_forall in H1.
        by apply H1 in hty.
      }
      apply mdef_incl_subst => //.
      { apply inherits_using_wf in hiA => //.
        by repeat destruct hiA as [? hiA].
      }
      rewrite subst_mdef_mdef //.
      { assert (hoB' := hoB).
        apply hm in hoB'.
        apply hoB' in hmB.
        apply inherits_using_wf in hiB => //.
        repeat destruct hiB as [? hiB].
        simplify_eq.
        by rewrite H2.
      }
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

  Lemma this_has_ty lty ty :
    expr_has_ty lty ThisE ty →
    expr_has_ty lty ThisE (this_type lty) ∧ (this_type lty) <: ty.
  Proof.
    move => h.
    remember ThisE as this.
    move: h Heqthis.
    induction 1 as [ z | b | | op e1 e2 hop h1 hi1 h2 hi2 |
      op e1 e2 hop h1 hi1 h2 hi2 | v ty h | | e s t h hi hsub ] => //= heq; try discriminate.
    - split; by constructor.
    - apply hi in heq as [h0 h1].
      split => //.
      by eauto.
  Qed.

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
    | CondTag2Ev n st v t cmd :
        ¬tag_match st v t →
        cmd_eval st (CondTagC v t cmd) st n
.

End ProgDef.

(* Hints and notations are local to the section. Re-exporting them *)
Global Hint Constructors subtype subtype_targs : core.
Global Hint Constructors has_field : core.
Global Hint Constructors has_method : core.
