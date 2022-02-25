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

Record classDef := {
  classname: tag;
  generics: nat; (* number of generics, no constraint for now *)
  superclass: option (tag * list lang_ty);
  classfields : stringmap lang_ty;
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
        length σ = def.(generics) →
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
   *)
  Definition wf_cdef_parent (prog: stringmap classDef) cdef : Prop :=
    match cdef.(superclass) with
    | None => True
    | Some (parent, σ) =>
        ∃ pdef, prog !! parent = Some pdef ∧
        length σ = pdef.(generics) ∧
        Forall wf_ty σ ∧
        Forall (bounded cdef.(generics)) σ
    end
  .
  
  Definition cdef_methods_bounded cdef : Prop :=
    map_Forall (λ _mname mdef, mdef_bounded cdef.(generics) mdef) cdef.(classmethods).

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
    Forall (bounded adef.(generics)) σ ∧
    length σ = bdef.(generics) ∧
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
        inherits_using A A (gen_targs (adef.(generics)))
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
    Forall (bounded adef.(generics)) σ ∧
    length σ = bdef.(generics) ∧
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
        exists (gen_targs bdef.(generics)); left; split; last by econstructor.
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
        apply bounded_subst with (generics bdef) => //.
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
    ∃ adef, Δ !! A = Some adef ∧ σ = gen_targs adef.(generics).
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
    | SubClass : ∀ A σA B σB adef,
        Δ !! A = Some adef →
        length σA = adef.(generics) →
        extends_using A B σB →
        subtype (ClassT A σA) (ClassT B (subst_ty σA <$> σB))
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
  .
  (* TODO: add Nothing <: t ? *)

  Hint Constructors subtype : core.

  Notation "s <: t" := (subtype s t) (at level 70, no associativity).

  Lemma subtype_wf A B:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    wf_ty A → A <: B → wf_ty B.
  Proof.
    move => hp hwf.
    induction 1 as [ ty | A σA B σB adef hΔ hA hext | | | | A args | s t h
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
    (subst_ty σ A) <: (subst_ty σ B).
  Proof.
    move => hp.
    induction 1 as [ ty | A σA B σB adef hΔ hA hext | | | | A args | s t h
      | s t h | s t u hs his ht hit | s t | s t | s t u hs his ht hit | s
      | s t u hst hist htu hitu ] => σ hσ //=.
    - rewrite map_subst_ty_subst.
      + econstructor => //.
        by rewrite map_length.
      + apply extends_using_wf in hext => //.
      destruct hext as (? & bdef & ? & hB & hF & hL).
      simplify_eq.
      by rewrite hA.
    - constructor.
      by apply wf_ty_subst.
    - constructor.
      by apply wf_ty_subst.
    - constructor; by eauto.
    - econstructor; by eauto.
    - econstructor; by eauto.
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
    length σA = adef.(generics) →
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
  Definition local_tys := stringmap lang_ty.

  (* Subtype / Inclusion of typing contexts *)
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

  Lemma lty_sub_insert_1 lhs ty lty0 lty1:
    lty0 <:< lty1 →
    <[lhs:=ty]> lty0 <:< <[lhs:=ty]> lty1.
  Proof.
    move => h x xty.
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
    move => hsub k ty.
    rewrite lookup_insert_Some.
    case => [[<- <-] | [hne hin]].
    - exists ty0; by rewrite lookup_insert.
    - exists ty; by rewrite lookup_insert_ne.
  Qed.

  Lemma lty_sub_subst σ lty rty:
    map_Forall (λ _ : string, wf_cdef_parent Δ) Δ →
    Forall wf_ty σ →
    lty <:< rty → (subst_ty σ <$> lty) <:< (subst_ty σ <$> rty).
  Proof.
    move => hp hσ hsub k A.
    rewrite lookup_fmap_Some.
    case => B [<- hk].
    apply hsub in hk as [ B' [HB' hsub']].
    exists (subst_ty σ B').
    rewrite lookup_fmap HB'; split; first done.
    by apply subtype_subst.
  Qed.

  (* has_field f C fty means that class C defines or inherits a field f
   * of type fty. The type is substituted accordingly so it can be
   * interpreted in C directly.
   *)
  Inductive has_field (fname: string) : tag -> lang_ty → Prop :=
    | HasField tag cdef typ:
        Δ !! tag = Some cdef →
        cdef.(classfields) !! fname = Some typ →
        has_field fname tag typ
    | InheritsField tag targs parent cdef typ:
        Δ !! tag = Some cdef →
        cdef.(classfields) !! fname = None →
        cdef.(superclass) = Some (parent, targs) →
        has_field fname parent typ →
        has_field fname tag (subst_ty targs typ)
  .

  Hint Constructors has_field : core.

  (* has_field is a functional relation *)
  Lemma has_field_fun fname A typ:
    has_field fname A typ →
    ∀ typ', has_field fname A typ' →
    typ = typ'.
  Proof.
    induction 1 as [ tag cdef typ hΔ hf
      | tag targs parent cdef typ hΔ hf hs h hi ] => typ' h'.
    - inv h'; by simplify_eq.
    - inv h'.
      + by simplify_eq.
      + simplify_eq.
        by rewrite (hi _ H2).
  Qed.

  (* A class cannot redeclare a field if it is already present in
   * any of its parent definition.
   * (No field override)
   *)
  Definition wf_cdef_fields cdef : Prop :=
    ∀ f fty super inst,
    cdef.(superclass) = Some (super, inst) →
    has_field f super fty →
    cdef.(classfields) !! f = None.

  (* All field types in a class must be bounded by the class generics *)
  Definition wf_cdef_fields_bounded cdef : Prop :=
    map_Forall (λ _fname, bounded cdef.(generics)) cdef.(classfields).

  (* All field types in a class must be well-formed *)
  Definition wf_cdef_fields_wf cdef : Prop :=
    map_Forall (λ _fname, wf_ty) cdef.(classfields). 

  Lemma has_field_wf f t fty :
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _, wf_cdef_fields_wf) Δ →
    has_field f t fty →
    wf_ty fty.
  Proof.
    move => /map_Forall_lookup hp /map_Forall_lookup hwf.
    induction 1 as [ tag cdef typ hΔ hf
      | tag targs parent cdef typ hΔ hf hs h hi ].
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
  Lemma has_field_extends_using f B typ:
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    has_field f B typ →
    ∀ A σB,
    extends_using A B σB →
    has_field f A (subst_ty σB typ).
  Proof.
    move => hwf hf A σB hext.
    rewrite map_Forall_lookup in hwf.
    inv hext.
    eapply InheritsField => //.
    by eapply hwf.
  Qed.

  Lemma has_field_bounded f t fty:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
    has_field f t fty →
    ∃ def, Δ !! t = Some def ∧ bounded def.(generics) fty.
  Proof.
    move => /map_Forall_lookup hwfparent /map_Forall_lookup hwfb.
    induction 1 as [ tag cdef typ hΔ hf
      | tag targs parent cdef typ hΔ hf hs h hi ].
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
  Lemma has_field_inherits_using f B typ:
    map_Forall (λ _cname, wf_cdef_parent Δ) Δ →
    map_Forall (λ _cname, wf_cdef_fields) Δ →
    map_Forall (λ _cname, wf_cdef_fields_bounded) Δ →
    has_field f B typ →
    ∀ A σB,
    inherits_using A B σB →
    has_field f A (subst_ty σB typ).
  Proof.
    move => hp hfs hfb hf A σB hin.
    induction hin as [ A adef | A B σ hext | A B σ C σC hext h hi].
    - rewrite subst_ty_id //.
      apply has_field_bounded in hf => //.
      destruct hf as [? [? h]].
      by simplify_eq.
    - by eapply has_field_extends_using.
    - destruct (has_field_bounded _ _ _ hp hfb hf) as (cdef & hcdef & hc).
      apply hi in hf; clear hi.
      apply has_field_extends_using with (A := A) (σB := σ) in hf => //.
      rewrite -subst_ty_subst //.
      apply inherits_using_wf in h => //.
      destruct h as (? & ? & ? & ? & ? & h & _).
      simplify_eq.
      by rewrite h.
  Qed.

  (* Helper predicate to collect all fields of a given class, as a map *)
  Definition has_fields A (fields: stringmap lang_ty) : Prop :=
    ∀ fname typ, has_field fname A typ ↔ fields !! fname = Some typ.

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
      { rewrite map_Forall_lookup in hp.
        apply hp in ht.
        rewrite /wf_cdef_parent hs in ht.
        by destruct ht as (? & ? & ? & ? & ?).
      }
      split.
      + apply map_Forall_lookup => k ty.
        rewrite lookup_fmap_Some.
        case => ty' [<- hk].
        apply wf_ty_subst => //.
        rewrite map_Forall_lookup in hia.
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
    move => /map_Forall_lookup hp /map_Forall_lookup hmb.
    induction 1 as [ A adef mdef hΔ hm | A parent orig σ cdef mdef hΔ hm hs h hi ].
    - exists adef, mdef; repeat split => //; first by econstructor.
      exists (gen_targs adef.(generics)); split; first by constructor.
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
        rewrite map_Forall_lookup in hb.
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
          rewrite map_Forall_lookup in hp.
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
      has_method m origA origA mA ∧ (* Not sure these are useful *)
      has_method m origB origB mB ∧
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
      exists (gen_targs oadef.(generics)),
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
      do 6 (split => //).
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
      do 12 (split => //).
      rewrite -subst_mdef_mdef; last first.
      { assert (hoB' := hoB).
        apply hm in hoB'.
        apply hoB' in hmB.
        apply inherits_using_wf in hiB => //.
        repeat destruct hiB as [? hiB].
        simplify_eq.
        apply bounded_subst_mdef with (generics obdef) => //.
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
        lty !! v = Some ty →
        expr_has_ty lty (VarE v) ty
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
    expr_has_ty (subst_ty σ <$> lty) e (subst_ty σ ty).
  Proof.
    move => hp hwf.
    induction 1 as [ z | b | | op e1 e2 hop h1 hi1 h2 hi2 |
      op e1 e2 hop h1 hi1 h2 hi2 | v ty h | e s t h hi hsub ] => //=; try (by constructor).
    - constructor.
      by rewrite lookup_fmap h.
    - econstructor; first by apply hi.
      + by apply wf_ty_subst.
      + by apply subtype_subst.
  Qed.

  Lemma expr_has_ty_wf lty e ty:
    map_Forall (λ _, wf_ty) lty →
    expr_has_ty lty e ty →
    wf_ty ty.
  Proof.
    move => hwf.
    induction 1 as [ z | b | | op e1 e2 hop h1 hi1 h2 hi2 |
      op e1 e2 hop h1 hi1 h2 hi2 | v ty h | e s t h hi hsub ] => //=; try (by constructor).
    rewrite map_Forall_lookup in hwf.
    by apply hwf in h.
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
    | GetTy: ∀ lty lhs recv t σ name fty,
        expr_has_ty lty recv (ClassT t σ) →
        has_field name t fty →
        cmd_has_ty lty (GetC lhs recv name) (<[lhs := subst_ty σ fty]>lty)
    | SetTy: ∀ lty recv fld rhs fty t σ,
        expr_has_ty lty recv (ClassT t σ) →
        has_field fld t fty →
        expr_has_ty lty rhs (subst_ty σ fty) →
        cmd_has_ty lty (SetC recv fld rhs) lty
    | NewTy: ∀ lty lhs t targs args fields (*cdef*),
        wf_ty (ClassT t targs) →
        has_fields t fields →
        dom (gset string) fields = dom _ args →
        (∀ f fty arg,
        fields !! f = Some fty →
        args !! f = Some arg →
        expr_has_ty lty arg (subst_ty targs fty)) →
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
        lty !! v = Some tv →
        lty <:< rty →
        cmd_has_ty (<[v:=InterT tv (ExT t)]> lty) cmd rty →
        cmd_has_ty lty (CondTagC v t cmd) rty
  .

  Lemma cmd_has_ty_wf lty cmd lty' :
    map_Forall (λ _ : string, wf_cdef_parent Δ) Δ →
    map_Forall (λ _ : string, wf_cdef_fields_wf) Δ →
    map_Forall (λ _ : string, wf_cdef_methods_wf) Δ →
    map_Forall (λ _, wf_ty) lty →
    cmd_has_ty lty cmd lty' →
    map_Forall (λ _, wf_ty) lty'.
  Proof.
    move => hp hfields hmethods hwf.
    induction 1 as [ lty | ????? h1 hi1 h2 hi2 | ???? he |
      ????? he h1 hi1 h2 hi2 | ??????? he hf |
      ??????? he hf hr | ?????? ht hf hdom hargs |
      ????????? he hm hdom hargs |
      ???? hsub h hi | ?????? hin hr h hi ] => //=; try (by eauto).
    - apply map_Forall_insert_2 => //.
      by apply expr_has_ty_wf in he.
    - apply map_Forall_insert_2 => //.
      apply wf_ty_subst.
      + apply expr_has_ty_wf in he => //.
        by apply wf_ty_class_inv in he.
      + by apply has_field_wf in hf.
    - by apply map_Forall_insert_2.
    - apply map_Forall_insert_2 => //.
      apply has_method_wf in hm => //.
      destruct hm as [hargs' hret'].
      apply wf_ty_subst => //.
      apply expr_has_ty_wf in he => //.
      by apply wf_ty_class_inv in he.
    - apply hi in hwf; clear hi h.
      rewrite map_Forall_lookup => k ty hty.
      apply hsub in hty.
      destruct hty as [ty' [ hty' hsub']].
      rewrite map_Forall_lookup in hwf; apply hwf in hty'.
      by eapply subtype_wf.
    - apply hi; clear hi.
      rewrite map_Forall_lookup => k ty.
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
    map_Forall (λ _, wf_ty) lty →
    Forall wf_ty σ →
    cmd_has_ty lty cmd lty' →
    cmd_has_ty (subst_ty σ <$> lty) cmd (subst_ty σ <$> lty').
  Proof.
    move => hp hfields hmethods hfb hmb hwf0 hwf1.
    induction 1 as [ lty | ????? h1 hi1 h2 hi2 | ???? he |
      ????? he h1 hi1 h2 hi2 | ??????? he hf |
      ??????? he hf hr | ?????? hwf hf hdom hargs |
      ????????? he hm hdom hargs |
      ???? hsub h hi | ?????? hin hr h hi ] => //=.
    - by constructor.
    - econstructor.
      + by eapply hi1.
      + eapply hi2.
        by apply cmd_has_ty_wf in h1.
    - rewrite fmap_insert.
      eapply LetTy.
      by eapply expr_has_ty_subst.
    - eapply IfTy => //.
      + change BoolT with (subst_ty σ BoolT).
        by eapply expr_has_ty_subst.
      + by apply hi1.
      + apply hi2.
        by apply cmd_has_ty_wf in h1.
    - rewrite fmap_insert subst_ty_subst; last first.
      { apply has_field_bounded in hf => //.
        destruct hf as (hdef & ht & hfty).
        apply expr_has_ty_wf in he => //.
        inv he; simplify_eq.
        by rewrite H2.
      }
      eapply GetTy; last done.
      change (ClassT t (subst_ty σ <$> σ0)) with (subst_ty σ (ClassT t σ0)).
      by eapply expr_has_ty_subst.
    - apply SetTy with (fty := fty) (t := t) (σ := subst_ty σ <$> σ0) => //; last first.
      + rewrite -subst_ty_subst; first by eapply expr_has_ty_subst.
        apply has_field_bounded in hf => //.
        destruct hf as (hdef & ht & hfty).
        apply expr_has_ty_wf in he => //.
        inv he; simplify_eq.
        by rewrite H2.
      + change (ClassT t (subst_ty σ <$> σ0)) with (subst_ty σ (ClassT t σ0)).
        by eapply expr_has_ty_subst.
    - rewrite fmap_insert /=.
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
      move => f fty arg hfty ha.
      rewrite -subst_ty_subst.
      + eapply expr_has_ty_subst => //.
        by eapply hargs.
      + apply hf in hfty.
        apply has_field_bounded in hfty => //.
        destruct hfty as (hdef & ht & hfty).
        inv hwf; simplify_eq.
        by rewrite H2.
    - rewrite fmap_insert /=.
      rewrite subst_ty_subst; last first.
      { apply has_method_from_def in hm => //.
        destruct hm as (odef & mo & ho & hmo & _ & [σo [hin ->]]).
        rewrite /subst_mdef /=.
        rewrite map_Forall_lookup in hmb.
        apply inherits_using_wf in hin => //.
        destruct hin as (tdef & ? & ht & ho' & hfo & hlo & htyo); simplify_eq.
        assert (ho' := ho).
        apply hmb in ho.
        apply ho in hmo.
        destruct hmo as [_ hret].
        apply bounded_subst with (n := generics odef) => //.
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
        rewrite map_Forall_lookup in hmb.
        apply inherits_using_wf in hin => //.
        destruct hin as (tdef & ? & ht & ho' & hfo & hlo & htyo); simplify_eq.
        assert (ho' := ho).
        apply hmb in ho.
        apply ho in hmo.
        destruct hmo as [hargs' _].
        rewrite map_Forall_lookup in hargs'.
        rewrite /subst_mdef /= in hty.
        rewrite lookup_fmap_Some in hty.
        destruct hty as [ty' [ <- hty]].
        apply hargs' in hty.
        apply bounded_subst with (n := generics odef) => //.
        apply expr_has_ty_wf in he => //.
        inv he; simplify_eq.
        by rewrite H2.
    - econstructor; first by apply lty_sub_subst.
      by apply hi.
    - eapply CondTagTy.
      + by rewrite lookup_fmap hin /=.
      + by apply lty_sub_subst.
      + rewrite fmap_insert /= in hi.
        apply hi.
        apply map_Forall_insert_2 => //.
        constructor; last by constructor.
        rewrite map_Forall_lookup in hwf0.
        by apply hwf0 in hin.
  Qed.

  (* Consider a class C<T0, ..., Tn>,
   * method bodies must be well-formed under a generic substitution mapping
   * Ti -> Ti.
   *)
  Definition wf_mdef_ty this σ mdef :=
    ∃ rty,
    cmd_has_ty (<["$this" := this]>(subst_ty σ <$> mdef.(methodargs))) mdef.(methodbody) rty ∧
    expr_has_ty rty mdef.(methodret) (subst_ty σ mdef.(methodrettype))
  .

  Definition cdef_wf_mdef_ty cname cdef :=
    let σ := gen_targs cdef.(generics) in
    map_Forall (λ _mname mdef, wf_mdef_ty (ClassT cname σ) σ mdef) cdef.(classmethods)
  .

  (* Collection of all program invariant (at the source level):
   * - no cycle (we have a forest)
   * - every type is well-formed/bounded
   * - every substitution's domain/codomain is valid
   *)
  Record wf_cdefs (prog: stringmap classDef) := {
    wf_extends_wf : wf_no_cycle prog;
    wf_parent : map_Forall (λ _cname, wf_cdef_parent prog) prog;
    wf_override : wf_method_override Δ;
    wf_fields : map_Forall (λ _cname, wf_cdef_fields) prog;
    wf_fields_bounded : map_Forall (λ _cname, wf_cdef_fields_bounded) prog;
    wf_fields_wf  : map_Forall (λ _cname, wf_cdef_fields_wf) prog;
    wf_methods_bounded : map_Forall (λ _cname, cdef_methods_bounded) prog;
    wf_methods_wf : map_Forall (λ _cname, wf_cdef_methods_wf) prog;
    wf_mdefs : map_Forall cdef_wf_mdef_ty prog;
  }
  .

  Lemma expr_has_ty_subl lty e ty:  
    map_Forall (λ _, wf_ty) lty →
    expr_has_ty lty e ty →
    ∀ lty', lty' <:< lty →
    expr_has_ty lty' e ty.
  Proof.
    move => hwf.
    induction 1 as [ z | b | | op e1 e2 hop h1 hi1 h2 hi2 |
      op e1 e2 hop h1 hi1 h2 hi2 | v ty h | e s t h hi hsub ] => lty' hlty//=; try (by constructor).
    - constructor; by eauto.
    - constructor; by eauto.
    - assert (hh : wf_ty ty) by (by apply hwf in h).
      apply hlty in h.
      destruct h as [ty' [ h hsub]].
      eapply ESubTy => //.
      by constructor.
    - apply hi in hlty.
      by econstructor.
  Qed.

  Lemma cmd_has_ty_subl lty cmd rty :
    map_Forall (λ _ : string, wf_cdef_parent Δ) Δ →
    map_Forall (λ _ : string, wf_ty) lty →
    cmd_has_ty lty cmd rty →
    ∀ lty', lty' <:< lty →
    cmd_has_ty lty' cmd rty.
  Proof.
    move => hp hwf.
    induction 1 as [ lty | ????? h1 hi1 h2 hi2 | ???? he |
      ????? he h1 hi1 h2 hi2 | ??????? he hf |
      ??????? he hf hr | ?????? ht hf hdom hargs |
      ????????? he hm hdom hargs |
      ???? hsub h hi | ?????? hin hr h hi ] => //= lty' hlty'.
    - apply SubTy with lty' => //.
      by constructor.
    - econstructor; by eauto.
    - eapply SubTy; first by apply lty_sub_insert_1.
      constructor.
      by apply expr_has_ty_subl with lty.
    - constructor; try (by eauto).
      by apply expr_has_ty_subl with lty1.
    - eapply SubTy; first by apply lty_sub_insert_1.
      econstructor; last done.
      by apply expr_has_ty_subl with lty.
    - apply SubTy with lty' => //.
      econstructor; [| done|]; by eapply expr_has_ty_subl.
    - eapply SubTy; first by apply lty_sub_insert_1.
      econstructor => //.
      move => f fty arg hfty ha.
      eapply expr_has_ty_subl => //.
      by eapply hargs.
    - eapply SubTy; first by apply lty_sub_insert_1.
      econstructor => //.
      + by eapply expr_has_ty_subl.
      + move => f fty arg hfty ha.
        eapply expr_has_ty_subl => //.
        by eapply hargs.
    - econstructor; by eauto.
    - destruct (hlty' _ _ hin) as [ty' [? ?]].
      eapply CondTagTy.
      + done.
      + by eapply lty_sub_transitive.
      + eapply hi.
        * rewrite map_Forall_lookup => x tx.
          rewrite lookup_insert_Some.
          case => [[? <-] | [? hx]].
          { constructor; last by constructor.
            by apply hwf in hin.
          }
          by apply hwf in hx.
        * eapply lty_sub_transitive; first by apply lty_sub_insert_1.
          apply lty_sub_insert_2.
          by eauto.
  Qed.

  Lemma wf_mdef_ty_inherits t0 t σ m mdef orig def def0:
    map_Forall (λ _ : string, wf_cdef_parent Δ) Δ →
    map_Forall (λ _ : string, wf_cdef_fields_wf) Δ →
    map_Forall (λ _ : string, wf_cdef_methods_wf) Δ →
    map_Forall (λ _ : string, wf_cdef_fields_bounded) Δ →
    map_Forall (λ _ : string, cdef_methods_bounded) Δ →
    Δ !! t = Some def →
    Δ !! t0 = Some def0 →
    has_method m t orig mdef →
    wf_mdef_ty (ClassT t (gen_targs def.(generics))) (gen_targs def.(generics)) mdef →
    inherits_using t0 t σ →
    wf_mdef_ty (ClassT t0 (gen_targs def0.(generics))) σ mdef.
  Proof.
    move => hp hfwf hmwf hfb hmb hΔt hΔt0 hm [rty [hbody hret]] hin.
    assert (h: Forall (bounded (generics def0)) σ
            ∧ length σ = generics def ∧ Forall wf_ty σ).
    { apply inherits_using_wf in hin => //.
      destruct hin as (? & ? & ? & ? &? & ? & ?).
      by simplify_eq.
    }
    destruct h as (hF & hL & hσ).
    apply has_method_from_def in hm => //.
    destruct hm as (def' & mdef_orig & ho & hmdef_orig & _ & σm & hσm & hmdef).
    apply inherits_using_wf in hσm => //.
    destruct hσm as (def'' & odef'' & ? & ? & ? & ? & ? );
    assert (ho' := ho).
    assert (hmdef_orig' := hmdef_orig).
    apply hmwf in ho'.
    apply ho' in hmdef_orig' as [hargs _].
    exists (subst_ty σ <$> rty); split.
    - apply cmd_has_ty_subl with (<["$this":=ClassT t σ]>(subst_ty σ <$> methodargs mdef)) => //.
      + rewrite map_Forall_lookup => x tx.
        rewrite lookup_insert_Some.
        simplify_eq.
        case => [[? <-]|[? ]].
        * econstructor => //.
          rewrite Forall_forall in hσ => k ty hk.
          apply elem_of_list_lookup_2 in hk.
          by apply hσ.
        * rewrite lookup_fmap_Some.
          case => [ty [<- ]].
          rewrite /subst_mdef /=.
          rewrite lookup_fmap_Some.
          case => [tz [<- hz]].
          apply wf_ty_subst => //.
          apply wf_ty_subst => //.
          by apply hargs in hz.
      + replace (ClassT t σ) with (subst_ty σ (ClassT t (gen_targs def.(generics)))); last first.
        { by rewrite /= subst_ty_gen_targs. }
        replace (<["$this":=subst_ty σ (ClassT t (gen_targs (generics def)))]> (subst_ty σ <$> methodargs mdef))
          with (subst_ty σ <$> (<["$this" := ClassT t (gen_targs (generics def))]> (methodargs mdef))); last first.
        { by rewrite fmap_insert. }
        apply cmd_has_ty_subst => //.
        * rewrite map_Forall_lookup => x tx.
          rewrite lookup_insert_Some.
          simplify_eq.
          case => [[? <-] | [? ]].
          { econstructor => //; first by rewrite length_gen_targs. 
            by apply gen_targs_wf.
          }
          rewrite /subst_mdef /=.
          rewrite lookup_fmap_Some.
          case => [tz [<- hz]].
          apply wf_ty_subst => //.
          by apply hargs in hz.
        * move: hbody.
          simplify_eq.
          rewrite fmap_subst_tys_id => //.
          rewrite map_Forall_lookup /subst_mdef /= => k tk.
          rewrite lookup_fmap_Some; case => [ty [<- hty]].
          eapply bounded_subst => //.
          apply hmb in ho.
          apply ho in hmdef_orig.
          by apply hmdef_orig in hty.
      + move => x tx.
        rewrite lookup_insert_Some.
        case => [[<- <-]|[?]].
        * rewrite lookup_insert.
          eexists; split => //.
          replace σ with (subst_ty (gen_targs def0.(generics)) <$> σ); last first.
          { by rewrite subst_tys_id. }
          eapply subtype_inherits_using => //.
          by rewrite length_gen_targs.
        * rewrite lookup_fmap_Some.
          case => [ty [<- hx]].
          rewrite lookup_insert_ne // lookup_fmap hx /=.
          by eexists.
    - apply expr_has_ty_subst => //.
      replace (methodrettype mdef) with (subst_ty (gen_targs (generics def)) (methodrettype mdef)); first done.
      simplify_eq.
      rewrite subst_ty_id // /subst_mdef /=.
      eapply bounded_subst => //.
      apply hmb in ho.
      apply ho in hmdef_orig.
      by apply hmdef_orig.
  Qed.
          
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
