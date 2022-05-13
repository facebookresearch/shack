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

Inductive binop :=
  | PlusO | MinusO | TimesO | DivO | LtO | GtO | EqO
.

Inductive uniop := | NotO.

Inductive expr :=
  | IntE (z: Z)
  | BoolE (b: bool)
  | NullE
  | BinOpE (op: binop) (e1: expr) (e2: expr)
  | UniOpE (op: uniop) (e: expr)
  | VarE (v: var)
  | ThisE (* $this *)
.

Inductive runtime_check :=
  | RCTag of tag
  | RCInt
  | RCBool
  | RCNull
  | RCNonNull
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
      (* tag test "if ($v is C<_>) { ... }".
       * For now, we'll only support the runtime check on
       * classes without generics. We'll support classes with
       * generics in a second phase.
       *)
  | RuntimeCheckC (v : var) (rc: runtime_check) (body : cmd)
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

(* S <: T *)
Definition constraint := (lang_ty * lang_ty)%type.

Definition bounded_constraint n c := bounded n c.1 ∧ bounded n c.2.

Record classDef := {
  classname: tag;
  (* variance of the generics *)
  generics: list variance;
  (* sets of constraints. All generics in this set must be bound
   * by the `generics` list above.
   *)
  constraints : list constraint;
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
