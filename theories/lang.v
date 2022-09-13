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
    | DynamicT
    | SupportDynT
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
  Hypothesis case_DynamicT : P DynamicT.
  Hypothesis case_SupportDynT : P SupportDynT.

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
    | DynamicT => case_DynamicT
    | SupportDynT => case_SupportDynT
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
  | DynamicIsBounded : bounded n DynamicT
  | SupportDynIsBounded : bounded n SupportDynT
.

Global Hint Constructors bounded : core.

Lemma bounded_ge ty n:
  bounded n ty → ∀ m, m ≥ n → bounded m ty.
Proof.
  induction ty as [ | | | | t σ hi | | | s t hs ht |
      s t hs ht | k | | ] => h m hge //=.
  - constructor.
    inv h.
    rewrite Forall_lookup => i ty hty.
    rewrite Forall_lookup in hi.
    apply hi with (m := m) in hty => //.
    rewrite Forall_lookup in H0.
    by apply H0 in hty.
  - inv h.
    constructor; by eauto.
  - inv h.
    constructor; by eauto.
  - inv h.
    constructor.
    by lia.
Qed.

Lemma bounded_rigid t start len:
  bounded (start + len) (ClassT t (map GenT (seq start len))).
Proof.
  constructor.
  rewrite Forall_lookup => i ty h.
  apply list_lookup_fmap_inv in h.
  destruct h as [k [-> h]].
  rewrite lookup_seq in h; destruct h as [-> h].
  constructor.
  by lia.
Qed.

(* To be used with `bounded`: Generics must be always bound *)
Fixpoint subst_ty (targs:list lang_ty) (ty: lang_ty):  lang_ty :=
  match ty with
  | ClassT cname cargs => ClassT cname (subst_ty targs <$> cargs)
  | UnionT s t => UnionT (subst_ty targs s) (subst_ty targs t)
  | InterT s t => InterT (subst_ty targs s) (subst_ty targs t)
  | GenT n => default ty (targs !! n)
  | _ => ty
  end.

Corollary subst_ty_nil ty : subst_ty [] ty = ty.
Proof.
  induction ty as [ | | | | cname targs hi | | | s t hs ht |
      s t hs ht | n | | ] => //=.
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
      s t hs ht | n | | ] => //=.
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
      s t hs ht | k | | ] => //= hb m σ hlen hσ.
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
  | UpcastE (e: expr) (ty: lang_ty)
.

Fixpoint subst_expr (σ:list lang_ty) (expr: expr) :=
  match expr with
  | BinOpE op e1 e2 => BinOpE op (subst_expr σ e1) (subst_expr σ e2)
  | UniOpE op e => UniOpE op (subst_expr σ e)
  | UpcastE e ty => UpcastE (subst_expr σ e) (subst_ty σ ty)
  | _ => expr
  end.

Lemma subst_expr_nil expr : subst_expr [] expr = expr.
Proof.
  induction expr as [ | | | op e1 hi1 e2 hi2 | op e hi | | | e hi ty] => //=.
  - by rewrite hi1 hi2.
  - by rewrite hi.
  - by rewrite hi subst_ty_nil.
Qed.

Lemma map_subst_expr_nil (l : list expr) : subst_expr [] <$> l = l.
Proof.
  induction l as [ | hd tl hi] => //.
  by rewrite fmap_cons subst_expr_nil hi.
Qed.

Lemma fmap_subst_expr_nil (l : stringmap expr) : subst_expr [] <$> l = l.
Proof.
  induction l as [| s e es Hs IH] using map_ind; first by rewrite fmap_empty.
  by rewrite fmap_insert subst_expr_nil IH.
Qed.

Inductive expr_bounded (n: nat) : expr → Prop :=
  | IntEBounded z : expr_bounded n (IntE z)
  | BoolEBounded b : expr_bounded n (BoolE b)
  | NullEBounded : expr_bounded n NullE
  | BinOpEBounded op e1 e2:
      expr_bounded n e1 →
      expr_bounded n e2 →
      expr_bounded n (BinOpE op e1 e2)
  | UniOpEBounded op e:
      expr_bounded n e →
      expr_bounded n (UniOpE op e)
  | VarEBounded v : expr_bounded n (VarE v)
  | ThisEBounded : expr_bounded n ThisE
  | UpcastEBounded e ty : expr_bounded n e →
      bounded n ty →
      expr_bounded n (UpcastE e ty)
.

Lemma subst_expr_subst k l expr :
  expr_bounded (length l) expr →
  subst_expr k (subst_expr l expr) = subst_expr (subst_ty k <$> l) expr.
Proof.
  move => hb.
  induction expr as [ | | | op e1 hi1 e2 hi2 | op e hi | | | e hi ty] => //=.
  - inv hb.
    by rewrite hi1 // hi2.
  - inv hb.
    by rewrite hi.
  - inv hb.
    by rewrite hi // subst_ty_subst.
Qed.

Lemma map_subst_expr_subst (j k: list lang_ty) (l: list expr):
  Forall (expr_bounded (length k)) l →
  subst_expr j <$> (subst_expr k <$> l) =
  subst_expr (subst_ty j <$> k) <$> l.
Proof.
  move => hwf.
  induction l as [ | hd tl hi] => //.
  inv hwf.
  rewrite !fmap_cons subst_expr_subst => //.
  f_equal.
  by rewrite list_fmap_compose -/subst_ty list_fmap_id -/fmap hi.
Qed.

Lemma fmap_subst_expr_subst j k (l: stringmap expr):
  map_Forall (λ _, expr_bounded (length k)) l →
  subst_expr j <$> (subst_expr k <$> l) =
  subst_expr (subst_ty j <$> k) <$> l.
Proof.
  move => hwf.
  move: j k hwf.
  induction l as [| s e es Hs IH] using map_ind => j k hwf;
    first by rewrite !fmap_empty.
  rewrite map_Forall_insert // in hwf.
  destruct hwf as [hhd htl].
  by rewrite !fmap_insert subst_expr_subst // IH.
Qed.

Lemma expr_bounded_subst n expr:
  expr_bounded n expr →
  ∀ m targs, length targs = n →
  Forall (bounded m) targs →
  expr_bounded m (subst_expr targs expr).
Proof.
  induction expr as [ | | | op e1 hi1 e2 hi2 | op e hi | | | e hi ty]
    => //= h m σ hlen hF; try by constructor.
  - inv h.
    constructor; first by apply hi1.
    by apply hi2.
  - inv h.
    constructor; by apply hi.
  - inv h.
    constructor; first by apply hi.
    by apply bounded_subst with (length σ).
Qed.

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
  | NewC (lhs: var) (class_name: tag) (type_args: list lang_ty) (args: stringmap expr)
  | GetC (lhs: var) (recv: expr) (name: string)
  | SetC (recv: expr) (fld: string) (rhs: expr)
      (* tag test "if ($v is C<_>) { ... }".  *)
  | RuntimeCheckC (v : var) (rc: runtime_check) (thn els: cmd)
  | ErrorC
.

Fixpoint subst_cmd (σ:list lang_ty) (cmd: cmd) :=
  match cmd with
  | SkipC => SkipC
  | SeqC fst snd => SeqC (subst_cmd σ fst) (subst_cmd σ snd)
  | LetC lhs e => LetC lhs (subst_expr σ e)
  | IfC cond thn els => IfC (subst_expr σ cond) (subst_cmd σ thn) (subst_cmd σ els)
  | CallC lhs recv name args =>
      CallC lhs (subst_expr σ recv) name (subst_expr σ <$> args)
  | NewC lhs C σ0 args =>
      NewC lhs C (subst_ty σ <$> σ0) (subst_expr σ <$> args)
  | GetC lhs recv name => GetC lhs (subst_expr σ recv) name
  | SetC recv fld rhs => SetC (subst_expr σ recv) fld (subst_expr σ rhs)
  | RuntimeCheckC v rc thn els =>
      RuntimeCheckC v rc (subst_cmd σ thn) (subst_cmd σ els)
  | ErrorC => ErrorC
  end.

Lemma subst_cmd_nil cmd : subst_cmd [] cmd = cmd.
Proof.
  induction cmd as [ | fst hi0 snd hi1 | lhs e | ? thn hi0 els hi1
    | lhs recv name args | lhs C σ0 args | lhs recv name
    | recv fld rhs | v rc thn hi0 els hi1 | ] => //=.
  - by rewrite hi0 hi1.
  - by rewrite subst_expr_nil.
  - by rewrite subst_expr_nil hi0 hi1.
  - by rewrite subst_expr_nil fmap_subst_expr_nil.
  - by rewrite map_subst_ty_nil fmap_subst_expr_nil.
  - by rewrite subst_expr_nil.
  - by rewrite !subst_expr_nil.
  - by rewrite hi0 hi1.
Qed.

Inductive cmd_bounded (n: nat) : cmd → Prop :=
  | SkipBounded : cmd_bounded n SkipC
  | SeqBounded fstc sndc : cmd_bounded n fstc →
      cmd_bounded n sndc → cmd_bounded n (SeqC fstc sndc)
  | LetBounded lhs e : expr_bounded n e → cmd_bounded n (LetC lhs e)
  | IfBounded cond thn els : expr_bounded n cond →
      cmd_bounded n thn → cmd_bounded n els → cmd_bounded n (IfC cond thn els)
  | CallBounded lhs recv name args:
      expr_bounded n recv →
      map_Forall (λ _, expr_bounded n) args →
      cmd_bounded n (CallC lhs recv name args)
  | NewBounded lhs C σ args:
      Forall (bounded n) σ →
      map_Forall (λ _, expr_bounded n) args →
      cmd_bounded n (NewC lhs C σ args)
  | GetBounded lhs recv name: expr_bounded n recv →
      cmd_bounded n (GetC lhs recv name)
  | SetBounded recv fld rhs : expr_bounded n recv →
      expr_bounded n rhs →
      cmd_bounded n (SetC recv fld rhs)
  | RuntimeCheckBounded v rc thn els:
      cmd_bounded n thn →
      cmd_bounded n els →
      cmd_bounded n (RuntimeCheckC v rc thn els)
  | ErrorBounded : cmd_bounded n ErrorC
.

Lemma subst_cmd_cmd k l cmd :
  cmd_bounded (length l) cmd →
  subst_cmd k (subst_cmd l cmd) = subst_cmd (subst_ty k <$> l) cmd.
Proof.
  move => hb.
  induction cmd as [ | fst hi0 snd hi1 | lhs e | ? thn hi0 els hi1
    | lhs recv name args | lhs C σ0 args | lhs recv name
    | recv fld rhs | v rc thn hi0 els hi1 | ] => //=.
  - inv hb.
    by rewrite hi0 // hi1.
  - inv hb.
    by rewrite subst_expr_subst.
  - inv hb.
    by rewrite subst_expr_subst // hi0 // hi1.
  - inv hb.
    by rewrite fmap_subst_expr_subst // subst_expr_subst.
  - inv hb.
    by rewrite fmap_subst_expr_subst // map_subst_ty_subst.
  - inv hb.
    by rewrite subst_expr_subst.
  - inv hb.
    by rewrite !subst_expr_subst.
  - inv hb.
    by rewrite hi0 // hi1.
Qed.

Lemma cmd_bounded_subst n cmd:
  cmd_bounded n cmd →
  ∀ m targs, length targs = n →
  Forall (bounded m) targs →
  cmd_bounded m (subst_cmd targs cmd).
Proof.
  induction cmd as [ | fst hi0 snd hi1 | lhs e | ? thn hi0 els hi1
    | lhs recv name args | lhs C σ0 args | lhs recv name
    | recv fld rhs | v rc thn hi0 els hi1 | ]
    => //= h m σ hlen hF; try by constructor.
  - inv h.
    constructor; first by apply hi0.
    by apply hi1.
  - inv h.
    constructor; by apply expr_bounded_subst with (length σ).
  - inv h.
    constructor; first by apply expr_bounded_subst with (length σ).
    { by apply hi0. }
    by apply hi1.
  - inv h.
    constructor; first by apply expr_bounded_subst with (length σ).
    rewrite map_Forall_lookup => i ?.
    rewrite lookup_fmap_Some => [[e [<- he]]].
    apply expr_bounded_subst with (length σ) => //.
    by apply H4 in he.
  - inv h.
    constructor.
    { rewrite Forall_lookup => ? hi hk.
      apply list_lookup_fmap_inv in hk as [ty [-> hty]].
      apply bounded_subst with (length σ) => //.
      rewrite Forall_lookup in H1.
      by eauto.
    }
    rewrite map_Forall_lookup => i ?.
    rewrite lookup_fmap_Some => [[e [<- he]]].
    apply expr_bounded_subst with (length σ) => //.
    by apply H4 in he.
  - inv h.
    constructor; by apply expr_bounded_subst with (length σ).
  - inv h.
    constructor; first by apply expr_bounded_subst with (length σ).
    by apply expr_bounded_subst with (length σ).
  - inv h.
    constructor; first by apply hi0.
    by apply hi1.
Qed.

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
    methodbody := subst_cmd targs mdef.(methodbody);
    methodret := subst_expr targs mdef.(methodret);
  |}.

Lemma subst_mdef_nil mdef : subst_mdef [] mdef = mdef.
Proof.
  rewrite /subst_mdef subst_ty_nil fmap_subst_ty_nil subst_cmd_nil subst_expr_nil.
  by destruct mdef.
Qed.

Definition mdef_bounded n mdef : Prop :=
  map_Forall (λ _argname, bounded n) mdef.(methodargs) ∧ bounded n mdef.(methodrettype) ∧
  cmd_bounded n mdef.(methodbody) ∧
  expr_bounded n mdef.(methodret).

Lemma subst_mdef_mdef k l mdef :
  mdef_bounded (length l) mdef →
  subst_mdef k (subst_mdef l mdef) = subst_mdef (subst_ty k <$> l) mdef.
Proof.
  rewrite /mdef_bounded map_Forall_lookup => [[hargs [hret [hbody hmret]]]].
  rewrite /subst_mdef; destruct mdef as [? args ret body ?]; f_equiv => //=.
  - by rewrite fmap_subst_ty_subst.
  - by rewrite subst_ty_subst.
  - by rewrite subst_cmd_cmd.
  - by rewrite subst_expr_subst.
Qed.

Lemma mdef_bounded_subst n mdef:
  mdef_bounded n mdef →
  ∀ m targs, length targs = n →
  Forall (bounded m) targs →
  mdef_bounded m (subst_mdef targs mdef).
Proof.
  move => [/map_Forall_lookup hargs [hret [hbody hmret]]] m σ hl hf.
  rewrite /mdef_bounded /subst_mdef /=; split.
  { rewrite map_Forall_lookup => k ty hty.
    apply lookup_fmap_Some in hty as [ty' [ <- hm]].
    apply bounded_subst with n => //.
    by eapply hargs.
  }
  split; first by apply bounded_subst with n.
  split; first by apply cmd_bounded_subst with n.
  by apply expr_bounded_subst with n.
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

Lemma bounded_constraints_ge Δ n m:
  Forall (bounded_constraint n) Δ → m ≥ n →
  Forall (bounded_constraint m) Δ.
Proof.
  move => /Forall_lookup h hge.
  rewrite Forall_lookup => i c hc.
  apply h in hc as [h0 h1].
  split; by eapply bounded_ge.
Qed.

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

Lemma lookup_gen_targs_ge:
  ∀ n pos, n <= pos → gen_targs n !! pos = None.
Proof.
  move => n pos h.
  by rewrite /gen_targs list_lookup_fmap lookup_seq_ge.
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
      s t hs ht | k | | ] => //=.
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

Lemma subst_expr_gen_targs n expr:
  expr_bounded n expr →
  subst_expr (gen_targs n) expr = expr.
Proof.
  induction expr as [ | | | op e1 hi1 e2 hi2 | op e hi | | | e hi ty]
    => //= h.
  - inv h.
    by rewrite hi1 // hi2.
  - inv h.
    by rewrite hi.
  - inv h.
    by rewrite subst_ty_id // hi.
Qed.

Lemma fmap_subst_exprs_id n (m: stringmap expr):
  map_Forall (λ _, expr_bounded n) m →
  subst_expr (gen_targs n) <$> m = m.
Proof.
  revert n.
  induction m as [| s e es Hs IH] using map_ind => n hm; first by rewrite fmap_empty.
  rewrite fmap_insert; f_equal.
  - apply subst_expr_gen_targs.
    apply hm with s.
    by rewrite lookup_insert.
  - apply IH.
    rewrite map_Forall_lookup => k tk hk.
    apply hm with k.
    rewrite lookup_insert_ne // => heq; subst.
    by rewrite Hs in hk.
Qed.

Lemma subst_cmd_gen_targs n cmd :
  cmd_bounded n cmd →
  subst_cmd (gen_targs n) cmd = cmd.
Proof.
  induction cmd as [ | fst hi0 snd hi1 | lhs e | ? thn hi0 els hi1
    | lhs recv name args | lhs C σ0 args | lhs recv name
    | recv fld rhs | v rc thn hi0 els hi1 | ] => //=h.
  - inv h.
    by rewrite hi0 // hi1.
  - inv h.
    by rewrite subst_expr_gen_targs.
  - inv h.
    by rewrite subst_expr_gen_targs // hi0 // hi1.
  - inv h.
    by rewrite subst_expr_gen_targs // fmap_subst_exprs_id.
  - inv h.
    by rewrite subst_tys_id // fmap_subst_exprs_id.
  - inv h.
    by rewrite subst_expr_gen_targs.
  - inv h.
    by rewrite !subst_expr_gen_targs.
  - inv h.
    by rewrite hi0 // hi1.
Qed.

Lemma subst_mdef_gen_targs n mdef :
  mdef_bounded n mdef →
  subst_mdef (gen_targs n) mdef = mdef.
Proof.
  rewrite /mdef_bounded /subst_mdef.
  move => [hargs [hret [hbody hmret]]].
  rewrite subst_ty_id //.
  rewrite fmap_subst_tys_id //.
  rewrite subst_cmd_gen_targs //.
  rewrite subst_expr_gen_targs //.
  by destruct mdef.
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
