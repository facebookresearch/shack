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
    | ClassT (exact: bool) (cname: tag) (targs: list lang_ty)
    | NullT
    | NonNullT
    | UnionT (s t: lang_ty)
    | InterT (s t: lang_ty)
    | GenT (n: nat)
    | DynamicT
    | SupportDynT
    | ThisT
  .

  Variable P : lang_ty -> Prop.
  Hypothesis case_IntT : P IntT.
  Hypothesis case_BoolT : P BoolT.
  Hypothesis case_NothingT : P NothingT.
  Hypothesis case_MixedT : P MixedT.
  Hypothesis case_ClassT : ∀ exact cname targs,
    Forall P targs → P (ClassT exact cname targs).
  Hypothesis case_NullT : P NullT.
  Hypothesis case_NonNullT : P NonNullT.
  Hypothesis case_UnionT :  ∀ s t, P s → P t → P (UnionT s t).
  Hypothesis case_InterT :  ∀ s t, P s → P t → P (InterT s t).
  Hypothesis case_GenT: ∀ n, P (GenT n).
  Hypothesis case_DynamicT : P DynamicT.
  Hypothesis case_SupportDynT : P SupportDynT.
  Hypothesis case_ThisT : P ThisT.

  Fixpoint lang_ty_ind (t : lang_ty) :=
    match t with
    | IntT => case_IntT
    | BoolT => case_BoolT
    | NothingT => case_NothingT
    | MixedT => case_MixedT
    | ClassT exact cname targs =>
        let H := (fix fold (xs : list lang_ty) : Forall P xs :=
          match xs with
          | nil => List.Forall_nil _
          | x :: xs => List.Forall_cons _ x xs (lang_ty_ind x) (fold xs)
          end) targs in
        case_ClassT exact cname targs H
    | NullT => case_NullT
    | NonNullT => case_NonNullT
    | UnionT s t => case_UnionT s t (lang_ty_ind s) (lang_ty_ind t)
    | InterT s t => case_InterT s t (lang_ty_ind s) (lang_ty_ind t)
    | GenT n => case_GenT n
    | DynamicT => case_DynamicT
    | SupportDynT => case_SupportDynT
    | ThisT => case_ThisT
    end.
End nested_ind.

Fixpoint no_this ty : bool :=
  match ty with
  | ClassT _ _ σ => List.forallb no_this σ
  | UnionT A B => no_this A && no_this B
  | InterT A B => no_this A && no_this B
  | ThisT => false
  | _ => true
  end.

(* A type is bounded by n if any generic that might be
 * present in it is < n
 *)
Inductive bounded (n: nat) : lang_ty → Prop :=
  | ClassIsBounded exact cname targs :
      Forall (bounded n) targs → bounded n (ClassT exact cname targs)
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
  | ThisIsBounded : bounded n ThisT
.

Global Hint Constructors bounded : core.

(* Inversion lemma, so we can name things more easily *)
Lemma boundedI n ty:
  bounded n ty →
  match ty with
  | ClassT _ _ σ => Forall (bounded n) σ
  | UnionT A B | InterT A B => bounded n A ∧ bounded n B
  | GenT k => k < n
  | _ => True
  end.
Proof. move => h; by inv h. Qed.

Lemma bounded_exact n ex0 ex1 t σ:
  bounded n (ClassT ex0 t σ) → bounded n (ClassT ex1 t σ).
Proof. move => h; inv h; by constructor. Qed.

Lemma bounded_ge ty n:
  bounded n ty → ∀ m, m ≥ n → bounded m ty.
Proof.
  elim: ty => //=.
  - move => ? t σ hi /boundedI h m hge.
    econstructor.
    rewrite !Forall_lookup in hi, h.
    rewrite Forall_lookup => k ty hk.
    eapply hi => //.
    by eapply h.
  - move => A B hA hB /boundedI [h0 h1] m hge.
    by eauto.
  - move => A B hA hB /boundedI [h0 h1] m hge.
    by eauto.
  - move => k /boundedI hlt m hge.
    constructor; by lia.
Qed.

Lemma bounded_rigid exact t start len:
  bounded (start + len) (ClassT exact t (map GenT (seq start len))).
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
  | ClassT exact cname cargs => ClassT exact cname (subst_ty targs <$> cargs)
  | UnionT s t => UnionT (subst_ty targs s) (subst_ty targs t)
  | InterT s t => InterT (subst_ty targs s) (subst_ty targs t)
  | GenT n => default ty (targs !! n)
  | _ => ty
  end.

Fixpoint subst_this this ty :=
  match ty with
  | ClassT ex cname cargs => ClassT ex cname (subst_this this <$> cargs)
  | UnionT s t => UnionT (subst_this this s) (subst_this this t)
  | InterT s t => InterT (subst_this this s) (subst_this this t)
  | ThisT => this
  | _ => ty
  end.

Corollary subst_ty_nil ty : subst_ty [] ty = ty.
Proof.
  elim: ty => //=.
  - move => ? t σ hi.
    f_equal.
    rewrite Forall_forall in hi.
    rewrite -{2}(map_id σ).
    apply map_ext_in => s /elem_of_list_In hin.
    by apply hi.
  - by move => ?? -> ->.
  - by move => ?? -> ->.
Qed.

Corollary map_subst_ty_nil (σ: list lang_ty) : subst_ty [] <$> σ = σ.
Proof.
  elim: σ => //= hd tl hi.
  f_equal; first by rewrite subst_ty_nil.
  by apply hi.
Qed.

Corollary fmap_subst_ty_nil (σ: stringmap lang_ty) : subst_ty [] <$> σ = σ.
Proof.
  (* TODO: ask PY *)
  induction σ as [| s ty ftys Hs IH] using map_ind.
  - by rewrite fmap_empty.
  - by rewrite fmap_insert IH subst_ty_nil.
Qed.

Lemma subst_ty_subst ty l k:
  bounded (length k) ty →
  subst_ty l (subst_ty k ty) = subst_ty (subst_ty l <$> k) ty.
Proof.
  elim: ty => //=.
  - move => ? t σ hi /boundedI h.
    f_equal.
    rewrite -list_fmap_compose.
    rewrite Forall_forall in hi.
    apply map_ext_in => s /elem_of_list_In hin.
    apply hi => //.
    rewrite Forall_forall in h.
    by apply h.
  - move => A B hiA hiB /boundedI [hA hB].
    by rewrite hiA // hiB.
  - move => A B hiA hiB /boundedI [hA hB].
    by rewrite hiA // hiB.
  - move => n /boundedI hlt.
    rewrite list_lookup_fmap.
    destruct (k !! n) as [ ty | ] eqn:hty => //=.
    apply lookup_lt_is_Some_2 in hlt.
    rewrite hty in hlt.
    by elim: hlt.
Qed.

Lemma map_subst_ty_subst (j k l: list lang_ty):
  Forall (bounded (length k)) l →
  subst_ty j <$> (subst_ty k <$> l) =
  subst_ty (subst_ty j <$> k) <$> l.
Proof.
  elim : l => //= hd lt hi hb.
  apply Forall_cons_1 in hb as [].
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
  elim: ty => //=.
  - move => ? t σ hi /boundedI hb m σ0 hlen hσ0.
    constructor.
    rewrite Forall_lookup => k ty hk.
    apply list_lookup_fmap_inv in hk as [ty0 [-> hty0]].
    rewrite Forall_lookup in hi.
    eapply hi => //.
    rewrite Forall_lookup in hb.
    by eapply hb.
  - move => s t his hit /boundedI [hs ht] m σ0 hlen hσ0.
    constructor; by eauto.
  - move => s t his hit /boundedI [hs ht] m σ0 hlen hσ0.
    constructor; by eauto.
  - move => k /boundedI hlt m σ0 hlen hσ0.
    rewrite -hlen in hlt.
    rewrite Forall_lookup in hσ0.
    apply (hσ0 k).
    apply lookup_lt_is_Some_2 in hlt.
    destruct (σ0 !! k) as [ ty | ] eqn:hty => //.
    by elim: hlt.
Qed.

Lemma bounded_subst_this n ty this:
  bounded n ty →
  bounded n this →
  bounded n (subst_this this ty).
Proof.
  elim : ty => //=.
  - move => ? t σ hi /boundedI hb hthis.
    constructor.
    rewrite Forall_forall => ty /elem_of_list_fmap hin.
    destruct hin as [ty' [-> hin]].
    rewrite Forall_forall in hi.
    apply hi in hin => //.
    rewrite Forall_forall in hb.
    by apply hb.
  - move => s t hs ht /boundedI [??] hthis.
    constructor; by eauto.
  - move => s t hs ht /boundedI [??] hthis.
    constructor; by eauto.
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
  elim: expr => //=.
  - move => op e1 hi1 e2 hi2 hb.
    inv hb.
    by rewrite hi1 // hi2.
  - move => op e hi hb.
    inv hb.
    by rewrite hi.
  - move => e hi ty hb.
    inv hb.
    by rewrite hi // subst_ty_subst.
Qed.

Lemma map_subst_expr_subst (j k: list lang_ty) (l: list expr):
  Forall (expr_bounded (length k)) l →
  subst_expr j <$> (subst_expr k <$> l) =
  subst_expr (subst_ty j <$> k) <$> l.
Proof.
  elim: l => //= hd tl hi hb.
  apply Forall_cons_1 in hb as [].
  f_equal; first by rewrite subst_expr_subst.
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
  elim: expr; try (intros; by constructor).
  - move => op e1 hi1 e2 hi2 h m σ hlen hF.
    inv h.
    constructor; first by apply hi1.
    by apply hi2.
  - move => op e hi h m σ hlen hF.
    inv h.
    constructor; by apply hi.
  - move => e hi ty h m σ hlen hF.
    inv h.
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
  (* When performing New, one can specify the type parameter, or
   * expect them to be infered (and pass nothing).
   * It is not possible to only pass some of them at the moment, it is
   * an all or nothing situation.
   *)
  | NewC (lhs: var) (class_name: tag) (targs: option (list lang_ty)) (args: stringmap expr)
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
  | NewC lhs C oσ args =>
      NewC lhs C ((λ (targs: list lang_ty), subst_ty σ <$> targs) <$> oσ) (subst_expr σ <$> args)
  | GetC lhs recv name => GetC lhs (subst_expr σ recv) name
  | SetC recv fld rhs => SetC (subst_expr σ recv) fld (subst_expr σ rhs)
  | RuntimeCheckC v rc thn els =>
      RuntimeCheckC v rc (subst_cmd σ thn) (subst_cmd σ els)
  | ErrorC => ErrorC
  end.

Lemma subst_cmd_nil cmd : subst_cmd [] cmd = cmd.
Proof.
  induction cmd as [ | fst hi0 snd hi1 | lhs e | ? thn hi0 els hi1
    | lhs recv name args | lhs C oσ args | lhs recv name
    | recv fld rhs | v rc thn hi0 els hi1 | ] => //=.
  - by rewrite hi0 hi1.
  - by rewrite subst_expr_nil.
  - by rewrite subst_expr_nil hi0 hi1.
  - by rewrite subst_expr_nil fmap_subst_expr_nil.
  - f_equal; last by rewrite fmap_subst_expr_nil.
    case: oσ => [ σ0 | ] //=.
    by rewrite map_subst_ty_nil.
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
  | NewBounded lhs C oσ args:
      match oσ with
      | None => True
      | Some σ => Forall (bounded n) σ
      end →
      map_Forall (λ _, expr_bounded n) args →
      cmd_bounded n (NewC lhs C oσ args)
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

Lemma cmd_boundedI n cmd:
  cmd_bounded n cmd →
  match cmd with
  | IfC e c0 c1 => expr_bounded n e ∧ cmd_bounded n c0 ∧ cmd_bounded n c1
  | GetC _ e _
  | LetC _ e => expr_bounded n e
  | SetC e0 _ e1 => expr_bounded n e0 ∧ expr_bounded n e1
  | CallC _ e _ args =>
      expr_bounded n e ∧ map_Forall (λ _, expr_bounded n) args
  | NewC _ _ oσ args =>
      match oσ with
      | None => True
      | Some σ => Forall (bounded n) σ
      end ∧ map_Forall (λ _, expr_bounded n) args
  | SeqC c0 c1
  | RuntimeCheckC _ _ c0 c1 => cmd_bounded n c0 ∧ cmd_bounded n c1
  | _ => True
  end.
Proof. move => h; by inv h. Qed.

Lemma subst_cmd_cmd k l cmd :
  cmd_bounded (length l) cmd →
  subst_cmd k (subst_cmd l cmd) = subst_cmd (subst_ty k <$> l) cmd.
Proof.
  elim: cmd => /=.
  - by idtac.
  - move => ? hi0 ? hi1 /cmd_boundedI [h0 h1].
    by rewrite hi0 // hi1.
  - move => lhs e /cmd_boundedI hb.
    by rewrite subst_expr_subst.
  - move => ?? hi0 ? hi1 /cmd_boundedI [? [? ?]].
    by rewrite subst_expr_subst // hi0 // hi1.
  - move => ???? /cmd_boundedI [??].
    by rewrite fmap_subst_expr_subst // subst_expr_subst.
  - move => ?? σ ? /cmd_boundedI [h0 ?].
    case: σ h0 => [ σ | ] h0 //=.
    + rewrite map_subst_ty_subst //.
      by rewrite fmap_subst_expr_subst.
    + by rewrite fmap_subst_expr_subst.
  - move => ??? /cmd_boundedI ?.
    by rewrite subst_expr_subst.
  - move => ??? /cmd_boundedI [??].
    by rewrite !subst_expr_subst.
  - move => ??? hi0 ? hi1 /cmd_boundedI [??].
    by rewrite hi0 // hi1.
  - by idtac.
Qed.

Lemma cmd_bounded_subst n cmd:
  cmd_bounded n cmd →
  ∀ m targs, length targs = n →
  Forall (bounded m) targs →
  cmd_bounded m (subst_cmd targs cmd).
Proof.
  elim: cmd => /=.
  - move => ?????; by constructor.
  - move => ? hi0 ? hi1 /cmd_boundedI [??] m σ hlen hF.
    constructor; first by apply hi0.
    by apply hi1.
  - move  => ?? /cmd_boundedI hb m σ hlen hF.
    rewrite -hlen in hb.
    constructor; by eapply expr_bounded_subst.
  - move => ?? hi0 ? hi1 /cmd_boundedI [he [??]] m σ hlen hF.
    rewrite -hlen in he.
    constructor; first by eapply expr_bounded_subst.
    + by apply hi0.
    + by apply hi1.
  - move => ???? /cmd_boundedI [h hs] m σ hlen hF.
    rewrite -hlen in h.
    constructor; first by eapply expr_bounded_subst.
    rewrite map_Forall_lookup => i ?.
    rewrite lookup_fmap_Some => [[e [<- he]]].
    apply expr_bounded_subst with (length σ) => //.
    apply hs in he.
    by rewrite hlen.
  - move => ?? oσ ? /cmd_boundedI [h ?] m σ hlen hF.
    constructor.
    { case: oσ h => [ σ0 | ] //= h.
      rewrite Forall_lookup => ? hi hk.
      apply list_lookup_fmap_inv in hk as [ty [-> hty]].
      apply bounded_subst with (length σ) => //.
      rewrite Forall_lookup in h.
      rewrite hlen.
      by eapply h.
    }
    rewrite map_Forall_lookup => i ?.
    rewrite lookup_fmap_Some => [[e [<- he]]].
    apply expr_bounded_subst with (length σ) => //.
    rewrite hlen.
    by eauto.
  - move => ??? /cmd_boundedI h m σ hlen hF.
    rewrite -hlen in h.
    constructor; by eapply expr_bounded_subst.
  - move => ??? /cmd_boundedI [h0 h1] m σ hlen hF.
    rewrite -hlen in h0.
    constructor; first by eapply expr_bounded_subst.
    by eapply expr_bounded_subst.
  - move => ??? hi0 ? hi1 /cmd_boundedI [??] m σ hlen hF.
    constructor; first by apply hi0.
    by apply hi1.
  - move => ?????; by constructor.
Qed.

Inductive visibility := Public | Private.

Record methodDef := {
  methodvisibility : visibility;
  methodargs: stringmap lang_ty;
  methodrettype: lang_ty;
  methodbody: cmd;
  methodret: expr;
}.

Definition subst_mdef targs mdef : methodDef := {|
    methodvisibility := mdef.(methodvisibility);
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

Lemma gen_targs_has_no_this n: Forall no_this (gen_targs n).
Proof.
  rewrite Forall_lookup => k ty hty.
  apply lookup_gen_targs in hty.
  by rewrite hty.
Qed.

Lemma subst_ty_has_no_this σ ty:
  no_this ty → Forall no_this σ → no_this (subst_ty σ ty).
Proof.
  elim: ty => //=.
  - move => ?? σ0 hi h hσ0.
    apply forallb_True in h.
    apply forallb_True.
    rewrite Forall_lookup => k ty hSome.
    apply list_lookup_fmap_inv in hSome as [ty0 [-> hty0]].
    rewrite Forall_lookup in h.
    rewrite Forall_lookup in hi.
    assert (hty0_ := hty0).
    apply h in hty0_; clear h.
    by apply hi in hty0.
  - move => s t hs ht h hσ0.
    apply andb_prop_elim in h as [h0 h1].
    apply andb_prop_intro; split; by firstorder.
  - move => s t hs ht h hσ0.
    apply andb_prop_elim in h as [h0 h1].
    apply andb_prop_intro; split; by firstorder.
  - move => k _ hσ; rewrite Forall_lookup in hσ.
    destruct (σ !! k) as [ ty0 | ] eqn:hty0; last done.
    by apply hσ in hty0.
Qed.

Lemma subst_ty_has_no_this_map (σ σ0: list lang_ty):
  Forall no_this σ → Forall no_this σ0 → Forall no_this (subst_ty σ <$> σ0).
Proof.
  move => h.
  induction σ0 as [ | hd tl hi] => h0; first done.
  apply Forall_cons in h0 as [hhd htl].
  constructor.
  { by apply subst_ty_has_no_this. }
  by apply hi.
Qed.

Lemma subst_this_has_no_this ty:
  ∀ this, no_this this → no_this (subst_this this ty).
Proof.
  elim: ty => //=.
  - move => _exact C σ hi this hthis.
    apply forallb_True.
    rewrite Forall_lookup => k ty hSome.
    apply list_lookup_fmap_inv in hSome as [ty0 [-> hty0]].
    rewrite Forall_lookup in hi.
    assert (hty0_ := hty0).
    by apply hi with (this := this) in hty0_.
  - move => s t hs ht this hthis.
    apply andb_prop_intro.
    firstorder.
  - move => s t hs ht this hthis.
    apply andb_prop_intro.
    firstorder.
Qed.

Lemma subst_ty_id n ty:
  bounded n ty →
  subst_ty (gen_targs n) ty = ty.
Proof.
  elim : ty => //=.
  - move => ? t σ hi /boundedI hf; f_equal.
    rewrite Forall_forall in hi.
    rewrite -{2}(map_id σ).
    apply map_ext_in => /= s /elem_of_list_In hin.
    apply hi => //.
    rewrite Forall_forall in hf.
    by apply hf.
  - move => s t his hit /boundedI [hs ht]; f_equal; by eauto.
  - move => s t his hit /boundedI [hs ht]; f_equal; by eauto.
  - move => k /boundedI hlt.
    by rewrite lookup_gen_targs_lt.
Qed.

Lemma subst_tys_id n σ:
  Forall (bounded n) σ →
  subst_ty (gen_targs n) <$> σ = σ.
Proof.
  elim: σ n => //= hd tl hi n hf.
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
  elim: expr => //=.
  - move => op e1 hi1 e2 hi2 h; inv h.
    by rewrite hi1 // hi2.
  - move => op e hi h; inv h.
    by rewrite hi.
  - move => e hi ty h; inv h.
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
  elim : cmd => /=.
  - by idtac.
  - move => ? hi0 ? hi1 /cmd_boundedI [??].
    by rewrite hi0 // hi1.
  - move => ?? /cmd_boundedI ?.
    by rewrite subst_expr_gen_targs.
  - move => ?? hi0 ? hi1 /cmd_boundedI [? [??]].
    by rewrite subst_expr_gen_targs // hi0 // hi1.
  - move => ???? /cmd_boundedI [??].
    by rewrite subst_expr_gen_targs // fmap_subst_exprs_id.
  - move => ?? oσ ? /cmd_boundedI [h ?].
    f_equal; last by rewrite fmap_subst_exprs_id.
    case: oσ h => [ σ | ] //= hσ.
    by rewrite subst_tys_id.
  - move => ??? /cmd_boundedI h.
    by rewrite subst_expr_gen_targs.
  - move => ??? /cmd_boundedI [??].
    by rewrite !subst_expr_gen_targs.
  - move => ??? hi0 ? hi1 /cmd_boundedI [??].
    by rewrite hi0 // hi1.
  - by idtac.
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

Lemma bounded_forall_ge n σ:
  Forall (bounded n) σ →
  ∀ m, m ≥ n → Forall (bounded m) σ.
Proof.
  move/Forall_lookup => h m hge.
  rewrite Forall_lookup => k ty hk.
  eapply bounded_ge; by eauto.
Qed.
