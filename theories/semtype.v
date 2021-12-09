(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 * 
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
From stdpp Require Import base strings gmap stringmap fin_maps.
From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Import iprop own.
From iris.algebra Require Import ofe cmra gmap_view.
From iris.proofmode Require Import tactics.

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

Canonical Structure tagO : ofe := leibnizO tag.

Definition loc := positive.
Global Instance loc_dec_eq (l l' : loc) : Decision (l = l') := _.

Inductive value : Set :=
  | IntV (z: Z)
  | BoolV (b: bool)
  | NullV
  | LocV (ℓ : loc).
Local Instance value_inhabited : Inhabited value := populate NullV.

(* interpretation of types *)
Definition sem_typeO (Σ : gFunctors) : ofe := value -d> iPropO Σ.

Class sem_heapG (Σ : gFunctors) : Set := SemHeapG {
  sem_heapG_heap :> inG Σ (gmap_viewR loc (prodO tagO (gmapO string (laterO (sem_typeO Σ)))));
}.

Inductive lang_ty :=
  | IntT
  | BoolT
  | NothingT
  | MixedT
  | ClassT (cname: tag)
  | NullT
  | NonNullT
  | UnionT (s t: lang_ty)
  | InterT (s t: lang_ty)
.
Canonical Structure lang_tyO : ofe := leibnizO lang_ty.

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

Record classDef := {
  classname: tag;
  superclass: option tag;
  classfields : stringmap lang_ty;
  classmethods : stringmap methodDef;
}.

Section proofs.
Context `{!sem_heapG Σ}.
Notation iProp := (iProp Σ).

(* assume a given set of class definitions *)
Context (Δ: stringmap classDef).

(* class A extends B *)
Definition extends (A B: tag) : Prop :=
  ∃ cdef,
  Δ !! A = Some cdef ∧
  cdef.(superclass) = Some B
.

(* Refl trans closure of extends *)
Definition inherits := rtc extends.

(* Note useful, just for sanity check: inherits are chains.
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
  | SubClass : ∀ A B, inherits A B → subtype (ClassT A) (ClassT B)
  | SubMixed2: subtype MixedT (UnionT NonNullT NullT)
  | SubIntNonNull: subtype IntT NonNullT
  | SubBoolNonNull: subtype BoolT NonNullT
  | SubClassNonNull: ∀ A, subtype (ClassT A) NonNullT
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

Definition local_tys := stringmap lang_ty.

(* has_field fname ty cname checks if the class cname has a field named fname of type ty *)
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

Ltac inv H := inversion H; subst; clear H.

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

Lemma has_field_inherits : map_Forall (fun _ => wf_cdef_fields) Δ → ∀ A B, inherits A B →
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

(* the interpretation of types is simply given by
   the carrier set of the sem_typeO ofe *)
Notation interpO := (sem_typeO Σ).
Definition interp := ofe_car interpO.
Eval hnf in interp.
(* = value → iPropO Σ *)
(*      : Type *)

(* now, let's interpret some ty *)

Definition interp_null : interp :=
  λ (v : value), ⌜v = NullV⌝%I.

Definition interp_int : interp :=
  λ (v : value), (∃ z, ⌜v = IntV z⌝)%I.

Definition interp_bool : interp :=
  λ (v : value), (∃ b, ⌜v = BoolV b⌝)%I.

Definition interp_union (iA : interp) (iB : interp) : interp :=
  λ (v : value), (iA v ∨ iB v)%I.

Definition interp_inter (iA : interp) (iB : interp) : interp :=
  λ (v : value), (iA v ∧ iB v)%I.

Definition interp_nothing : interp :=
  λ (_: value), False%I.

(* name for the semantic heap *)
Context (γ : gname).

Notation sem_heap_mapsto ℓ t iFs :=
  (own γ (gmap_view_frag ℓ DfracDiscarded (t, iFs))).

Notation ty_interpO := (lang_ty -d> interpO).


(* I need these two intermediate definition to make Coq/Type Classes instaces
 * happy.
 *)
Definition interp_ty_next (rec: ty_interpO) (typ: lang_ty): laterO interpO :=
  Next (rec typ)
.

Definition interp_tys_next (rec: ty_interpO) (ftys: stringmap lang_ty) : gmapO string (laterO interpO) :=
  (interp_ty_next rec) <$> ftys
.

(* interpret a class type given the tag and the
   interpretation of their fields *)
Definition interp_class (cname : tag) (rec : ty_interpO) : interp :=
  λ (w : value),
    (∃ ℓ t (fields:stringmap lang_ty),
    ⌜w = LocV ℓ ∧ inherits t cname ∧ has_fields t fields⌝ ∗
    sem_heap_mapsto ℓ t (interp_tys_next rec fields))%I.

Definition interp_nonnull (rec : ty_interpO) : interp :=
  λ (v : value),
     ((interp_int v) ∨
     (interp_bool v) ∨
     (∃ t, interp_class t rec v))%I.

Definition interp_mixed (rec: ty_interpO) : interp :=
 λ (v: value), (interp_nonnull rec v ∨ interp_null v)%I.

(* we use a blend of Coq/Iris recursion, the
   Coq recursion lets us handle simple structural
   cases, and we use Iris' recursion to deal with
   the more complicated case of class types *)
Definition interp_type_pre (rec : ty_interpO) : ty_interpO :=
  λ (typ : lang_ty),
    (fix go (typ : lang_ty) : interp :=
       match typ with
       | IntT => interp_int
       | BoolT => interp_bool
       | NothingT => interp_nothing
       | MixedT => interp_mixed rec
       | ClassT t => interp_class t rec
       | NullT => interp_null
       | NonNullT => interp_nonnull rec
       | UnionT A B => interp_union (go A) (go B)
       | InterT A B => interp_inter (go A) (go B)
       end) typ.

(* we cannot use solve_contractive out of the box because of
 * the 'fix' combinator above
 *)
Local Instance interp_type_pre_contractive:
  Contractive (interp_type_pre).
Proof.
move => n i1 i2 hdist.
move => ty.
elim : ty; intros => //=;
    [ (* mixed *)| (*class*) | (*nonnull*) 
    | solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv])
    | solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv])
    ].
    (* TODO: factor out interp class and interp nonnull *)
- move => v; rewrite /interp_mixed.
  f_equiv.
  rewrite /interp_nonnull.
  f_equiv.
  f_equiv.
  f_equiv.
  f_equiv.
  (* interp class *)
  rewrite /interp_class.
  do 3 (f_equiv; intro).
  do 4 f_equiv.
  rewrite /interp_tys_next /interp_ty_next.
  apply gmap_fmap_ne_ext => k ty hin.
  f_contractive.
  by destruct n.
- move => v; rewrite /interp_class.
  do 3 (f_equiv; intro).
  do 4 f_equiv.
  rewrite /interp_tys_next /interp_ty_next.
  apply gmap_fmap_ne_ext => k ty hin.
  f_contractive.
  by destruct n.
- move => v; rewrite /interp_nonnull.
  f_equiv.
  f_equiv.
  f_equiv.
  f_equiv.
  (* interp class *)
  rewrite /interp_class.
  do 3 (f_equiv; intro).
  do 4 f_equiv.
  rewrite /interp_tys_next /interp_ty_next.
  apply gmap_fmap_ne_ext => k ty hin.
  f_contractive.
  by destruct n.
Qed.

(* the interpretation of types can now be
   defined as a fixpoint (because class types
   can be (mutually) recursive) *)
Definition interp_type := fixpoint interp_type_pre.

Lemma interp_type_unfold (ty : lang_ty) (v : value) :
  interp_type ty v ⊣⊢ interp_type_pre interp_type ty v.
Proof.
  rewrite {1}/interp_type.
  apply (fixpoint_unfold interp_type_pre ty v).
Qed.

(* #hyp *)
Global Instance interp_type_persistent : ∀ t v, Persistent (interp_type t v).
Proof.
  elim => [ | | | | cname | | |s hs t ht | s hs t ht] v;
      rewrite interp_type_unfold //=; try by apply _.
  - rewrite /interp_union.
    by apply bi.or_persistent; rewrite -!interp_type_unfold.
  - rewrite /interp_union.
    by apply bi.and_persistent; rewrite -!interp_type_unfold.
Qed.

Lemma dom_interp_tys_next fields:
  dom stringset (interp_tys_next interp_type fields) ≡ dom _ fields.
Proof. by rewrite /interp_tys_next /interp_ty_next dom_fmap. Qed.

(* Derived rules *)
Lemma subtype_union_comm : ∀ A B, (UnionT A B) <: (UnionT B A).
Proof.
by auto.
Qed.

Lemma subtype_inter_comm : ∀ A B, (InterT A B) <: (InterT B A).
Proof.
by auto.
Qed.

Lemma subtype_union_assoc:
  ∀ A B C, (UnionT (UnionT A B) C) <: (UnionT A (UnionT B C)).
Proof.
by eauto.
Qed.

Lemma subtype_inter_assoc:
  ∀ A B C, (InterT (InterT A B) C) <: (InterT A (InterT B C)).
Proof.
by eauto.
Qed.


(* A <: B → ΦA ⊂ ΦB *)
Theorem subtype_is_inclusion_aux:
  ∀ A B, A <: B →
  ∀ v,
  interp_type_pre interp_type A v -∗
  interp_type_pre interp_type B v.
Proof.
induction 1 as [A | A B hext | | | | A | A B| A B | A B C h0 hi0 h1 hi1
  | A B | A B | A B C h0 hi0 h1 hi1 | A | A B C h0 hi0 h1 hi1 ];
      move => v /=.
- rewrite /interp_mixed.
  elim: A v => /=.
  + move => v; iIntros "h"; by repeat iLeft.
  + move => v; iIntros "h"; by iLeft; iRight; iLeft.
  + move => v; by rewrite /interp_nothing; iIntros "h".
  + done.
  + rewrite /interp_class => v cname.
    iIntros "h".
    iDestruct "h" as (ℓ t fields) "[%h0 h1]".
    destruct h0 as [-> [hext hfields]].
    iLeft.
    iRight.
    iRight.
    by iExists t, _, _, _; iFrame.
  + move => v; iIntros "h"; by iRight.
  + move => v; by iIntros "h"; iLeft.
  + move => s hs t ht v.
    rewrite /interp_union.
    iIntros "h".
    iDestruct "h" as "[ h | h ]"; first by iApply hs.
    by iApply ht.
  + move => s hs t ht v.
    rewrite /interp_inter.
    iIntros "h".
    iDestruct "h" as "[? _]"; by iApply hs.
- rewrite /interp_class.
  iIntros "h".
  iDestruct "h" as (ℓ t fields) "[%h hsem]".
  destruct h as [-> [hext2 hfields ]].
  iExists ℓ, t, fields.
  iSplit.
  { iPureIntro; split; first by done.
    split; last done.
    by eapply rtc_transitive.
  }
  by iFrame.
- by rewrite /= /interp_mixed.
- iIntros "h"; by iLeft.
- iIntros "h"; by iRight; iLeft.
- rewrite /interp_class.
  iIntros "h"; iRight; iRight.
  iDestruct "h" as (ℓ t fields) "[%h0 h1]".
  destruct h0 as [-> [hext hfields]].
  by iExists t, _, _, _; iFrame.
- rewrite /interp_union.
  by iIntros "h"; iLeft.
- rewrite /interp_union.
  by iIntros "h"; iRight.
- rewrite /interp_union.
  iIntros "[h | h]"; first by iApply hi0.
  by iApply hi1.
- rewrite /interp_inter.
  by iIntros "[? _]".
- rewrite /interp_inter.
  by iIntros "[_ ?]".
- rewrite /interp_inter.
  iIntros "h".
  iSplit; first by iApply hi0.
  by iApply hi1.
- done.
- iIntros "h".
  iApply hi1.
  by iApply hi0.
Qed.

Theorem subtype_is_inclusion:
  ∀ A B, A <: B →
  ∀ v, interp_type A v -∗ interp_type B v.
Proof.
  move => A B hAB v.
  rewrite !interp_type_unfold.
  by iApply subtype_is_inclusion_aux.
Qed.

Corollary inherits_is_inclusion:
  ∀ A B, inherits A B →
  ∀ v, interp_class A interp_type v -∗ interp_class B interp_type v.
Proof.
  move => A B hAB v; iIntros "h".
  iDestruct (subtype_is_inclusion (ClassT A) (ClassT B)) as "H"; first by eauto.
  rewrite !interp_type_unfold /=.
  by iApply "H".
Qed.

(* language statics & semantics *)

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
  | GetTy: ∀ lty lhs recv t name fty,
      expr_has_ty lty recv (ClassT t) →
      has_field name fty t →
      cmd_has_ty lty (GetC lhs recv name) (<[lhs := fty]>lty)
  | SetTy: ∀ lty recv fld rhs fty t,
      expr_has_ty lty recv (ClassT t) →
      expr_has_ty lty rhs fty →
      has_field fld fty t →
      cmd_has_ty lty (SetC recv fld rhs) lty
  | NewTy: ∀ lty lhs t args fields,
      has_fields t fields →
      dom (gset string) fields = dom _ args →
      (∀ f fty arg,
        fields !! f = Some fty →
        args !! f = Some arg →
        expr_has_ty lty arg fty) →
      cmd_has_ty lty (NewC lhs t args) (<[ lhs := ClassT t]>lty)
  | CallTy: ∀ lty lhs recv t name mdef args,
      expr_has_ty lty recv (ClassT t) →
      has_method name mdef t →
      dom (gset string) mdef.(methodargs) = dom _ args →
      (∀ x ty arg,
        mdef.(methodargs) !! x = Some ty →
        args !! x = Some arg →
        expr_has_ty lty arg ty) →
      cmd_has_ty lty (CallC lhs recv name args) (<[lhs := mdef.(methodrettype)]>lty)
  | WeakenTy: ∀ lty c rty' rty,
      rty ⊆ rty' →
      cmd_has_ty lty c rty' →
      cmd_has_ty lty c rty
  | SubTy: ∀ lty c rty' rty,
      dom stringset rty' = dom _ rty →
      (∀ k A B, rty' !! k = Some A → rty !! k = Some B →  A <: B) →
      cmd_has_ty lty c rty' →
      cmd_has_ty lty c rty
  | CondTagTy lty v tv t cmd :
      lty !! v = Some tv →
      cmd_has_ty (<[v:=InterT tv (ClassT t)]> lty) cmd lty →
      cmd_has_ty lty (CondTagC v t cmd) lty
.

Corollary CallTy_: ∀ lty lhs recv t name mdef args,
      expr_has_ty lty recv (ClassT t) →
      has_method name mdef t →
      dom (gset string) mdef.(methodargs) = dom _ args →
      (∀ x ty arg,
        mdef.(methodargs) !! x = Some ty →
        args !! x = Some arg →
        ∃ ty', ty' <: ty ∧ expr_has_ty lty arg ty') →
      cmd_has_ty lty (CallC lhs recv name args) (<[lhs := mdef.(methodrettype)]>lty).
Proof.
  move => lty lhs recv t name mdef args hrecv hmdef hdom hargs.
  econstructor; [done | done | done | ].
  move => k ty arg hk ha.
  destruct (hargs _ _ _ hk ha) as (ty' & hsub & he).
  by econstructor.
Qed.

Lemma CallTyGen: ∀ lty lhs recv t name mdef args ret,
      expr_has_ty lty recv (ClassT t) →
      has_method name mdef t →
      dom (gset string) mdef.(methodargs) = dom _ args →
      (∀ x ty arg,
        mdef.(methodargs) !! x = Some ty →
        args !! x = Some arg →
        ∃ ty', ty' <: ty ∧ expr_has_ty lty arg ty') →
      mdef.(methodrettype) <: ret →
      cmd_has_ty lty (CallC lhs recv name args) (<[lhs := ret]>lty).
Proof.
  move =>lty lhs ????? ret hrecv hm hdom hargs hret.
  eapply SubTy; last by eapply CallTy_.
  { by rewrite !dom_insert_L. }
  move => k A B hin.
  rewrite lookup_insert_Some in hin.
  destruct hin as [[<- <-] | [hne heq]].
  - rewrite lookup_insert.
    by case => <-.
  - rewrite lookup_insert_ne //.
    move => h; rewrite h in heq.
    by case: heq => ->.
Qed.

Definition wf_mdef_ty t mdef :=
  ∃ lty,
  cmd_has_ty (<["$this" := ClassT t]>mdef.(methodargs)) mdef.(methodbody) lty ∧
  expr_has_ty lty mdef.(methodret) mdef.(methodrettype)
.

Record wf_cdefs (prog: stringmap classDef)  := {
  wf_fields : map_Forall (fun cname => wf_cdef_fields) prog;
  wf_methods : map_Forall (fun cname => wf_cdef_methods) prog;
  wf_mdefs :
  map_Forall (fun cname cdef =>
    map_Forall (fun mname mdef => wf_mdef_ty cname mdef) cdef.(classmethods)) prog
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

Definition map_args {A B: Type} (f: A → option  B) (m: stringmap A) : option (stringmap B) :=
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
  rewrite /map_args => A B f k a m n h/=.
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
      cmd_eval (le, h) (LetC v e) (<[v:=val]> le, h) 0
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

(* heap models relation; the semantic heap does
   not appear because it is hidden in iProp  *)
(* Helper defintion to state that fields are correctly modeled *)
Definition heap_models_fields
  (iFs: gmapO string (laterO (sem_typeO Σ))) (vs: stringmap value) : iProp :=
  ⌜dom (gset string) vs ≡ dom _ iFs⌝ ∗
  ∀ f (iF: interp),
  iFs !! f ≡ Some (Next iF) -∗ ∃ v, (⌜vs !! f = Some v⌝ ∗ ▷iF v).

Lemma heap_models_fields_ext_L: ∀ iFs iFs' vs,
  iFs ≡ iFs' -∗ heap_models_fields iFs vs -∗ heap_models_fields iFs' vs.
Proof.
  move => iFs iFs' vs.
  iIntros "heq h".
  rewrite /heap_models_fields.
  iDestruct "h" as "[%hdom h]".
  iSplit.
  { rewrite gmap_equivI.
    fold_leibniz.
    rewrite set_eq hdom.
    iIntros (s).
    rewrite !elem_of_dom.
    by iRewrite ("heq" $! s).
  }
  iIntros (f iF) "hiF".
  iApply "h".
  by iRewrite "heq".
Qed.

Definition heap_models (h : heap) : iProp :=
  ∃ (sh: gmap loc (prodO tagO (gmapO string (laterO (sem_typeO Σ))))),
    own γ (gmap_view_auth (DfracOwn 1) sh) ∗ ⌜dom (gset loc) sh = dom _ h⌝ ∗
    □ ∀ (ℓ : loc) (t : tag) (vs : stringmap value),
      ⌜h !! ℓ = Some (t, vs)⌝ -∗
        ∃ (iFs : gmapO string (laterO (sem_typeO Σ))),
        sh !! ℓ ≡ Some (t, iFs) ∗ heap_models_fields iFs vs.

Definition interp_local_tys
  (lty : local_tys) (le : local_env) : iProp :=
  (∀ v ty, ⌜lty !! v = Some ty⌝ -∗
           ∃ val, ⌜le !! v = Some val⌝ ∗ interp_type ty val)%I.

Lemma expr_adequacy e lty le ty val :
  expr_eval le e = Some val →
  expr_has_ty lty e ty →
  interp_local_tys lty le -∗
  interp_type ty val.
Proof.
  move => he h; move: le val he.
  elim: h => [z | b | | op e1 e2 hop he1 hi1 he2 hi2 |
      op e1 e2 hop he1 hi1 he2 hi2 |
      v vty hv | exp S T hS hi hsub ] le val he; iIntros "#Hlty".
  - inv he; rewrite interp_type_unfold /=; by eauto.
  - inv he; rewrite interp_type_unfold /=; by eauto.
  - inv he; rewrite interp_type_unfold /=; by eauto.
  - inv he.
    case heq1 : (expr_eval le e1) => [v1 | ]; rewrite heq1 in H0; last by done.
    apply hi1 in heq1.
    iDestruct (heq1 with "Hlty") as "hv1".
    rewrite interp_type_unfold /=.
    iDestruct "hv1" as (z1) "%hz1".
    rewrite hz1 in H0.
    case heq2 : (expr_eval le e2) => [v2 | ]; rewrite heq2 in H0; last by done.
    apply hi2 in heq2.
    iDestruct (heq2 with "Hlty") as "hv2".
    rewrite interp_type_unfold /=.
    iDestruct "hv2" as (z2) "%hz2".
    rewrite hz2 in H0.
    case: H0 => <-.
    rewrite interp_type_unfold /= /interp_int.
    move: hop; rewrite /is_bool_op; destruct op => //= _; by iExists _.
  - inv he.
    case heq1 : (expr_eval le e1) => [v1 | ]; rewrite heq1 in H0; last by done.
    apply hi1 in heq1.
    iDestruct (heq1 with "Hlty") as "hv1".
    rewrite interp_type_unfold /=.
    iDestruct "hv1" as (z1) "%hz1".
    rewrite hz1 in H0.
    case heq2 : (expr_eval le e2) => [v2 | ]; rewrite heq2 in H0; last by done.
    apply hi2 in heq2.
    iDestruct (heq2 with "Hlty") as "hv2".
    rewrite interp_type_unfold /=.
    iDestruct "hv2" as (z2) "%hz2".
    rewrite hz2 in H0.
    case: H0 => <-.
    rewrite interp_type_unfold /= /interp_bool.
    move: hop; rewrite /is_bool_op; destruct op => //= _; by iExists _.
  - inv he.
    iDestruct ("Hlty" with "[//]") as (?) "[% H]".
    rewrite H0 in H; by case: H => ->.
  - apply hi in he.
    iApply subtype_is_inclusion; first by apply hsub.
    by iApply he.
Qed.

Lemma interp_local_tys_update v lty le ty val :
  interp_local_tys lty le -∗
  interp_type ty val -∗
  interp_local_tys (<[v:=ty]>lty) (<[v:=val]>le).
Proof.
  iIntros "#Hi #?". iIntros (v' ty') "H".
  rewrite lookup_insert_Some.
  iDestruct "H" as %[[<- <-]|[??]].
  - iExists _. rewrite lookup_insert. by iSplit.
  - rewrite lookup_insert_ne; last done. by iApply "Hi".
Qed.

Lemma interp_local_tys_weaken_ty v A B lty lty' le:
  lty !! v = Some A →
  lty' !! v = Some B →
  (∀ w, v ≠ w → lty !! w = lty' !! w) →
  A <: B →
  interp_local_tys lty le -∗
  interp_local_tys lty' le.
Proof.
  move => hin1 hin2 hs hAB; iIntros "H".
  rewrite /interp_local_tys.
  iIntros (w ty) "%Hin".
  destruct (decide (v = w)) as [<- | hne].
  - rewrite hin2 in Hin; case: Hin => <-.
    iSpecialize ("H" $! v A).
    iDestruct ("H" with "[//]") as (val) "[%Hin #h]".
    iExists val; iSplitR; first done.
    by iApply subtype_is_inclusion.
  - iSpecialize ("H" $! w ty).
    rewrite -hs in Hin => //.
    iDestruct ("H" with "[//]") as (val) "[%Hin' #h]".
    iExists val; by iSplitR.
Qed.

Lemma interp_local_tys_subset_eq lty lty' le:
  lty' ⊆ lty →
  interp_local_tys lty le -∗
  interp_local_tys lty' le.
Proof.
  move => hs; iIntros "H" (w ty) "%Hle".
  iSpecialize ("H" $! w ty).
  rewrite (@lookup_weaken _ _ _ _ _ _ w ty Hle hs).
  iDestruct ("H" with "[//]") as (val) "[%hw H]".
  iExists val.
  by rewrite hw; iSplit.
Qed.

Lemma interp_local_tys_list lty le targs args vargs:
  dom stringset targs = dom stringset args →
  map_args (expr_eval le) args = Some vargs →
  (∀ (x : string) (ty : lang_ty) (arg : expr),
       targs !! x = Some ty →
       args !! x = Some arg →
       expr_has_ty lty arg ty) →
  interp_local_tys lty le -∗
  interp_local_tys targs vargs.
Proof.
  move => hdom hargs helt.
  iIntros "#Hle" (v ty) "%hin".
  assert (ha: ∃ arg, args !! v = Some arg).
  { apply elem_of_dom.
    rewrite -hdom.
    apply elem_of_dom.
    now rewrite hin.
  }
  destruct ha as [arg harg].
  apply helt with v ty arg in hin; last done.
  assert (hv: ∃ varg, vargs !! v = Some varg).
  { apply elem_of_dom.
    apply dom_map_args in hargs.
    rewrite hargs.
    apply elem_of_dom.
    now rewrite harg.
  }
  destruct hv as [varg hvarg].
  iExists varg; rewrite hvarg; iSplitR; first done.
  rewrite (map_args_lookup _ _ _ args vargs hargs v) harg /= in hvarg.
  by iApply expr_adequacy.
Qed.

Lemma heap_models_lookup l h A vs t :
  h !! l = Some (t, vs) →
  heap_models h -∗
  interp_type (ClassT A) (LocV l) -∗
  ∃ fields, heap_models h ∗
    ⌜inherits t A ∧ has_fields t fields⌝ ∗
    ∀ f fty, ⌜fields !! f = Some fty⌝ → 
    ∃ v, ⌜vs !! f = Some v⌝ ∗
    ▷ interp_type fty v.
Proof.
  move => hheap.
  iIntros "hmodels hl".
  rewrite interp_type_unfold /= /interp_class.
  iDestruct "hl" as (???) "[%H H◯]".
  destruct H as [[= <-] [hinherits hf]].
  iDestruct "hmodels" as (sh) "(H● & % & #Hh)".
  iDestruct (own_valid_2 with "H● H◯") as "#Hv".
  rewrite gmap_view_both_validI.
  iDestruct "Hv" as "[_ HΦ]".
  iDestruct ("Hh" with "[//]") as (?) "[H H▷]".
  iRewrite "H" in "HΦ".
  rewrite option_equivI prod_equivI /=.
  iDestruct "HΦ" as "[-> HΦ]".
  iExists fields.
  iSplitL. { iExists _. iFrame. by iSplit. }
  iSplitR; first by rewrite H0.
  iIntros (f fty) "%hfield".
  iDestruct "H▷" as "[%hdf h]".
  rewrite gmap_equivI.
  iSpecialize ("HΦ" $! f).
  rewrite /interp_tys_next /interp_ty_next lookup_fmap hfield /=.
  iAssert (⌜is_Some (iFs !! f)⌝)%I as "%hiFs".
  { destruct (iFs !! f) eqn:hh; first done.
    by rewrite hh option_equivI.
  }
  destruct hiFs as [[iF] hIF].
  iDestruct ("h" $! f iF with "[]") as (v) "[%hv hl]"; first by rewrite hIF.
  iExists v; iSplitR; first done.
  rewrite hIF option_equivI later_equivI discrete_fun_equivI.
  iNext.
  iSpecialize ("HΦ" $! v).
  by iRewrite -"HΦ".
Qed.

Lemma heap_models_class l h A vs t :
  h !! l = Some (t, vs) →
  heap_models h -∗
  interp_type (ClassT A) (LocV l) -∗
  heap_models h ∗ interp_type (ClassT t) (LocV l).
Proof.
  move => hheap.
  iIntros "hmodels hl".
  rewrite !interp_type_unfold /= /interp_class.
  iDestruct "hl" as (???) "[%H #H◯]".
  destruct H as [[= <-] [hinherits hf]].
  iDestruct "hmodels" as (sh) "(H● & % & #Hh)".
  iDestruct (own_valid_2 with "H● H◯") as "#Hv".
  rewrite gmap_view_both_validI.
  iDestruct "Hv" as "[_ HΦ]".
  iDestruct ("Hh" with "[//]") as (?) "[H H▷]".
  iRewrite "H" in "HΦ".
  rewrite option_equivI prod_equivI /=.
  iDestruct "HΦ" as "[-> HΦ]".
  fold_leibniz; rewrite H0.
  iSplitL.
  { iExists _; iFrame; by iSplit. }
  iExists l, t0, fields; by iSplitR.
Qed.

Lemma heap_models_fields_update iFs vs f v (Φ : interpO)
  `{∀ v, Persistent (Φ v)} :
  iFs !! f = Some (Next Φ) →
  heap_models_fields iFs vs -∗
  Φ v -∗
  heap_models_fields iFs (<[ f := v]>vs).
Proof.
  move => hf.
  iIntros "hm hΦ".
  iDestruct "hm" as "[%hdom h]".
  rewrite /heap_models_fields.
  iSplitR.
  { iPureIntro.
    rewrite dom_insert_lookup //.
    by rewrite -elem_of_dom hdom elem_of_dom hf.
  }
  iIntros (f' iF) "hf".
  destruct (decide (f = f')) as [-> | hne].
  - rewrite lookup_insert.
    iExists v; iSplitR; first done.
    rewrite hf option_equivI later_equivI discrete_fun_equivI.
    iNext.
    iSpecialize ("hf" $! v).
    by iRewrite -"hf".
  - rewrite lookup_insert_ne //.
    by iApply "h".
Qed.

Lemma heap_models_update h l t t0 vs f v fty:
  wf_cdefs Δ →
  h !! l = Some (t, vs) →
  has_field f fty t0 →
  inherits t t0 →
  heap_models h -∗
  interp_type (ClassT t0) (LocV l) -∗
  interp_type fty v -∗
  heap_models (<[l:=(t, (<[f := v]>vs))]> h).
Proof.
  move => wfΔ hheap hf hinherits.
  iIntros "hmodels #hl #hv".
  iDestruct "hmodels" as (sh) "[hown [%hdom #h]]".
  iExists sh.
  rewrite interp_type_unfold /= /interp_class.
  iDestruct "hl" as (?? fields) "[%H hsem]".
  destruct H as [[= <-] [ hinherits' hfields]].
  iDestruct (own_valid_2 with "hown hsem") as "#Hv".
  rewrite gmap_view_both_validI.
  iDestruct "Hv" as "[_ Hv]".
  iSplitL; first by iFrame.
  iSplitR.
  { iPureIntro.
    by rewrite hdom dom_insert_lookup_L.
  }
  iModIntro.
  iIntros (ℓ t' vs') "%Heq".
  destruct (decide (l = ℓ)) as [-> | hne].
  - rewrite lookup_insert in Heq.
    injection Heq; intros <- <-; clear Heq.
    iAssert (t1 ≡ t)%I as "%Ht".
    { iSpecialize ("h" $! ℓ t vs with "[//]").
      iDestruct "h" as (iFs) "[hsh hmodels]".
      iRewrite "Hv" in "hsh".
      rewrite !option_equivI prod_equivI /=.
      by iDestruct "hsh" as "[? ?]".
    }
    iExists _; iSplitR.
    { rewrite Ht.
      by iRewrite "Hv".
    }
    iApply heap_models_fields_update; first by apply interp_type_persistent.
    + rewrite /interp_tys_next /interp_ty_next lookup_fmap.
      destruct (hfields f fty) as [h0 h1].
      rewrite h0; first by done.
      apply has_field_inherits with t0 => //.
      now apply wfΔ.
    + iSpecialize ("h" $! ℓ t vs with "[//]").
      iDestruct "h" as (iFs) "[hsh hmodels]".
      iRewrite "Hv" in "hsh".
      rewrite !option_equivI prod_equivI /=.
      iDestruct "hsh" as "[? h]".
      iApply heap_models_fields_ext_L; first by iRewrite "h".
      done.
    + done.
  - iApply "h".
    iPureIntro.
    by rewrite lookup_insert_ne // in Heq.
Qed.

Notation "|=▷^ n Q" := (Nat.iter n (λ P, |==> ▷ P) Q)%I
  (at level 99, n at level 9, Q at level 200,
   format "|=▷^ n  Q") : bi_scope.

Lemma updN_zero (Q : iProp) : (|=▷^0 Q) ⊣⊢ Q.
Proof. done. Qed.

Lemma updN_S n (Q : iProp) :
  (|=▷^(S n) Q) ⊣⊢ |==> ▷ |=▷^n Q.
Proof. done. Qed.

Lemma updN_mono n (P Q : iProp) :
  (P -∗ Q) → (|=▷^n P) -∗ (|=▷^n Q).
Proof.
  elim: n => [//|n HI H /=].
  iApply bupd_mono.
  iApply bi.later_mono.
  by iApply HI.
Qed.

Lemma updN_mono_I n (P Q : iProp) :
  (P -∗ Q) -∗ (|=▷^n P) -∗ (|=▷^n Q).
Proof.
  elim: n => [|n hi]; first done.
  iIntros "H".
  rewrite !updN_S.
  iIntros "HH".
  iMod "HH".
  iModIntro.
  iNext.
  by iApply (hi with "H").
Qed.

Lemma updN_intro n (P: iProp) : P -∗ (|=▷^n P).
Proof.
  elim: n => [// | n hi /=].
  iIntros "p".
  iApply bupd_intro.
  apply bi.later_mono in hi.
  by iApply hi.
Qed.

Lemma updN_sep n (P R: iProp) : ((|=▷^n P) ∗ (|=▷^n R)) -∗ |=▷^n (P ∗ R).
Proof.
  elim: n => [// | n hi /=].
  iIntros "[H0 H1]".
  iMod "H0".
  iMod "H1".
  iModIntro.
  iNext.
  iApply hi.
  by iSplitL "H0".
Qed.

Lemma updN_frame_r n (P R: iProp) : (|=▷^n P) ∗ R -∗ |=▷^n P ∗ R.
Proof.
  elim: n => [// | n hi /=].
  iIntros "[H HR]".
  iMod "H"; iModIntro.
  iNext.
  iApply hi.
  by iSplitL "H".
Qed.

Lemma updN_plus n1 (P: iProp) : ∀ n2,
  (|=▷^n1 P) -∗ (|=▷^(n1 + n2) P).
Proof.
  elim:n1 => [ | n1 hi] /= => n2; iIntros "h1"; first by iApply updN_intro.
  iMod "h1".
  iModIntro.
  iNext.
  by iApply hi.
Qed.


Lemma interp_type_loc_inversion h le lty (v: string) l T t fields:
    h !! l = Some (t, fields) →
    le !! v = Some (LocV l) →
    interp_local_tys lty le -∗
    heap_models h -∗
    interp_type T (LocV l) -∗
    heap_models h ∗ interp_type (ClassT t) (LocV l).
Proof.
  rewrite interp_type_unfold => hl hv;  elim: T v hv => /=.
  - move => ??; iIntros "? ? H".
    iDestruct "H" as (z) "%H"; discriminate.
  - move => ??; iIntros "? ? H".
    iDestruct "H" as (b) "%H"; discriminate.
  - move => ??; iIntros "? ? H".
    iDestruct "H" as "%H"; by elim H.
  - move => v hv; iIntros "#Hs Hh H".
    iDestruct "H" as "[H | H]"; last first.
    { iDestruct "H" as "%H"; discriminate. }
    (* start of nonnull as part of mixed. TODO: factor outTODO: factor out class/nonnull *)
    iDestruct "H" as "[H | H]".
    { iDestruct "H" as (z) "%H"; discriminate. }
    iDestruct "H" as "[H | H]".
    { iDestruct "H" as (b) "%H"; discriminate. }
    iDestruct "H" as (cname) "H".
    iDestruct ((heap_models_class _ _ cname _ _ hl) with "[Hh //]") as "Hv".
    iApply "Hv".
    by rewrite interp_type_unfold.
  - move => cname v hv; iIntros "Hs Hh H".
    iDestruct ((heap_models_class _ _ cname _ _ hl) with "[Hh //]") as "Hv".
    iApply "Hv".
    by rewrite interp_type_unfold.
  - move => ??; iIntros "? ? H".
    iDestruct "H" as "%H"; discriminate.
  - move => v hv; iIntros "#Hs Hh H".
    iDestruct "H" as "[H | H]".
    { iDestruct "H" as (z) "%H"; discriminate. }
    iDestruct "H" as "[H | H]".
    { iDestruct "H" as (b) "%H"; discriminate. }
    iDestruct "H" as (cname) "H".
    iDestruct ((heap_models_class _ _ cname _ _ hl) with "[Hh //]") as "Hv".
    iApply "Hv".
    by rewrite interp_type_unfold.
  - move => S hS T hT v hv; iIntros "#Hs Hh H".
    iDestruct "H" as "[H | H]".
    + apply hS in hv.
      by iApply (hv with "Hs Hh H").
    + apply hT in hv.
      by iApply (hv with "Hs Hh H").
  - move => S hS T hT v hv; iIntros "#Hs Hh H".
    rewrite /interp_inter -!interp_type_unfold.
    iDestruct "H" as "[HS HT]".
    apply hS in hv.
    rewrite -!interp_type_unfold in hv.
    by iApply (hv with "Hs Hh HS").
Qed.

Lemma cmd_adequacy_ lty cmd lty' :
  wf_cdefs Δ →
  ⌜cmd_has_ty lty cmd lty'⌝ -∗
   ∀ st st' n, ⌜cmd_eval st cmd st' n⌝ -∗
   heap_models st.2 ∗ interp_local_tys lty st.1 -∗ |=▷^n
   heap_models st'.2 ∗ interp_local_tys lty' st'.1.
Proof.
  move => wfΔ.
  iLöb as "IH" forall (lty cmd lty').
  iIntros "%hty" (st st' n) "%hc".
  move: st st' n hc.
  induction hty as [ lty | lty1 lty2 lty3 fstc sndc hfst hi1 hsnd hi2 |
      lty lhs e ty he | lty1 lty2 cond thn els hcond hthn hi1 hels hi2 |
      lty lhs recv t name fty hrecv hf |
      lty recv fld rhs fty t hrecv hrhs hf |
      lty lhs t args fields hf hdom harg |
      lty lhs recv t name mdef args hrecv hm hdom |
      lty c rty' rty hsubset h hi |
		  lty c rty' rty hdom hsub h hi |
      lty v tv t cmd hv h hi
      ] => st st' n hc.
  - inv hc.
    rewrite updN_zero.
    by iIntros "?".
  - inv hc.
    apply hi1 in H2; clear hi1.
    apply hi2 in H5; clear hi2.
    iIntros "H".
    iAssert(
     heap_models st.2 ∗ interp_local_tys lty1 st.1 -∗
     |=▷^n1 heap_models st2.2 ∗ interp_local_tys lty2 st2.1
     )%I as "H1"; first by apply H2.
    clear H2.
    iSpecialize ("H1" with "H").
    iAssert(
     heap_models st2.2 ∗ interp_local_tys lty2 st2.1 -∗
     |=▷^n2 heap_models st'.2 ∗ interp_local_tys lty3 st'.1
     )%I as "H2"; first by apply H5.
    clear H5.
    iAssert (
        (|=▷^n1 (heap_models st2.2 ∗ interp_local_tys lty2 st2.1)) -∗
        |=▷^n1 (|=▷^n2 heap_models st'.2 ∗ interp_local_tys lty3 st'.1)
        )%I as "H2'"; first by iApply updN_mono_I.
    rewrite Nat_iter_add.
    by iApply "H2'".
  - inv hc.
    iIntros "[? #Hle]".
    rewrite updN_zero. iFrame.
    iDestruct (expr_adequacy with "Hle") as "#?"; try done.
    by iApply interp_local_tys_update.
  - iIntros "H".
    inv hc.
    + apply hi1 in H6; clear hi1 hi2.
      iAssert (
     heap_models st.2 ∗ interp_local_tys lty1 st.1 -∗
     |=▷^n heap_models st'.2 ∗ interp_local_tys lty2 st'.1
     )%I as "H1"; first by apply H6.
     clear H6.
     by iApply "H1".
    + apply hi2 in H6; clear hi1 hi2.
      iAssert (
     heap_models st.2 ∗ interp_local_tys lty1 st.1 -∗
     |=▷^n heap_models st'.2 ∗ interp_local_tys lty2 st'.1
     )%I as "H1"; first by apply H6.
     clear H6.
     by iApply "H1".
  - inv hc.
    iIntros "[Hh #Hle]". simpl.
    iModIntro. (* keep the later *)
    iDestruct (expr_adequacy with "Hle") as "#He"; try done.
    iDestruct (heap_models_lookup with "Hh He") as (fields) "(Hh&Ht&Hv)"; first done.
    iDestruct "Ht" as %[? ?].
    rewrite bi.later_sep.
    iSplitL "Hh"; first done.
    assert (hfield: fields !! name = Some fty).
    { apply has_fields_inherits_lookup with t0 t => //.
      by apply wfΔ.
    }
    iDestruct ("Hv" $! name fty hfield) as (w) "[%hw hi]".
    rewrite H7 in hw; case: hw => ->.
    iNext. by iApply interp_local_tys_update.
  - inv hc.
    iIntros "[Hh #Hle]" => /=.
    iSplitL; last done.
    iDestruct (expr_adequacy recv with "Hle") as "#Hrecv" => //.
    iDestruct (expr_adequacy rhs with "Hle") as "#Hrhs" => //.
    iDestruct (heap_models_lookup with "Hh Hrecv") as (fields) "(Hh&Ht&?)"; first done.
    iDestruct "Ht" as %[? ?].
    by iApply (heap_models_update with "Hh").
  - inv hc; simpl.
    iIntros "[Hh #Hle]".
    (* we need one modality to update the
       semantic heap *)
    iDestruct "Hh" as (sh) "(H●&Hdom&#Hh)".
    iDestruct "Hdom" as %Hdom.
    iMod (own_update with "H●") as "[H● H◯]".
    { apply (gmap_view_alloc _ new DfracDiscarded
        (t, interp_tys_next interp_type fields)); last done.
      apply (not_elem_of_dom (D:=gset loc)).
      by rewrite Hdom not_elem_of_dom. }
    iIntros "!> !>". iDestruct "H◯" as "#H◯".
    iAssert (interp_type (ClassT t) (LocV new))
      with "[]" as "#Hl".
    { rewrite interp_type_unfold /=.
      iExists _, _, _. by iSplit. }
    iSplitL; last first.
    by iApply interp_local_tys_update.
    iExists _. iFrame. iSplit; first by rewrite !dom_insert_L Hdom.
    iModIntro. iIntros (???) "Hlook".
    rewrite lookup_insert_Some.
    iDestruct "Hlook" as %[[<- [= <- <-]]|[Hℓ Hlook]].
    + iExists _. rewrite lookup_insert.
      iSplitR; first done.
      rewrite /heap_models_fields.
      iSplitR.
      { 
        apply dom_map_args in H6.
        by rewrite dom_interp_tys_next H6 -hdom.
      }
      iIntros (f iF) "hiF".
      iAssert (⌜f ∈ dom stringset fields⌝)%I as "%hfield".
      {
        rewrite -dom_interp_tys_next elem_of_dom.
        rewrite /interp_tys_next /interp_ty_next.
        rewrite !lookup_fmap.
        by iRewrite "hiF".
      }
      assert (h0: is_Some (args !! f)).
      {
        apply elem_of_dom.
        by rewrite -hdom.
      }
      destruct h0 as [a0 ha0].
      assert (h1: is_Some (vargs !! f)).
      {
        apply elem_of_dom.
        apply dom_map_args in H6.
        by rewrite H6 -hdom.
      }
      destruct h1 as [v0 hv0].
      assert (h2: is_Some (fields !! f)) by (by apply elem_of_dom).
      destruct h2 as [fty hty].
      iExists v0; iSplitR; first done.
      rewrite /interp_tys_next /interp_ty_next lookup_fmap.
      assert (heval0: expr_eval le a0 = Some v0).
      { rewrite (map_args_lookup _ _ _ args vargs H6 f) in hv0.
        by rewrite ha0 in hv0.
      }
      assert (hty0: expr_has_ty lty a0 fty) by (by apply harg with f).
      rewrite hty /= option_equivI later_equivI.
      iNext.
      rewrite discrete_fun_equivI.
      iSpecialize ("hiF" $! v0).
      iRewrite -"hiF".
      by iDestruct (expr_adequacy a0 with "Hle") as "#Ha0".
    + rewrite lookup_insert_ne; last done.
      by iApply "Hh".
  - iIntros "[Hh #Hle]".
    inv hc; simpl in *.
    assert (wfbody: ∃B, wf_mdef_ty B mdef0 ∧ inherits t0 B).
    { destruct wfΔ as [? ? hbodies].
      rewrite map_Forall_lookup in hbodies.
      apply has_method_from in H8.
      destruct H8 as (B & cdef & hB & heq & hin).
      apply hbodies in hB.
      rewrite map_Forall_lookup in hB.
      apply hB in heq.
      exists B; split; first done.
      by eapply rtc_transitive.
    }
    destruct wfbody as (B & wfbody & hinherits).
    destruct wfbody as (lty_body & hbody & hret).
    iAssert(⌜inherits t0 t⌝ ∗ interp_type (ClassT B) (LocV l))%I as "#Hl".
    { iDestruct (expr_adequacy recv with "Hle") as "#Hrecv" => //.
      rewrite !interp_type_unfold /= /interp_class.
      iDestruct "Hrecv" as (? t1 ?) "[%hpure Hsem]".
      destruct hpure as [[= <-] [hinherits' ?]].
      iDestruct "Hh" as (sh) "(H● & % & #Hh)".
      iDestruct (own_valid_2 with "H● Hsem") as "#Hv".
      rewrite gmap_view_both_validI.
      iDestruct "Hv" as "[_ HΦ]".
      iDestruct ("Hh" with "[//]") as (?) "[H H▷]".
      iRewrite "H" in "HΦ".
      rewrite option_equivI prod_equivI /=.
      iDestruct "HΦ" as "[-> HΦ]".
      iSplitR; first done.
      by iExists l, t1, fields; iSplitR.
    }
    iDestruct "Hl" as "[%Hinherits #Hl]".
    assert (hincl: mdef_incl mdef0 mdef).
    {
      eapply has_method_inherits in Hinherits; [ | by apply wfΔ | done ].
      destruct Hinherits as [? [? ?]].
      replace x with mdef0 in * by (by eapply has_method_fun).
      done.
    }
    iModIntro; iNext.
    iSpecialize ("IH" $! _ _ _ hbody  _ _ _ H12); simpl.
    iDestruct ("IH" with "[Hh Hle]") as "H".
    { iFrame.
      iApply interp_local_tys_update => //.
      iApply interp_local_tys_list => //;
      first by (destruct hincl as [? _]; by rewrite -hdom).
      move => x ty arg hx harg.
      destruct hincl as [hdom' [hincl _]].
      destruct (methodargs mdef !! x) as [ty' | ] eqn:hty'.
      { apply (H _ _ _ hty') in harg.
        econstructor; first by apply harg.
        by eapply hincl.
      }
      apply mk_is_Some in hx.
      apply elem_of_dom in hx.
      rewrite hdom' in hx.
      apply elem_of_dom in hx.
      rewrite hty' in hx.
      by elim: hx.
    }
    iRevert "H".
    iApply updN_mono_I.
    iIntros "[Hh Hle2]"; iFrame.
    iApply interp_local_tys_update; first by done.
    destruct hincl as [? [? hret']].
    iApply subtype_is_inclusion; first by apply hret'.
    by iDestruct (expr_adequacy (methodret mdef0) with "Hle2") as "#Hret".
  - apply hi in hc; clear hi.
    iAssert(
     heap_models st.2 ∗ interp_local_tys lty st.1 -∗
     |=▷^n heap_models st'.2 ∗ interp_local_tys rty' st'.1
     )%I as "HC"; first by apply hc.
    iClear "IH".
    clear hc.
    iIntros "H".
    iSpecialize ("HC" with "H").
    iRevert "HC".
    iApply updN_mono_I.
    iIntros "[Hh #Hlty]".
    iFrame.
    iIntros (x ty) "%hx".
    apply (lookup_weaken _ _ _ _ hx) in hsubset.
    iApply "Hlty".
    by rewrite hsubset.
  - apply hi in hc; clear hi.
    iAssert(
     heap_models st.2 ∗ interp_local_tys lty st.1 -∗
     |=▷^n heap_models st'.2 ∗ interp_local_tys rty' st'.1
     )%I as "HC"; first by apply hc.
    iClear "IH".
    clear hc.
    iIntros "H".
    iSpecialize ("HC" with "H").
    iRevert "HC".
    iApply updN_mono_I.
    iIntros "[Hh #Hlty]".
    iFrame.
    iIntros (x ty) "%hx".
    destruct (rty' !! x) as [ ty' | ] eqn:hx'; last first.
    { apply mk_is_Some in hx; apply elem_of_dom in hx.
      rewrite -hdom in hx; apply elem_of_dom in hx.
      rewrite hx' in hx; by elim:hx.
    }
    apply (hsub _ _ _ hx') in hx.
    iSpecialize ("Hlty" $! x ty' hx').
    iDestruct "Hlty" as (val) "[%heq hinterp]".
    iExists val; rewrite heq; iSplitR; first done.
    by iApply subtype_is_inclusion.
  - inv hc.
    + apply hi in H6; clear hi.
      iAssert (
     heap_models st.2 ∗
     interp_local_tys (<[v:=InterT tv (ClassT t)]> lty) st.1 -∗
     |=▷^n heap_models st'.2 ∗ interp_local_tys lty st'.1
      )%I as "HC"; first by apply H6.
      iClear "IH".
      clear H6.
      destruct H5 as (l & hl & t' & fields & hlt & hinherits).
      iIntros "[H #Hle]".
      iApply "HC"; iClear "HC".
      iDestruct ("Hle" $! v with "[//]") as (?) "[%Hlev Hv]".
      rewrite Hlev in hl; simplify_eq.
      iAssert(heap_models st.2 ∗ interp_type (ClassT t') (LocV l))%I with "[H]" as "[H #Hinv]";
        first by (iApply (interp_type_loc_inversion with "Hle H Hv")).
      iFrame.
      iIntros (w tw).
      rewrite lookup_insert_Some.
      iIntros "%Hw".
      destruct Hw as [[<- <-] | [hne hw]].
      { iExists (LocV l); rewrite Hlev; iSplitR; first done.
        rewrite !interp_type_unfold /= /interp_inter; iSplit; first done.
        by iApply inherits_is_inclusion.
      }
      by iApply "Hle".
    + by iApply updN_intro.
Qed.

Lemma cmd_adequacy lty cmd lty' :
  wf_cdefs Δ →
  cmd_has_ty lty cmd lty' →
   ∀ st st' n, cmd_eval st cmd st' n →
   heap_models st.2 ∗ interp_local_tys lty st.1 -∗ |=▷^n
   heap_models st'.2 ∗ interp_local_tys lty' st'.1.
Proof.
  move => ? hty ??? hc.
  iApply cmd_adequacy_.
  done.
  by iPureIntro.
  by iPureIntro.
Qed.

End proofs.

Print Assumptions cmd_adequacy.
