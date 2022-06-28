(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
From stdpp Require Import base strings gmap stringmap fin_maps.
(* Not using iris but importing their ssreflect dependencies *)
From iris.proofmode Require Import tactics.
From shack Require Import lang.

(* A program is a collection of classes *)
Class ProgDefContext := { pdefs : stringmap classDef }.

Section ProgDef.
  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.

  (* A type is well-formed w.r.t. pdefs if all classes are
   * defined in pdefs, substitution applied to classes have the
   * correct length, and they are all made of well-formed types.
   *)
  Inductive wf_ty : lang_ty → Prop :=
    | WfInt : wf_ty IntT
    | WfBool : wf_ty BoolT
    | WfNothing : wf_ty NothingT
    | WfMixed : wf_ty MixedT
    | WfClassT t σ def:
        pdefs !! t = Some def →
        length σ = length def.(generics) →
        (∀ k ty, σ !! k = Some ty → wf_ty ty) →
        wf_ty (ClassT t σ)
    | WfNull : wf_ty NullT
    | WfNonNull : wf_ty NonNullT
    | WfUnion s t : wf_ty s → wf_ty t → wf_ty (UnionT s t)
    | WfInter s t : wf_ty s → wf_ty t → wf_ty (InterT s t)
    | WfGen k: wf_ty (GenT k)
    | WfEx t : wf_ty (ExT t)
    | WfDynamic : wf_ty DynamicT
    | WfSupportDyn : wf_ty SupportDynT
  .

  Hint Constructors wf_ty : core.

  Lemma wf_ty_class t σ def:
    pdefs !! t = Some def →
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
        s t hs his ht hit | s t hs his ht hit | | | | ] => //=; try (by constructor).
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

  (* All constraints in a class definition must be well-formed and bounded
   * by the class generics.
   *)
  Definition wf_constraint c := wf_ty c.1 ∧ wf_ty c.2.

  Definition wf_cdef_constraints_wf cdef :=
    Forall wf_constraint cdef.(constraints).

  Definition wf_cdef_constraints_bounded cdef :=
    Forall (bounded_constraint (length cdef.(generics))) cdef.(constraints).

  (* A class definition 'parent' information is valid if the parent type is:
   * - well-formed (tag exists, class is fully applied)
   * - bounded by the current class (must only mention generics of the current class)
   * - respect variance (see wf_cdef_mono)
   *)
  Definition wf_cdef_parent (prog: stringmap classDef) cdef : Prop :=
    match cdef.(superclass) with
    | None => True
    | Some (parent, σ) =>
        wf_ty (ClassT parent σ) ∧
        Forall (bounded (length cdef.(generics))) σ
    end
  .

  Definition cdef_methods_bounded cdef : Prop :=
    map_Forall (λ _mname mdef, mdef_bounded (length cdef.(generics)) mdef) cdef.(classmethods).

  (* source relation `class A<...> extends B<...>` *)
  Inductive extends_using : tag → tag → list lang_ty → Prop :=
    | ExtendsUsing A B adef σB:
        pdefs !! A = Some adef →
        adef.(superclass) = Some (B, σB) →
        extends_using A B σB.

  Hint Constructors extends_using : core.

  Lemma extends_using_wf A B σ:
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    extends_using A B σ →
    ∃ adef,
    pdefs !! A = Some adef ∧
    Forall (bounded (length adef.(generics))) σ ∧
    wf_ty (ClassT B σ).
  Proof.
    move => /map_Forall_lookup hwf hext.
    destruct hext as [A B adef σB hadef hsuper].
    exists adef; split => //.
    apply hwf in hadef.
    rewrite /wf_cdef_parent hsuper in hadef.
    destruct hadef as [hwfB hf].
    by split.
  Qed.

  Inductive inherits_using : tag → tag → list lang_ty → Prop :=
    | InheritsRefl A adef:
        pdefs !! A = Some adef →
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
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    inherits_using A B σ →
    ∃ adef,
    pdefs !! A = Some adef ∧
    Forall (bounded (length adef.(generics))) σ ∧
    wf_ty (ClassT B σ).
  Proof.
    move => hwf.
    induction 1 as [ A adef hpdefs | A B σ hext | A B σ C σC hext h hi ].
    - exists adef; repeat split => //.
      + by apply bounded_gen_targs.
      + econstructor => //; first by rewrite length_gen_targs.
        move => x hx h.
        by apply gen_targs_wf in h.
    - by apply extends_using_wf.
    - apply extends_using_wf in hext => //.
      destruct hext as (adef & hadef & hF0 & hwfB).
      destruct hi as (bdef & hbdef & hF1 & hwfC).
      exists adef; repeat split => //.
      + rewrite Forall_forall => ty hin.
        apply elem_of_list_fmap_2 in hin as [ty' [-> hin]].
        rewrite Forall_forall in hF1; apply hF1 in hin.
        eapply bounded_subst => //.
        inv hwfB; by simplify_eq.
      + inv hwfC.
        econstructor => //; first by rewrite map_length.
        move => k x hx.
        apply list_lookup_fmap_inv in hx as [ty [-> hty]].
        apply wf_ty_subst => //; first by apply wf_ty_class_inv in hwfB.
        by eauto.
  Qed.

  Lemma inherits_using_trans A B C σB σC:
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    inherits_using A B σB →
    inherits_using B C σC →
    inherits_using A C (subst_ty σB <$> σC).
  Proof.
    move => hwf h;
    move : h C σC.
    induction 1 as [ A cdef hpdefs | A B s hext | A B s C t hext h hi] => Z σ' hin.
    - rewrite subst_tys_id //.
      apply inherits_using_wf in hin => //.
      destruct hin as (? & ? & hF & _ ).
      by simplify_eq.
    - by econstructor.
    - assert (hCZ := hin).
      apply hi in hin; clear hi.
      rewrite -map_subst_ty_subst; first by eapply InheritsTrans.
      apply inherits_using_wf in h => //.
      apply inherits_using_wf in hCZ => //.
      destruct h as (bdef & hbdef & hF0 & hwfC).
      destruct hCZ as (cdef & hcdef & hF1 & hwfZ).
      inv hwfC; simplify_eq; by rewrite H2.
  Qed.

  (* Stripped version of extends_using/inherits_using, mostly for
   * evaluation when we don't care about the generics.
   *)
  Inductive extends: tag → tag → Prop :=
    | Extends A B cdef σB:
        pdefs !! A = Some cdef →
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
    induction 1 as [ A adef hpdefs | A B σ hext | A B σ C σC hext h hi ].
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
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    inherits_using A B σ →
    ∀ C σ', inherits_using A C σ' →
    (∃ σ'', (subst_ty σ <$> σ'' = σ' ∧ inherits_using B C σ'') ∨
            (subst_ty σ' <$> σ'' = σ ∧ inherits_using C B σ'')).
  Proof.
    move => hwf.
    induction 1 as [ A adef hpdefs | A B s hext | A B s C t hext h hi] => Z σ' hz.
    - exists σ'; left; split => //.
      apply subst_tys_id.
      apply inherits_using_wf in hz => //.
      destruct hz as (? & ? & hF & _ ).
      by simplify_eq.
    - inv hext; inv hz.
      + simplify_eq.
        exists s; right; split; last by econstructor; econstructor.
        apply subst_tys_id.
        apply hwf in H.
        rewrite /wf_cdef_parent H0 in H.
        by destruct H as (_ & hF).
      + inv H1.
        simplify_eq.
        apply hwf in H.
        rewrite /wf_cdef_parent H0 in H.
        destruct H as (hwfB & hF).
        inv hwfB.
        exists (gen_targs (length def.(generics))); left; split; last by econstructor.
        by rewrite subst_ty_gen_targs.
      + inv H1.
        simplify_eq.
        exists σC; by left.
    - destruct (inherits_using_wf _ _ _ hwf hz) as (adef & hadef & hF0 & hwfZ).
      inv hext; inv hz.
      + simplify_eq.
        exists (subst_ty s <$> t); right; split; last first.
        { eapply InheritsTrans => //.
          by econstructor.
        }
        rewrite subst_tys_id // Forall_forall => ty hty.
        apply elem_of_list_fmap_2 in hty as [ ty' [ -> hty']].
        apply hwf in hadef.
        rewrite /wf_cdef_parent H0 in hadef.
        destruct hadef as (hwfB & hF1).
        inv hwfB.
        apply bounded_subst with (length (generics def)) => //.
        apply inherits_using_wf in h => //.
        destruct h as (? & ? & hF2 & hwfC); simplify_eq.
        by rewrite Forall_forall in hF2; apply hF2.
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
          destruct h as (bdef & hbdef & hF1 & hwfC).
          destruct hx as (cdef & hcdef & hF2 & hwfZ').
          simplify_eq.
          inv hwfC; simplify_eq.
          by rewrite H3.
        * exists σ''; right; split; last done.
          rewrite map_subst_ty_subst //.
          apply inherits_using_wf in h => //.
          apply inherits_using_wf in hx => //.
          destruct h as (bdef & hbdef & hF1 & hwfC).
          destruct hx as (zdef & hzdef & hF2 & hwfC').
          inv hwfZ; simplify_eq.
          rewrite map_length in H3.
          by rewrite H3.
  Qed.

  Lemma inherits_using_refl A σ:
    wf_no_cycle pdefs →
    inherits_using A A σ →
    ∃ adef, pdefs !! A = Some adef ∧ σ = gen_targs (length adef.(generics)).
  Proof.
    move => hwf hA.
    assert (h: ∃ adef, pdefs !! A = Some adef).
    { inv hA.
      - by exists adef.
      - inv H.
        by exists adef.
      - inv H.
        by exists adef.
    }
    destruct h as [adef hpdefs].
    exists adef; split => //.
    eapply hwf; first by apply hA.
    by constructor.
  Qed.

  Lemma inherits_using_fun A B σ:
    wf_no_cycle pdefs →
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    inherits_using A B σ →
    ∀ σ', inherits_using A B σ' → σ = σ'.
  Proof.
    move => hwf hp.
    induction 1 as [ A adef hpdefs | A B s hext | A B s C t hext h hi ] => σ' hother.
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
        destruct H as [H ?].
        inv H.
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
        destruct H as [H ?].
        inv H.
        by simplify_eq.
      + inv H1; simplify_eq.
        apply hi in H2; by subst.
  Qed.

  (* has_field f C vis fty orig means that class C defines or inherits a field f
   * of type fty. Its visibility is vis in the class orig.
   * The type fty is substituted accordingly so it can be
   * interpreted in C directly.
   *)
  Inductive has_field (fname: string) : tag → visibility → lang_ty → tag → Prop :=
    | HasField tag cdef vtyp:
        pdefs !! tag = Some cdef →
        cdef.(classfields) !! fname = Some vtyp →
        has_field fname tag vtyp.1 vtyp.2 tag
    | InheritsField tag targs parent cdef vis typ orig:
        pdefs !! tag = Some cdef →
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
    induction 1 as [ tag cdef [vis typ] hpdefs hf
      | tag targs parent cdef vis typ orig hpdefs hf hs h hi ] => vis' typ' orig' h'.
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
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _, wf_cdef_fields_wf) pdefs →
    has_field f t vis fty orig →
    wf_ty fty.
  Proof.
    move => hp hwf.
    induction 1 as [ tag cdef [? typ] hpdefs hf
      | tag targs parent cdef vis typ orig hpdefs hf hs h hi ].
    - apply hwf in hpdefs.
      by apply hpdefs in hf.
    - apply wf_ty_subst => //.
      apply hp in hpdefs.
      rewrite /wf_cdef_parent hs in hpdefs.
      destruct hpdefs as [hwft _].
      by apply wf_ty_class_inv in hwft.
  Qed.

  (* If a class has a field f, then any subclass will inherit it,
   * with the right substituted type.
   *)
  Lemma has_field_extends_using f B vis typ orig:
    map_Forall (λ _cname, wf_cdef_fields) pdefs →
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
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _cname, wf_cdef_fields_bounded) pdefs →
    has_field f t vis fty orig →
    ∃ def, pdefs !! t = Some def ∧ bounded (length def.(generics)) fty.
  Proof.
    move => hwfparent hwfb.
    induction 1 as [ tag cdef [? typ] hpdefs hf
      | tag targs parent cdef vis typ orig hpdefs hf hs h hi ].
    - exists cdef; split => //.
      apply hwfb in hpdefs.
      by apply hpdefs in hf.
    - exists cdef; split => //.
      destruct hi as [pdef [ hp hb]].
      apply hwfparent in hpdefs.
      rewrite /wf_cdef_parent hs in hpdefs.
      destruct hpdefs as [hpdefs hF].
      inv hpdefs; simplify_eq.
      by eapply bounded_subst.
  Qed.

  (* like has_field_extends_using, for any chain of inheritance. *)
  Lemma has_field_inherits_using f B vis typ orig:
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _cname, wf_cdef_fields) pdefs →
    map_Forall (λ _cname, wf_cdef_fields_bounded) pdefs →
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
      destruct h as (bdef & hbdef & hF & hwfC).
      inv hwfC.
      simplify_eq.
      by rewrite H2.
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
        pdefs !! tag = Some cdef →
        cdef.(classmethods) !! mname = Some mdef →
        has_method mname tag tag mdef
    | InheritsMethod tag parent orig σ cdef mdef:
        pdefs !! tag = Some cdef →
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
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _, wf_cdef_methods_wf) pdefs →
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
        destruct ht as [ht _].
        by apply wf_ty_class_inv in ht.
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

  (* has_method is a functional relation *)
  Lemma has_method_fun: ∀ A name mdef0 mdef1 orig0 orig1,
    has_method name A orig0 mdef0 → has_method name A orig1 mdef1 →
    orig0 = orig1 ∧ mdef0 = mdef1.
  Proof.
    move => A name mdef0 mdef1 orig0 orig1 h; move: mdef1.
    induction h as [ current cdef mdef hpdefs hm
      | current parent orig inst cdef mdef hpdefs hm hs hp hi ] => mdef1 h1.
    - inv h1; by simplify_eq.
    - inv h1.
      + by simplify_eq.
      + simplify_eq.
        apply hi in H2 as []; by subst.
  Qed.

  (* Helper lemma that gives all the relevant info from a has_method
   * statement:
   * - the class where it was originall defined
   * - the substitutions needed to interpret it in A, or in its original
   *   location.
   *)
  Lemma has_method_from_def A m orig mdef:
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _cname, cdef_methods_bounded) pdefs →
    has_method m A orig mdef →
    ∃ cdef mdef_orig,
      pdefs !! orig = Some cdef ∧
      cdef.(classmethods) !! m = Some mdef_orig ∧
      has_method m orig orig mdef_orig ∧
      ∃ σ, inherits_using A orig σ ∧ mdef = subst_mdef σ mdef_orig.
  Proof.
    move => hp hmb.
    induction 1 as [ A adef mdef hpdefs hm | A parent orig σ cdef mdef hpdefs hm hs h hi ].
    - exists adef, mdef; repeat split => //; first by econstructor.
      exists (gen_targs (length adef.(generics))); split; first by constructor.
      rewrite subst_mdef_gen_targs //.
      apply hmb in hpdefs.
      by apply hpdefs in hm.
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
      apply inherits_using_wf in hin as (? & ? & hf & hwf0) => //.
      inv hwf0; simplify_eq.
      by rewrite H3.
  Qed.

  (* Helper lemma: If A inherits a method m from class orig, and
   * A <: B <: orig, then B must also inherits method m from orig.
   *)
  Lemma has_method_below_orig A m orig mdef:
    wf_no_cycle pdefs →
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    map_Forall (λ _cname, cdef_methods_bounded) pdefs →
    has_method m A orig mdef →
    ∀ B σ σ', inherits_using A B σ → inherits_using B orig σ' →
    ∃ odef mdefo mdefB,
    pdefs !! orig = Some odef ∧
    odef.(classmethods) !! m = Some mdefo ∧
    has_method m B orig mdefB ∧
    mdefB = subst_mdef σ' mdefo.
  Proof.
    move => hc hp hb.
    induction 1 as [ A cdef mdef hpdefs hm | A parent orig σ cdef mdef hpdefs hm hs h hi ] =>
          B σA σB hAB hBO.
    - destruct (hc _ _ _ _ hAB hBO) as [-> ->].
      apply inherits_using_refl in hAB as [ ? [? ->]] => // ; simplify_eq.
      exists cdef, mdef, mdef; repeat split => //.
      + by econstructor.
      + rewrite subst_mdef_gen_targs //.
        apply hb in hpdefs.
        by apply hpdefs in hm.
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
          apply inherits_using_wf in hBO as (? & ? & hF & hwf0) => //.
          inv hwf0; simplify_eq.
          apply hb in H.
          apply H in hmo.
          rewrite map_length in H4.
          by rewrite H4.
      + inv H; simplify_eq; clear hi.
        destruct (has_method_from_def _ _ _ _ hp hb h) as (odef & modef & ? & hmo & _ & [σo [hin ->]]).
        exists odef, modef, (subst_mdef σo modef); repeat split => //.
        replace σB with σo; first done.
        by eapply inherits_using_fun.
      + inv H; simplify_eq.
        destruct (hi _ _ _ H0 hBO) as (odef & mdefo & mdefB & ? & ? & ? & ->).
        by exists odef, mdefo, (subst_mdef σB mdefo).
  Qed.
End ProgDef.

(* Hints and notations are local to the section. Re-exporting them *)
Global Hint Constructors has_field : core.
Global Hint Constructors has_method : core.
Global Hint Constructors wf_ty : core.
Global Hint Constructors extends_using : core.
Global Hint Constructors inherits_using : core.
