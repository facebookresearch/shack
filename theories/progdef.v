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
    | WfClass exact t σ def:
        pdefs !! t = Some def →
        length σ = length def.(generics) →
        Forall wf_ty σ →
        wf_ty (ClassT exact t σ)
    | WfNull : wf_ty NullT
    | WfNonNull : wf_ty NonNullT
    | WfUnion s t : wf_ty s → wf_ty t → wf_ty (UnionT s t)
    | WfInter s t : wf_ty s → wf_ty t → wf_ty (InterT s t)
    | WfGen k: wf_ty (GenT k)
    | WfDynamic : wf_ty DynamicT
    | WfSupportDyn : wf_ty SupportDynT
    | WfThis : wf_ty ThisT
  .

  Hint Constructors wf_ty : core.

  Lemma wf_tyI ty:
    wf_ty ty →
    match ty with
    | ClassT _ t σ =>
        ∃ def, pdefs !! t = Some def ∧
        length σ = length def.(generics) ∧
        Forall wf_ty σ
    | UnionT A B
    | InterT A B => wf_ty A ∧ wf_ty B
    | _ => True
    end.
  Proof. move => h; inv h; by eauto. Qed.

  Lemma wf_ty_classI exact t σ:
    wf_ty (ClassT exact t σ) → Forall wf_ty σ.
  Proof. move => h. inv h. by eauto. Qed.

  Lemma wf_ty_exact ex0 ex1 t σ:
    wf_ty (ClassT ex0 t σ) → wf_ty (ClassT ex1 t σ).
  Proof. move => h; inv h; by eauto. Qed.

  Lemma wf_ty_subst σ ty :
    Forall wf_ty σ →
    wf_ty ty → wf_ty (subst_ty σ ty).
  Proof.
    move => hwf.
    elim : ty => //=.
    - move => ?? targs hi /wf_tyI [def [hdef [hlen hF]]].
      econstructor; [ done | by rewrite map_length | ].
      rewrite Forall_lookup => k ty.
      rewrite list_lookup_fmap.
      destruct (targs !! k) as [ tk | ] eqn:htk => //=.
      case => <-.
      rewrite !Forall_lookup in hi, hF.
      eapply hi; first done.
      by eapply hF.
    - move => s t hi0 hi1 /wf_tyI [h0 h1].
      by eauto.
    - move => s t hi0 hi1 /wf_tyI [h0 h1].
      by eauto.
    - move => k _.
      destruct (σ !! k) as [ ty | ] eqn:hty => /=; last by constructor.
      by rewrite Forall_lookup in hwf; apply hwf in hty.
  Qed.

  Lemma wf_ty_subst_this this ty :
    wf_ty this → wf_ty ty → wf_ty (subst_this this ty).
  Proof.
    move => hwf.
    elim: ty => //=.
    - move => ? t σ hi /wf_tyI [? [? [? hσ]]].
      econstructor; [ done | by rewrite map_length | ].
      rewrite Forall_lookup => k ty.
      rewrite list_lookup_fmap.
      destruct (σ !! k) as [ tk | ] eqn:htk => //=.
      case => <-.
      rewrite !Forall_lookup in hi, hσ.
      by eauto.
    - move => s t hs ht /wf_tyI [??]; by eauto.
    - move => s t hs ht /wf_tyI [??]; by eauto.
  Qed.

  Lemma wf_ty_subst_map σ σ':
    Forall wf_ty σ →
    Forall wf_ty σ' →
    Forall wf_ty (subst_ty σ <$> σ').
  Proof.
    move => h.
    elim : σ' => //= hd tl hi h'.
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

  Lemma gen_targs_wf_2 n: Forall wf_ty (gen_targs n).
  Proof. apply Forall_lookup => ??; by apply gen_targs_wf. Qed.

  (* All constraints in a class definition must be well-formed and bounded
   * by the class generics.
   *)
  Definition wf_constraint c := wf_ty c.1 ∧ wf_ty c.2.

  Definition no_this_constraint c := no_this c.1 ∧ no_this c.2.

  Definition wf_cdef_constraints_wf cdef :=
    Forall wf_constraint cdef.(constraints).

  Definition wf_cdef_constraints_no_this cdef :=
    Forall no_this_constraint cdef.(constraints).

  Definition wf_cdef_constraints_bounded cdef :=
    Forall (bounded_constraint (length cdef.(generics))) cdef.(constraints).

  Definition subst_constraint σ c := (subst_ty σ c.1, subst_ty σ c.2).
  Definition subst_constraints σ (cs: list constraint) :=
    subst_constraint σ <$> cs.

  Lemma subst_constraint_gen_targs n c:
    bounded_constraint n c →
    subst_constraint (gen_targs n) c = c.
  Proof.
    rewrite /subst_constraint.
    case : c => s t [] /= hs ht.
    f_equal; by apply subst_ty_id.
  Qed.

  Lemma subst_constraints_gen_targs n (Σ: list constraint):
    Forall (bounded_constraint n) Σ →
    subst_constraints (gen_targs n) Σ = Σ.
  Proof.
    move/Forall_lookup => h.
    apply list_eq => k.
    rewrite /subst_constraints list_lookup_fmap.
    destruct (Σ !! k) as [c | ] eqn:hc.
    - rewrite hc /= subst_constraint_gen_targs //.
      by apply h in hc.
    - by rewrite hc.
  Qed.

  Lemma subst_constraint_subst σ0 σ1 c:
    bounded_constraint (length σ1) c →
    subst_constraint σ0 (subst_constraint σ1 c) =
    subst_constraint (subst_ty σ0 <$> σ1) c.
  Proof.
    case : c => s t [??].
    rewrite /subst_constraint /=.
    by rewrite !subst_ty_subst.
  Qed.

  Lemma subst_constraints_subst σ0 σ1 Σ:
    Forall (bounded_constraint (length σ1)) Σ →
    subst_constraints σ0 (subst_constraints σ1 Σ) =
    subst_constraints (subst_ty σ0 <$> σ1) Σ.
  Proof.
    rewrite /subst_constraints => h.
    apply list_eq => k.
    rewrite !list_lookup_fmap.
    destruct (Σ !! k) as [c | ] eqn:hc; last done.
    rewrite /= subst_constraint_subst //.
    rewrite Forall_lookup in h.
    by apply h in hc.
  Qed.

  Lemma subst_constraints_app σ Σ0 Σ1:
    subst_constraints σ (Σ0 ++ Σ1) =
    subst_constraints σ Σ0 ++ subst_constraints σ Σ1.
  Proof.  by rewrite /subst_constraints fmap_app. Qed.

  (* A class definition 'parent' information is valid if the parent type is:
   * - well-formed (tag exists, class is fully applied)
   * - bounded by the current class (must only mention generics of the current class)
   * - respect variance (see wf_cdef_mono)
   * - the substitution doesn't refer to the `ThisT` type
   *)
  Definition wf_cdef_parent (prog: stringmap classDef) cdef : Prop :=
    match cdef.(superclass) with
    | None => True
    | Some (parent, σ) =>
        wf_ty (ClassT true parent σ) ∧
        Forall (bounded (length cdef.(generics))) σ ∧
        Forall no_this σ
    end
  .

  Definition cdef_methods_bounded cdef : Prop :=
    map_Forall (λ _mname mdef, mdef_bounded (length cdef.(generics)) mdef)
      cdef.(classmethods).

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
    wf_ty (ClassT true B σ) ∧
    Forall no_this σ.
  Proof.
    move => /map_Forall_lookup hwf hext.
    destruct hext as [A B adef σB hadef hsuper].
    exists adef; split => //.
    apply hwf in hadef.
    rewrite /wf_cdef_parent hsuper in hadef.
    destruct hadef as (? & ? & ?).
    by repeat split.
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
    wf_ty (ClassT true B σ) ∧
    Forall no_this σ.
  Proof.
    move => hwf.
    induction 1 as [ A adef hpdefs | A B σ hext | A B σ C σC hext h hi ].
    - exists adef; repeat split => //.
      + by apply bounded_gen_targs.
      + econstructor => //; first by rewrite length_gen_targs.
        rewrite Forall_lookup => x hx h.
        by apply gen_targs_wf in h.
      + by apply gen_targs_has_no_this.
    - by apply extends_using_wf.
    - apply extends_using_wf in hext => //.
      destruct hext as (adef & hadef & hF0 & hwfB & hnothisB).
      destruct hi as (bdef & hbdef & hF1 & hwfC & hnothis).
      exists adef; repeat split => //.
      + rewrite Forall_lookup => ? ty hin.
        apply list_lookup_fmap_inv in hin as [ty' [-> hin]].
        rewrite Forall_lookup in hF1; apply hF1 in hin.
        eapply bounded_subst => //.
        apply wf_tyI in hwfB as [def [hdef [? ?]]].
        by simplify_eq.
      + apply wf_tyI in hwfC as [def [hdef [? hF]]].
        econstructor => //; first by rewrite map_length.
        rewrite Forall_lookup => k x hx.
        apply list_lookup_fmap_inv in hx as [ty [-> hty]].
        apply wf_ty_subst => //; first by apply wf_ty_classI in hwfB.
        rewrite Forall_lookup in hF.
        by eauto.
      + by apply subst_ty_has_no_this_map.
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
      destruct h as (bdef & hbdef & hF0 & hwfC & _).
      destruct hCZ as (cdef & hcdef & hF1 & hwfZ & _).
      apply wf_tyI in hwfC as (? & ? & hlen & _); simplify_eq.
      by rewrite hlen.
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

  Lemma inherits_using_ex t t' def:
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    pdefs !! t = Some def →
    inherits t t' → ∃ σ, inherits_using t t' σ.
  Proof.
    move => hp hpdef h; move : def hpdef.
    induction h as [ A | A B C hAB hBC hi ] => def hpdef.
    - exists (gen_targs (length def.(generics))); by constructor.
    - destruct hAB as [A B adef' σB hadef hsuper]; simplify_eq.
      assert (hadef' := hadef).
      apply hp in hadef.
      rewrite /wf_cdef_parent hsuper in hadef.
      destruct hadef as [hwfB ?].
      apply wf_tyI in hwfB as (bdef & hbdef & ? & ?).
      apply hi in hbdef as [σC hC].
      exists (subst_ty σB <$> σC).
      eapply InheritsTrans => //.
      by econstructor.
  Qed.

End ProgDef.

Global Hint Constructors wf_ty : core.

(* From Pierre-Yves Strub *)
Variant option_spec {T : Type} (x : option T) : Type :=
  | OptionSome (y : T) : x = Some y -> option_spec x
  | OptionNone : x = None -> option_spec x
.

Lemma optionP {T : Type} (x : option T) : option_spec x.
Proof. by case: x => [y|]; [constructor 1 with y | constructor 2]. Qed.

(* Infra to be able to use the `extends` relation into a `parent`
 * relation that gives the list of all parents of a class.
 *)
Section CloseUp.
  Context (T : Type) (r : relation T) (c : T -> option T).

  Context
  (rP      : ∀ x y, c x = Some y -> r x y).

  Context (wf : ∀ c, Acc (fun x y => r y x) c).

  Definition cs (x : T) :=
    @Fix
    T
    (fun x y => r y x)
    wf
    (fun _ => list T)
    (fun x ih =>
    x :: if optionP (c x) is OptionSome _ y e then ih _ (rP _ _ e) else [])
    x.

  Lemma csE (x : T) :
    cs x = x :: (if c x is Some y then cs y else []).
  Proof.
    rewrite /cs Fix_eq => [|??? ih] /=; congr (_ :: _).
    - by case: optionP => [y|] ->.
    - by case: optionP.
  Qed.

  Lemma csP (x : T): ∀ y, y ∈ cs x → rtc r x y.
  Proof.
    move: x.
    elim/(well_founded_ind wf) => x hi y.
    rewrite csE elem_of_cons.
    case => [-> | ]; first done.
    move: (rP x).
    case: (c x) => [p | ]; last first.
    { move => _ h.
      by apply not_elem_of_nil in h.
    }
    move => h hin.
    apply rtc_l with p; first by apply h.
    apply hi => //.
    by apply h.
  Qed.
End CloseUp.

Class ProgDefAcc `{ PDC: ProgDefContext} := { pacc : ∀ c : tag, Acc (λ x y : tag, extends y x) c; }.

Section ProgDef2.

  Context `{PDA: ProgDefAcc}.

  Definition parent C :=
    match pdefs !! C with
    | None => None
    | Some cdef =>
        match cdef.(superclass) with
        | Some (P, _) => Some P
        | None => None
        end
    end.

  Lemma parent_spec C P: parent C = Some P → extends C P.
  Proof.
    rewrite /parent.
    destruct (pdefs !! C) as [ cdef | ] eqn:hcdef => //.
    destruct cdef.(superclass) as [[p ?] |] eqn:hsuper => //.
    case => h; subst.
    by econstructor.
  Qed.

  Lemma extends_is_not_reflexive: ∀ c, ~ extends c c.
  Proof.
    move => c hext.
    destruct PDA as [hwf].
    induction (hwf c) as [c h hi].
    by apply hi with c.
  Qed.

  Derive Inversion_clear inheritsI with (∀ A B, inherits A B) Sort Prop.
  Derive Inversion_clear inherits_usingI with
    (∀ A B σ, inherits_using A B σ) Sort Prop.

  Lemma wf_no_cycle_ :
    ∀ A B, inherits A B → inherits B A → A = B.
  Proof.
    destruct PDA as [ hwf ].
    move => A B h0 h1.
    move: B h0 h1.
    induction (hwf A) as [A h hi] => B h0 h1.
    elim/inheritsI: h0 => // C hext hexts.
    assert (hAC := hext).
    apply hi with (B := A) in hext.
    - rewrite hext in hAC.
      by apply extends_is_not_reflexive in hAC.
    - by transitivity B.
    - by econstructor.
  Qed.

  Definition parents : tag → list tag :=
    cs tag extends parent parent_spec PDA.(pacc).

  Lemma parents_spec A B adef:
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    pdefs !! A = Some adef →
    B ∈ parents A → ∃ σ, inherits_using A B σ.
  Proof.
    move => hp hadef hin.
    apply csP in hin.
    by eapply inherits_using_ex.
  Qed.

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
    - destruct hext as [A B adef σ hadef hsuper].
      elim/inherits_usingI: hz hadef hsuper.
      + move => zdef hzdef hzdef' hsuper; simplify_eq.
        exists σ; right; split; last by econstructor; econstructor.
        apply subst_tys_id.
        apply hwf in hzdef.
        rewrite /wf_cdef_parent hsuper in hzdef.
        by destruct hzdef as (_ & hF & _).
      + case => {A}{Z}{σ'}.
        move => A Z adef' σ' hadef hsuper ? ?; simplify_eq.
        apply hwf in hadef.
        rewrite /wf_cdef_parent hsuper in hadef.
        destruct hadef as (hwfB & hF).
        apply wf_tyI in hwfB as (zdef & ? & ? & ?).
        exists (gen_targs (length zdef.(generics))); left; split; last by econstructor.
        by rewrite subst_ty_gen_targs.
      + move => B0 σB σC. case => {A}{B0}{σ'}{σB}.
        move => A B0 adef' σB hadef' hsuper0 hin hadef hsuper; simplify_eq.
        exists σC; by left.
    - destruct (inherits_using_wf _ _ _ hwf hz) as (adef & hadef & hF0 & hwfZ & _).
      destruct hext as [A B adef' σ hadef' hsuper]; simplify_eq.
      elim/inherits_usingI: hz hadef' hsuper hF0 hwfZ.
      + move => zdef hzdef ? hsuper hF0 hwfZ; simplify_eq.
        exists (subst_ty σ <$> t); right; split; last first.
        { eapply InheritsTrans => //.
          by econstructor.
        }
        rewrite subst_tys_id // Forall_lookup => ? ty hty.
        apply list_lookup_fmap_inv in hty as [ty' [-> hty']].
        apply hwf in hzdef.
        rewrite /wf_cdef_parent hsuper in hzdef.
        destruct hzdef as (hwfB & hF1 & _).
        apply wf_tyI in hwfB as (bdef & ? & ? & ?).
        apply bounded_subst with (length (generics bdef)) => //.
        apply inherits_using_wf in h => //.
        destruct h as (? & ? & hF2 & hwfC); simplify_eq.
        rewrite Forall_lookup in hF2; by eauto.
      + case => {A}{Z}{σ'}.
        move => A B0 adef σB hadef hsuper ? ? hF0 hwfZ; simplify_eq.
        exists t; by right.
      + move => B0 σB σC.
        case => {A}{B0}{σB}{σ'}.
        move => A B0 adef σB hadef hsuper hin ? ? hF0 hwfZ; simplify_eq.
        apply hi in hin as [σ'' [ [<- hx] | [<- hx]]]; clear hi.
        * exists σ''; left; split; last done.
          rewrite map_subst_ty_subst //.
          apply inherits_using_wf in h => //.
          apply inherits_using_wf in hx => //.
          destruct h as (bdef & hbdef & hF1 & hwfC & _).
          destruct hx as (cdef & hcdef & hF2 & hwfZ' & _).
          simplify_eq.
          apply wf_tyI in hwfC as (? & ? & hlen & ?).
          simplify_eq.
          by rewrite hlen.
        * exists σ''; right; split; last done.
          rewrite map_subst_ty_subst //.
          apply inherits_using_wf in h => //.
          apply inherits_using_wf in hx => //.
          destruct h as (bdef & hbdef & hF1 & hwfC & _).
          destruct hx as (zdef & hzdef & hF2 & hwfC' & _).
          apply wf_tyI in hwfZ as (? & ? & hlen & ?); simplify_eq.
          rewrite map_length in hlen.
          by rewrite hlen.
  Qed.

  Lemma inherits_using_refl A σ:
    inherits_using A A σ →
    ∃ adef, pdefs !! A = Some adef ∧ σ = gen_targs (length adef.(generics)).
  Proof.
    move => hA.
    assert (h: ∃ adef, pdefs !! A = Some adef).
    { elim/inherits_usingI : hA.
      - move => adef hadef; by exists adef.
      - move/extends_using_erase => hext.
        by apply extends_is_not_reflexive in hext.
      - move => B0 σB σC.
        case => {A}{σB}.
        move => A B adef σB hadef ? ?; by exists adef.
    }
    destruct h as [adef hpdefs].
    exists adef; split => //.
    elim/inherits_usingI : hA adef hpdefs.
    - move => adef hadef ? ?; by simplify_eq.
    - move/extends_using_erase => hext.
      by apply extends_is_not_reflexive in hext.
    - move => B σB σC /extends_using_erase hext /inherits_using_erase hin.
      move => adef hadef.
      replace B with A in *; last first.
      { eapply wf_no_cycle_ => //.
        by econstructor.
      }
      by apply extends_is_not_reflexive in hext.
  Qed.

  Lemma extends_using_fun A B σ:
    extends_using A B σ →
    ∀ B' σ', extends_using A B' σ' → B = B' ∧ σ = σ'.
  Proof.
    destruct 1 as [ A B adef σ hadef hsuper].
    destruct 1 as [ A B' ? σ' ? hsuper'].
    by simplify_eq.
  Qed.

  Lemma inherits_using_fun A B σ:
    map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs →
    inherits_using A B σ →
    ∀ σ', inherits_using A B σ' → σ = σ'.
  Proof.
    move => hp.
    induction 1 as [ A adef hpdefs | A B s hext | A B s C t hext h hi ] => σ' hother.
    - apply inherits_using_refl in hother as [? [h ->]] => //.
      by simplify_eq.
    - elim/inherits_usingI : hother s hext.
      + move => bdef hbdef σB hext.
        apply extends_using_erase in hext.
        by apply extends_is_not_reflexive in hext.
      + move => hext σB hext'.
        by destruct (extends_using_fun _ _ _ hext _ _ hext') as [? ->].
      + move => B0 σB σC hext hin σ hext'.
        destruct (extends_using_fun _ _ _ hext _ _ hext') as [-> ->].
        apply inherits_using_refl in hin as [bdef [hb ->]].
        rewrite subst_ty_gen_targs //.
        destruct hext as [A B0 adef σB hadef hsuper].
        apply hp in hadef.
        rewrite /wf_cdef_parent hsuper in hadef.
        destruct hadef as [hwfb ?].
        apply wf_tyI in hwfb as (? & ? & ? & ?).
        by simplify_eq.
    - elim/inherits_usingI : hother B s hext h hi.
      + move => cdef hcdef B σB hext hin hi.
        apply extends_using_erase in hext.
        apply inherits_using_erase in hin.
        replace C with B in *; last first.
        { apply wf_no_cycle_ => //.
          by econstructor.
        }
        by apply extends_is_not_reflexive in hext.
      + move => hext B σB hext' hin hi.
        destruct (extends_using_fun _ _ _ hext _ _ hext') as [-> ->].
        apply inherits_using_refl in hin => //.
        destruct hin as [bdef [hB ->]].
        rewrite subst_ty_gen_targs //.
        destruct hext' as [A C adef σ' hadef hsuper].
        apply hp in hadef.
        rewrite /wf_cdef_parent hsuper in hadef.
        destruct hadef as [hwfc ?].
        apply wf_tyI in hwfc as (? & ? & ? & ?).
        by simplify_eq.
      + move => B0 σB σC hext hin B σ hext' hin' hi.
        destruct (extends_using_fun _ _ _ hext _ _ hext') as [-> ->].
        apply hi in hin; by subst.
  Qed.

  (* Our class inheritance tree/forest doesn't have cycles. Which means
   * inherits A B → inherits B A → A = B.
   *)
  Lemma wf_no_cycle :
    ∀ A B σ σ', inherits_using A B σ → inherits_using B A σ' → A = B ∧ σ = σ'.
  Proof.
    move => A B σ σ' h0 h1.
    replace B with A in *; last first.
    { apply wf_no_cycle_; by eapply inherits_using_erase. }
    apply inherits_using_refl in h0 as (adef & hadef & ->).
    apply inherits_using_refl in h1 as (? & ? & ->); by simplify_eq.
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
    - destruct h'; by simplify_eq.
    - destruct h' as [tag tdef vtyp h0 h1 | ?????????? h0 ]; first by simplify_eq.
      simplify_eq.
      by destruct (hi _ _ _ h0) as [-> [-> ->]].
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
      by apply wf_ty_classI in hwft.
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
    destruct hext as [A B adef σB hsuper].
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
      destruct hpdefs as (hwf & hF & _).
      apply wf_tyI in hwf as (? & ? & ? & ?); simplify_eq.
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
      destruct h as (bdef & hbdef & hF & hwfC & _).
      apply wf_tyI in hwfC as (? & ? & hlen & ?); simplify_eq.
      by rewrite hlen.
  Qed.

  (* Helper predicate to collect all fields of a given class, as a map.
   * We collect both public and private fields, and their origins.
   *)
  Definition has_fields A (fields: stringmap ((visibility * lang_ty) * tag)) : Prop :=
    ∀ fname vis typ orig, has_field fname A vis typ orig ↔ fields !! fname = Some (vis, typ, orig).

  Lemma has_fields_fun A fs0 fs1:
    has_fields A fs0 → has_fields A fs1 → fs0 = fs1.
  Proof.
    move => hfs0 hfs1.
    apply map_eq => k.
    destruct (fs0 !! k) as [[[v ty] t] | ] eqn:hf0.
    { apply hfs0 in hf0.
      by apply hfs1 in hf0.
    }
    destruct (fs1 !! k) as [[[v ty] t] | ] eqn:hf1; last done.
    apply hfs1 in hf1.
    apply hfs0 in hf1.
    by rewrite hf1 in hf0.
  Qed.

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
        by apply wf_ty_classI in ht.
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
    - destruct h1 as [ | ????????? h0]; first by simplify_eq.
      simplify_eq.
      apply hi in h0 as []; by subst.
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
      apply inherits_using_wf in hin as (? & ? & hf & hwf0 & _) => //.
      apply wf_tyI in hwf0 as (? & ? & hlen & ?); simplify_eq.
      by rewrite hlen.
  Qed.

  (* Helper lemma: If A inherits a method m from class orig, and
   * A <: B <: orig, then B must also inherits method m from orig.
   *)
  Lemma has_method_below_orig A m orig mdef:
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
    move => hp hb.
    induction 1 as [ A adef mdef hadef hm
      | A parent orig σ adef mdef hadef hm hs h hi ] => B σA σB hAB hBO.
    - destruct (wf_no_cycle _ _ _ _ hAB hBO) as [-> ->].
      apply inherits_using_refl in hAB as [ ? [? ->]] => // ; simplify_eq.
      exists adef, mdef, mdef; repeat split => //.
      + by econstructor.
      + rewrite subst_mdef_gen_targs //.
        apply hb in hadef.
        by apply hadef in hm.
    - elim/inherits_usingI: hAB adef hadef hm hs hi hBO.
      + move => bdef hbdef ? ? hm hs hi hBO; simplify_eq.
        destruct (has_method_from_def _ _ _ _ hp hb h) as (odef & modef & ? & hmo & _ & [σo [hin ->]]).
        exists odef, modef, (subst_mdef σ (subst_mdef σo modef)); repeat split => //.
        * by econstructor.
        * assert (hσ: subst_ty σ <$> σo = σB).
          { eapply inherits_using_fun => //.
            eapply InheritsTrans; last done.
            by econstructor.
          }
          rewrite subst_mdef_mdef; first by rewrite hσ.
          apply inherits_using_wf in hBO as (? & ? & hF & hwf0 & _) => //.
          apply wf_tyI in hwf0 as (? & hodef & hlen & ?); simplify_eq.
          apply hb in hodef.
          apply hodef in hmo.
          rewrite map_length in hlen.
          by rewrite hlen.
      + case => {A}{B}{σA}.
        move => A B adef ? hadef hsuper ?? hm hs _ hBO; simplify_eq.
        destruct (has_method_from_def _ _ _ _ hp hb h) as (odef & modef & ? & hmo & _ & [σo [hin ->]]).
        exists odef, modef, (subst_mdef σo modef); repeat split => //.
        replace σB with σo; first done.
        by eapply inherits_using_fun.
      + move => B0 σB0 σC.
        case => {A}{B0}{σB0}{σA}.
        move => A B0 adef ? hadef hsuper hin ?? hm hsuper' hi hBO; simplify_eq.
        destruct (hi _ _ _ hin hBO) as (odef & mdefo & mdefB & ? & ? & ? & ->).
        by exists odef, mdefo, (subst_mdef σB mdefo).
  Qed.

  (* For runtime check, we want to introduce fresh new generic types,
   * and keep their constraints around. To this purpose, we need
   * to 'lift' constraints deBruijn to match the right indexes.
   *)
  Fixpoint lift_ty n (ty: lang_ty) : lang_ty :=
    match ty with
    | ClassT exact t σ => ClassT exact t (lift_ty n <$> σ)
    | UnionT s t => UnionT (lift_ty n s) (lift_ty n t)
    | InterT s t => InterT (lift_ty n s) (lift_ty n t)
    | GenT k => GenT (k + n)
    | IntT | BoolT | NothingT | MixedT | NullT |
      NonNullT | DynamicT | SupportDynT | ThisT => ty
    end.

  Lemma lift_ty_O ty : lift_ty 0 ty = ty.
  Proof.
    elim : ty => //=.
    - move => ? t σ hi.
      f_equal.
      apply list_eq => k.
      rewrite Forall_lookup in hi.
      rewrite list_lookup_fmap.
      destruct (σ !! k) as [ty | ] eqn:h; last done.
      apply hi in h.
      by rewrite /= h.
    - move => s t hs ht; by rewrite hs ht.
    - move => s t hs ht; by rewrite hs ht.
    - move => k; f_equal; by lia.
  Qed.

  Lemma lift_tys_O (σ : list lang_ty) : lift_ty 0 <$> σ = σ.
  Proof.
    apply list_eq => k.
    rewrite list_lookup_fmap.
    destruct (σ !! k) as [ty | ] eqn:h; last done.
    by rewrite /= lift_ty_O.
  Qed.

  Lemma lift_ty_wf ty: ∀ n, wf_ty ty → wf_ty (lift_ty n ty).
  Proof.
    elim: ty => //=.
    - move => ? t σ hi n /wf_tyI [tdef [htdef [hlen hwf]]].
      econstructor => //.
      + by rewrite map_length.
      + rewrite Forall_lookup => k ty h.
        apply list_lookup_fmap_inv in h as [ty' [-> h]].
        rewrite !Forall_lookup in hi, hwf.
        by eauto.
    - move => s t hs ht n /wf_tyI [??]; constructor; by eauto.
    - move => s t hs ht n /wf_tyI [??]; constructor; by eauto.
  Qed.

  Lemma lift_ty_bounded ty: ∀ n m, bounded m ty → bounded (n + m) (lift_ty n ty).
  Proof.
    elim: ty => //=.
    - move => ? t σ hi n m /boundedI hb.
      constructor => //.
      rewrite Forall_lookup => k ty h.
      apply list_lookup_fmap_inv in h as [ty' [-> h]].
      rewrite Forall_lookup in hi.
      rewrite Forall_lookup in hb.
      by eauto.
    - move => s t hs ht n m /boundedI [??]; constructor; by eauto.
    - move => s t hs ht n m /boundedI [??]; constructor; by eauto.
    - move => k n m /boundedI hlt; constructor.
      by lia.
  Qed.

  Lemma lift_subst_gen_targs n ty:
    bounded n ty →
    subst_ty (lift_ty n <$> gen_targs n) ty =
    lift_ty n ty.
  Proof.
    elim: ty => //=.
    - move => ? t σ hi /boundedI hb.
      f_equal.
      apply list_eq => k.
      rewrite Forall_lookup in hi.
      rewrite !list_lookup_fmap.
      destruct (σ !! k) as [ty | ] eqn:hty; last done.
      simpl; f_equal.
      apply hi in hty => //.
      rewrite Forall_lookup in hb.
      by eauto.
    - move => s t hs ht /boundedI [??]; by rewrite hs // ht.
    - move => s t hs ht /boundedI [??]; by rewrite hs // ht.
    - move => k /boundedI hlt.
      by rewrite list_lookup_fmap lookup_gen_targs_lt.
  Qed.

  Definition lift_constraint n c := (lift_ty n c.1, lift_ty n c.2).

  Definition lift_constraints n (Δ : list constraint) :=
    lift_constraint n <$> Δ.

  Lemma lift_constraints_wf n Δ:
    Forall wf_constraint Δ → Forall wf_constraint (lift_constraints n Δ).
  Proof.
    move => /Forall_lookup h.
    rewrite Forall_lookup => k ty hty.
    apply list_lookup_fmap_inv in hty as [ty' [-> hty]].
    apply h in hty as [].
    split; by apply lift_ty_wf.
  Qed.

  Lemma lift_constraints_bounded m n Δ:
    Forall (bounded_constraint m) Δ →
    Forall (bounded_constraint (n + m)) (lift_constraints n Δ).
  Proof.
    move => /Forall_lookup h.
    rewrite Forall_lookup => k ty hty.
    apply list_lookup_fmap_inv in hty as [ty' [-> hty]].
    apply h in hty as [].
    split; by apply lift_ty_bounded.
  Qed.

  Lemma lift_subst_gen_targs_constraint n c:
    bounded_constraint n c →
    subst_constraint (lift_ty n <$> gen_targs n) c =
    lift_constraint n c.
  Proof.
    case : c => s t [] /= hs ht.
    rewrite /subst_constraint /=.
    f_equal; by rewrite !lift_subst_gen_targs.
  Qed.

  Lemma lift_subst_gen_targs_constraints n (Δ: list constraint):
    Forall (bounded_constraint n) Δ →
    subst_constraints (lift_ty n <$> gen_targs n) Δ =
    lift_constraints n Δ.
  Proof.
    move/Forall_lookup => hb.
    apply list_eq => k.
    rewrite /subst_constraints /lift_constraints !list_lookup_fmap.
    destruct (Δ !! k) as [c | ] eqn:hc.
    - rewrite hc /= lift_subst_gen_targs_constraint //.
      by apply hb in hc.
    - by rewrite hc.
  Qed.
End ProgDef2.

(* Hints and notations are local to the section. Re-exporting them *)
Global Hint Constructors has_field : core.
Global Hint Constructors has_method : core.
Global Hint Constructors extends_using : core.
Global Hint Constructors inherits_using : core.
