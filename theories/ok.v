(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
From stdpp Require Import base strings gmap stringmap fin_maps.
(* Not using iris but importing their ssreflect dependencies *)
From iris.proofmode Require Import tactics.
From shack Require Import lang progdef subtype.

Section Ok.
  (* assume a given set of class definitions and their SDT annotations. *)
  Context `{SDTCS: SDTClassSpec}.

  (* Helping the inference with this notation that hides pdefs *)
  Local Notation "Δ ⊢ s <D: t" := (@subtype _ _ Δ Aware s t) (at level 70, s at next level, no associativity).

  (* At class + substitution is `ok` w.r.t. to a set of constraints `Δ` if
   * - all the types in the substitution are ok
   * - all the constraints of that class are satisfied.
   *)
  Inductive ok_ty (Δ: list constraint) : lang_ty → Prop :=
    | OkInt: ok_ty Δ IntT
    | OkBool: ok_ty Δ BoolT
    | OkNothing: ok_ty Δ NothingT
    | OkMixed: ok_ty Δ MixedT
    | OkClass exact_ t σ def:
        (∀ i ty, σ !! i = Some ty → ok_ty Δ ty) →
        pdefs !! t = Some def →
        (∀ i c, def.(constraints) !! i = Some c → Δ ⊢ (subst_ty σ c.1) <D: (subst_ty σ c.2)) →
        ok_ty Δ (ClassT exact_ t σ)
    | OkNull: ok_ty Δ NullT
    | OkNonNull: ok_ty Δ NonNullT
    | OkUnion s t: ok_ty Δ s → ok_ty Δ t → ok_ty Δ (UnionT s t)
    | OkInter s t: ok_ty Δ s → ok_ty Δ t → ok_ty Δ (InterT s t)
    | OkGen n: ok_ty Δ (GenT n)
    | OkDynamic : ok_ty Δ DynamicT
    | OkSupportDyn : ok_ty Δ SupportDynT
    | OkThis: ok_ty Δ ThisT
  .

  Lemma ok_tyI Δ ty:
    ok_ty Δ ty →
    match ty with
    | ClassT _ t σ =>
        ∃ def, pdefs !! t = Some def ∧
        (∀ i ty, σ !! i = Some ty → ok_ty Δ ty) ∧
        (∀ i c, def.(constraints) !! i = Some c → Δ ⊢ (subst_ty σ c.1) <D: (subst_ty σ c.2))
    | UnionT A B
    | InterT A B => ok_ty Δ A ∧ ok_ty Δ B
    | _ => True
    end.
  Proof. move => h; inv h; intros; by eauto. Qed.

  Lemma ok_ty_exact Δ ex0 ex1 t σ:
    ok_ty Δ (ClassT ex0 t σ) → ok_ty Δ (ClassT ex1 t σ).
  Proof. move => h; inv h; by econstructor. Qed.

  Lemma ok_ty_weaken Δ t: ok_ty Δ t → ∀ Δ', Δ ⊆ Δ' → ok_ty Δ' t.
  Proof.
    induction 1 as [ | | | | ? t σ def hσ hi hdef hconstr
      | | | s t hs hi ht hit | s t hs hi ht hit | n | | | ]
      => Δ' hincl; try by constructor.
    - apply OkClass with def => //.
      + move => i ty h; by apply hi with i.
      + move => i c h.
        apply subtype_weaken with Δ => //; by eauto.
    - constructor; by eauto.
    - constructor; by eauto.
  Qed.

  Lemma ok_ty_classI Δ exact_ t σ:
    ok_ty Δ (ClassT exact_ t σ) → Forall (ok_ty Δ) σ.
  Proof.
    move/ok_tyI => [def [hdef [h ?]]].
    rewrite Forall_lookup => ? x hin.
    by eauto.
  Qed.

  Lemma ok_ty_subst Δ t:
    map_Forall (λ _, wf_cdef_parent) pdefs →
    map_Forall (λ _, wf_cdef_constraints_bounded) pdefs →
    ok_ty Δ t →
    wf_ty t →
    ∀ Δ' σ, Forall wf_ty σ →
         Forall (ok_ty Δ') σ →
         ok_ty (Δ' ++ (subst_constraints σ Δ)) (subst_ty σ t).
  Proof.
    move => hwp hcb.
    induction 1 as [ | | | | ? t σt def hσt hi hdef hconstr
      | | | s t hs his ht hit | s t hs his ht hit | n | | | ]
      => hwf Δ' σ hwfσ hokσ /=; try (constructor; by eauto).
    - apply OkClass with def => //.
      + move => i ty h.
        apply list_lookup_fmap_inv in h as [ty' [-> h]].
        apply wf_ty_classI in hwf.
        apply hi with i => //.
        rewrite Forall_lookup in hwf.
        by apply hwf in h.
      + move => i c h.
        assert (hdef' := hdef).
        apply hcb in hdef'.
        rewrite /wf_cdef_constraints_bounded Forall_lookup in hdef'.
        assert (h' := h).
        apply hdef' in h as [].
        apply subtype_weaken with (subst_constraints σ Δ) => //; last by set_solver.
        rewrite -!subst_ty_subst.
        * apply subtype_subst => //.
          by apply hconstr with i.
        * apply wf_tyI in hwf as [? [? [hlen ?]]]; simplify_eq.
          by rewrite hlen.
        * apply wf_tyI in hwf as [? [? [hlen ?]]]; simplify_eq.
          by rewrite hlen.
    - apply wf_tyI in hwf as [??].
      constructor; by eauto.
    - apply wf_tyI in hwf as [??].
      constructor; by eauto.
    - destruct (σ !! n) as [ ty | ] eqn:hty; last by constructor.
      simpl.
      rewrite Forall_lookup in hokσ.
      apply hokσ in hty.
      apply ok_ty_weaken with Δ'; first by apply hty.
      by set_solver.
  Qed.

  Lemma ok_ty_constraint_trans kd Δ ty:
    ok_ty Δ ty →
    ∀ Δ', Δentails kd Δ' Δ →
    ok_ty Δ' ty.
  Proof.
    induction 1 as [ | | | | ? t σt def hσt hi hdef hconstr
      | | | s t hs his ht hit | s t hs his ht hit | n | | | ]
      => Δ' hΔ /=; try (constructor; by eauto).
    econstructor; [ | done | ].
    - move => k ty hty.
      eapply hi; first by apply hty.
      done.
    - move => k c hc.
      eapply subtype_constraint_trans.
      + by eapply hconstr.
      + move => l c' hc'.
        apply subtype_to_Aware with (kd := kd).
        by eapply hΔ.
  Qed.

  Definition ok_constraint Δ (c: constraint) :=
    ok_ty Δ c.1 ∧ ok_ty Δ c.2.

  Definition ok_constraints Δ G := Forall (ok_constraint Δ) G.

  Definition wf_cdef_parent_ok cdef :=
    match cdef.(superclass) with
    | None => True
    | Some (parent, σ) =>
        ok_ty cdef.(constraints) (ClassT true parent σ)
    end
  .

  Lemma extends_using_ok A B σ:
    map_Forall (λ _cname, wf_cdef_parent_ok) pdefs →
    extends_using A B σ →
    ∃ adef,
    pdefs !! A = Some adef ∧
    ok_ty adef.(constraints) (ClassT true B σ).
  Proof.
    move => hok h.
    destruct h as [A B adef σ hpdefs hsuper].
    exists adef; split => //.
    apply hok in hpdefs.
    by rewrite /wf_cdef_parent_ok hsuper in hpdefs.
  Qed.

  Lemma gen_targs_ok Δ n:
    ∀ i ty, gen_targs n !! i = Some ty →
    ok_ty Δ ty.
  Proof.
    move => i ty /lookup_gen_targs ->.
    by constructor.
  Qed.

  Lemma ok_ty_trans Δ ty:
    ok_ty Δ ty →
    ∀ Δ',
    (∀ i c, Δ !! i = Some c → Δ' ⊢ c.1 <D: c.2) →
    ok_ty Δ' ty.
  Proof.
    induction 1 as [ | | | | ? t σ def hσ hi hdef hconstr
      | | | s t hs hi ht hit | s t hs hi ht hit | n | | | ]
      => Δ' hΔ; try by constructor.
    - econstructor => //.
      + move => k ty hk; by eauto.
      + move => k c' hc'.
        apply hconstr in hc'.
        apply subtype_constraint_trans with Δ; by eauto.
    - constructor; by eauto.
    - constructor; by eauto.
  Qed.

  Lemma inherits_using_ok A B σ:
    map_Forall (λ _ : string, wf_cdef_parent) pdefs →
    map_Forall (λ _cname, wf_cdef_parent_ok) pdefs →
    map_Forall (λ _ : string, wf_cdef_constraints_bounded) pdefs →
    inherits_using A B σ →
    ∃ adef,
    pdefs !! A = Some adef ∧
    ok_ty adef.(constraints) (ClassT true B σ).
  Proof.
    move => hp hok hcb.
    induction 1 as [ A adef hpdefs | A B σ hext | A B σ C σC hext h hi ].
    - exists adef; split => //.
      econstructor => //.
      + by apply gen_targs_ok.
      + move => i c hc.
        rewrite !subst_ty_id.
        * constructor.
          apply elem_of_list_lookup.
          exists i; by rewrite hc {1}(surjective_pairing c).
        * apply hcb in hpdefs.
          rewrite /wf_cdef_constraints_bounded Forall_lookup in hpdefs.
          by apply hpdefs in hc as [].
        * apply hcb in hpdefs.
          rewrite /wf_cdef_constraints_bounded Forall_lookup in hpdefs.
          by apply hpdefs in hc as [].
    - by apply extends_using_ok in hext.
    - destruct hi as (bdef & hB & hokB).
      assert (hwfB: wf_ty (ClassT true B σ)).
      { apply extends_using_wf in hext => //.
        by repeat destruct hext as [? hext].
      }
      assert (hwfC: wf_ty (ClassT true C σC)).
      { apply inherits_using_wf in h => //.
        by repeat destruct h as [? h].
      }
      apply wf_tyI in hwfC as [cdef [hcdef [? hwfC]]].
      rewrite Forall_lookup in hwfC.
      destruct hext as [A B adef σ hadef hsuper].
      exists adef; split => //.
      econstructor => //.
      { move => i ty hi.
        apply list_lookup_fmap_inv in hi as [ty' [-> hi]].
        eapply ok_ty_trans.
        + eapply ok_ty_subst => //.
          { apply ok_tyI in hokB as [? [? [??]]]; by eauto. }
          { by eauto. }
          { by apply wf_ty_classI in hwfB. }
          apply hok in hadef.
          rewrite /wf_cdef_parent_ok hsuper in hadef.
          by apply ok_ty_classI in hadef.
        + move => j c.
          rewrite lookup_app_Some.
          case => [hc | [? ]].
          * apply SubConstraint.
            apply elem_of_list_lookup_2 in hc.
            by rewrite -surjective_pairing.
          * rewrite /subst_constraints => hc.
            apply list_lookup_fmap_inv in hc as [c' [-> hc]].
            rewrite /subst_constraint /=.
            apply hok in hadef.
            rewrite /wf_cdef_parent_ok hsuper in hadef.
            apply ok_tyI in hadef as [? [? [??]]]; simplify_eq.
            by eauto.
      }
      move => i c hc.
      rewrite -!subst_ty_subst.
      + eapply subtype_constraint_trans.
        * apply subtype_subst => //; last by apply wf_ty_classI in hwfB.
          apply ok_tyI in hokB as [? [? [??]]]; simplify_eq; by eauto.
        * move => j c'.
          rewrite /subst_constraints => hc'.
          apply list_lookup_fmap_inv in hc' as [c'' [-> hc']].
          rewrite /subst_constraint /=.
          apply hok in hadef.
          rewrite /wf_cdef_parent_ok hsuper in hadef.
          apply ok_tyI in hadef as [? [? [??]]]; simplify_eq.
          by eauto.
      + assert (hC := hcdef).
        apply hcb in hC.
        rewrite /wf_cdef_constraints_bounded Forall_lookup in hC.
        apply hC in hc as [].
        apply inherits_using_wf in h as (? & ? & ? & hwf & _)=> //.
        apply wf_tyI in hwf as [? [? [hlen ?]]]; simplify_eq.
        by rewrite hlen.
      + assert (hC := hcdef).
        apply hcb in hC.
        rewrite /wf_cdef_constraints_bounded Forall_lookup in hC.
        apply hC in hc as [].
        apply inherits_using_wf in h as (? & ? & ? & hwf & _)=> //.
        apply wf_tyI in hwf as [? [? [hlen ?]]]; simplify_eq.
        by rewrite hlen.
  Qed.

  Definition wf_cdef_constraints_ok cdef :=
    ok_constraints cdef.(constraints) cdef.(constraints).

  Definition mdef_ok Δ mdef : Prop :=
    map_Forall (λ _argname, ok_ty Δ) mdef.(methodargs) ∧ ok_ty Δ mdef.(methodrettype).

  Definition cdef_methods_ok cdef :=
    map_Forall (λ _mname, mdef_ok cdef.(constraints)) cdef.(classmethods).
End Ok.
