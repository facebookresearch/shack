(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
From stdpp Require Import base strings gmap stringmap fin_maps.

From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import iprop own wsat.
From iris.algebra.lib Require Import gmap_view.

From shack Require Import lang progdef subtype ok typing.
From shack Require Import eval heap modality interp.

From shack.reflect Require Import lang progdef subtype.

(*
 * << SDT when T = Dynamic >>
 * class Box<T> {
 *   private T $x;
 *
 *   << SDT when T <: Dynamic >>
 *   function get(): T { $ret = $this->x; return $ret; }
 *
 *   << SDT when T :> Dynamic >>
 *   function set(T $y) : void { $this->x = $y; }
 * }
 *)
Definition Get := {|
  methodargs := ∅;
  methodrettype := GenT 0;
  methodbody := GetC "$ret" ThisE "$x";
  methodret := VarE "$ret";
  methodvisibility := Public;
|}.

Definition BoxSet := {|
  methodargs := {["$y" := GenT 0 ]};
  methodrettype := NullT;
  methodbody := SetC ThisE "$x" (VarE "$y");
  methodret := NullE;
  methodvisibility := Public;
|}.

Definition Box := {|
  superclass := None;
  generics := [Invariant];
  constraints := [];
  classfields := {["$x" := (Private, GenT 0)]};
  classmethods := {["set" := BoxSet; "get" := Get]};
|}.

(*
 * << SDT when T <: Dynamic >>
 * class ROBox<T> extends Box<T> {
 *   << SDT when True >>
 *   function set(mixed $y) : void { error }
 * }
 *)
Definition ROBoxSet := {|
  methodargs := {["$y" := MixedT ]};
  methodrettype := NullT;
  methodbody := ErrorC;
  methodret := NullE;
  methodvisibility := Public;
|}.

Definition ROBox := {|
  superclass := Some ("Box", [GenT 0]);
  generics := [Invariant];
  constraints := [];
  classfields := ∅;
  classmethods := {["set" := ROBoxSet ]};
|}.

Definition pdefs0: stringmap classDef := {[ "ROBox" := ROBox; "Box" := Box ]}.

Local Instance PDC : ProgDefContext := { pdefs := pdefs0 }.

Lemma pacc : ∀ c, Acc (λ x y, extends y x) c.
Proof.
  apply check_acc_defs_correct with (n := 100).
  by exact (I <: True).
Qed.

Local Instance PDA : ProgDefAcc  := { pacc := pacc }.

(* This is where we encode the <<SDT>> attribute *)
Definition BoxSDT := [(GenT 0, DynamicT); (DynamicT, GenT 0)].

Definition ROBoxSDT := [(GenT 0, DynamicT)].

Definition BoxGetSDT := [(GenT 0, DynamicT)].

Definition BoxSetSDT := [(DynamicT, GenT 0)].

Definition ROBoxSetSDT : list constraint := [].

(* TODO: move this in typing or subtype and add
 * wf/bounded lemmas.
 *)
Definition CFalse : constraint := (IntT, BoolT).

Definition SDT (t: tag)  : list constraint :=
  if String.eqb t "Box" then BoxSDT else
  if String.eqb t "ROBox" then ROBoxSDT else
  [CFalse]
.

Definition SDT_M (t: tag) (m: string) : list constraint :=
  if String.eqb t "Box" && String.eqb m "get" then BoxGetSDT else
  if String.eqb t "Box" && String.eqb m "set" then BoxSetSDT else
  if String.eqb t "ROBox" && String.eqb m "set" then ROBoxSetSDT else
  [CFalse]
.

Local Instance SDTCC : SDTClassConstraints := {
  Δsdt := SDT;
  Δsdt_m := SDT_M;
}.

Local Instance SDTCS : SDTClassSpec.
Proof.
  split.
  - rewrite /Δsdt /= /SDT => A k c.
    destruct (A =? "Box")%string.
    { rewrite /BoxSDT.
      case : k => [ | [ | k]] /=.
      - case => <-; by repeat constructor.
      - case => <-; by repeat constructor.
      - by rewrite lookup_nil.
    }
    destruct (A =? "ROBox")%string.
    { rewrite /ROBoxSDT.
      rewrite list_lookup_singleton.
      case : k => [ | k] //=.
      case => <-; by repeat constructor.
    }
    rewrite list_lookup_singleton.
    case : k => [ | k] //=.
    case => <-; by repeat constructor.
  - rewrite /Δsdt_m /= /SDT_M => A m k c.
    destruct (A =? "Box")%string eqn:h0 => /=.
    { destruct (m =? "get")%string => /=.
      { case : k => [ | k] /=.
        - case => <-; by repeat constructor.
        - by rewrite lookup_nil.
      }
      destruct (m =? "set")%string => /=.
      { case : k => [ | k] /=.
        - case => <-; by repeat constructor.
        - by rewrite lookup_nil.
      }
      destruct (A =? "ROBox")%string => //=.
      - rewrite list_lookup_singleton.
        case : k => [ | k] //=.
        case => <-; by repeat constructor.
      - rewrite list_lookup_singleton.
        case : k => [ | k] //=.
        case => <-; by repeat constructor.
    }
    destruct (A =? "ROBox")%string eqn:h1 => /=.
    { destruct (m =? "set")%string => /=.
      { by case : k => [ | k]. }
      rewrite list_lookup_singleton.
      case : k => [ | k] //=.
      case => <-; by repeat constructor.
    }
    rewrite list_lookup_singleton_Some => [[? <-]].
    by repeat constructor.
  - rewrite /Δsdt /= /SDT => A adef k c.
    rewrite lookup_insert_Some => [[[<- <-] | ]] /=.
    { rewrite /ROBoxSDT.
      rewrite list_lookup_singleton.
      case : k => [ | k] //=.
      case => <-; by repeat constructor.
    }
    case => ?; rewrite lookup_singleton_Some => [[<- <-]] /=.
    rewrite /BoxSDT.
    case : k => [ | [ | k]] /=.
    + case => <-; by repeat constructor.
    + case => <-; by repeat constructor.
    + by rewrite lookup_nil.
  - rewrite /Δsdt_m /= /SDT_M => A m adef k c.
    rewrite lookup_insert_Some => [[[<- <-] | ]] /=.
    { destruct (m =? "set")%string.
      + by rewrite /ROBoxSetSDT lookup_nil.
      + case : k => [ | k] //=.
        case => <-; by repeat constructor.
    }
    case => ?; rewrite lookup_singleton_Some => [[<- <-]] /=.
    rewrite /BoxGetSDT.
    destruct (m =? "get")%string eqn:h0.
    { rewrite list_lookup_singleton_Some => [[<- <-]].
      by repeat constructor.
    }
    destruct (m =? "set")%string.
    { rewrite /BoxSetSDT.
      rewrite list_lookup_singleton_Some => [[<- <-]].
      by repeat constructor.
    }
    rewrite list_lookup_singleton_Some => [[<- <-]].
    by repeat constructor.
  - rewrite /Δsdt /= /SDT => A k c.
    destruct (A =? "Box")%string.
    { rewrite /BoxSDT.
      case : k => [ | [ | k]] /=.
      - case => <-; by repeat constructor.
      - case => <-; by repeat constructor.
      - by rewrite lookup_nil.
    }
    destruct (A =? "ROBox")%string.
    { rewrite /ROBoxSDT.
      rewrite list_lookup_singleton.
      case : k => [ | k] //=.
      case => <-; by repeat constructor.
    }
    rewrite list_lookup_singleton.
    case : k => [ | k] //=.
    case => <-; by repeat constructor.
  - rewrite /Δsdt_m /= /SDT_M => A m k c.
    destruct (A =? "Box")%string eqn:h0 => /=.
    { destruct (m =? "get")%string => /=.
      { case : k => [ | k] /=.
        - case => <-; by repeat constructor.
        - by rewrite lookup_nil.
      }
      destruct (m =? "set")%string => /=.
      { case : k => [ | k] /=.
        - case => <-; by repeat constructor.
        - by rewrite lookup_nil.
      }
      destruct (A =? "ROBox")%string => //=.
      - rewrite list_lookup_singleton.
        case : k => [ | k] //=.
        case => <-; by repeat constructor.
      - rewrite list_lookup_singleton.
        case : k => [ | k] //=.
        case => <-; by repeat constructor.
    }
    destruct (A =? "ROBox")%string eqn:h1 => /=.
    { destruct (m =? "set")%string => /=.
      { by case : k => [ | k]. }
      rewrite list_lookup_singleton.
      case : k => [ | k] //=.
      case => <-; by repeat constructor.
    }
    rewrite list_lookup_singleton_Some => [[? <-]].
    by repeat constructor.
Qed.

Local Instance SDTCVS : SDTClassVarianceSpec.
Proof.
  split.
  move => Δ kd A adef σ0 σ1 hadef hσ.
  move => i c0 h.
  assert (hl0: length adef.(generics) = length σ0) by by eapply length_subtype_targs_v0.
  assert (hl1: length σ0 = length σ1).
  { rewrite -hl0; by eapply length_subtype_targs_v1. }
  apply list_lookup_fmap_inv in h as [c [-> hc]].
  rewrite /Δsdt /= /SDT /= in hc.
  rewrite lookup_insert_Some in hadef.
  destruct hadef as [[<- <-] | hadef]; simpl in *.
  { inv hσ; simpl in *.
    case: hl0 => hl0.
    symmetry in hl0.
    apply nil_length_inv in hl0; subst.
    case: hl1 => /= hl1.
    symmetry in hl1.
    apply nil_length_inv in hl1; subst.
    rewrite list_lookup_singleton_Some in hc.
    case: hc => ? <- /=.
    rewrite /subst_constraint /=.
    apply SubTrans with ty1.
    - apply subtype_weaken with Δ => //.
      by set_solver.
    - apply SubConstraint; by set_solver.
  }
  destruct hadef as (? & h).
  rewrite lookup_singleton_Some in h.
  destruct h as [<- <-]; simpl in *.
  inv hσ; simpl in *.
  case: hl0 => hl0.
  symmetry in hl0.
  apply nil_length_inv in hl0; subst.
  case: hl1 => /= hl1.
  symmetry in hl1.
  apply nil_length_inv in hl1; subst.
  rewrite /BoxSDT in hc.
  destruct i as [ | i]; simpl in *.
  - case : hc => <- /=.
    rewrite /subst_constraint /=.
    apply SubTrans with ty1.
    + apply subtype_weaken with Δ => //.
      by set_solver.
    + apply SubConstraint; by set_solver.
  - rewrite list_lookup_singleton_Some in hc.
    case: hc => ? <- /=.
    rewrite /subst_constraint /=.
    apply SubTrans with ty1.
    + apply SubConstraint; by set_solver.
    + apply subtype_weaken with Δ => //.
      by set_solver.
Qed.

Lemma has_fields_Box : has_fields "Box" {[ "$x" := (Private, GenT 0, "Box") ]}.
Proof.
  move => f vis fty orig; split => h.
  - inv h.
    + rewrite /pdefs /= lookup_insert_ne // lookup_insert in H.
      simplify_eq.
      rewrite /Box /= lookup_singleton_Some in H0.
      by destruct H0 as [<- <-].
    + by rewrite /pdefs /= lookup_insert_ne // lookup_insert in H; simplify_eq.
  - rewrite lookup_singleton_Some in h.
    destruct h as [<- [= <- <- <-]].
    change Private with (Private, GenT 0).1.
    by econstructor.
Qed.

Lemma has_fields_ROBox : has_fields "ROBox" {[ "$x" := (Private, GenT 0, "Box") ]}.
Proof.
  move => f vis fty orig; split => h.
  - inv h.
    + rewrite /pdefs /= lookup_insert in H.
      by simplify_eq.
    + rewrite /pdefs /= lookup_insert in H; simplify_eq.
      rewrite /ROBox /= in H1.
      case : H1 => ? <-.
      subst.
      move : has_fields_Box => hf.
      apply hf in H2.
      rewrite lookup_singleton_Some in H2.
      case : H2 => <-.
      by case => <- <- <-.
  - rewrite lookup_singleton_Some in h.
    destruct h as [<- [= <- <- <-]].
    change (GenT 0) with (subst_ty [GenT 0] (GenT 0)).
    eapply InheritsField => //.
    change Private with (Private, GenT 0).1.
    by econstructor.
Qed.

Lemma wf_extends_dyn : map_Forall wf_cdef_extends_dyn pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]].
  { exists Box; split => //.
    move => i c.
    rewrite /Δsdt /= /SDT /ROBoxSDT /BoxSDT.
    destruct ("ROBox" =? "Box")%string eqn:hfalse; first done.
    destruct ("ROBox" =? "ROBox")%string eqn:hfalse_; last done.
    rewrite /wf_cdef_extends_dyn_targs /=.
    rewrite list_lookup_singleton_Some => [[? <-]] /=.
    apply SubConstraint; by set_solver.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]] //.
Qed.

Lemma has_method_Box m o mdef:
  has_method m "Box" o mdef →
  (m = "get" ∧ o = "Box" ∧ mdef = Get) ∨
  (m = "set" ∧ o = "Box" ∧ mdef = BoxSet).
Proof.
  move => h; inv h; last first.
  { rewrite lookup_insert_ne // lookup_insert in H.
    by simplify_eq.
  }
  rewrite lookup_insert_ne // lookup_insert in H.
  simplify_eq.
  rewrite lookup_insert_Some in H0.
  case: H0 => [[? <-]|[?]].
  - by firstorder.
  - rewrite lookup_singleton_Some => h.
    by firstorder.
Qed.

Lemma has_method_ROBox m o mdef:
  has_method m "ROBox" o mdef →
  (m = "get" ∧ o = "Box" ∧ mdef = subst_mdef [GenT 0] Get) ∨
  (m = "set" ∧ o = "ROBox" ∧ mdef = ROBoxSet).
Proof.
  move => h; inv h.
  - rewrite lookup_insert // in H.
    simplify_eq.
    rewrite lookup_singleton_Some in H0.
    by firstorder.
  - rewrite lookup_insert // in H.
    simplify_eq.
    rewrite /ROBox /= in H1, H0.
    simplify_eq.
    rewrite lookup_singleton_None in H0.
    apply has_method_Box in H2.
    case : H2 => [ [<- [<- <-]]| ].
    { by left. }
    by case => h; subst.
Qed.

Lemma wf_parent : map_Forall (λ _cname, wf_cdef_parent) pdefs.
Proof.
  apply map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[? <-] | [?]].
  { split.
    + econstructor => //.
      by repeat constructor.
    + by repeat constructor.
  }
  rewrite lookup_insert_Some.
  by case => [[? <-] | [?]].
Qed.

Global Hint Resolve wf_parent : core.

Lemma wf_methods_dyn : map_Forall wf_cdef_methods_dyn_wf pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]].
  { move => m o mdef hm.
    apply has_method_ROBox in hm as [(-> & -> & ->) | (-> & -> & ->)].
    - exists [GenT 0].
      split.
      { apply inherits_using_extends => //.
        by econstructor.
      }
      move => i c /=.
      rewrite list_lookup_singleton_Some.
      case => ? <- /=.
      constructor; by set_solver.
    - exists (gen_targs (length ROBox.(generics))).
      split; first by constructor.
      move => i c /=.
      rewrite /SDT_M /ROBoxSetSDT /=.
      by rewrite lookup_nil.
  }
  rewrite lookup_singleton_Some.
  case => [<- <-].
  move => m o mdef hm.
  apply has_method_Box in hm as [(-> & -> & ->) | (-> & -> & ->)].
  + exists (gen_targs (length Box.(generics))).
    split; first by constructor.
    move => i c /=.
    rewrite list_lookup_singleton_Some.
    case => ? <-.
    constructor; by set_solver.
  + exists (gen_targs (length Box.(generics))).
    split; first by constructor.
    move => i c /=.
    rewrite list_lookup_singleton_Some.
    case => ? <-.
    constructor; by set_solver.
Qed.

Lemma wf_fields_dyn : map_Forall wf_cdef_fields_dyn_wf pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]].
  { move => fields hf.
    move : has_fields_ROBox => hf0.
    rewrite (has_fields_fun _ _ _  hf hf0).
    by apply map_Forall_singleton.
  }
  rewrite lookup_singleton_Some.
  case => [<- <-].
  move => fields hf.
  move : has_fields_Box => hf0.
  rewrite (has_fields_fun _ _ _  hf hf0).
  by apply map_Forall_singleton.
Qed.

Lemma wf_mdefs_dyn : map_Forall cdef_wf_mdef_dyn_ty pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]].
  { move => k m hm.
    rewrite lookup_singleton_Some in hm.
    case : hm => <- <-.
    rewrite /ROBox /= /ROBoxSet /SDT_M /= /ROBoxSetSDT /wf_mdef_dyn_ty /=.
    pose (Γ := (to_dyn <$> {["$y" := MixedT]} : local_tys)).
    assert (wf_lty Γ).
    { rewrite /Γ /=.
      apply map_Forall_lookup => i ty.
      rewrite lookup_fmap fmap_Some => [[ty0]].
      rewrite lookup_singleton_Some.
      by case => [[? <-]] ->.
    }
    exists Γ; split; first done.
    split.
    - constructor => //.
      apply map_Forall_lookup => i ty.
      rewrite lookup_fmap fmap_Some => [[ty0]].
      rewrite lookup_singleton_Some.
      by case => [[? <-]] ->.
    - apply ESubTy with NullT => //.
      + by constructor.
      + by constructor.
      + apply SubTrans with SupportDynT; by eauto.
  }
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]] //.
  { move => k m hm.
    rewrite lookup_insert_Some in hm.
    case : hm => [[<- <-] | ].
    - rewrite /wf_mdef_dyn_ty.
      pose (Γ := (to_dyn <$> {[ "$y" := GenT 0 ]} : local_tys)).
      assert (wf_lty Γ).
      { rewrite /Γ /=.
        apply map_Forall_lookup => i ty.
        rewrite lookup_fmap fmap_Some => [[ty0]].
        rewrite lookup_singleton_Some.
        by case => [[? <-]] ->.
      }
      exists Γ; split; first done.
      rewrite /BoxSet /= /SDT_M /= /BoxSetSDT /=.
      split.
      + eapply SetPrivTy => //.
        apply ESubTy with DynamicT => //=.
        { by constructor. }
        { constructor. by lia. }
        { by constructor. }
        { apply SubConstraint.
          by set_solver.
        }
      + apply ESubTy with NullT => //=.
        * by constructor.
        * by constructor.
        * apply SubTrans with SupportDynT; by eauto.
    - case => ?.
      rewrite lookup_singleton_Some => [[<- <-]].
      rewrite /wf_mdef_dyn_ty.
      pose (Γ := ({[ "$ret" := GenT 0 ]}: local_tys)).
      assert (wf_lty Γ).
      { rewrite /Γ /=.
        by apply map_Forall_singleton.
      }
      pose (Γ0 := (to_dyn <$> ∅ : local_tys)).
      exists Γ; split; first done.
      rewrite /Get /= /SDT_M /= /BoxGetSDT /=.
      split.
      + replace Γ with (<[ "$ret" := subst_ty (gen_targs 1) (GenT 0)]> Γ0) ; last first.
        { rewrite /Γ0 /Γ /=.
          f_equal.
          by rewrite fmap_empty insert_empty.
        }
        by eapply GetPrivTy.
      + apply ESubTy with (GenT 0) => //=.
        * by constructor.
        * by constructor.
        * apply SubConstraint.
          by set_solver.
  }
Qed.

Lemma helper_ext: ∀ A B σ0, extends_using A B σ0 → A = "ROBox" ∧ B = "Box" ∧ σ0 = [GenT 0].
Proof.
  move => A B σ0 h; inv h.
  rewrite /pdefs /= lookup_insert_Some in H.
  destruct H as [[<- <-] | [? H]].
  { split => //.
    rewrite /ROBox /= in H0; by simplify_eq.
  }
  rewrite lookup_singleton_Some in H.
  destruct H as [<- <-].
  by rewrite /Box /= in H0.
Qed.

Lemma helper_in_Box : ∀ T σt, inherits_using "Box" T σt → T = "Box" ∧ σt = [GenT 0].
Proof.
  move => T σt h; inv h.
  + rewrite /pdefs /=.
    do 1 (rewrite lookup_insert_ne // in H).
    rewrite lookup_insert in H.
    by simplify_eq.
  + apply helper_ext in H.
    destruct H; discriminate.
Qed.

Lemma helper_in_ROBox : ∀ T σt, inherits_using "ROBox" T σt →
  (T = "ROBox" ∧ σt = [GenT 0]) ∨
  (T = "Box" ∧ σt = [GenT 0]).
Proof.
  move => T σt h; inv h.
  + rewrite /pdefs /=.
    rewrite lookup_insert in H.
    left.
    by simplify_eq.
  + apply helper_ext in H.
    destruct H as [_ [-> ->]]; right.
    apply helper_in_Box in H0 as [-> ->].
    done.
Qed.

Lemma helper_in: ∀ A B σ0, inherits_using A B σ0 →
     (A = "Box" ∧ B = "Box" ∧ σ0 = [GenT 0]) ∨
     (A = "ROBox" ∧ B = "Box" ∧ σ0 = [GenT 0]) ∨
     (A = "ROBox" ∧ B = "ROBox" ∧ σ0 = [GenT 0]).
Proof.
  move => A B σ0 h.
  inv h.
  + rewrite /pdefs /=.
    rewrite lookup_insert_Some in H.
    destruct H as [[<- <-]|[? H]].
    { by right; right. }
    rewrite lookup_singleton_Some in H.
    case : H => <- <-.
    by left.
  + apply helper_ext in H as [-> [-> ->]].
    apply helper_in_Box in H0 as [-> ->].
    by right; left.
Qed.

Lemma wf_override : wf_method_override.
Proof.
  move => A B adef bdef m σ0 mA mB hA hB hin hmA hmB.
  apply helper_in in hin.
  destruct hin as [[-> [-> ->]] | hin].
  { rewrite /pdefs /= in hA, hB.
    rewrite lookup_insert_ne // in hA.
    rewrite lookup_insert_ne // in hB.
    rewrite !lookup_insert in hA, hB.
    simplify_eq.
    change [GenT 0] with (gen_targs 1).
    rewrite /Box /= in hmA.
    rewrite lookup_insert_Some in hmA.
    case: hmA => [[? <-] | ].
    - rewrite /Box /BoxSet /=.
      rewrite subst_mdef_gen_targs; first by apply mdef_incl_reflexive.
      split => /=.
      { apply map_Forall_singleton.
        by repeat constructor.
      }
      split; first by constructor.
      split; first by repeat constructor.
      by repeat constructor.
    - case => ?.
      rewrite lookup_singleton_Some => [[? <-]].
      rewrite /= subst_mdef_gen_targs; first by apply mdef_incl_reflexive.
      split => /=; first by apply map_Forall_empty.
      split; first by repeat constructor.
      split; first by repeat constructor.
      by repeat constructor.
  }
  destruct hin as [[-> [-> ->]] | hin].
  { rewrite /pdefs /= in hA, hB.
    rewrite lookup_insert in hA.
    rewrite  lookup_insert_ne // lookup_insert in hB.
    simplify_eq.
    rewrite /ROBox /= lookup_singleton_Some in hmA.
    destruct hmA as [<- <-].
    rewrite /Box /= lookup_insert in hmB.
    simplify_eq.
    rewrite /ROBox /ROBoxSet /BoxSet /=.
    split; last split => /=.
    - by set_solver.
    - move => k A B.
      rewrite lookup_singleton_Some => [[<- <-]] /=.
      rewrite lookup_fmap lookup_insert /= => [[<-]].
      by eauto.
    - by eauto.
  }
  destruct hin as [-> [-> ->]].
  rewrite /pdefs /= in hA, hB.
  rewrite !lookup_insert in hA, hB.
  simplify_eq.
  change [GenT 0] with (gen_targs 1).
  rewrite /ROBox /= in hmA.
  rewrite lookup_insert_Some in hmA.
  case: hmA => [[? <-] | ].
  - rewrite /ROBoxSet /=.
    rewrite subst_mdef_gen_targs; first by apply mdef_incl_reflexive.
    split => /=.
    { apply map_Forall_singleton.
      by repeat constructor.
    }
    split; first by constructor.
    split; first by repeat constructor.
    by repeat constructor.
  - case => ?.
    by rewrite lookup_empty.
Qed.

Lemma wf_fields : map_Forall (λ _cname, wf_cdef_fields) pdefs.
Proof.
  apply (wf_fields_correct _ 100).
  by exact (I <: True).
Qed.

Lemma wf_fields_bounded : map_Forall (λ _cname, wf_cdef_fields_bounded) pdefs.
Proof.
  apply wf_cdef_fields_bounded_context_correct.
  by exact (I <: True).
Qed.

Lemma wf_fields_wf  : map_Forall (λ _cname, wf_cdef_fields_wf) pdefs.
Proof.
  apply: wf_cdef_fields_wf_context_correct.
  exact (I <: True).
Qed.

Lemma wf_fields_mono : map_Forall (λ _cname, wf_field_mono) pdefs.
Proof.
  apply wf_fields_mono_correct.
  exact (I <: True).
Qed.

Lemma wf_methods_bounded : map_Forall (λ _cname, cdef_methods_bounded) pdefs.
Proof.
  apply cdef_methods_bounded_context_correct.
  by exact (I <: True).
Qed.

Lemma wf_methods_wf : map_Forall (λ _cname, wf_cdef_methods_wf) pdefs.
Proof.
  apply: wf_cdef_methods_wf_context_correct.
  exact (I <: True).
Qed.

Lemma wf_methods_mono : map_Forall (λ _cname, wf_cdef_methods_mono) pdefs.
Proof.
  apply wf_methods_mono_correct.
  exact (I <: True).
Qed.

Lemma wf_mdefs : map_Forall cdef_wf_mdef_ty pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]].
  { move => k m hm.
    rewrite lookup_singleton_Some in hm.
    case : hm => ? <-.
    rewrite /ROBox /= /ROBoxSet /wf_mdef_dyn_ty /=.
    pose (Γ := ({["$y" := MixedT]}: local_tys)).
    assert (wf_lty Γ).
    { rewrite /Γ /=.
      by apply map_Forall_singleton.
    }
    exists Γ; split; first done.
    split.
    - constructor => //.
      by apply map_Forall_singleton.
    - by constructor.
  }
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]] //.
  { move => k m hm.
    rewrite lookup_insert_Some in hm.
    case : hm => [[? <-] | ].
    - rewrite /wf_mdef_dyn_ty.
      pose (Γ := ({[ "$y" := GenT 0 ]}: local_tys)).
      assert (wf_lty Γ).
      { rewrite /Γ /=.
        by apply map_Forall_singleton.
      }
      exists Γ; split; first done.
      rewrite /BoxSet /= /BoxSetSDT /=.
      split.
      + eapply SetPrivTy => //.
        change Private with (Private, GenT 0).1.
        by econstructor.
      + by constructor.
    - case => ?.
      rewrite lookup_singleton_Some => [[? <-]].
      rewrite /wf_mdef_dyn_ty.
      pose (Γ := ({[ "$ret" := GenT 0 ]} : local_tys)).
      assert (wf_lty Γ).
      { rewrite /Γ /=.
        by apply map_Forall_singleton.
      }
      pose (Γ0 := (∅ : local_tys)).
      exists Γ; split; first done.
      rewrite /Get /= /BoxGetSDT /=.
      split.
      + replace Γ with (<[ "$ret" := subst_ty (gen_targs 1) (GenT 0)]> Γ0) ; last first.
        { rewrite /Γ0 /Γ /=.
          by f_equal.
        }
        by eapply GetPrivTy.
      + by constructor.
  }
Qed.

Lemma wf_mono : map_Forall (λ _cname, wf_cdef_mono) pdefs.
Proof.
  apply wf_mono_correct.
  exact (I <: True).
Qed.

Lemma wf_constraints_wf : map_Forall (λ _cname, wf_cdef_constraints_wf) pdefs.
Proof.
  apply: wf_cdef_constraints_wf_context_correct.
  exact (I <: True).
Qed.

Lemma wf_constraints_bounded : map_Forall (λ _cname, wf_cdef_constraints_bounded) pdefs.
Proof.
  apply wf_cdef_constraints_bounded_context_correct.
  by exact (I <: True).
Qed.

Lemma wf_parent_ok : map_Forall (λ _cname, wf_cdef_parent_ok) pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_cdef_parent_ok /=.
    econstructor => // i ty.
    rewrite list_lookup_singleton_Some => [[? <-]].
    by constructor.
  }
  rewrite lookup_singleton_Some.
  case => [? <-].
  by rewrite /wf_cdef_parent_ok.
Qed.

Lemma wf_constraints_ok : map_Forall (λ _cname, wf_cdef_constraints_ok) pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  {  rewrite /wf_cdef_constraints_ok /ROBox /=.
    by constructor.
  }
  rewrite lookup_singleton_Some => [[? <-]].
  { rewrite /wf_cdef_constraints_ok /Box /=.
    by constructor.
  }
Qed.

Lemma wf_methods_ok : map_Forall (λ _cname, cdef_methods_ok) pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /cdef_methods_ok /ROBox /=.
    apply map_Forall_singleton.
    rewrite /mdef_ok /=.
    split; last by constructor.
    apply map_Forall_singleton.
    by constructor.
  }
  rewrite lookup_singleton_Some => [[? <-]].
  rewrite /cdef_methods_ok /Box /=.
  rewrite map_Forall_lookup => x mx.
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  * rewrite /mdef_ok /BoxSet /=.
    split; last by constructor.
    apply map_Forall_singleton.
    by constructor.
  * rewrite lookup_singleton_Some => [[? <-]].
    rewrite /mdef_ok /Get /=.
    split; first by apply map_Forall_empty.
    by constructor.
Qed.

Lemma wf_constraints_no_this: map_Forall (λ _ : string, wf_cdef_constraints_no_this) pdefs.
Proof.
 apply wf_constraints_no_this_correct.
  by exact (I <: True).
Qed.

Lemma wf: wf_cdefs.
Proof.
  split.
  by apply wf_parent.
  by apply wf_parent_ok.
  by apply wf_constraints_wf.
  by apply wf_constraints_ok.
  by apply wf_constraints_bounded.
  by apply wf_constraints_no_this.
  by apply wf_override.
  by apply wf_fields.
  by apply wf_fields_bounded.
  by apply wf_fields_wf.
  by apply wf_fields_mono.
  by apply wf_methods_bounded.
  by apply wf_methods_wf.
  by apply wf_methods_mono.
  by apply wf_methods_ok.
  by apply wf_mdefs.
  by apply wf_mono.
  by apply wf_extends_dyn.
  by apply wf_methods_dyn.
  by apply wf_fields_dyn.
  by apply wf_mdefs_dyn.
Qed.
