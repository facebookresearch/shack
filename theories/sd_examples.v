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

From shack Require Import lang progdef subtype typing eval heap modality interp soundness.

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
  methodname := "get";
  methodargs := ∅;
  methodrettype := GenT 0;
  methodbody := GetC "$ret" ThisE "$x";
  methodret := VarE "$ret";
|}.

Definition BoxSet := {|
  methodname := "set";
  methodargs := {["$y" := GenT 0 ]};
  methodrettype := NullT;
  methodbody := SetC ThisE "$x" (VarE "$y");
  methodret := NullE;
|}.

Definition Box := {|
  classname := "Box";
  superclass := None;
  generics := [Invariant];
  constraints := [];
  classfields := {["$x" := (Private, GenT 0)]};
  classmethods := {["set" := BoxSet; "get" := Get]};
|}.

(*
 * << SDT when T <: Dynamic >>
 * class ROBox<+T> extends Box<T> {
 *   << SDT when True >>
 *   function set(mixed $y) : void { error }
 * }
 *)
Definition ROBoxSet := {|
  methodname := "set";
  methodargs := {["$y" := MixedT ]};
  methodrettype := NullT;
  methodbody := ErrorC;
  methodret := NullE;
|}.

Definition ROBox := {|
  classname := "ROBox";
  superclass := Some ("Box", [GenT 0]);
  generics := [Covariant];
  constraints := [];
  classfields := ∅;
  classmethods := {["set" := ROBoxSet ]};
|}.

Local Instance PDC : ProgDefContext := {
  pdefs := {[ "ROBox" := ROBox; "Box" := Box ]};
}.

(* This is where we encode the <<SDT>> attribute *)
Definition BoxSDT (σ: list lang_ty) :=
  (subst_ty σ (GenT 0), DynamicT) :: (DynamicT, subst_ty σ (GenT 0)) :: [].

Definition ROBoxSDT (σ: list lang_ty) :=
  (subst_ty σ (GenT 0), DynamicT) :: [].

Definition BoxGetSDT (σ: list lang_ty) :=
  (subst_ty σ (GenT 0), DynamicT) :: [].

Definition BoxSetSDT (σ: list lang_ty) :=
  (DynamicT, subst_ty σ (GenT 0)) :: [].

Definition ROBoxSetSDT (_: list lang_ty) : list constraint := [].

Definition SDT (t: tag) (_ : list variance) (σ : list lang_ty) : list constraint :=
  if String.eqb t "Box" then BoxSDT σ else
  if String.eqb t "ROBox" then ROBoxSDT σ else
  (IntT, BoolT) :: []
.

Definition SDT_M (t: tag) (m: string) (_ : list variance) (σ : list lang_ty) : list constraint :=
  if String.eqb t "Box" && String.eqb m "get" then BoxGetSDT σ else
  if String.eqb t "Box" && String.eqb m "set" then BoxSetSDT σ else
  if String.eqb t "ROBox" && String.eqb m "set" then ROBoxSetSDT σ else
  (IntT, BoolT) :: []
.

Local Instance SDTCC : SDTClassConstraints := {
  Δsdt := SDT;
  Δsdt_m := SDT_M;
}.

Local Instance SDTCP : SDTClassSpec.
Proof.
  split.
  - move => A ? σ /Forall_lookup hwf.
    apply Forall_lookup => k c.
    rewrite /Δsdt /= /SDT.
    destruct (A =? "Box")%string.
    { rewrite /BoxSDT.
      case : k => [ | [ | k]] /=.
      - case => <-.
        destruct (σ !! 0) as [ ty | ] eqn:h; last by split; constructor.
        by apply hwf in h; split.
      - case => <-.
        destruct (σ !! 0) as [ ty | ] eqn:h; last by split; constructor.
        by apply hwf in h; split.
      - by rewrite lookup_nil.
    }
    destruct (A =? "ROBox")%string.
    { rewrite /ROBoxSDT.
      rewrite list_lookup_singleton.
      case : k => [ | k] //=.
      case => <-.
      destruct (σ !! 0) as [ ty | ] eqn:h; last by split; constructor.
      by apply hwf in h; split.
    }
    rewrite list_lookup_singleton.
    case : k => [ | k] //=.
    case => <-.
    by split.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

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

Lemma wf_methods_dyn : map_Forall wf_cdef_methods_dyn_wf pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]].
  { move => m o mdef hm.
    apply has_method_ROBox in hm as [(-> & -> & ->) | (-> & -> & ->)].
    - exists Box, [GenT 0]; split => //.
      split; first by eauto.
      move => i c /=.
      rewrite list_lookup_singleton_Some.
      case => ? <- /=.
      constructor; by set_solver.
    - exists ROBox, (gen_targs (length ROBox.(generics))); split => //.
      split; first by constructor.
      move => i c /=.
      rewrite /SDT_M /ROBoxSetSDT /=.
      by rewrite lookup_nil.
  }
  rewrite lookup_singleton_Some.
  case => [<- <-].
  move => m o mdef hm.
  apply has_method_Box in hm as [(-> & -> & ->) | (-> & -> & ->)].
  + exists Box, (gen_targs (length Box.(generics))); split => //.
    split; first by constructor.
    move => i c /=.
    rewrite list_lookup_singleton_Some.
    case => ? <-.
    constructor; by set_solver.
  + exists Box, (gen_targs (length Box.(generics))); split => //.
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
    pose (Γ := {|
        type_of_this := ("ROBox", gen_targs 1);
        ctxt := to_dyn <$> {["$y" := MixedT]};
      |}
      ).
    assert (wf_lty Γ).
    { split => //.
      - rewrite /this_type /=.
        apply wf_ty_class with ROBox => //.
        by apply gen_targs_wf_2.
      - rewrite /Γ /=.
        apply map_Forall_lookup => i ty.
        rewrite lookup_fmap fmap_Some => [[ty0]].
        rewrite lookup_singleton_Some.
        by case => [[? <-]] ->.
    }
    exists Γ; split; first done.
    split.
    - constructor; first done.
      constructor; first by repeat constructor.
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
      pose (Γ := {|
        type_of_this := ("Box", gen_targs 1);
        ctxt := to_dyn <$> {[ "$y" := GenT 0 ]};
      |}
      ).
      assert (wf_lty Γ).
      { split => //.
        - rewrite /this_type /=.
          apply wf_ty_class with Box => //.
          by apply gen_targs_wf_2.
        - rewrite /Γ /=.
          apply map_Forall_lookup => i ty.
          rewrite lookup_fmap fmap_Some => [[ty0]].
          rewrite lookup_singleton_Some.
          by case => [[? <-]] ->.
      }
      exists Γ; split; first done.
      rewrite /BoxSet /= /SDT_M /= /BoxSetSDT /=.
      split.
      + eapply SetPrivTy => //.
        * change Private with (Private, GenT 0).1.
          by econstructor.
        * apply ESubTy with DynamicT => //=.
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
      pose (Γ := {|
        type_of_this := ("Box", gen_targs 1);
        ctxt := {[ "$ret" := GenT 0 ]};
      |}
      ).
      assert (wf_lty Γ).
      { split => //.
        - rewrite /this_type /=.
          apply wf_ty_class with Box => //.
          by apply gen_targs_wf_2.
        - rewrite /Γ /=.
          by apply map_Forall_singleton.
      }
      pose (Γ0 := {| type_of_this := ("Box", gen_targs 1); ctxt := to_dyn <$> ∅ |}).
      exists Γ; split; first done.
      rewrite /Get /= /SDT_M /= /BoxGetSDT /=.
      split.
      + replace Γ with (<[ "$ret" := subst_ty (gen_targs 1) (GenT 0)]> Γ0) ; last first.
        { rewrite /Γ0 /Γ /= /local_tys_insert /=.
          f_equal.
          by rewrite fmap_empty insert_empty.
        }
        eapply GetPrivTy => //.
        change Private with (Private, GenT 0).1.
        by econstructor.
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
  + apply helper_ext in H.
    destruct H; discriminate.
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
    by right; left.
  + apply helper_ext in H as [-> [-> ->]].
    apply helper_in_Box in H0 as [-> ->].
    by right; left.
Qed.

Lemma wf_override : wf_method_override pdefs.
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
    rewrite subst_mdef_gen_targs; first by apply mdef_incl_reflexive.
    rewrite /Box /= in hmA.
    rewrite lookup_insert_Some in hmA.
    case: hmA => [[? <-] | ].
    - rewrite /Box /BoxSet /=.
      split => /=.
      { apply map_Forall_singleton.
        by repeat constructor.
      }
      split; first by constructor.
      split; first by repeat constructor.
      by repeat constructor.
    - case => ?.
      rewrite lookup_singleton_Some => [[? <-]].
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
  rewrite subst_mdef_gen_targs; first by apply mdef_incl_reflexive.
  rewrite /ROBox /= in hmA.
  rewrite lookup_insert_Some in hmA.
  case: hmA => [[? <-] | ].
  - rewrite /ROBoxSet /=.
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
