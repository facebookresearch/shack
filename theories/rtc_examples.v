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

From shack Require Import lang progdef subtype typing eval heap.
From shack Require Import modality interp soundness.

From shack.reflect Require Import progdef.

Definition C := {|
  superclass := None;
  generics := [Invariant];
  constraints := [(GenT 0, IntT)];
  classfields := {[ "x" := (Public, GenT 0)]};
  classmethods := ∅;
|}.

(* function push(T $_) : void { } *)
Definition Push := {|
  methodargs := {[ "$v" := GenT 0]};
  methodrettype := NullT;
  methodbody := SkipC;
  methodret := NullE;
  methodvisibility := Public;
|}.

Definition V := {|
  superclass := None;
  generics := [Covariant];
  constraints := [];
  classfields := ∅;
  classmethods := {[ "push" := Push ]};
|}.

(* function f(mixed $c) : void {
  $v = new V<int>();

  if $c is C<_> {
     $v.push($c->x);
  }
}
*)
Definition f : cmd :=
  SeqC (NewC "$v" "V" (Some [IntT]) ∅)
       (RuntimeCheckC "$c" (RCTag "C")
         (SeqC (GetC "$x" (VarE "$c") "x")
               (CallC "$_" (VarE "$v") "push" {["$v" := VarE "$x"]}))
         SkipC
       ).

Definition F := {|
  methodargs := {[ "$c" := MixedT ]};
  methodrettype := NullT;
  methodbody := f;
  methodret := NullE;
  methodvisibility := Public;
|}.

Definition Test := {|
  superclass := None;
  generics := [];
  constraints := [];
  classfields := ∅;
  classmethods := {[ "f" := F ]};
|}.

Definition pdefs0: stringmap classDef :=
  {[ "C" := C; "V" := V; "Test" := Test ]}.
Local Instance PDC : ProgDefContext := { pdefs := pdefs0 }.

Lemma pacc : ∀ c, Acc (λ x y, extends y x) c.
Proof.
  apply check_acc_defs_correct with (n := 100).
  by exact (I <: True).
Qed.

Local Instance PDA : ProgDefAcc  := { pacc := pacc }.

(* Invalid constraint, so we can prove anything trivially *)
Local Instance SDTCC : SDTClassConstraints := {
  Δsdt := λ _, [(IntT, BoolT) ];
  Δsdt_m := λ _ _, [(IntT, BoolT) ];
}.

Local Instance SDTCS : SDTClassSpec.
Proof.
  split.
  - move => ???; rewrite list_lookup_singleton_Some => [[? <-]]; by constructor.
  - move => ????; rewrite list_lookup_singleton_Some => [[? <-]]; by constructor.
  - move => ?????; rewrite list_lookup_singleton_Some => [[? <-]]; by constructor.
  - move => ??????; rewrite list_lookup_singleton_Some => [[? <-]]; by constructor.
  - move => ???; rewrite list_lookup_singleton_Some => [[? <-]]; by constructor.
  - move => ????; rewrite list_lookup_singleton_Some => [[? <-]]; by constructor.
Qed.

Local Instance SDTCVS : SDTClassVarianceSpec.
Proof.
  split.
  move => ????????.
  move => ??.
  rewrite list_lookup_singleton_Some.
  case => ? <- /=.
  apply SubConstraint.
  by set_solver.
Qed.

Lemma Cfields : has_fields "C" {[ "x" := ((Public, GenT 0), "C") ]}.
Proof.
  move => f ???; split => h.
  - inv h.
    + rewrite lookup_insert in H.
      case : H => ?; subst.
      rewrite /= in H0.
      apply lookup_singleton_Some in H0 as [<- <-].
      by rewrite lookup_insert.
    + rewrite lookup_insert in H.
      case : H => ?; subst.
      by simpl in H1.
  - apply lookup_singleton_Some in h as [? ?].
    case: H0 => <- <- <-.
    change Public with (Public, GenT 0).1.
    econstructor => //.
    by rewrite -H.
Qed.

Lemma Vfields: has_fields "V" ∅.
Proof.
  move => f ???; split => h.
  - inv h.
    { rewrite lookup_insert_ne // lookup_insert in H.
      case : H => ?; subst.
      by rewrite lookup_empty in H0.
    }
    rewrite lookup_insert_ne // lookup_insert in H.
    case : H => ?; subst.
    by simpl in H1.
  - by rewrite lookup_empty in h.
Qed.

Lemma wf_mdef_ty_f: wf_mdef_ty "Test" [(ThisT, ClassT false "Test" [])] 0 F.
Proof.
  rewrite /wf_mdef_ty.
  exists (<["$v" := ClassT true "V" [IntT]]> F.(methodargs)).
  split.
  {rewrite /= /wf_lty.
    rewrite map_Forall_insert; last done.
    split.
    + eapply WfClass => //.
      by constructor.
    + by apply map_Forall_singleton.
  }
  split.
  { rewrite /F /= /f.
    eapply SeqTy.
    - eapply NewTy.
      + reflexivity.
      + econstructor => //.
        by constructor.
      + constructor.
        by apply Forall_singleton.
      + econstructor => //.
        move => k ty h; apply list_lookup_singleton_Some in h as [? <-].
        by constructor.
      + by exact Vfields.
      + by rewrite !dom_empty_L.
      + by move => ?????.
    - eapply TagCheckTy.
      + by rewrite /= lookup_insert_ne.
      + done.
      + rewrite /=.
        eapply SeqTy.
        { eapply GetPubTy with (t := "C") (σ := [GenT 0]) (fty := GenT 0).
          - eapply ESubTy.
            + by constructor.
            + econstructor => //.
              by constructor.
            + constructor.
              apply Forall_singleton.
              constructor; by lia.
            + econstructor => //.
              * move => i ty h.
                rewrite list_lookup_singleton_Some in h.
                destruct h as [? <-].
                by constructor.
              * move => i [c0 c1] hc.
                rewrite /C /= list_lookup_singleton_Some in hc.
                destruct hc as [? hc].
                case : hc => <- <- /=.
                apply SubConstraint.
                by set_solver.
            + by econstructor.
          - change Public with (Public, GenT 0).1.
            by eapply HasField.
          - by right.
        }
        eapply SubTy; last first.
        * eapply CallPubTy.
          { constructor.
            by rewrite /= lookup_insert_ne.
          }
          { by econstructor. }
          { by left. }
          { done. }
          { by set_solver. }
          { move => k ty arg hk0 hk1.
            apply lookup_singleton_Some in hk1 as [<- <-].
            rewrite /Push /= in hk0.
            apply lookup_singleton_Some in hk0 as [? <-].
            eapply ESubTy.
            - by constructor.
            - apply wf_ty_subst => //.
              + by apply Forall_singleton.
              + by constructor.
            - eapply bounded_subst => //; last by apply Forall_singleton.
              constructor; simpl.
              by lia.
            - by econstructor.
            - simpl.
              apply SubConstraint.
              by set_solver.
          }
        * rewrite /bounded_lty /= map_Forall_insert; last done.
          split.
          { constructor.
            by apply Forall_singleton.
          }
          apply map_Forall_singleton.
          by constructor.
        * move => k ty h.
          apply lookup_insert_Some in h as [[<- <-] | [? h]].
          { by eexists. }
          apply lookup_singleton_Some in h as [<- <-].
          by eexists.
      + by constructor.
  }
  rewrite /F /=.
  by constructor.
Qed.
