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

Definition C := {|
  classname := "C";
  superclass := None;
  generics := [Invariant];
  constraints := [(GenT 0, IntT)];
  classfields := {[ "x" := (Public, GenT 0)]};
  classmethods := ∅;
|}.

(* function push(T $_) : void { } *)
Definition Push := {|
  methodname := "push";
  methodargs := {[ "$v" := GenT 0]};
  methodrettype := NullT;
  methodbody := SkipC;
  methodret := NullE;
|}.

Definition V := {|
  classname := "V";
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
  SeqC (NewC "$v" "V" [IntT] ∅)
       (RuntimeCheckC "$c" (RCTag "C")
         (SeqC (GetC "$x" (VarE "$c") "x")
               (CallC "$_" (VarE "$v") "push" {["$v" := VarE "$x"]}))
         SkipC
       ).

Definition F := {|
  methodname := "f";
  methodargs := {[ "$c" := MixedT ]};
  methodrettype := NullT;
  methodbody := f;
  methodret := NullE;
|}.

Definition Test := {|
  classname := "Test";
  superclass := None;
  generics := [];
  constraints := [];
  classfields := ∅;
  classmethods := {[ "f" := F ]};
|}.

Local Instance PDC : ProgDefContext := { pdefs := {[ "C" := C; "V" := V; "Test" := Test ]} }.

(* Invalid constraint, so we can prove anything trivially *)
Local Instance SDTCC : SDTClassConstraints := {
  Δsdt := λ _ _ _, [(IntT, BoolT) ];
  Δsdt_m := λ _ _ _ _, [(IntT, BoolT) ];
}.


Local Instance SDTCP : SDTClassSpec.
Proof.
  split.
  - move => ????; apply Forall_singleton; by constructor.
  - move => ?????; apply Forall_singleton; by constructor.
  - by move => ????.
  - by move => ?????.
  - move => ?????; apply Forall_singleton; by constructor.
  - move => ??????; apply Forall_singleton; by constructor.
  - by move => ????.
  - move => ?????????.
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

Lemma wf_mdef_ty_f: wf_mdef_ty "Test" [] 0 (gen_targs 0) F.
Proof.
  rewrite /wf_mdef_ty.
  exists {| type_of_this := ("Test", gen_targs 0);
    ctxt := <["$v" := ClassT "V" [IntT]]> F.(methodargs); |}.
  split.
  { split.
    - rewrite /this_type /=.
      by econstructor.
    - rewrite /=.
      rewrite map_Forall_insert; last done.
      split.
      + econstructor => // k ty h.
        by apply list_lookup_singleton_Some in h as [? <-].
      + by apply map_Forall_singleton.
  }
  split.
  { rewrite /F /= /f.
    eapply SeqTy.
    - eapply NewTy.
      + econstructor => //.
        move => k ty h; by apply list_lookup_singleton_Some in h as [? <-].
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
        { eapply GetPubTy with (t := "C") (σ := [GenT 0]); last first.
          - change Public with (Public, GenT 0).1.
            by eapply HasField.
          - eapply ESubTy.
            + by constructor.
            + econstructor => //.
              move => k ty h; rewrite list_lookup_singleton_Some in h.
              by destruct h as [? <-].
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
        }
        eapply SubTy; last first.
        * eapply CallTy.
          { constructor.
            by rewrite /= lookup_insert_ne.
          }
          { by econstructor. }
          { by set_solver. }
          { move => k ty arg hk0 hk1.
            apply lookup_singleton_Some in hk1 as [<- <-].
            rewrite /Push /= in hk0.
            apply lookup_singleton_Some in hk0 as [? <-].
            eapply ESubTy.
            - by constructor.
            - apply wf_ty_subst => //.
              by apply Forall_singleton.
            - eapply bounded_subst => //; last by apply Forall_singleton.
              constructor; simpl.
              by lia.
            - by econstructor.
            - simpl.
              apply SubConstraint.
              by set_solver.
          }
        * split.
          { rewrite /this_type /=.
            constructor.
            by apply Forall_nil.
          }
          rewrite /= map_Forall_insert; last done.
          split.
          { constructor.
            by apply Forall_singleton.
          }
          apply map_Forall_singleton.
          by constructor.
        * split => /=.
          { by rewrite /local_tys_insert /= /this_type /=. }
          move => k ty h.
          apply lookup_insert_Some in h as [[<- <-] | [? h]].
          { by eexists. }
          apply lookup_singleton_Some in h as [<- <-].
          by eexists.
      + by constructor.
  }
  rewrite /F /=.
  by constructor.
Qed.
