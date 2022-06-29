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

Definition like (T: lang_ty) : lang_ty := UnionT T DynamicT.

(*
class SDBox<T as Dynamic> {
  public function __construct(private ~T $x) {}
  public function get() : ~T {return $this->x;}
  public function set(~T $y) : void {$this->x = $y;}
}
*)
Definition Get := {|
  methodname := "get";
  methodargs := ∅;
  methodrettype := like (GenT 0);
  methodbody := GetC "$ret" ThisE "$data";
  methodret := VarE "$ret";
  method_support_dynamic := true;
|}.

Definition FunSet := {|
  methodname := "set";
  methodargs := {["$data" := like (GenT 0) ]};
  methodrettype := NullT;
  methodbody := SetC ThisE "$data" (VarE "$data");
  methodret := NullE;
  method_support_dynamic := true;
|}.

Definition SDBox := {|
  classname := "SDBox";
  superclass := None;
  generics := [Invariant];
  constraints := [(GenT 0, DynamicT)];
  classfields := {["$data" := (Private, like (GenT 0))]};
  classmethods := {["set" := FunSet; "get" := Get]};
  support_dynamic := true;
|}.

(* Test functions:
   <<SD>>
   function test0() : int {
     return 2;
   }

   // Not SD
   function test1(): Dynamic {
     return Upcast(2, Dynamic);
   }
*)
Definition Test0 := {|
  methodname := "test0";
  methodargs := ∅;
  methodrettype := IntT;
  methodbody := SkipC;
  methodret := IntE 2;
  method_support_dynamic := true;
|}.

Definition Test1 := {|
  methodname := "test1";
  methodargs := ∅;
  methodrettype := DynamicT;
  methodbody := SkipC;
  methodret := UpcastE (IntE 2) DynamicT;
  method_support_dynamic := false;
|}.

Definition Test := {|
  classname := "test";
  superclass := None;
  generics := [];
  constraints := [];
  classfields := ∅;
  classmethods := {["test0" := Test0; "test1" := Test1]};
  support_dynamic := false;
 |}.

(* Main program:
   function main(): bool {
     return true;
   }
*)

Definition EntryPoint := {|
  methodname := "entry_point";
  methodargs := ∅;
  methodrettype := BoolT;
  methodbody := SkipC;
  methodret := BoolE true;
  method_support_dynamic := false;
|}.

Definition Main := {|
  classname := "Main";
  superclass := None;
  generics := [];
  constraints := [];
  classfields := ∅;
  classmethods := {["entry_point" := EntryPoint]};
  support_dynamic := false;
 |}.

Local Instance PDC : ProgDefContext := { pdefs := {[ "SDBox" := SDBox; "Test" := Test; "Main" := Main ]} }.

Lemma helper_ext: ∀ A B σ0, extends_using A B σ0 → False.
Proof.
  move => A B σ0 h; inv h.
  rewrite /pdefs /= lookup_insert_Some in H.
  destruct H as [[<- <-] | [? H]].
  { by rewrite /SDBox in H0. }
  rewrite lookup_insert_Some in H.
  destruct H as [[<- <-] | [? H]].
  { by rewrite /Test in H0. }
  rewrite lookup_singleton_Some in H.
  destruct H as [<- <-].
  rewrite /Main in H0; discriminate.
Qed.

Lemma helper_in_Main : ∀ T σt, inherits_using "Main" T σt → T = "Main" ∧ σt = [].
Proof.
  move => T σt h; inv h.
  + do 2 (rewrite lookup_insert_ne // in H).
    rewrite lookup_singleton_Some in H.
    by case : H => _ <-.
  + by apply helper_ext in H.
  + by apply helper_ext in H.
Qed.

Lemma helper_in_Test : ∀ T σt, inherits_using "Test" T σt → T = "Test" ∧ σt = [].
Proof.
  move => T σt h; inv h.
  + rewrite /pdefs /= in H.
    rewrite lookup_insert_ne // in H.
    rewrite lookup_insert in H.
    by case : H => <-.
  + by apply helper_ext in H.
  + by apply helper_ext in H.
Qed.

Lemma helper_in_Box : ∀ T σt, inherits_using "SDBox" T σt → T = "SDBox" ∧ σt = [GenT 0].
Proof.
  move => T σt h; inv h.
  + rewrite /pdefs /= in H.
    rewrite lookup_insert in H.
    by case : H => <-.
  + by apply helper_ext in H.
  + by apply helper_ext in H.
Qed.

Lemma helper_in: ∀ A B σ0, inherits_using A B σ0 →
     (A = "SDBox" ∧ B = "SDBox" ∧ σ0 = [GenT 0]) ∨
     (A = "Main" ∧ B = "Main" ∧ σ0 = []) ∨
     (A = "Test" ∧ B = "Test" ∧ σ0 = []).
Proof.
  move => A B σ0 h.
  inv h.
  + rewrite /pdefs /=.
    rewrite lookup_insert_Some in H.
    destruct H as [[<- ?]|[? H]]; first by left; rewrite -H.
    rewrite lookup_insert_Some in H.
    destruct H as [[<- ?]|[? H]]; first by right; right; rewrite -H.
    rewrite lookup_singleton_Some in H.
    destruct H as [<- <-]; by right; left.
  + by apply helper_ext in H.
  + by apply helper_ext in H.
Qed.

Lemma wf_mdefs : map_Forall cdef_wf_mdef_ty pdefs.
Proof.
  apply map_Forall_lookup => cname cdef h.
  rewrite /pdefs /= in h.
  rewrite lookup_insert_Some in h.
  destruct h as [[<- <-] | [? h]].
  { rewrite /cdef_wf_mdef_ty.
    apply map_Forall_lookup => mname mdef h.
    rewrite /SDBox /= in h.
    rewrite lookup_insert_Some in h.
    destruct h as [[<- <-] | [? h]].
    + rewrite /wf_mdef_ty /SDBox /=.
      eexists.
      split; first last.
      { split.
        * econstructor => //=.
          { change Private with (Private, like (GenT 0)).1.
            by eapply HasField.
          }
          { by econstructor. }
        * by econstructor.
      }
      split => /=.
      { rewrite /this_type /=.
        econstructor => //.
        by apply gen_targs_wf.
      }
      apply map_Forall_lookup => s ? h.
      apply lookup_singleton_Some in h.
      destruct h as [? <-]; by constructor.
    + rewrite lookup_singleton_Some in h.
      destruct h as [? <-].
      rewrite /SDBox /= /Get /=.
      eexists => /=.
      split; first last.
      { split.
        * econstructor => //=.
          change Private with (Private, like (GenT 0)).1.
          by eapply HasField.
        * by econstructor.
      }
      split => /=.
      { rewrite /this_type /=.
        econstructor => //.
        by apply gen_targs_wf.
      }
      rewrite insert_empty.
      apply map_Forall_singleton.
      by repeat constructor.
  }
  rewrite lookup_insert_Some in h.
  destruct h as [[<- <-] | [? h]].
  { rewrite /cdef_wf_mdef_ty /wf_mdef_ty /Test /=.
    rewrite map_Forall_lookup => mnane mdef h.
    rewrite lookup_insert_Some in h.
    destruct h as [[<- <-] | [? h]].
    + eexists.
      split; first last.
      { split.
        * by econstructor.
        * by econstructor.
      }
      split => /=.
      { rewrite /this_type /=.
        econstructor => //.
      }
      by apply map_Forall_empty.
    + rewrite lookup_singleton_Some in h.
      destruct h as [? <-].
      rewrite /Test /= /Test1 /=.
      eexists => /=.
      split; first last.
      { split.
        * by econstructor.
        * eapply UpcastTy.
          { by constructor. }
          { by constructor. }
          { by constructor. }
          by eauto.
      }
      split => /=.
      { rewrite /this_type /=.
        by econstructor.
      }
      by apply map_Forall_empty.
  }
  apply lookup_singleton_Some in h.
  destruct h as [? <-].
  rewrite /cdef_wf_mdef_ty /=.
  apply map_Forall_singleton.
  eexists.
  split; first last.
  + split; by constructor.
  + split => //.
    rewrite /this_type /=.
    econstructor => //=.
    { by rewrite -H1 lookup_insert_ne //. }
    done.
Qed.

Lemma wf_mdef_dyn_ty : map_Forall cdef_wf_mdef_dyn_ty pdefs.
Proof.
  apply map_Forall_lookup => cname cdef h.
  rewrite /pdefs /= in h.
  rewrite lookup_insert_Some in h.
  destruct h as [[<- <-] | [? h]].
  { rewrite /cdef_wf_mdef_dyn_ty.
    apply map_Forall_lookup => mname mdef h.
    rewrite /SDBox /= in h.
    rewrite lookup_insert_Some in h.
    destruct h as [[<- <-] | [? h]] => /=.
    + rewrite /wf_mdef_dyn_ty /SDBox /=.
      eexists.
      split; first last.
      { split.
        * econstructor => //=.
          { change Private with (Private, like (GenT 0)).1.
            by eapply HasField.
          }
          simpl.
          eapply ESubTy.
          { by econstructor. }
          { by repeat constructor. }
          { by repeat constructor. }
          rewrite /to_dyn.
          by eauto.
        * eapply ESubTy.
          { by econstructor. }
          { by repeat constructor. }
          { by repeat constructor. }
          rewrite /to_dyn.
          by eauto.
      }
      split => /=.
      { rewrite /this_type /=.
        econstructor => //.
        by apply gen_targs_wf.
      }
      apply map_Forall_lookup => s ? h.
      apply lookup_fmap_Some in h as [ty [<- h]].
      by constructor.
    + rewrite lookup_singleton_Some in h.
      destruct h as [? <-].
      rewrite /SDBox /= /Get /=.
      eexists => /=.
      split; first last.
      { split.
        * econstructor => //=.
          change Private with (Private, like (GenT 0)).1.
          by eapply HasField.
        * eapply ESubTy.
          { by econstructor. }
          { by repeat constructor. }
          { by repeat constructor. }
          rewrite /to_dyn /=.
          eapply SubUnionLower; last done.
          eapply SubConstraint; by set_solver.
      }
      split => /=.
      { rewrite /this_type /=.
        econstructor => //.
        by apply gen_targs_wf.
      }
      rewrite fmap_empty insert_empty.
      apply map_Forall_singleton.
      by repeat constructor.
  }
  rewrite lookup_insert_Some in h.
  destruct h as [[<- <-] | [? h]].
  { rewrite /cdef_wf_mdef_dyn_ty /wf_mdef_ty /Test /=.
    rewrite map_Forall_lookup => mnane mdef h.
    rewrite lookup_insert_Some in h.
    destruct h as [[<- <-] | [? h]].
    + rewrite /Test0 /=.
      eexists => /=.
      split; first last.
      { split.
        * by econstructor.
        * eapply ESubTy.
          { by econstructor. }
          { by econstructor. }
          { by econstructor. }
          by eauto.
      }
      split => /=.
      { rewrite /this_type /=.
        econstructor => //.
      }
      rewrite fmap_empty.
      by apply map_Forall_empty.
    + rewrite lookup_singleton_Some in h.
      destruct h as [? <-].
      by rewrite /Test /= /Test1 /=.
  }
  apply lookup_singleton_Some in h.
  destruct h as [? <-].
  rewrite /cdef_wf_mdef_dyn_ty /=.
  apply map_Forall_singleton.
  done.
Qed.
