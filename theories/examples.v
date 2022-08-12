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

Definition arraykey := UnionT IntT BoolT.

(* TODO: we don't have void atm so I'm using null ;) *)

(* Definition of class ROBox<+T as arraykey>:
 * class ROBox<+T> {
 *   private T $data;
 *   function get(): T { $ret = $this->data; return $ret; }
 *)
Definition Get := {|
  methodname := "get";
  methodargs := ∅;
  methodrettype := GenT 0;
  methodbody := GetC "$ret" ThisE "$data";
  methodret := VarE "$ret";
|}.

Definition ROBox := {|
  classname := "ROBox";
  superclass := None;
  generics := [Covariant];
  constraints := [(GenT 0, arraykey)];
  classfields := {["$data" := (Private, GenT 0)]};
  classmethods := {["get" := Get]};
|}.

(* Definition of class Box<T>:
 * class Box<T> {
 *   public T $data;
 *   function set(T $data) : void { $this->data = $data; }
 *   function get(): T { $ret = $this->data; return $ret; }
 * }
 *)
Definition BoxSet := {|
  methodname := "set";
  methodargs := {["$data" := GenT 0 ]};
  methodrettype := NullT;
  methodbody := SetC ThisE "$data" (VarE "$data");
  methodret := NullE;
|}.

Definition Box := {|
  classname := "Box";
  superclass := None;
  generics := [Invariant];
  constraints := [];
  classfields := {["$data" := (Public, GenT 0)]};
  classmethods := {["set" := BoxSet; "get" := Get]};
|}.

(* Definition of class IntBoxS:
 * class IntBoxS extends Box<int> {
 * function set(int $data) : void { $this->data = $data + 1; }
 *)

Definition σ : list lang_ty := [IntT].

Definition IntBoxSSet := {|
  methodname := "set";
  methodargs := {["$data" := IntT ]};
  methodrettype := NullT;
  methodbody := SetC ThisE "$data" (BinOpE PlusO (VarE "$data") (IntE 1%Z));
  methodret := NullE;
|}.

Definition IntBoxS := {|
  classname := "IntBoxS";
  superclass := Some ("Box", σ);
  generics := [];
  constraints := [];
  classfields := ∅;
  classmethods := {["set" := IntBoxSSet]};
|}.

(* Main program:
 * function main(): bool {
 *   $robox = new ROBox(43);
 *   $init = $robox->get();
 *   $box = new IntBoxS($init);
 *   $tmp = $box->get();
 *   $tmp = $tmp + 20;
 *   $_ = $box->set($tmp - 10);
 *   $tmp = $box->data;
 *   return ($tmp == 43);
 * }
 *)
Definition ProgramBody :=
   SeqC (NewC "$robox" "ROBox" [IntT] {["$data" := IntE 32]})
  (SeqC (CallC "$init" (VarE "$robox") "get" ∅)
  (SeqC (NewC "$box" "IntBoxS" [] {["$data" := VarE "$init"]})
  (SeqC (CallC "$tmp" (VarE "$box") "get" ∅)
  (SeqC (LetC "$tmp" (BinOpE PlusO (VarE "$tmp") (IntE 20)))
  (SeqC (CallC "$_" (VarE "$box") "set"
           {["$data" := BinOpE MinusO (VarE "$tmp") (IntE 10)]})
        (GetC "$tmp" (VarE "$box") "$data")
  ))))).

Definition EntryPoint := {|
  methodname := "entry_point";
  methodargs := ∅;
  methodrettype := BoolT;
  methodbody := ProgramBody;
  methodret := BinOpE EqO (VarE "$tmp") (IntE 43);
|}.

Definition Main := {|
  classname := "Main";
  superclass := None;
  generics := [];
  constraints := [];
  classfields := ∅;
  classmethods := {["entry_point" := EntryPoint]};
 |}.

Local Instance PDC : ProgDefContext := { pdefs := {[ "ROBox" := ROBox; "Box" := Box; "IntBoxS" := IntBoxS; "Main" := Main ]} }.

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

Lemma wfσ : Forall wf_ty σ.
Proof.
  apply Forall_lookup => x ? hx.
  apply list_lookup_singleton_Some in hx as [-> <-].
  by constructor.
Qed.

Lemma σbounded : Forall (bounded (length (generics IntBoxS))) σ.
Proof.
  apply Forall_lookup => x ? hx.
  apply list_lookup_singleton_Some in hx as [-> <-].
  by constructor.
Qed.

Lemma has_method_get0: has_method "get" "ROBox" "ROBox" Get.
Proof. by repeat econstructor; eauto. Qed.

Lemma has_method_get1: has_method "get" "IntBoxS" "Box" (subst_mdef σ Get).
Proof. by repeat econstructor; eauto. Qed.

Lemma has_method_set: has_method "set" "IntBoxS" "IntBoxS" IntBoxSSet.
Proof. by repeat econstructor; eauto. Qed.

Lemma has_fields_ROBox : has_fields "ROBox" {[ "$data" := (Private, GenT 0, "ROBox") ]}.
Proof.
  move => f vis fty orig; split => h.
  - inv h.
    + rewrite /pdefs /= lookup_insert in H.
      simplify_eq.
      rewrite /ROBox /= lookup_singleton_Some in H0.
      by destruct H0 as [<- <-].
    + by rewrite /pdefs /= lookup_insert in H; simplify_eq.
  - rewrite lookup_singleton_Some in h.
    destruct h as [<- [= <- <- <-]].
    change Private with (Private, GenT 0).1.
    by econstructor.
Qed.

Lemma has_fields_Box : has_fields "Box" {[ "$data" := (Public, GenT 0, "Box") ]}.
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
    change Public with (Public, GenT 0).1.
    by econstructor.
Qed.

Lemma has_fields_IntBoxS : has_fields "IntBoxS" {[ "$data" := (Public, IntT, "Box") ]}.
Proof.
  move => f vis fty orig; split => h.
  - inv h.
    + rewrite /pdefs /= lookup_insert_ne // lookup_insert_ne // lookup_insert in H; by simplify_eq.
    + rewrite /pdefs /= lookup_insert_ne // lookup_insert_ne // lookup_insert in H; simplify_eq.
      apply lookup_singleton_Some.
      rewrite /IntBoxS /= in H1 H0.
      injection H1; intros; subst; clear H1.
      inv H2.
      * rewrite /pdefs /= lookup_insert_ne // lookup_insert in H; simplify_eq.
        rewrite /Box /= lookup_singleton_Some in H1.
        by destruct H1 as [<- <-].
      * by rewrite /pdefs /= lookup_insert_ne // lookup_insert in H; simplify_eq.
  - rewrite lookup_singleton_Some in h.
    destruct h as [<- [= <- <- <-]].
    change IntT with (subst_ty σ (GenT 0)).
    eapply InheritsField => //.
    change Public with (Public, GenT 0).1.
    econstructor; first done.
    by rewrite /Box /=.
Qed.

Lemma has_fields_Main : has_fields "Main" ∅.
Proof.
  move => f vis fty orig; split => h; last by rewrite lookup_empty in h.
  inv h.
  - rewrite lookup_insert_ne // lookup_insert_ne // in H.
    rewrite lookup_insert_ne // lookup_insert in H.
    by simplify_eq.
  - rewrite lookup_insert_ne // lookup_insert_ne // in H.
    rewrite lookup_insert_ne // lookup_insert in H.
    by simplify_eq.
Qed.

Definition final_le le new_loc1 new_loc2 : local_env :=
   <["$_":=NullV]>
  (<["$tmp":=IntV 43]>
  (<["$box":=LocV new_loc1]>
  (<["$init":= IntV 32]>
  (<["$robox":= LocV new_loc2]> le)))).

Definition final_heap (h: heap) new_loc1 new_loc2 :=
   <[new_loc1 := ("IntBoxS", {["$data" := IntV 43]})]>
  (<[new_loc2 := ("ROBox", {["$data" := IntV 32]})]> h).

Lemma Main_eval st:
 ∀ new_loc1 new_loc2,
 st.2 !! new_loc1 = None →
 st.2 !! new_loc2 = None →
 new_loc1 <> new_loc2 →
 cmd_eval "Main" st ProgramBody (final_le st.1 new_loc1 new_loc2, final_heap st.2 new_loc1 new_loc2) 8.
Proof.
  case: st => le h /= new_loc1 new_loc2 hnew1 hnew2 hnew.
  rewrite /ProgramBody.
  change 8 with (1 + (2 + (1 + (2 + (0 + (1 + 1)))))).
  eapply SeqEv.
  { apply NewEv; first by apply hnew2.
    rewrite /map_args option_guard_True /=; first by rewrite omap_singleton.
    by apply map_Forall_singleton.
  }
  eapply SeqEv.
  { eapply CallEv => /=.
    - by rewrite lookup_insert.
    - rewrite /map_args option_guard_True; first done.
      by apply map_Forall_empty.
    - by rewrite lookup_insert.
    - by apply has_method_get0.
    - by rewrite /Get /= !dom_empty_L.
    - by rewrite omap_empty.
    - eapply GetEv.
      + by constructor.
      + by rewrite lookup_insert.
      + by rewrite lookup_insert.
      + rewrite /visibility_check.
        exists Private, (GenT 0), "ROBox"; split; last done.
        change Private with (Private, GenT 0).1.
        by econstructor.
    - by rewrite /Get /= lookup_insert.
  }
  eapply SeqEv.
  { apply NewEv.
    - rewrite lookup_insert_ne; first by exact hnew1.
      done.
    - rewrite /map_args option_guard_True /=; first by rewrite omap_singleton.
      apply map_Forall_singleton => /=.
      by rewrite lookup_insert.
  }
  eapply SeqEv.
  { eapply CallEv => /=.
    - by rewrite lookup_insert.
    - rewrite /map_args option_guard_True; first done.
      by apply map_Forall_empty.
    - by rewrite lookup_insert.
    - by apply has_method_get1.
    - by rewrite /Get /= fmap_empty !dom_empty_L.
    - by rewrite omap_empty.
    - eapply GetEv.
      + by constructor.
      + by rewrite lookup_insert.
      + by rewrite lookup_insert.
      + exists Public, (subst_ty [IntT] (GenT 0)), "Box"; split; last done.
        eapply InheritsField => //.
        change Public with (Public, GenT 0).1.
        by econstructor.
    - by rewrite /Get /= lookup_insert.
  }
  eapply SeqEv.
  { (* Let *)
    eapply LetEv => /=.
    by rewrite lookup_insert.
  }
  eapply SeqEv.
  { eapply CallEv => /=.
    - rewrite lookup_insert_ne //.
      by rewrite lookup_insert_ne // lookup_insert.
    - rewrite /map_args option_guard_True; first done.
      apply map_Forall_singleton => /=.
      by rewrite lookup_insert.
    - by rewrite lookup_insert.
    - by apply has_method_set.
    - by rewrite /IntBoxSSet /= !dom_singleton_L.
    - by rewrite omap_singleton /= lookup_insert.
    - rewrite /IntBoxSSet /=.
      eapply SetEv.
      + by constructor.
      + by constructor.
      + by rewrite lookup_insert.
      + done.
      + exists Public, (subst_ty [IntT] (GenT 0)), "Box"; split; last done.
        eapply InheritsField => //.
        change Public with (Public, GenT 0).1.
        by econstructor.
    - by rewrite /IntBoxSSet /=.
  }
  rewrite lookup_insert.
  replace (final_le le new_loc1 new_loc2) with
    ( <["$tmp" := IntV 43]>
     (<["$_":=NullV]>
     (<["$tmp":=IntV (32 + 20)]>
     (<["$tmp":=IntV 32]>
     (<["$box":=LocV new_loc1]>
     (<["$init":= IntV 32]>
     (<["$robox":= LocV new_loc2]> le))))))); last first.
  { rewrite /final_le.
    destruct le as [vthis lenv] => /=.
    rewrite /local_env_insert /=.
    f_equal.
    rewrite insert_commute //.
    f_equal.
    by rewrite !insert_insert.
  }
  replace (final_heap h new_loc1 new_loc2) with
    ( <[new_loc1:=("IntBoxS", {["$data" := IntV (33 + 20 - 10); "$data" := IntV 32]})]>
     (<[new_loc1:=("IntBoxS", {["$data" := IntV 32]})]>
     (<[new_loc2:=("ROBox", {["$data" := IntV 32]})]> h))); last first.
  { rewrite /final_heap.
    by rewrite !insert_insert.
  }
  eapply GetEv.
  - do 3 (rewrite /= lookup_insert_ne //).
    by rewrite lookup_insert.
  - by rewrite lookup_insert.
  - by rewrite lookup_insert.
  - exists Public, (subst_ty [IntT] (GenT 0)), "Box"; split; last done.
    eapply InheritsField => //.
    change Public with (Public, GenT 0).1.
    by econstructor.
Qed.

Definition final_lty lty : local_tys :=
   <["$tmp"   := IntT]>
  (<["$_"     := NullT]>
  (<["$box"   := ClassT "IntBoxS" []]>
  (<["$init"  := IntT]>
  (<["$robox" := ClassT "ROBox" [IntT]]> lty)))).

Lemma Main_ty n lty :
  bounded_lty n lty →
  cmd_has_ty "Main" [] Plain n lty ProgramBody (final_lty lty).
Proof.
  move => hb.
  rewrite /final_lty /ProgramBody.
  eapply SeqTy.
  { eapply NewTy with (targs := [IntT]).
    + econstructor => //.
      move => k ty; rewrite list_lookup_singleton_Some.
      case => _ <-; by constructor.
    + constructor.
      by rewrite Forall_singleton.
    + econstructor => //.
      * move => i ty.
        rewrite list_lookup_singleton_Some => [[? <-]].
        by constructor.
      * rewrite /ROBox /= => i [??] h.
        apply list_lookup_singleton_Some in h as [? heq].
        case: heq => <- <- /=.
        by eauto.
    + by apply has_fields_ROBox.
    + by set_solver.
    + move => f fty arg.
      rewrite !lookup_singleton_Some.
      case => <- <- [_ <-].
      by constructor.
  }
  eapply SeqTy.
  { eapply CallTy.
    + constructor.
      by rewrite lookup_insert.
    + by apply has_method_get0.
    + by set_solver.
    + move => ????; by rewrite lookup_empty.
  }
  eapply SeqTy.
  { eapply NewTy with (targs := []).
    + by econstructor.
    + by econstructor.
    + by econstructor.
    + by apply has_fields_IntBoxS.
    + by set_solver.
    + move => f fty arg.
      rewrite !lookup_singleton_Some.
      case => <- <- [_ <-].
      constructor.
      by rewrite lookup_insert.
  }
  eapply SeqTy.
  { eapply CallTy.
    + econstructor.
      by rewrite lookup_insert.
    + by apply has_method_get1.
    + by set_solver.
    + by move => x ty arg; rewrite /Get /= lookup_empty.
  }
  eapply SeqTy.
  { eapply LetTy.
    constructor; first done.
    + constructor; by rewrite lookup_insert.
    + by constructor.
  }
  eapply SeqTy.
  { eapply CallTy.
    + econstructor.
      rewrite lookup_insert_ne // lookup_insert_ne //.
      by rewrite lookup_insert.
    + by apply has_method_set.
    + by set_solver.
    + move => x ty arg; rewrite /Get /= !lookup_singleton_Some.
      case => <- <- [_ <-].
      constructor; first done.
      - constructor; by rewrite lookup_insert.
      - by constructor.
  }
  rewrite /IntBoxSSet /=.
  eapply SubTy; last first.
  - eapply GetPubTy; last by apply has_fields_IntBoxS.
    constructor.
    do 3 (rewrite lookup_insert_ne //).
    by rewrite lookup_insert.
  - apply insert_bounded_lty; first done.
    split => /=.
    { rewrite /this_type /=.
      constructor.
      destruct lty as [[this σ] Γ]; simpl.
      destruct hb as [hb _].
      rewrite /this_type /= in hb.
      by inv hb.
    }
    apply map_Forall_insert_2; first done.
    apply map_Forall_insert_2.
    { apply bounded_ge with 0; last by lia.
      constructor.
      by apply Forall_nil.
    }
    apply map_Forall_insert_2; first done.
    apply map_Forall_insert_2.
    { apply bounded_ge with 0; last by lia.
      constructor.
      by apply Forall_singleton.
    }
    by apply hb.
  - split => /=.
    { by rewrite /this_type. }
    move => v ty.
    rewrite lookup_insert_Some.
    case => [[<- <-] | [? h]].
    + exists IntT; by rewrite lookup_insert.
    + rewrite lookup_insert_ne //.
      destruct (decide (v = "$_")) as [-> | ?].
      * rewrite lookup_insert in h.
        case: h => <-.
        exists NullT; by rewrite lookup_insert.
      * rewrite lookup_insert_ne //.
        rewrite lookup_insert_ne //.
        rewrite lookup_insert_ne //.
      destruct (decide (v = "$box")) as [-> | ?].
      { rewrite lookup_insert.
        rewrite lookup_insert_ne // lookup_insert in h.
        case : h => <-.
        by eexists.
      }
      rewrite lookup_insert_ne // in h.
      rewrite lookup_insert_ne // in h.
      exists ty.
      by rewrite lookup_insert_ne.
Qed.

Lemma wf_mdef_ty_Main: wf_mdef_ty "Main" [] 0 (gen_targs 0) EntryPoint.
Proof.
  rewrite /wf_mdef_ty.
  exists (final_lty {| type_of_this := ("Main", gen_targs 0); ctxt := methodargs EntryPoint|}).
  repeat split.
  - rewrite /final_lty /this_type /=.
    by econstructor.
  - rewrite /final_lty /=.
    rewrite map_Forall_lookup => k tk.
    rewrite lookup_insert_Some.
    case => [[? <-] | [?]]; first by constructor.
    rewrite lookup_insert_Some.
    case => [[? <-] | [?]]; first by econstructor.
    rewrite lookup_insert_Some.
    case => [[? <-] | [?]]; first by econstructor.
    rewrite lookup_insert_Some.
    case => [[? <-] | [?]]; first by econstructor.
    rewrite lookup_insert_Some.
    case => [[? <-] | [?]]; last by rewrite lookup_empty.
    econstructor => //.
    move => ? ?; rewrite list_lookup_singleton_Some.
    case => _ <-.
    by constructor.
  - apply Main_ty .
    split.
    + rewrite /this_type /=.
      constructor.
      by apply Forall_nil.
    + simpl.
      by apply map_Forall_empty.
  - rewrite /final_lty.
    constructor => //.
    + constructor.
      by rewrite /= lookup_insert.
    + by constructor.
Qed.

Lemma helper_ext: ∀ A B σ0, extends_using A B σ0 → A = "IntBoxS" ∧ B = "Box" ∧ σ0 = σ.
Proof.
  move => A B σ0 h; inv h.
  rewrite /pdefs /= lookup_insert_Some in H.
  destruct H as [[<- <-] | [? H]].
  { by rewrite /Box in H0. }
  rewrite lookup_insert_Some in H.
  destruct H as [[<- <-] | [? H]].
  { rewrite /Box /= in H0; by simplify_eq. }
  rewrite lookup_insert_Some in H.
  destruct H as [[<- <-] | [? H]].
  { rewrite /IntBoxS /= in H0; by simplify_eq. }
  rewrite lookup_singleton_Some in H.
  destruct H as [<- <-].
  rewrite /Main in H0; discriminate.
Qed.

Lemma helper_in_ROBox : ∀ T σt, inherits_using "ROBox" T σt → T = "ROBox" ∧ σt = [GenT 0].
Proof.
  move => T σt h; inv h.
  + rewrite /pdefs /=.
    rewrite lookup_insert in H.
    by simplify_eq.
  + apply helper_ext in H.
    destruct H; discriminate.
  + apply helper_ext in H.
    destruct H; discriminate.
Qed.

Lemma helper_in_Main : ∀ T σt, inherits_using "Main" T σt → T = "Main" ∧ σt = [].
Proof.
  move => T σt h; inv h.
  + rewrite /pdefs /=.
    do 3 (rewrite lookup_insert_ne // in H).
    rewrite lookup_singleton_Some in H.
    by case : H => _ <-.
  + apply helper_ext in H.
    destruct H; discriminate.
  + apply helper_ext in H.
    destruct H; discriminate.
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

Lemma helper_in_IntBoxS : ∀ T σt, inherits_using "IntBoxS" T σt →
  (T = "IntBoxS" ∧ σt = []) ∨
  (T = "Box" ∧ σt = σ).
Proof.
  move => T σt h; inv h.
  + rewrite /pdefs /=.
    do 2 (rewrite lookup_insert_ne // in H).
    rewrite lookup_insert in H.
    left.
    by simplify_eq.
  + apply helper_ext in H.
    destruct H; right; by simplify_eq.
  + apply helper_ext in H.
    destruct H as [_ [-> ->]]; right.
    apply helper_in_Box in H0 as [-> ->].
    done.
Qed.

Lemma helper_in: ∀ A B σ0, inherits_using A B σ0 →
     (A = "IntBoxS" ∧ B = "Box" ∧ σ0 = σ) ∨
     (A = "IntBoxS" ∧ B = "IntBoxS" ∧ σ0 = []) ∨
     (A = "Box" ∧ B = "Box" ∧ σ0 = [GenT 0]) ∨
     (A = "ROBox" ∧ B = "ROBox" ∧ σ0 = [GenT 0]) ∨
     (A = "Main" ∧ B = "Main" ∧ σ0 = []).
Proof.
  move => A B σ0 h.
  inv h.
  + rewrite /pdefs /=.
    rewrite lookup_insert_Some in H.
    destruct H as [[<- ?]|[? H]]; first (right; right; right; left; by rewrite -H).
    rewrite lookup_insert_Some in H.
    destruct H as [[<- ?]|[? H]]; first (right; right; left; by rewrite -H).
    rewrite lookup_insert_Some in H.
    destruct H as [[<- ?]|[? H]]; first (right; left; by rewrite -H).
    rewrite lookup_insert_Some in H.
    destruct H as [[<- ?]|[? H]]; last by (by rewrite lookup_empty in H).
    right; right; right; right; by rewrite -H.
  + apply helper_ext in H as [-> [-> ->]].
    by left.
  + apply helper_ext in H as [-> [-> ->]].
    apply helper_in_Box in H0 as [-> ->].
    by left.
Qed.

Lemma wf_extends_wf : wf_no_cycle pdefs.
Proof.
  move => A B σ0 σ1 h0 h1.
  apply helper_in in h0.
  destruct h0 as [[-> [-> ->]] | h0].
  { apply helper_in_Box in h1; by destruct h1; discriminate. }
  destruct h0 as [[-> [-> ->]] | h0].
  { by apply helper_in_IntBoxS in h1 as [[_ ->] | [h ?]]. }
  destruct h0 as [[-> [-> ->]] | h0].
  { by apply helper_in_Box in h1 as [_ ->]. }
  destruct h0 as [[-> [-> ->]] | h0].
  { by apply helper_in_ROBox in h1 as [_ ->]. }
  destruct h0 as [-> [-> ->]].
  by apply helper_in_Main in h1 as [_ ->].
Qed.

Lemma wf_parent : map_Forall (λ _cname, wf_cdef_parent pdefs) pdefs.
Proof.
  apply map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[? <-] | [?]] => //.
  rewrite lookup_insert_Some.
  case => [[? <-] | [?]] => //.
  rewrite lookup_insert_Some.
  case => [[? <-] | [?]].
  { split.
    + eapply wf_ty_class => //.
      by apply wfσ.
    + by apply σbounded.
  }
  rewrite lookup_singleton_Some.
  by case => [? <-].
Qed.

Lemma wf_override : wf_method_override pdefs.
Proof.
  move => A B adef bdef m σ0 mA mB hA hB hin hmA hmB.
  apply helper_in in hin.
  destruct hin as [[-> [-> ->]] | hin].
  { rewrite /pdefs /= in hA, hB.
    do 2 (rewrite lookup_insert_ne // in hA).
    do 1 (rewrite lookup_insert_ne // in hB).
    rewrite !lookup_insert in hA, hB.
    simplify_eq.
    rewrite /IntBoxS /= in hmA.
    rewrite /Box /= in hmB.
    rewrite lookup_singleton_Some in hmA.
    destruct hmA as [<- <-].
    rewrite lookup_insert in hmB.
    case : hmB => <-.
    rewrite /mdef_incl /IntBoxSSet /BoxSet /subst_mdef /σ /=.
    split; first by set_solver.
    split; last done.
    move => k A B.
    rewrite lookup_singleton_Some.
    case => [<- <-].
    rewrite lookup_fmap_Some.
    case => [ty [<-]].
    rewrite lookup_insert.
    by case => <-.
  }
  destruct hin as [[-> [-> ->]] | hin].
  { simplify_eq.
    rewrite /pdefs /=.
    do 2 (rewrite  lookup_insert_ne // in hA).
    rewrite lookup_insert in hA.
    injection hA; intros; subst; clear hA.
    rewrite /Main /= in hmA.
    rewrite lookup_singleton_Some in hmA.
    destruct hmA as [_ <-].
    rewrite subst_mdef_nil.
    by apply mdef_incl_reflexive.
  }
  destruct hin as [[-> [-> ->]] | hin].
  { simplify_eq.
    rewrite /pdefs /=.
    do 1 (rewrite  lookup_insert_ne // in hA).
    rewrite lookup_insert in hA.
    injection hA; intros; subst; clear hA.
    rewrite /Box /= in hmA.
    rewrite lookup_insert_Some in hmA.
    destruct hmA as [[<- <-]|[? hmA]].
    + rewrite /mdef_incl /BoxSet /subst_mdef /=.
      split; first by set_solver.
      split; last done.
      move => k A B.
      rewrite lookup_singleton_Some.
      case => [<- <-].
      rewrite lookup_fmap lookup_insert /=.
      by case => <-.
    + rewrite lookup_singleton_Some in hmA.
      destruct hmA as [<- <-].
      rewrite /mdef_incl /Get /subst_mdef /=.
      split; first by set_solver.
      split; last done.
      move => k A B.
      by rewrite lookup_empty.
  }
  destruct hin as [[-> [-> ->]] | hin].
  { simplify_eq.
    rewrite /pdefs /=.
    rewrite lookup_insert in hA.
    injection hA; intros; subst; clear hA.
    rewrite /IntBoxS /= in hmA.
    rewrite lookup_singleton_Some in hmA.
    destruct hmA as [<- <-].
    rewrite /mdef_incl /IntBoxSSet /subst_mdef /=.
    split; first by set_solver.
    split; last done.
    move => k A B.
    by rewrite lookup_empty.
  }
  destruct hin as [-> [-> ->]].
  { simplify_eq.
    rewrite /pdefs /=.
    do 3 (rewrite lookup_insert_ne // in hA).
    rewrite lookup_singleton_Some in hA.
    destruct hA as [_ <-].
    rewrite /Main /= in hmA.
    rewrite lookup_singleton_Some in hmA.
    destruct hmA as [<- <-].
    rewrite /mdef_incl /EntryPoint /subst_mdef /=.
    split; first by set_solver.
    split; last done.
    move => k A B.
    by rewrite lookup_empty.
  }
Qed.

Lemma wf_fields : map_Forall (λ _cname, wf_cdef_fields) pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { by rewrite /wf_cdef_fields /ROBox. }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { by rewrite /wf_cdef_fields /Box. }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { by rewrite /wf_cdef_fields /IntBoxS. }
  rewrite lookup_singleton_Some.
  case => [? <-].
  by rewrite /wf_cdef_fields /Main.
Qed.

Lemma wf_fields_bounded : map_Forall (λ _cname, wf_cdef_fields_bounded) pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_cdef_fields_bounded /ROBox /=.
    rewrite map_Forall_singleton.
    econstructor.
    by auto with arith.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_cdef_fields_bounded /Box /=.
    rewrite map_Forall_singleton.
    econstructor.
    by auto with arith.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_cdef_fields_bounded /IntBoxS /=.
    by apply map_Forall_empty.
  }
  rewrite lookup_singleton_Some.
  case => [? <-].
  by rewrite /wf_cdef_fields /Main.
Qed.

Lemma wf_fields_wf  : map_Forall (λ _cname, wf_cdef_fields_wf) pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_cdef_fields_wf /ROBox /=.
    rewrite map_Forall_singleton.
    econstructor.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_cdef_fields_wf /Box /=.
    rewrite map_Forall_singleton.
    by econstructor.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_cdef_fields_wf /IntBoxS /=.
    by apply map_Forall_empty.
  }
  rewrite lookup_singleton_Some.
  case => [? <-].
  rewrite /wf_cdef_fields_wf /Main /=.
  by apply map_Forall_empty.
Qed.

Lemma wf_fields_mono : map_Forall (λ _cname, wf_field_mono) pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_field_mono /ROBox /=.
    rewrite map_Forall_lookup => x mx.
    rewrite lookup_singleton_Some.
    case => [? <-].
    split; by constructor.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_field_mono /Box /=.
    rewrite map_Forall_lookup => x mx.
    rewrite lookup_singleton_Some.
    case => [? <-].
    split; by constructor.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_field_mono /IntBoxS /=.
    by apply map_Forall_empty.
  }
  rewrite lookup_singleton_Some.
  case => [? <-].
  rewrite /wf_field_mono /Main /=.
  by apply map_Forall_empty.
Qed.

Lemma wf_methods_bounded : map_Forall (λ _cname, cdef_methods_bounded) pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /cdef_methods_bounded /ROBox /=.
    apply map_Forall_singleton.
    split.
    { rewrite /Get /=.
      by apply map_Forall_empty.
    }
    split.
    { rewrite /Get /=.
      constructor; by auto with arith.
    }
    split; first by repeat constructor.
    by repeat constructor.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /cdef_methods_bounded /Box /=.
    rewrite map_Forall_lookup => x mx.
    rewrite lookup_insert_Some.
    case => [[? <-]|[?]].
    + split.
      { rewrite /BoxSet /=.
        apply map_Forall_singleton.
        constructor.
        by auto with arith.
      }
      split; by repeat constructor.
    + rewrite lookup_singleton_Some.
      case => [? <-].
      split.
      * rewrite /Get /=.
        by apply map_Forall_empty.
      * rewrite /Get /=.
        constructor; first by auto with arith.
        by repeat constructor.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /cdef_methods_bounded /IntBoxS /=.
    rewrite map_Forall_singleton.
    split.
    { rewrite /IntBoxSSet /=.
      rewrite map_Forall_singleton.
      by constructor.
    }
    split; by repeat constructor.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]]; last by rewrite lookup_empty.
  rewrite /cdef_methods_bounded /Main /=.
  apply map_Forall_singleton.
  split; first by apply map_Forall_empty.
  split; first by constructor.
  split.
  { constructor.
    - constructor.
      + by repeat constructor.
      + rewrite map_Forall_singleton.
        by repeat constructor.
    - constructor; first by repeat constructor.
      constructor.
      { constructor; first by repeat constructor.
        rewrite map_Forall_singleton.
        by repeat constructor.
      }
      constructor.
      { constructor; first by repeat constructor.
        by apply map_Forall_empty.
      }
      constructor; first by repeat constructor.
      constructor.
      { constructor; first by repeat constructor.
        rewrite map_Forall_singleton.
        by repeat constructor.
      }
      by repeat constructor.
  }
  by repeat constructor.
Qed.

Lemma wf_methods_wf : map_Forall (λ _cname, wf_cdef_methods_wf) pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_cdef_methods_wf /ROBox /=.
    rewrite map_Forall_singleton.
    split.
    + rewrite /Get /=.
      by apply map_Forall_empty.
    + rewrite /Get /=.
      by constructor.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_cdef_methods_wf /Box /=.
    rewrite map_Forall_lookup => x mx.
    rewrite lookup_insert_Some.
    case => [[? <-]|[?]].
    + split; last by constructor.
      rewrite /BoxSet /=.
      rewrite map_Forall_singleton.
      by constructor.
    + rewrite lookup_insert_Some.
      case => [[? <-]|[?]]; last by rewrite lookup_empty.
      split.
      * rewrite /Get /=.
        by apply map_Forall_empty.
      * rewrite /Get /=.
        by constructor.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_cdef_methods_wf /IntBoxS /=.
    rewrite map_Forall_singleton.
    split.
    + rewrite /IntBoxSSet /=.
      rewrite map_Forall_singleton.
      by constructor.
    + rewrite /IntBoxSSet /=.
      by constructor.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]]; last by rewrite lookup_empty.
  rewrite /wf_cdef_methods_wf /Main /=.
  apply map_Forall_singleton.
  split; last by constructor.
  by apply map_Forall_empty.
Qed.

Lemma wf_methods_mono : map_Forall (λ _cname, wf_cdef_methods_mono) pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_cdef_methods_mono /ROBox /=.
    apply map_Forall_singleton.
    rewrite /wf_mdef_mono /Get /=.
    split; last by constructor.
    by apply map_Forall_empty.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_cdef_methods_mono /Box /=.
    rewrite map_Forall_lookup => x mx.
    rewrite lookup_insert_Some.
    case => [[? <-]|[?]].
    * rewrite /wf_mdef_mono /BoxSet /=.
      split; last by constructor.
      apply map_Forall_singleton.
      by constructor.
    * rewrite lookup_insert_Some.
      case => [[? <-]|[?]]; last by rewrite lookup_empty.
      rewrite /wf_mdef_mono /Get /=.
      split; first by apply map_Forall_empty.
      by constructor.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_cdef_methods_mono /IntBoxS /=.
    apply map_Forall_singleton.
    rewrite /wf_mdef_mono /IntBoxSSet /=.
    split; last by constructor.
    apply map_Forall_singleton.
    by constructor.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]]; last by rewrite lookup_empty.
  rewrite /wf_cdef_methods_mono /Main /=.
  apply map_Forall_singleton.
  split; last by constructor.
  by apply map_Forall_empty.
Qed.

Lemma wf_mdefs : map_Forall cdef_wf_mdef_ty pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]].
  { rewrite /cdef_wf_mdef_ty /ROBox /=.
    rewrite map_Forall_singleton.
    eexists.
    split; first last.
    - rewrite /Get /=; split.
      + eapply GetPrivTy => //.
        by apply has_fields_ROBox.
      + by econstructor.
    - split.
      { rewrite /this_type /=.
        econstructor => //.
        by apply gen_targs_wf.
      }
      rewrite map_Forall_lookup => x tx /=.
      rewrite lookup_insert_Some.
      case => [[? <-]|[?]]; last by rewrite lookup_empty.
      by constructor.
  }
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]].
  { rewrite /cdef_wf_mdef_ty /Box /=.
    rewrite map_Forall_lookup => x mx.
    rewrite lookup_insert_Some.
    case => [[? <-]|[?]].
    * rewrite /wf_mdef_ty /BoxSet /=.
      eexists.
      split; first last.
      { split ; last by constructor.
        eapply SetPubTy.
        - by constructor.
        - simpl.
          change Public with (Public, GenT 0).1.
          by eapply HasField.
        - by constructor.
      }
      split.
      { rewrite /this_type /=.
        econstructor => //.
        by apply gen_targs_wf.
      }
      rewrite map_Forall_lookup => k t /=.
      rewrite lookup_singleton_Some.
      case => [? <-].
      by constructor.
    * rewrite lookup_insert_Some.
      case => [[? <-]|[?]]; last by rewrite lookup_empty.
      rewrite /wf_mdef_ty /Get /=.
      eexists; split; first last.
      { split.
        - eapply GetPubTy.
          + by constructor.
          + change Public with (Public, GenT 0).1.
            by eapply HasField.
        - by constructor.
      }
      split.
      { rewrite /this_type /=.
        econstructor => //.
        by apply gen_targs_wf.
      }
      rewrite map_Forall_lookup => k t /=.
      rewrite lookup_insert_Some.
      case => [[? <-]|[?]]; first by constructor.
      by rewrite lookup_empty.
  }
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]].
  { rewrite /cdef_wf_mdef_ty /IntBoxS /=.
    rewrite map_Forall_singleton.
    eexists.
    split; first last.
    * split; last by constructor.
      rewrite /IntBoxSSet /=.
      eapply SetPubTy.
      { by constructor. }
      { eapply InheritsField => //.
        change Public with (Public, GenT 0).1.
        by eapply HasField.
      }
      { constructor => //.
        - constructor.
          by rewrite /= lookup_insert.
        - by constructor.
      }
    * split.
      { rewrite /this_type /=.
        by econstructor.
      }
      rewrite map_Forall_lookup => x tx /=.
      rewrite lookup_singleton_Some.
      case => [? <-].
      by constructor.
  }
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]]; last by rewrite lookup_empty.
  rewrite /cdef_wf_mdef_ty /Main /=.
  apply map_Forall_singleton.
  by apply wf_mdef_ty_Main.
Qed.

Lemma wf_mono : map_Forall (λ _cname, wf_cdef_mono) pdefs.
Proof.
  rewrite map_Forall_lookup => x cx.
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]]; first done.
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]]; first done.
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_cdef_mono /IntBoxS /=.
    econstructor => //.
    + move => i wi ti //=.
      rewrite list_lookup_singleton_Some.
      case => [-> <-].
      simpl.
      case => <- _.
      by constructor.
    + move => i wi ti //=.
      rewrite list_lookup_singleton_Some.
      case => [-> <-].
      simpl.
      case => <- _.
      by constructor.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]]; last by rewrite lookup_empty.
  done.
Qed.

Lemma wf_constraints_wf : map_Forall (λ _cname, wf_cdef_constraints_wf) pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_cdef_constraints_wf /ROBox /= Forall_singleton.
    split; by constructor.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { by rewrite /wf_cdef_constraints_wf /= Forall_nil. }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { by rewrite /wf_cdef_constraints_wf /= Forall_nil. }
  rewrite lookup_singleton_Some.
  case => [? <-].
  by rewrite /wf_cdef_constraints_wf /= Forall_nil.
Qed.

Lemma wf_constraints_bounded : map_Forall (λ _cname, wf_cdef_constraints_bounded) pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_cdef_constraints_bounded /= Forall_singleton.
    split; by repeat constructor.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { by rewrite /wf_cdef_constraints_bounded /= Forall_nil. }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { by rewrite /wf_cdef_constraints_bounded /= Forall_nil. }
  rewrite lookup_singleton_Some.
  case => [? <-].
  by rewrite /wf_cdef_constraints_bounded /= Forall_nil.
Qed.

Lemma wf_parent_ok : map_Forall (λ _cname, wf_cdef_parent_ok) pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { by rewrite /wf_cdef_parent_ok . }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { by rewrite /wf_cdef_parent_ok. }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_cdef_parent_ok /=.
    econstructor => //.
    rewrite /σ => i ty.
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
  { rewrite /wf_cdef_constraints_ok /ROBox /= /ok_constraints Forall_singleton.
    split => /=; by repeat constructor.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_cdef_constraints_ok; by constructor. }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /wf_cdef_constraints_ok; by constructor. }
  rewrite lookup_singleton_Some.
  case => [? <-].
  rewrite /wf_cdef_constraints_ok; by constructor.
Qed.

Lemma wf_methods_ok : map_Forall (λ _cname, cdef_methods_ok) pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /cdef_methods_ok /ROBox /=.
    apply map_Forall_singleton.
    rewrite /mdef_ok /Get /=.
    split; last by constructor.
    by apply map_Forall_empty.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /cdef_methods_ok /Box /=.
    rewrite map_Forall_lookup => x mx.
    rewrite lookup_insert_Some.
    case => [[? <-]|[?]].
    * rewrite /mdef_ok /BoxSet /=.
      split; last by constructor.
      apply map_Forall_singleton.
      by constructor.
    * rewrite lookup_insert_Some.
      case => [[? <-]|[?]]; last by rewrite lookup_empty.
      rewrite /mdef_ok /Get /=.
      split; first by apply map_Forall_empty.
      by constructor.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]].
  { rewrite /cdef_methods_ok /IntBoxS /=.
    apply map_Forall_singleton.
    rewrite /mdef_ok /IntBoxSSet /=.
    split; last by constructor.
    apply map_Forall_singleton.
    by constructor.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]]; last by rewrite lookup_empty.
  rewrite /cdef_methods_ok /Main /=.
  apply map_Forall_singleton.
  split; last by constructor.
  by apply map_Forall_empty.
Qed.

Lemma wf_extends_dyn : map_Forall wf_cdef_extends_dyn pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]] //.
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]] //.
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]] //.
  { rewrite /wf_cdef_extends_dyn /IntBoxS /=.
    exists Box; split => //.
    move => i c /=.
    rewrite list_lookup_singleton_Some.
    case => ? <-.
    constructor; by set_solver.
  }
  rewrite lookup_insert_Some.
  case => [[? <-]|[?]]; last by rewrite lookup_empty.
  done.
Qed.

Lemma has_method_ROBox m o mdef:
  has_method m "ROBox" o mdef →
  m = "get" ∧ o = "ROBox" ∧ mdef = Get.
Proof.
  move => h; inv h; last first.
  { rewrite lookup_insert in H.
    by simplify_eq.
  }
  rewrite lookup_insert in H.
  simplify_eq.
  rewrite lookup_singleton_Some in H0.
  by firstorder.
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

Lemma has_method_IntBoxS m o mdef:
  has_method m "IntBoxS" o mdef →
  (m = "get" ∧ o = "Box" ∧ mdef = subst_mdef σ Get) ∨
  (m = "set" ∧ o = "Box" ∧ mdef = subst_mdef σ BoxSet) ∨
  (m = "set" ∧ o = "IntBoxS" ∧ mdef = IntBoxSSet).
Proof.
  move => h; inv h.
  - rewrite lookup_insert_ne // in H.
    rewrite lookup_insert_ne // lookup_insert in H.
    simplify_eq.
    rewrite lookup_singleton_Some in H0.
    by firstorder.
  - rewrite lookup_insert_ne // in H.
    rewrite lookup_insert_ne // lookup_insert in H.
    simplify_eq.
    rewrite /IntBoxS /= in H1.
    simplify_eq.
    apply has_method_Box in H2.
    case : H2 => [ [<- [<- <-]]| ].
    { by left. }
    case => <- [<- <-].
    right; by left.
Qed.

Lemma has_method_Main m o mdef:
  has_method m "Main" o mdef →
  m = "entry_point" ∧ o = "Main" ∧ mdef = EntryPoint.
Proof.
  move => h; inv h; last first.
  { rewrite lookup_insert_ne // in H.
    rewrite lookup_insert_ne // in H.
    rewrite lookup_insert_ne // lookup_insert in H.
    by simplify_eq.
  }
  rewrite lookup_insert_ne // in H.
  rewrite lookup_insert_ne // in H.
  rewrite lookup_insert_ne // lookup_insert in H.
  simplify_eq.
  rewrite lookup_singleton_Some in H0.
  by firstorder.
Qed.

Lemma wf_methods_dyn : map_Forall wf_cdef_methods_dyn_wf pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]].
  { move => m o mdef hm.
    apply has_method_ROBox in hm as (-> & -> & ->).
    exists (gen_targs (length ROBox.(generics))).
    split; first by constructor.
    move => i c /=.
    rewrite list_lookup_singleton_Some.
    case => ? <-.
    constructor; by set_solver.
  }
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]].
  { move => m o mdef hm.
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
  }
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]].
  { move => m o mdef hm.
    apply has_method_IntBoxS in hm as [(-> & -> & ->) | [(-> & -> & ->) | (-> & -> & ->)]].
    + exists σ.
      split; first by eauto.
      move => i c /=.
      rewrite list_lookup_singleton_Some.
      case => ? <-.
      constructor; by set_solver.
    + exists σ.
      split; first by eauto.
      move => i c /=.
      rewrite list_lookup_singleton_Some.
      case => ? <-.
      constructor; by set_solver.
    + exists (gen_targs (length IntBoxS.(generics))).
      split; first by constructor.
      move => i c /=.
      rewrite list_lookup_singleton_Some.
      case => ? <-.
      constructor; by set_solver.
  }
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]]; last by rewrite lookup_empty.
  { move => m o mdef hm.
    apply has_method_Main in hm as (-> & -> & ->).
    exists (gen_targs (length Main.(generics))).
    split; first by constructor.
    move => i c /=.
    rewrite list_lookup_singleton_Some.
    case => ? <-.
    constructor; by set_solver.
  }
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
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]].
  { move => fields hf.
    move : has_fields_Box => hf0.
    rewrite (has_fields_fun _ _ _  hf hf0).
    apply map_Forall_singleton => /=; split.
    + apply SubFalse; first done.
      constructor; by set_solver.
    + apply SubFalse; first done.
      constructor; by set_solver.
  }
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]].
  { move => fields hf.
    move : has_fields_IntBoxS => hf0.
    rewrite (has_fields_fun _ _ _  hf hf0).
    apply map_Forall_singleton => /=; split.
    + apply SubFalse; first done.
      constructor; by set_solver.
    + apply SubFalse; first done.
      constructor; by set_solver.
  }
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]]; last by rewrite lookup_empty.
  { move => fields hf.
    move : has_fields_Main => hf0.
    rewrite (has_fields_fun _ _ _ hf hf0).
    by apply map_Forall_empty.
  }
Qed.

Lemma wf_mdefs_dyn : map_Forall cdef_wf_mdef_dyn_ty pdefs.
Proof.
  rewrite map_Forall_lookup => c0 d0.
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]].
  { move => k m hm.
    pose (Γ := {|
        type_of_this := ("ROBox", gen_targs (length (generics ROBox)));
        ctxt := ∅;
      |}
      ).
    assert (wf_lty Γ).
    { split => //.
      rewrite /this_type /=.
      apply wf_ty_class with ROBox => //.
      by apply gen_targs_wf_2.
    }
    (* dummy Γ *)
    exists Γ; split; first done.
    split.
    - apply FalseCmdTy => //.
      + split => //.
        rewrite /Γ /this_type /=.
        constructor.
        by repeat constructor.
      + apply SubConstraint.
        by set_solver.
    - apply FalseTy => //.
      apply SubConstraint.
      by set_solver.
  }
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]] //.
  { move => k m hm.
    pose (Γ := {|
        type_of_this := ("Box", gen_targs (length (generics Box)));
        ctxt := ∅;
      |}
      ).
    assert (wf_lty Γ).
    { split => //.
      rewrite /this_type /=.
      apply wf_ty_class with Box => //.
      by apply gen_targs_wf_2.
    }
    (* dummy Γ *)
    exists Γ; split; first done.
    split.
    - apply FalseCmdTy => //.
      + split => //.
        rewrite /Γ /this_type /=.
        constructor.
        by repeat constructor.
      + apply SubConstraint.
        by set_solver.
    - apply FalseTy => //.
      apply SubConstraint.
      by set_solver.
  }
  rewrite lookup_insert_Some.
  case => [[<- <-]|[?]] //.
  { move => k m hm.
    pose (Γ := {|
        type_of_this := ("IntBoxS", gen_targs (length (generics IntBoxS)));
        ctxt := ∅;
      |}
      ).
    assert (wf_lty Γ).
    { split => //.
      rewrite /this_type /=.
      apply wf_ty_class with IntBoxS => //.
      by apply gen_targs_wf_2.
    }
    (* dummy Γ *)
    exists Γ; split; first done.
    split.
    - apply FalseCmdTy => //.
      + split => //.
        rewrite /Γ /this_type /=.
        constructor.
        by repeat constructor.
      + apply SubConstraint.
        by set_solver.
    - apply FalseTy => //.
      apply SubConstraint.
      by set_solver.
  }
  rewrite lookup_singleton_Some.
  case => <- <-.
{ move => k m hm.
    pose (Γ := {|
        type_of_this := ("Main", gen_targs (length (generics Main)));
        ctxt := ∅;
      |}
      ).
    assert (wf_lty Γ).
    { split => //.
      rewrite /this_type /=.
      apply wf_ty_class with Main => //.
      by apply gen_targs_wf_2.
    }
    (* dummy Γ *)
    exists Γ; split; first done.
    split.
    - apply FalseCmdTy => //.
      + split => //.
        rewrite /Γ /this_type /=.
        constructor.
        by repeat constructor.
      + apply SubConstraint.
        by set_solver.
    - apply FalseTy => //.
      apply SubConstraint.
      by set_solver.
  }
Qed.

Lemma wf: wf_cdefs pdefs.
Proof.
  split.
  by apply wf_extends_wf.
  by apply wf_parent.
  by apply wf_parent_ok.
  by apply wf_constraints_wf.
  by apply wf_constraints_ok.
  by apply wf_constraints_bounded.
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

(* Director level theorem: every execution that should produce an int
 * actually produceGs an int.
 *)
Theorem int_soundness cmd st lty n:
  cmd_eval "Main" (main_le, main_heap "Main") cmd st n →
  cmd_has_ty "Main" [] Plain 0 (main_lty "Main") cmd lty →
  ∀ v, lty.(ctxt) !! v = Some IntT →
  ∃ z, st.1.(lenv) !! v = Some (IntV z).
Proof.
  assert (wfinit : wf_lty (main_lty "Main")).
  { rewrite /main_lty; split => /=.
    - rewrite /this_type /=.
      by econstructor.
    - by apply map_Forall_empty.
  }
  assert (hinit: pdefs !! "Main" = Some (main_cdef "Main" {["entry_point" := EntryPoint ]})) by done.
  move => he ht v hin.
  apply (@step_updN_soundness sem_heapΘ n).
  iMod sem_heap_init as (Hheap) "Hmain" => //.
  iModIntro.
  iAssert (Σinterp [] []) as "Σcoherency".
  { iIntros (? ? h).
    by rewrite lookup_nil in h.
  }
  assert (wfΔ : Forall wf_constraint []) by by apply Forall_nil.
  iAssert (interp_env_as_mixed []) as "wfΣ".
  { iIntros (? ? h).
    by rewrite lookup_nil in h.
  }
  assert (hbounded: bounded_lty 0 (main_lty "Main")).
  { split; last by apply map_Forall_empty.
    rewrite /main_lty /this_type /=.
    constructor.
    by apply Forall_nil.
  }
  assert (hΔb : Forall (bounded_constraint 0) []) by by apply Forall_nil.
  iDestruct ((cmd_soundness "Main" [] _ [] _ _ _ wf wfinit hbounded wfΔ hΔb ht _ _ _ he) with "wfΣ Σcoherency Hmain") as "H" => /=.
  iRevert "H".
  iApply updN_mono.
  iIntros "[Hh [Hthis Hl]]".
  iSpecialize ("Hl" $! v IntT hin).
  iDestruct "Hl" as (w hw) "Hw".
  rewrite interp_type_unfold /=.
  iDestruct "Hw" as (z) "->".
  by eauto.
Qed.

Theorem class_soundness cmd st lty n:
  cmd_eval "Main" (main_le, main_heap "Main") cmd st n →
  cmd_has_ty "Main" [] Plain 0 (main_lty "Main") cmd lty →
  ∀ v T σ, lty.(ctxt) !! v = Some (ClassT T σ) →
  ∃ l Tdyn vs, st.1.(lenv) !! v = Some (LocV l) ∧
          st.2 !! l = Some (Tdyn, vs) ∧
          inherits Tdyn T.
Proof.
  assert (wfinit : wf_lty (main_lty "Main")).
  { rewrite /main_lty; split => /=.
    - rewrite /this_type /=.
      by econstructor.
    - by apply map_Forall_empty.
  }
  assert (hinit: pdefs !! "Main" = Some (main_cdef "Main" {["entry_point" := EntryPoint ]})) by done.
  move => he ht v T σ hin.
  apply (@step_updN_soundness sem_heapΘ n).
  iMod sem_heap_init as (Hheap) "Hmain" => //.
  iModIntro.
  iAssert (Σinterp [] []) as "Σcoherency".
  { iIntros (? ? h).
    by rewrite lookup_nil in h.
  }
  assert (wfΔ : Forall wf_constraint []) by by apply Forall_nil.
  iAssert (interp_env_as_mixed []) as "wfΣ".
  { iIntros (? ? h).
    by rewrite lookup_nil in h.
  }
  assert (hbounded: bounded_lty 0 (main_lty "Main")).
  { split; last by apply map_Forall_empty.
    rewrite /main_lty /this_type /=.
    constructor.
    by apply Forall_nil.
  }
  assert (hΔb : Forall (bounded_constraint 0) []) by by apply Forall_nil.
  iDestruct ((cmd_soundness "Main" [] _ [] _ _ _ wf wfinit hbounded wfΔ hΔb ht _ _ _ he) with "wfΣ Σcoherency Hmain") as "H" => /=.
  iRevert "H".
  iApply updN_mono.
  iIntros "[Hh [_ Hl]]".
  iSpecialize ("Hl" $! v (ClassT T σ) hin).
  iDestruct "Hl" as (w hw) "Hw".
  rewrite interp_type_unfold /=.
  rewrite interp_tag_equiv; last by apply wf_parent.
  iDestruct "Hw" as (l t cdef tdef σ0 Σt fields ifields) "[%hpure [#hmixed [#hΣt [#hinst [#hdyn #Hl]]]]]".
  destruct hpure as (-> & hcdef & htdef & hl0 & hl1 & hinherits & hfields & hidom).
  destruct st as [le h]; simpl in *.
  iDestruct "Hh" as (sh) "(H● & %Hdom & #Hh)".
  iDestruct (sem_heap_own_valid_2 with "H● Hl") as "#HΦ".
  iAssert (⌜is_Some (sh !! l)⌝)%I as "%h_sh_l".
  { by iRewrite "HΦ". }
  assert (h_h_l : is_Some (h !! l)).
  { assert (hh: l ∈ dom sh) by (by apply elem_of_dom).
    rewrite Hdom in hh.
    by apply elem_of_dom in hh.
  }
  destruct h_h_l as [[Tdyn vs] hl].
  iDestruct ("Hh" with "[//]") as (?) "[H H▷]".
  iRewrite "H" in "HΦ".
  rewrite option_equivI prod_equivI /=.
  iDestruct "HΦ" as "[%Ht HΦ]".
  fold_leibniz; subst.
  iPureIntro.
  exists l, t, vs; repeat split => //.
  by apply inherits_using_erase in hinherits.
Qed.

Print Assumptions int_soundness.
