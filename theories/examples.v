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

From shack Require Import lang heap modality interp adequacy.

(* TODO: we don't have void atm so I'm using null ;) *)

(* Definition of class Box<T>:
 * class Box<T> {
 *   T $data;
 *   function set(T $data) : void { $this->data = $data; }
 *   function get(): T { $ret = $this->data; return $ret; }
 * }
 *)
Definition BoxSet := {|
  methodname := "set";
  methodargs := {["$data" := GenT 0 ]};
  methodrettype := NullT;
  methodbody := SetC (VarE "$this") "$data" (VarE "$data");
  methodret := NullE;
|}.

Definition BoxGet := {|
  methodname := "get";
  methodargs := ∅;
  methodrettype := GenT 0;
  methodbody := GetC "$ret" (VarE "$this") "$data";
  methodret := VarE "$ret";
|}.

Definition Box := {|
  classname := "Box";
  superclass := None;
  generics := [Invariant];
  classfields := {["$data" := GenT 0]};
  classmethods := {["set" := BoxSet; "get" := BoxGet]};
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
  methodbody := SetC (VarE "$this") "$data" (OpE PlusO (VarE "$data") (IntE 1%Z));
  methodret := NullE;
|}.

Definition IntBoxS := {|
  classname := "IntBoxS";
  superclass := Some ("Box", σ);
  generics := [];
  classfields := ∅;
  classmethods := {["set" := IntBoxSSet]};
|}.

(* Main program:
 * function main(): bool {
 *   $box = new IntBoxS(32);
 *   $tmp = $box->get();
 *   $tmp = $tmp + 20;
 *   $_ = $box->set($tmp - 10);
 *   $tmp = $box->data;
 *   return ($tmp == 43);
 * }
 *)
Definition ProgramBody :=
   SeqC (NewC "$box" "IntBoxS" {["$data" := IntE 32]})
  (SeqC (CallC "$tmp" (VarE "$box") "get" ∅)
  (SeqC (LetC "$tmp" (OpE PlusO (VarE "$tmp") (IntE 20)))
  (SeqC (CallC "$_" (VarE "$box") "set"
           {["$data" := OpE MinusO (VarE "$tmp") (IntE 10)]})
        (GetC "$tmp" (VarE "$box") "$data")
  ))).

Definition Main := {|
  methodname := "main";
  methodargs := ∅;
  methodrettype := BoolT;
  methodbody := ProgramBody;
  methodret := OpE EqO (VarE "$tmp") (IntE 43);
|}.

Local Instance PDC : ProgDefContext := { Δ := {[ "Box" := Box; "IntBoxS" := IntBoxS ]} }.

Lemma wfσ : Forall wf_ty σ.
Proof.
  apply Forall_forall => x hx.
  apply elem_of_list_lookup_1 in hx.
  destruct hx as [n hx].
  rewrite /σ /= in hx.
  apply list_lookup_singleton_Some in hx as [-> <-].
  by constructor.
Qed.

Lemma σbounded : Forall (bounded (length (generics IntBoxS))) σ.
Proof.
  apply Forall_forall => x hx.
  apply elem_of_list_lookup_1 in hx.
  destruct hx as [n hx].
  rewrite /σ /= in hx.
  apply list_lookup_singleton_Some in hx as [-> <-].
  by constructor.
Qed.

Lemma has_method_get: has_method "get" "IntBoxS" "Box" (subst_mdef σ BoxGet).
Proof. by repeat econstructor; eauto. Qed.

Lemma has_method_set: has_method "set" "IntBoxS" "IntBoxS" IntBoxSSet.
Proof. by repeat econstructor; eauto. Qed.

Lemma has_fields_IntBoxS : has_fields "IntBoxS" {[ "$data" := IntT ]}.
Proof.
  move => f fty; split => h.
  - inv h.
    + rewrite /Δ /= lookup_insert_ne // lookup_insert in H; by simplify_eq.
    + rewrite /Δ /= lookup_insert_ne // lookup_insert in H; simplify_eq.
      rewrite /IntBoxS /= in H1 H0.
      injection H1; intros; subst; clear H1.
      inv H2.
      * rewrite /Δ /= lookup_insert in H; simplify_eq.
        rewrite /Box /= lookup_insert_Some in H1.
        destruct H1 as [[<- <-]|[?]]; last by rewrite lookup_empty in H1.
        by rewrite lookup_insert.
      * by rewrite /Δ /= lookup_insert in H; simplify_eq.
  - rewrite lookup_insert_Some in h.
    destruct h as [[<- <-] | [? h]]; last by rewrite lookup_empty in h.
    change IntT with (subst_ty σ (GenT 0)).
    eapply InheritsField => //.
    econstructor.
    + by rewrite /Δ /= lookup_insert.
    + by rewrite /Box /=.
Qed.

Definition final_le le new_loc : local_env :=
   <["$_":=NullV]>
  (<["$tmp":=IntV 43]>
  (<["$box":=LocV new_loc]> le)).

Definition final_heap (h: heap) new_loc :=
  <[new_loc := ("IntBoxS", {["$data" := IntV 43]})]> h.

Lemma Main_eval st:
 ∀ new_loc, st.2 !! new_loc = None →
 cmd_eval st ProgramBody (final_le st.1 new_loc, final_heap st.2 new_loc) 5.
Proof.
  case: st => le h /= new_loc hnew.
  rewrite /ProgramBody.
  change 5 with (1 + (2 + (0 + (1 + 1)))).
  apply SeqEv with (<["$box" := LocV new_loc]>le,
                    <[new_loc := ("IntBoxS", {["$data" := IntV 32]})]> h).
  { apply NewEv; first done.
    rewrite /map_args option_guard_True /=; first by rewrite omap_singleton.
    by apply map_Forall_singleton.
  }
  eapply SeqEv.
  { eapply CallEv => /=.
    - by rewrite lookup_insert.
    - rewrite /map_args option_guard_True; first done.
      by apply map_Forall_empty.
    - by rewrite lookup_insert.
    - by apply has_method_get.
    - by rewrite omap_empty.
    - eapply GetEv.
      + by rewrite /= lookup_insert.
      + by rewrite lookup_insert.
      + by rewrite lookup_insert.
    - by rewrite /BoxGet /= lookup_insert.
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
    - by rewrite omap_singleton /= lookup_insert.
    - rewrite /IntBoxSSet /=.
      eapply SetEv.
      + by rewrite /= lookup_insert.
      + by rewrite /= lookup_insert_ne.
      + by rewrite lookup_insert.
      + done.
    - by rewrite /IntBoxSSet /=.
  }
  replace (final_le le new_loc) with
    ( <["$tmp" := IntV 43]>
     (<["$_":=NullV]>
     (<["$tmp":=IntV (32 + 20)]>
     (<["$tmp":=IntV 32]> (<["$box":=LocV new_loc]> le))))); last first.
  { (* TODO: set/naive solver ? *) apply map_eq => k.
    rewrite /final_le.
    destruct (decide (k = "$tmp")) as [-> | ?];
        first by rewrite lookup_insert lookup_insert_ne // lookup_insert.
    rewrite lookup_insert_ne //.
    destruct (decide (k = "$_")) as [-> | ?]; first by rewrite !lookup_insert.
    do 3 (rewrite lookup_insert_ne //).
    destruct (decide (k = "$box")) as [-> | ?]; last by rewrite !lookup_insert_ne.
    rewrite lookup_insert lookup_insert_ne // lookup_insert_ne //.
    by rewrite lookup_insert.
  }
  replace (final_heap h new_loc) with
    ( <[new_loc:=("IntBoxS", {["$data" := IntV (33 + 20 - 10); "$data" := IntV 32]})]>
     (<[new_loc:=("IntBoxS", {["$data" := IntV 32]})]> h)); last first.
  { rewrite /final_heap.
    apply map_eq => k.
    destruct (decide (k = new_loc)) as [-> | hne].
    + rewrite !lookup_insert.
      repeat f_equal.
      apply map_eq => k.
      destruct (decide (k = "$data")) as [-> | ?]; first by rewrite !lookup_insert.
      by rewrite !lookup_insert_ne.
    + by rewrite !lookup_insert_ne.
  }
  eapply GetEv.
  - rewrite /= lookup_insert_ne // lookup_insert_ne //.
    by rewrite lookup_insert_ne // lookup_insert.
  - by rewrite lookup_insert. 
  - by rewrite lookup_insert.
Qed.

Definition final_lty lty : local_tys :=
   <["$tmp":=IntT]>
  (<["$_" := NullT]>
  (<["$box":=ClassT "IntBoxS" []]> lty)).

Lemma Main_ty lty :
  cmd_has_ty lty ProgramBody (final_lty lty).
Proof.
  rewrite /final_lty /ProgramBody.
  eapply SeqTy.
  { eapply NewTy with (targs := []).
    + by econstructor.
    + by apply has_fields_IntBoxS.
    + by set_solver.
    + move => f fty arg.
      rewrite !lookup_insert_Some.
      case => [[<- <-] | [? ?]].
      * case => [[_ <-] | [? ?]]; last done.
        by constructor.
      * case => [[? ?] | [? ?]]; by simplify_eq.
  }
  eapply SeqTy.
  { eapply CallTy.
    + econstructor.
      by rewrite lookup_insert.
    + by apply has_method_get.
    + rewrite /BoxGet /=.
      by set_solver.
    + by move => x ty arg; rewrite /BoxGet /= lookup_empty.
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
      rewrite lookup_insert_ne //.
      rewrite lookup_insert_ne //.
      by rewrite lookup_insert.
    + by apply has_method_set.
    + rewrite /BoxGet /=.
      by set_solver.
    + move => x ty arg; rewrite /BoxGet /= lookup_insert_Some.
      case => [[<- <-]|[? ?]].
      * rewrite lookup_insert => [= <-].
        constructor; first done.
        - constructor; by rewrite lookup_insert.
        - by constructor.
      * rewrite lookup_insert_Some.
        case => [[? ?]| [? ?]]; by simplify_eq.
  }
  rewrite /IntBoxSSet /=.
  eapply SubTy; last first.
  - eapply GetTy; last by apply has_fields_IntBoxS.
    constructor.
    do 3 (rewrite lookup_insert_ne //).
    by rewrite lookup_insert.
  - move => v ty.
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


Lemma helper_ext: ∀ A B σ0, extends_using A B σ0 → A = "IntBoxS" ∧ B = "Box" ∧ σ0 = σ.
Proof.
  move => A B σ0 h; inv h.
  rewrite /Δ /= lookup_insert_Some in H.
  destruct H as [[<- <-] | [? H]].
  + by rewrite /Box in H0.
  + rewrite lookup_insert_Some in H.
    destruct H as [[<- <-] | [? H]]; last by rewrite lookup_empty in H.
    rewrite /IntBoxS /= in H0; by simplify_eq.
Qed.

Lemma helper_in_Box : ∀ T σt, inherits_using "Box" T σt → T = "Box" ∧ σt = [GenT 0].
Proof.
  move => T σt h; inv h.
  + rewrite /Δ /= lookup_insert in H.
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
  + rewrite /Δ /= lookup_insert_ne // lookup_insert in H.
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
     (A = "Box" ∧ B = "Box" ∧ σ0 = [GenT 0]).
Proof.
  move => A B σ0 h.
  inv h.
  + rewrite /Δ /= lookup_insert_Some in H.
    destruct H as [[<- ?]|[? H]]; first (right; right; by rewrite -H).
    rewrite lookup_insert_Some in H.
    destruct H as [[<- ?]|[? H]]; first (right; left; by rewrite -H).
    by rewrite lookup_empty in H.
  + apply helper_ext in H as [-> [-> ->]].
    by left.
  + apply helper_ext in H as [-> [-> ->]].
    apply helper_in_Box in H0 as [-> ->].
    by left.
Qed.

Lemma wf: wf_cdefs Δ.
Proof.
  rewrite /Δ /=.
  split.
  - move => A B σ0 σ1 h0 h1.
    apply helper_in in h0.
    destruct h0 as [[-> [-> ->]] | [[-> [-> ->]] | [-> [-> ->]]]].
    + apply helper_in_Box in h1; by destruct h1; discriminate.
    + apply helper_in_IntBoxS in h1 as [[_ ->] | [h ?]]; last discriminate.
      done.
    + apply helper_in_Box in h1 as [_ ->].
      done.
  - apply map_Forall_lookup => c0 d0.
    rewrite lookup_insert_Some.
    case => [[? <-] | [?]] => //.
    rewrite lookup_insert_Some.
    case => [[? <-] | [?]] => //.
    exists Box;repeat split => //.
    + by apply wfσ.
    + by apply σbounded.
  - move => A B adef bdef m σ0 mA mB hA hB hin hmA hmB.
    apply helper_in in hin.
    destruct hin as [[-> [-> ->]] | [[-> [-> ->]] | [-> [-> ->]]]]; first last.
    + simplify_eq.
      rewrite /Δ /= lookup_insert in hA.
      injection hA; intros; subst; clear hA.
      rewrite /Box /= in hmA.
      rewrite lookup_insert_Some in hmA.
      destruct hmA as [[<- <-]|[? hmA]].
      * rewrite /mdef_incl /BoxSet /subst_mdef /=.
        split; first by set_solver.
        split; last done.
        move => k A B.
        rewrite lookup_insert_Some.
        case => [[<- <-]|[?]]; last by rewrite lookup_empty.
        rewrite lookup_fmap lookup_insert /=.
        by case => <-.
      * rewrite lookup_insert_Some in hmA.
        destruct hmA as [[<- <-]|[? hmA]]; last by rewrite lookup_empty in hmA.
        rewrite /mdef_incl /BoxGet /subst_mdef /=.
        split; first by set_solver.
        split; last done.
        move => k A B.
        by rewrite lookup_empty.
    + simplify_eq.
      rewrite /Δ /= lookup_insert_ne // lookup_insert in hA.
      injection hA; intros; subst; clear hA.
      rewrite /IntBoxS /= in hmA.
      rewrite lookup_insert_Some in hmA.
      destruct hmA as [[<- <-]|[? hmA]]; last by rewrite lookup_empty in hmA.
      rewrite /mdef_incl /IntBoxSSet /subst_mdef /=.
      split; first by set_solver.
      split; last done.
      move => k A B.
      rewrite lookup_insert_Some.
      case => [[<- <-]|[?]]; last by rewrite lookup_empty.
      rewrite lookup_fmap lookup_insert /=.
      by case => <-.
    + rewrite /Δ /= in hA, hB.
      rewrite lookup_insert_ne // in hA.
      rewrite !lookup_insert in hA, hB.
      injection hA; injection hB; intros; subst; clear hA hB.
      rewrite /IntBoxS /= in hmA.
      rewrite /Box /= in hmB.
      rewrite lookup_insert_Some in hmA.
      destruct hmA as [[<- <-]|[? hmA]]; last by rewrite lookup_empty in hmA.
      rewrite lookup_insert in hmB.
      injection hmB; intros; subst; clear hmB.
      rewrite /mdef_incl /IntBoxSSet /BoxSet /subst_mdef /σ /=.
      split; first by set_solver.
      split; last done.
      move => k A B.
      rewrite lookup_insert_Some.
      case => [[<- <-]|[?]]; last by rewrite lookup_empty.
      rewrite lookup_fmap_Some.
      case => [ty [<-]].
      rewrite lookup_insert.
      by case => <-.
  - rewrite map_Forall_lookup => c0 d0.
    rewrite lookup_insert_Some.
    case => [[? <-]|[?]].
    { by rewrite /wf_cdef_fields /Box. }
    rewrite lookup_insert_Some.
    case => [[? <-]|[?]]; last by rewrite lookup_empty.
    by rewrite /wf_cdef_fields /IntBoxS.
  - rewrite map_Forall_lookup => c0 d0.
    rewrite lookup_insert_Some.
    case => [[? <-]|[?]].
    { rewrite /wf_cdef_fields_bounded /Box /=.
      rewrite map_Forall_singleton.
      econstructor.
      by auto with arith.
    }
    rewrite lookup_insert_Some.
    case => [[? <-]|[?]]; last by rewrite lookup_empty.
    rewrite /wf_cdef_fields_bounded /IntBoxS /=.
    by apply map_Forall_empty.
  - rewrite map_Forall_lookup => c0 d0.
    rewrite lookup_insert_Some.
    case => [[? <-]|[?]].
    { rewrite /wf_cdef_fields_wf /Box /=.
      rewrite map_Forall_singleton.
      by econstructor.
    }
    rewrite lookup_insert_Some.
    case => [[? <-]|[?]]; last by rewrite lookup_empty.
    rewrite /wf_cdef_fields_bounded /IntBoxS /=.
    by apply map_Forall_empty.
  - rewrite map_Forall_lookup => c0 d0.
    rewrite lookup_insert_Some.
    case => [[? <-]|[?]].
    { rewrite /wf_field_mono /Box /=.
      rewrite map_Forall_lookup => x mx.
      rewrite lookup_insert_Some.
      case => [[? <-]|[?]]; last by rewrite lookup_empty.
      split; by constructor.
    }
    rewrite lookup_insert_Some.
    case => [[? <-]|[?]]; last by rewrite lookup_empty.
    rewrite /wf_field_mono /IntBoxS /=.
    by apply map_Forall_empty.
  - rewrite map_Forall_lookup => c0 d0.
    rewrite lookup_insert_Some.
    case => [[? <-]|[?]].
    { rewrite /cdef_methods_bounded /Box /=.
      rewrite map_Forall_lookup => x mx.
      rewrite lookup_insert_Some.
      case => [[? <-]|[?]].
      + split; last by constructor.
        rewrite /BoxSet /=.
        rewrite map_Forall_singleton.
        constructor.
        by auto with arith.
      + rewrite lookup_insert_Some.
        case => [[? <-]|[?]]; last by rewrite lookup_empty.
        split.
        * rewrite /BoxGet /=.
          by apply map_Forall_empty.
        * rewrite /BoxGet /=.
          constructor.
          by auto with arith.
    }
    rewrite lookup_insert_Some.
    case => [[? <-]|[?]]; last by rewrite lookup_empty.
    rewrite /cdef_methods_bounded /IntBoxS /=.
    rewrite map_Forall_singleton.
    split; last done.
    rewrite /IntBoxSSet /=.
    rewrite map_Forall_singleton.
    by constructor.
  - rewrite map_Forall_lookup => c0 d0.
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
        * rewrite /BoxGet /=.
          by apply map_Forall_empty.
        * rewrite /BoxGet /=.
          by constructor.
    }
    rewrite lookup_insert_Some.
    case => [[? <-]|[?]]; last by rewrite lookup_empty.
    rewrite /wf_cdef_methods_wf /IntBoxS /=.
    rewrite map_Forall_singleton.
    split.
    + rewrite /IntBoxSSet /=.
      rewrite map_Forall_singleton.
      by constructor.
    + rewrite /IntBoxSSet /=.
      by constructor.
  - rewrite map_Forall_lookup => c0 d0.
    rewrite lookup_insert_Some.
    case => [[? <-]|[?]].
    + rewrite /wf_cdef_methods_mono /Box /=.
      rewrite map_Forall_lookup => x mx.
      rewrite lookup_insert_Some.
      case => [[? <-]|[?]].
      * rewrite /wf_mdef_mono /BoxSet /=.
        split; last by constructor.
        apply map_Forall_singleton.
        by constructor.
      * rewrite lookup_insert_Some.
        case => [[? <-]|[?]]; last by rewrite lookup_empty.
        rewrite /wf_mdef_mono /BoxGet /=.
        split; first by apply map_Forall_empty.
        by constructor.
    + rewrite lookup_insert_Some.
      case => [[? <-]|[?]]; last by rewrite lookup_empty.
      rewrite /wf_cdef_methods_mono /IntBoxS /=.
      apply map_Forall_singleton.
      rewrite /wf_mdef_mono /IntBoxSSet /=.
      split; last by constructor.
      apply map_Forall_singleton.
      by constructor.
  - rewrite map_Forall_lookup => c0 d0.
    rewrite lookup_insert_Some.
    case => [[<- <-]|[?]].
    + rewrite /cdef_wf_mdef_ty /Box /=.
      rewrite map_Forall_lookup => x mx.
      rewrite lookup_insert_Some.
      case => [[? <-]|[?]].
      * rewrite /wf_mdef_ty /BoxSet /=.
        eexists.
        split; first last.
        { split ; last by constructor.
          eapply SetTy.
          - constructor.
            by rewrite lookup_insert.
          - by eapply HasField.
          - constructor.
            by rewrite lookup_insert_ne.
        }
        rewrite map_Forall_lookup => k t /=.
        rewrite lookup_insert_Some.
        case => [[? <-]|[?]].
        { econstructor => //.
          by apply gen_targs_wf.
        }
        rewrite lookup_fmap_Some.
        case => [ty [<- ]].
        rewrite lookup_singleton_Some.
        case => ? <-.
        by constructor.
      * rewrite lookup_insert_Some.
        case => [[? <-]|[?]]; last by rewrite lookup_empty.
        rewrite /wf_mdef_ty /BoxGet /=.
        eexists; split; first last.
        { split.
          - eapply GetTy.
            + constructor.
              by rewrite lookup_insert.
            + by eapply HasField.
          - constructor.
            by rewrite lookup_insert.
        }
        rewrite map_Forall_lookup => k t /=.
        rewrite lookup_insert_Some.
        case => [[? <-]|[?]]; first by constructor.
        rewrite lookup_insert_Some.
        case => [[? <-]|[?]].
        { econstructor => //.
          by apply gen_targs_wf.
        }
        by rewrite fmap_empty lookup_empty.
    + rewrite lookup_insert_Some.
      case => [[<- <-]|[?]]; last by rewrite lookup_empty.
      rewrite /cdef_wf_mdef_ty /IntBoxS /=.
      rewrite map_Forall_singleton.
      eexists.
      split; first last.
      * split; last by constructor.
        rewrite /IntBoxSSet /=.
        eapply SetTy.
        { constructor.
          by rewrite lookup_insert.
        }
        { eapply InheritsField => //.
          by eapply HasField.
        }
        { constructor => //.
          - constructor.
            by rewrite lookup_insert_ne.
          - by constructor.
        }
      * rewrite map_Forall_lookup => x tx.
        rewrite lookup_insert_Some.
        case => [[? <-]|[?]]; first by econstructor.
        rewrite lookup_fmap_Some.
        case => [ty [<-]].
        rewrite lookup_singleton_Some.
        case => [? <-].
        by constructor.
  - rewrite map_Forall_lookup => x cx.
    rewrite lookup_insert_Some.
    case => [[? <-]|[?]]; first done.
    rewrite lookup_singleton_Some.
    case => [? <-].
    rewrite /wf_cdef_mono /IntBoxS /=.
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
Qed.

(* Director level theorem: every execution that should produce an int
 * actually produces an int.
 *)
Theorem int_adequacy cmd st lty n:
  cmd_eval (∅, ∅) cmd st n →
  cmd_has_ty ∅ cmd lty →
  ∀ v, lty !! v = Some IntT →
  ∃ z, st.1 !! v = Some (IntV z).
Proof.
  assert (wfemp : map_Forall (λ _ : string, wf_ty) ∅) by apply map_Forall_empty.
  move => he ht v hin.
  apply (@step_updN_soundness sem_heapΣ n).
  iMod sem_heap_init as (Hheap) "Hemp".
  iModIntro.
  iDestruct ((cmd_adequacy interp_env_empty _ _ _ wf wfemp ht _ _ _ he) with "Hemp") as "H" => /=.
  iRevert "H".
  iApply updN_mono.
  iIntros "[Hh Hl]".
  iSpecialize ("Hl" $! v IntT hin).
  iDestruct "Hl" as (w hw) "Hw".
  rewrite interp_type_unfold /=.
  iDestruct "Hw" as (z) "->".
  by eauto.
Qed.

Print Assumptions int_adequacy.
