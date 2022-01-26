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
(* Definition of class BoxInt:
 * class BoxInt {
 *   int $data;
 *   function set(int $data) : void { $this->data = $data; }
 *   function get(): int { $ret = $this->data; return $ret; }
 * }
 *)
Definition BoxIntSet := {|
  methodname := "set";
  methodargs := {["$data" := IntT ]};
  methodrettype := NullT;
  methodbody := SetC (VarE "$this") "$data" (VarE "$data");
  methodret := NullE;
|}.

Definition BoxIntGet := {|
  methodname := "get";
  methodargs := ∅;
  methodrettype := IntT;
  methodbody := GetC "$ret" (VarE "$this") "$data";
  methodret := VarE "$ret";
|}.

Definition BoxInt := {|
  classname := "BoxInt";
  superclass := None;
  generics := 0;
  classfields := {["$data" := IntT]};
  classmethods := <["set" := BoxIntSet]>{["get" := BoxIntGet]};
|}.

(* Main program:
 * function main(): bool {
 *   $box = new BoxInt(32);
 *   $tmp = $box->get();
 *   $tmp = $tmp + 20;
 *   $_ = $box->set($tmp - 10);
 *   $tmp = $box->data;
 *   return ($tmp == 42);
 * }
 *)
Definition ProgramBody :=
   SeqC (NewC "$box" "BoxInt" [] {["$data" := IntE 32]})
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
  methodret := OpE EqO (VarE "$tmp") (IntE 42);
|}.

Local Instance PDC : ProgDefContext := { Δ := {[ "BoxInt" := BoxInt ]} }.

Lemma has_method_get: has_method "get" BoxIntGet "BoxInt".
Proof. by repeat econstructor; eauto. Qed.

Lemma has_method_set: has_method "set" BoxIntSet "BoxInt".
Proof. by repeat econstructor; eauto. Qed.

Lemma has_fields_BoxInt : has_fields "BoxInt" {[ "$data" := IntT ]}.
Proof.
  move => f fty; split => h.
  - inv h.
    + rewrite /Δ /= lookup_insert in H; simplify_eq.
      by rewrite /BoxInt /= in H0.
    + rewrite /Δ /= lookup_insert in H; by simplify_eq.
  - rewrite lookup_insert_Some in h.
    destruct h as [[<- <-] | [? ?]]; first by eauto.
    by rewrite lookup_empty in H0.
Qed.

Definition final_le le new_loc : local_env :=
   <["$_":=NullV]>
  (<["$tmp":=IntV 42]>
  (<["$box":=LocV new_loc]> le)).

Definition final_heap (h: heap) new_loc :=
  <[new_loc := ("BoxInt", {["$data" := IntV 42]})]> h.

Lemma Main_eval st:
 ∀ new_loc, st.2 !! new_loc = None →
 cmd_eval st ProgramBody (final_le st.1 new_loc, final_heap st.2 new_loc) 5.
Proof.
  case: st => le h /= new_loc hnew.
  rewrite /ProgramBody.
  change 5 with (1 + (2 + (0 + (1 + 1)))).
  apply SeqEv with (<["$box" := LocV new_loc]>le,
                    <[new_loc := ("BoxInt", {["$data" := IntV 32]})]> h).
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
    - by rewrite /BoxIntGet /= lookup_insert.
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
    - rewrite /BoxIntSet /=.
      eapply SetEv.
      + by rewrite /= lookup_insert.
      + by rewrite /= lookup_insert_ne.
      + by rewrite lookup_insert.
      + done.
    - by rewrite /BoxIntSet /=.
  }
  replace (final_le le new_loc) with
    ( <["$tmp" := IntV 42]>
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
    ( <[new_loc:=("BoxInt", {["$data" := IntV (32 + 20 - 10); "$data" := IntV 32]})]>
     (<[new_loc:=("BoxInt", {["$data" := IntV 32]})]> h)); last first.
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
  (<["$box":=ClassT "BoxInt" []]> lty)).

Lemma Main_ty lty :
  cmd_has_ty lty ProgramBody (final_lty lty).
Proof.
  rewrite /final_lty /ProgramBody.
  eapply SeqTy.
  { eapply NewTy.
    + by apply has_fields_BoxInt.
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
    + rewrite /BoxIntGet /=.
      by set_solver.
    + by move => x ty arg; rewrite /BoxIntGet /= lookup_empty.
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
    + rewrite /BoxIntGet /=.
      by set_solver.
    + move => x ty arg; rewrite /BoxIntGet /= lookup_insert_Some.
      case => [[<- <-]|[? ?]].
      * rewrite lookup_insert => [= <-].
        constructor; first done.
        - constructor; by rewrite lookup_insert.
        - by constructor.
      * rewrite lookup_insert_Some.
        case => [[? ?]| [? ?]]; by simplify_eq.
  }
  rewrite /BoxIntSet /=.
  eapply SubTy; last first.
  - eapply GetTy; last by apply has_fields_BoxInt.
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
        case : h => ->.
        by exists ty.
      }
      rewrite lookup_insert_ne // in h.
      rewrite lookup_insert_ne // in h.
      exists ty.
      by rewrite lookup_insert_ne.
Qed.

Lemma wf: wf_cdefs Δ.
Proof.
  rewrite /Δ /=.
  split.
  - apply map_Forall_singleton.
    by rewrite /wf_cdef_fields /BoxInt /= => f fty super.
  - apply map_Forall_singleton.
    by rewrite /wf_cdef_methods /BoxInt /=.
  - apply map_Forall_singleton.
    rewrite /BoxInt /=.
    apply map_Forall_lookup => m mdef.
    rewrite lookup_insert_Some.
    case => [[? ?] | [? h]]; simplify_eq.
    + rewrite /BoxIntSet /wf_mdef_ty /=.
      eexists; split; last by constructor.
      econstructor.
      * constructor.
        by rewrite lookup_insert.
      * by eauto.
      * constructor.
        by rewrite lookup_insert_ne.
    + rewrite /wf_mdef_ty /=.
      rewrite lookup_insert_Some in h.
      destruct h as [[<- <-]|[hne hin]].
      * rewrite /BoxIntGet /=.
        eexists; split.
        { econstructor.
          constructor.
          by rewrite lookup_insert.
          by eauto.
        }
        constructor.
        by rewrite lookup_insert.
      * by rewrite lookup_empty in hin.
Qed.

Theorem int_adequacy cmd st lty n:
  cmd_eval (∅, ∅) cmd st n →
  cmd_has_ty ∅ cmd lty →
  ∀ v, lty !! v = Some IntT →
  ∃ z, st.1 !! v = Some (IntV z).
Proof.
  move => he ht v hin.
  apply (@step_updN_soundness sem_heapΣ n).
  iMod sem_heap_init as (Hheap) "Hemp".
  iModIntro.
  iDestruct ((cmd_adequacy interp_env_empty _ _ _ wf ht _ _ _ he) with "Hemp") as "H" => /=.
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
