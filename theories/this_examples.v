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
From shack Require Import eval heap.

From shack.reflect Require Import lang progdef.

Definition arraykey := UnionT IntT BoolT.

(* Definition of class C:
 * class C {
 *   function f(this $_): void {}
 *)
Definition f := {|
  methodargs := {[ "$in" := ThisT ]};
  methodrettype := NullT;
  methodbody := SkipC;
  methodret := NullE;
  methodvisibility := Public;
|}.

Definition C := {|
  superclass := None;
  generics := [];
  constraints := [];
  classfields := ∅;
  classmethods := {["f" := f]};
|}.

(* TODO simpl g *)
(* Definition of class D:
 * class D extends C {
 *   function f(this $in): void {
        $in->g($in);
   }
 *   function g(this $_): void {}
 *)
Definition f2 := {|
  methodargs := {[ "$in" := ThisT ]};
  methodrettype := NullT;
  methodbody := CallC "$_" (VarE "$in") "g" {[ "$in" := VarE "$in" ]};
  methodret := NullE;
  methodvisibility := Public;
|}.

Definition g := f.

Definition D := {|
  superclass := Some ("C", []);
  generics := [];
  constraints := [];
  classfields := ∅;
  classmethods := {["f" := f2; "g" := g]};
|}.

(* Main program:
    function problem(C $c0, C $c1) : void {
      $r = $c0->f($c1);
   }

    function main(): void {
      problem(new D(), new C());
    }
*)
Definition MainBody :=
   SeqC (NewC "$d" "D" (Some []) ∅)
  (SeqC (NewC "$c" "C" (Some []) ∅)
        (CallC "$tmp" ThisE "problem" {[ "$c0" := VarE "$d"; "$c1" := VarE "$c"]}))
  .

Definition problem := {|
  methodargs := {[ "$c0" := ClassT false "C" []; "$c1" := ClassT false "C" [] ]};
  methodrettype := NullT;
  methodbody := CallC "$_" (VarE "$c0") "f" {[ "$in" := VarE "$c1" ]};
  methodret := NullE;
  methodvisibility := Public;
|}.

Definition main := {|
  methodargs := ∅;
  methodrettype := NullT;
  methodbody := MainBody;
  methodret := NullE;
  methodvisibility := Public;
|}.

Definition Main := {|
  superclass := None;
  generics := [];
  constraints := [];
  classfields := ∅;
  classmethods := {["main" := main; "problem" := problem ]}
 |}.

Definition pdefs0: stringmap classDef := {[ "C" := C; "D" := D; "Main" := Main ]}.

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
  - move =>>; rewrite list_lookup_singleton_Some => [[? <-]]; by constructor.
  - move =>>; rewrite list_lookup_singleton_Some => [[? <-]]; by constructor.
  - move =>> ?; rewrite list_lookup_singleton_Some => [[? <-]]; by constructor.
  - move =>> ?; rewrite list_lookup_singleton_Some => [[? <-]]; by constructor.
  - move =>>; rewrite list_lookup_singleton_Some => [[? <-]]; by constructor.
  - move =>>; rewrite list_lookup_singleton_Some => [[? <-]]; by constructor.
Qed.

Lemma has_method_C_f: has_method "f" "C" "C" f.
Proof. by repeat econstructor; eauto. Qed.

Lemma has_method_D_f: has_method "f" "D" "D" f2.
Proof. by repeat econstructor; eauto. Qed.

Lemma has_method_D_g: has_method "g" "D" "D" g.
Proof. by repeat econstructor; eauto. Qed.

Lemma has_method_Main_problem: has_method "problem" "Main" "Main" problem.
Proof. by repeat econstructor; eauto. Qed.

Lemma has_method_Main_main: has_method "main" "Main" "Main" main.
Proof. by repeat econstructor; eauto. Qed.

Lemma has_fields_C : has_fields "C" ∅.
Proof.
  move => f vis fty orig; split => h.
  - inv h.
    + rewrite /pdefs /= lookup_insert in H.
      by simplify_eq.
    + by rewrite /pdefs /= lookup_insert in H; simplify_eq.
  - by rewrite lookup_empty in h.
Qed.

Lemma has_fields_D : has_fields "D" ∅.
Proof.
  move => f vis fty orig; split => h.
  - inv h.
    + rewrite /pdefs /= lookup_insert_ne in H; last done.
      rewrite lookup_insert in H.
      by simplify_eq.
    + rewrite /pdefs /= lookup_insert_ne in H; last done.
      rewrite lookup_insert in H; simplify_eq.
      rewrite /D /= in H1; simplify_eq.
      move : has_fields_C => hf0.
      apply hf0 in H2.
      by rewrite lookup_empty in H2.
  - by rewrite lookup_empty in h.
Qed.

Lemma has_fields_Main : has_fields "Main" ∅.
Proof.
  move => f vis fty orig; split => h.
  - inv h.
    + rewrite /pdefs /= lookup_insert_ne in H; last done.
      rewrite lookup_insert_ne in H; last done.
      rewrite lookup_insert in H.
      by simplify_eq.
    + rewrite /pdefs /= lookup_insert_ne in H; last done.
      rewrite lookup_insert_ne in H; last done.
      rewrite lookup_insert in H; by simplify_eq.
  - by rewrite lookup_empty in h.
Qed.

(* TODO: name this *)
Definition ΔC :=
  let n := length C.(generics) in
  let σ := gen_targs n in
  (ThisT, ClassT false "C" σ) :: C.(constraints).

Lemma wf_mdef_ty_C_f: wf_mdef_ty "C" ΔC 0 f.
Proof.
  rewrite /wf_mdef_ty.
  exists f.(methodargs).
  repeat split.
  - apply map_Forall_lookup => k tk. 
    rewrite /f /=.
    by rewrite lookup_singleton_Some => [[? <-]].
  - rewrite /f /=.
    by apply SkipTy.
  - rewrite /f /=.
    by apply NullTy.
Qed.

Definition ΔD :=
  let n := length D.(generics) in
  let σ := gen_targs n in
  (ThisT, ClassT false "D" σ) :: D.(constraints).

Lemma wf_mdef_ty_D_f: wf_mdef_ty "D" ΔD 0 f2.
Proof.
  rewrite /wf_mdef_ty /f2 /=.
  exists (<[ "$_" := NullT]> f2.(methodargs)).
  repeat split.
  - apply map_Forall_insert_2; first by constructor.
    apply map_Forall_singleton; by constructor.
  - rewrite /f2 /=.
    change {["$_" := NullT; "$in" := ThisT]}
    with (<["$_" := g.(methodrettype)]> f2.(methodargs)).
    apply CallThisTy  with (cdef := D) (orig := "D") => //.
    + constructor.
      by set_solver.
    + by apply HasMethod with (cdef := D).
    + by rewrite /g /= !dom_insert_L !dom_empty_L.
    + move => k ty arg hk.
      rewrite lookup_singleton_Some => [[heq <-]]; simplify_eq.
      by constructor.
  - by apply NullTy.
Qed.

Lemma wf_mdef_ty_D_g: wf_mdef_ty "D" ΔD 0 g.
Proof.
  rewrite /wf_mdef_ty.
  exists g.(methodargs).
  repeat split.
  - apply map_Forall_lookup => k tk. 
    rewrite /g /=.
    by rewrite lookup_singleton_Some => [[? <-]].
  - rewrite /g /=.
    by apply SkipTy.
  - rewrite /g /=.
    by apply NullTy.
Qed.

Definition ΔM :=
  let n := length Main.(generics) in
  let σ := gen_targs n in
  (ThisT, ClassT false "Main" σ) :: Main.(constraints).

Definition Γmain : stringmap lang_ty :=
  (<[ "$c" := ClassT true "C" [] ]>
  (<[ "$d" := ClassT true "D" [] ]> main.(methodargs))).

Lemma wf_mdef_ty_main: wf_mdef_ty "main" ΔM 0 main.
Proof.
  rewrite /wf_mdef_ty.
  exists (<[ "$tmp" := NullT]> Γmain).
  repeat split.
  - apply map_Forall_insert_2; first by constructor.
    apply map_Forall_insert_2; first by repeat econstructor.
    apply map_Forall_insert_2; first by repeat econstructor.
    by apply map_Forall_empty.
  - rewrite /main /=.
    eapply SeqTy.
    { eapply NewTy => //.
      - by repeat econstructor.
      - by repeat econstructor.
      - by econstructor.
      - by exact has_fields_D.
      - by rewrite !dom_empty_L.
    }
    eapply SeqTy.
    { eapply NewTy => //.
      - by repeat econstructor.
      - by repeat econstructor.
      - by econstructor.
      - by exact has_fields_C.
      - by rewrite !dom_empty_L.
    }
    change (<["$tmp" := NullT]> Γmain)
    with (<["$tmp" := subst_fty false "Main" [] problem.(methodrettype)]>  Γmain).
    apply CallPubTy with (orig := "Main").
    + eapply ESubTy.
      * by constructor.
      * by econstructor.
      * by econstructor.
      * by econstructor.
      * apply SubConstraint.
        by set_solver.
    + by apply HasMethod with (cdef := Main).
    + right.
      rewrite /no_this_mdef /problem /=.
      split => //.
      rewrite map_Forall_lookup => k ty.
      rewrite lookup_insert_Some => [[ [? <-] | [?] ]] //.
      by rewrite lookup_singleton_Some => [[? <-]].
    + done.
    + by rewrite /problem /= !dom_insert_L !dom_empty_L.
    + rewrite /problem => k ty arg /=.
      rewrite lookup_insert_Some => [[ [<- <-] | [?] ]] /=.
      * rewrite lookup_insert => [ [<-] ].
        rewrite /subst_fty /=.
        eapply ESubTy.
        -- constructor.
           by set_solver.
        -- by apply wf_ty_correct.
        -- by apply generic_bounded_correct.
        -- by econstructor.
        -- apply SubTrans with (ClassT false "D" []).
           { by apply SubExact with D. }
           change (ClassT false "C" []) with (ClassT false "C" (subst_ty [] <$> [])).
           apply SubClass with D => //.
           by apply ExtendsUsing with D.
      * rewrite lookup_singleton_Some => [[<- <-]]; simpl_map => [[<-]].
        rewrite /subst_fty /=.
        eapply ESubTy.
        -- constructor.
           by set_solver.
        -- by apply wf_ty_correct.
        -- by apply generic_bounded_correct.
        -- by econstructor.
        -- by apply SubExact with C.
  - by apply NullTy.
Qed.

(* Lemma wf_mdef_ty_problem: wf_mdef_ty "problem" ΔM 0 problem → False. *)
(* Proof. *)
(*   rewrite /wf_mdef_ty /problem /=. *)
(*   case => Γf. *)
(*   case => hwfΓf. *)
(*   case => hc _. *)
(*   inv hc. *)
(*   - apply var_has_ty_inv in H3. *)
(*     rewrite lookup_insert in H3. *)


(* Qed. *)

Lemma wf_mdef_ty_problem: wf_mdef_ty "problem" ΔM 0 problem.
Proof.
  rewrite /wf_mdef_ty.
  exists (<[ "$_" := NullT]> problem.(methodargs)).
  repeat split.
  - apply map_Forall_insert_2; first by constructor.
    apply map_Forall_insert_2; first by repeat econstructor.
    apply map_Forall_insert_2; first by repeat econstructor.
    by apply map_Forall_empty.
  - rewrite /problem /=.
    change ({["$_" := NullT; "$c0" := ClassT false "C" []; "$c1" := ClassT false "C" []]})
    with (<["$_" := subst_fty false "C" [] f.(methodrettype)]> problem.(methodargs)).
    apply CallPubTy with "C".
    + by apply VarTy.
    + by econstructor.
    + (* Can't prove either side *)
      Abort.
