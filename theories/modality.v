(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 * 
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
From iris Require Import fancy_updates.
From iris.proofmode Require Import base tactics classes.

From shack Require Import heap.

Section Modality.

(* Iris semantic context *)
Context `{!sem_heapG Σ}.

Notation "|=▷^ n Q" := (Nat.iter n (λ P, |==> ▷ P) Q)%I
    (at level 99, n at level 9, Q at level 200,
    format "|=▷^ n  Q") : bi_scope.

Lemma updN_zero (Q : iProp Σ) : (|=▷^0 Q) ⊣⊢ Q.
Proof. done. Qed.

Lemma updN_S n (Q : iProp Σ) :
  (|=▷^(S n) Q) ⊣⊢ |==> ▷ |=▷^n Q.
Proof. done. Qed.

Lemma updN_mono n (P Q : iProp Σ) :
  (P -∗ Q) → (|=▷^n P) -∗ (|=▷^n Q).
Proof.
  elim: n => [//|n HI H /=].
  iApply bupd_mono.
  iApply bi.later_mono.
  by iApply HI.
Qed.

Lemma updN_mono_I n (P Q : iProp Σ) :
  (P -∗ Q) -∗ (|=▷^n P) -∗ (|=▷^n Q).
Proof.
  elim: n => [|n hi]; first done.
  iIntros "H".
  rewrite !updN_S.
  iIntros "HH".
  iMod "HH".
  iModIntro.
  iNext.
  by iApply (hi with "H").
Qed.

Lemma updN_intro n (P: iProp Σ) : P -∗ (|=▷^n P).
Proof.
  elim: n => [// | n hi /=].
  iIntros "p".
  iApply bupd_intro.
  apply bi.later_mono in hi.
  by iApply hi.
Qed.

Lemma updN_sep n (P R: iProp Σ) : ((|=▷^n P) ∗ (|=▷^n R)) -∗ |=▷^n (P ∗ R).
Proof.
  elim: n => [// | n hi /=].
  iIntros "[H0 H1]".
  iMod "H0".
  iMod "H1".
  iModIntro.
  iNext.
  iApply hi.
  by iSplitL "H0".
Qed.

Lemma updN_frame_r n (P R: iProp Σ) : (|=▷^n P) ∗ R -∗ |=▷^n P ∗ R.
Proof.
  elim: n => [// | n hi /=].
  iIntros "[H HR]".
  iMod "H"; iModIntro.
  iNext.
  iApply hi.
  by iSplitL "H".
Qed.

Lemma updN_plus n1 (P: iProp Σ) : ∀ n2,
  (|=▷^n1 P) -∗ (|=▷^(n1 + n2) P).
Proof.
  elim:n1 => [ | n1 hi] /= => n2; iIntros "h1"; first by iApply updN_intro.
  iMod "h1".
  iModIntro.
  iNext.
  by iApply hi.
Qed.

Lemma step_updN_step_fupdN `{!invGS Σ} (P : iProp Σ) n :
  (|=▷^n P) ⊢ (|={∅}▷=>^n P)%I.
Proof.
  iInduction n as [|n ] "IH"; first by eauto.
  iIntros "H". iMod "H". do 3 iModIntro. by iApply "IH".
Qed.

Lemma step_updN_step_fupdN_soundness `{!invGpreS Σ} φ n:
  (⊢ |=▷^n (⌜φ⌝ : iProp Σ)) → φ.
Proof.
  intros Hvdash. eapply step_fupdN_soundness.
  iIntros (Hinv). iPoseProof Hvdash as "H".
  iDestruct (step_updN_step_fupdN with "H") as "H'".
  iApply fupd_mask_intro_discard; auto.
Qed.
End Modality.

Notation "|=▷^ n Q" := (Nat.iter n (λ P, |==> ▷ P) Q)%I
    (at level 99, n at level 9, Q at level 200,
    format "|=▷^ n  Q") : bi_scope.
