(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
From iris Require Import fancy_updates.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop own wsat.

Section Modality.

(* Iris semantic context *)
Context `{Θ: gFunctors}.

(* Helper to iterate laters *)
Lemma laterN_soundness n (P : iProp Θ) : (⊢ ▷^n P) → ⊢ P.
Proof.
  elim : n => [ | n hi] //= h.
  apply uPred.later_soundness in h.
  by apply hi.
Qed.

Lemma bupd_elim (P Q: iProp Θ) : (Q -∗ (|==> P)) → (|==> Q) -∗ (|==> P).
Proof.
  move => ->.
  iIntros "H".
  by iMod "H".
Qed.

Lemma bupd_plainly_later (P : iProp Θ) : (▷ |==> ■ P) ⊢ |==> ▷ ◇ P.
Proof.
  iIntros "H".
  iModIntro.
  iNext.
  rewrite bupd_plainly.
  by auto.
Qed.

Lemma bupd_plain_later (P: iProp Θ) `{!Plain P} : (▷ |==> P) ⊢ |==> ▷ ◇ P.
Proof.  by rewrite {1}(plain P) bupd_plainly_later. Qed.

Notation "|=▷^ n Q" := (Nat.iter n (λ P, |==> ▷ P) Q)%I
    (at level 99, n at level 9, Q at level 200,
    format "|=▷^ n  Q") : bi_scope.

Lemma updN_zero (Q : iProp Θ) : (|=▷^0 Q) ⊣⊢ Q.
Proof. done. Qed.

Lemma updN_S n (Q : iProp Θ) :
  (|=▷^(S n) Q) ⊣⊢ |==> ▷ |=▷^n Q.
Proof. done. Qed.

Lemma updN_mono n (P Q : iProp Θ) :
  (P -∗ Q) → (|=▷^n P) -∗ (|=▷^n Q).
Proof.
  elim: n => [//|n HI H /=].
  iApply bupd_mono.
  iApply bi.later_mono.
  by iApply HI.
Qed.

Lemma updN_mono_I n (P Q : iProp Θ) :
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

Lemma updN_intro n (P: iProp Θ) : P -∗ (|=▷^n P).
Proof.
  elim: n => [// | n hi /=].
  iIntros "p".
  iApply bupd_intro.
  apply bi.later_mono in hi.
  by iApply hi.
Qed.

Lemma updN_sep n (P R: iProp Θ) : ((|=▷^n P) ∗ (|=▷^n R)) -∗ |=▷^n (P ∗ R).
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

Lemma updN_frame_r n (P R: iProp Θ) : (|=▷^n P) ∗ R -∗ |=▷^n P ∗ R.
Proof.
  elim: n => [// | n hi /=].
  iIntros "[H HR]".
  iMod "H"; iModIntro.
  iNext.
  iApply hi.
  by iSplitL "H".
Qed.

Lemma updN_plus n1 (P: iProp Θ) : ∀ n2,
  (|=▷^n1 P) -∗ (|=▷^(n1 + n2) P).
Proof.
  elim:n1 => [ | n1 hi] /= => n2; iIntros "h1"; first by iApply updN_intro.
  iMod "h1".
  iModIntro.
  iNext.
  by iApply hi.
Qed.

Lemma step_upd_plain (P: iProp Θ) `{!Plain P} : (|==> ▷ |==> P) -∗ |==> ▷ ◇ P.
Proof.
  apply bupd_elim.
  by rewrite bupd_plain_later.
Qed.

Lemma step_updN_plain n (P: iProp Θ) `{!Plain P} : (|=▷^n P) -∗ |==> ▷^n ◇ P.
Proof.
  elim : n => [ | n hi] /=.
  - rewrite -bupd_intro; by auto.
  - rewrite hi step_upd_plain.
    apply bupd_mono.
    by rewrite bi.except_0_laterN bi.except_0_idemp.
Qed.

End Modality.

Notation "|=▷^ n Q" := (Nat.iter n (λ P, |==> ▷ P) Q)%I
    (at level 99, n at level 9, Q at level 200,
    format "|=▷^ n  Q") : bi_scope.

Lemma step_updN_soundness Θ n φ: (⊢@{iPropI Θ} |==> |=▷^n ⌜ φ ⌝) → φ.
Proof.
  move => Hiter.
  apply (uPred.soundness (M:=iResUR Θ) _  (S n)); simpl.
  apply uPred.bupd_plain_soundness.
  { rewrite -bi.later_laterN.
    apply laterN_plain.
    by apply pure_plain.
  }
  iPoseProof Hiter as "H". clear Hiter.
  iMod (step_updN_plain with "H") as "H2".
  iMod "H2".
  iModIntro.
  rewrite -bi.later_laterN bi.laterN_later.
  iNext. iMod "H2" as %Hφ. auto.
Qed.

Print Assumptions step_updN_soundness.
