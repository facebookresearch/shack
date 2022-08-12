(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
From stdpp Require Import base strings gmap stringmap fin_maps.
From iris.base_logic Require Import upred derived.
From iris.base_logic.lib Require Import iprop own.
From iris.algebra Require Import ofe cmra gmap_view.
From iris.proofmode Require Import tactics.

From shack Require Import lang progdef subtype typing eval heap modality interp.
From shack.soundness Require Import expr defs.

Section proofs.
  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.
  (* assume some SDT constraints and their properties *)
  Context `{SDTCS: SDTClassSpec}.

  (* Iris semantic context *)
  Context `{!sem_heapGS Θ}.

  Lemma get_priv_soundness C Δ rigid Γ lhs t σ name fty:
    wf_cdefs pdefs →
    wf_lty Γ →
    type_of_this Γ = (t, σ) →
    has_field name t Private fty C →
    ∀ Σ st st' n,
    length Σ = rigid →
    cmd_eval C st (GetC lhs ThisE name) st' n →
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σ (<[lhs:=subst_ty σ fty]> Γ) st'.1.
  Proof.
    move => wfpdefs wflty hthis hf Σ st st' n hrigid hc.
    iIntros "hΣ hΣΔ".
    inv hc.
    iIntros "[Hh #Hle]".
    iModIntro. (* keep the later *)
    destruct Γ as [[this thisσ] Γ].
    destruct Ω as [vthis Ω].
    destruct wflty as [wfthis wflty].
    rewrite /this_type /= in wfthis, hthis.
    injection hthis; intros; subst; clear hthis.
    inv H2.
    simpl in *.
    iDestruct "Hle" as "[Hthis Hle]".
    rewrite /this_type /=.
    rewrite /interp_this_type interp_this_unseal /interp_this_def /=.
    iDestruct "Hthis" as (???? σ0 ???) "[%H [#hmixed [#? [#hinst [#hdyn H◯]]]]]".
    destruct H as ([= <-] & hdef & hdef1 & hlen & ? & hinherits & hidom & hfields).
    iAssert (⌜t0 = t1⌝ ∗ heap_models h ∗ ▷ interp_type (subst_ty σ fty) Σ v)%I with "[Hh]" as "[%Ht [Hh Hv]]".
    { iDestruct "Hh" as (sh) "(H● & %hdom & #Hh)".
      iDestruct (sem_heap_own_valid_2 with "H● H◯") as "#HΦ".
      iDestruct ("Hh" with "[//]") as (iFs) "[H H▷]".
      iRewrite "H" in "HΦ".
      rewrite option_equivI prod_equivI /=.
      iDestruct "HΦ" as "[%Ht HΦ]".
      fold_leibniz; subst.
      iSplitR; first done.
      iSplitL. { iExists _. iFrame. by iSplit. }
      assert (hfC: has_field name t1 Private (subst_ty σ0 fty) C) by (destruct wfpdefs; by eapply has_field_inherits_using).
      iSpecialize ("hdyn" $! name Private (subst_ty σ0 fty) C hfC).
      iDestruct "H▷" as "[hdf h]".
      rewrite later_equivI. iNext.
      iRewrite -"HΦ" in "hdyn".
      iSpecialize ("h" $! name _ with "[hdyn]"); first done.
      iDestruct "h" as (w) "[%hw hiw]".
      simplify_eq.
      rewrite interp_type_subst; last first.
      { destruct wfpdefs.
        apply has_field_bounded in hf => //.
        destruct hf as (? & ? & ?).
        apply inherits_using_wf in hinherits => //.
        destruct hinherits as (? & ?& ? & hh).
        inv wfthis; simplify_eq.
        by rewrite H10.
      }
      iRewrite -"hinst".
      rewrite -interp_type_subst //.
      destruct wfpdefs.
      apply has_field_bounded in hf => //.
      destruct hf as (? & ? & ?).
      apply inherits_using_wf in hinherits => //.
      destruct hinherits as (? & ?& ? & hh).
      inv hh; simplify_eq.
      by rewrite H10.
    }
    subst.
    iNext.
    iFrame.
    iApply interp_local_tys_update => //.
    iSplit; last done.
    rewrite /type_of_this /interp_this_type interp_this_unseal.
    iExists l, t1, cdef, tdef, σ0, Σt, fields, ifields.
    by repeat iSplit.
  Qed.

  Lemma get_pub_soundness C Δ kd rigid Γ lhs recv t σ name fty orig:
    wf_cdefs pdefs →
    wf_lty Γ →
    Forall wf_constraint Δ →
    expr_has_ty Δ Γ rigid kd recv (ClassT t σ) →
    has_field name t Public fty orig →
    ∀ Σ st st' n,
    length Σ = rigid →
    cmd_eval C st (GetC lhs recv name) st' n →
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σ (<[lhs:=subst_ty σ fty]> Γ) st'.1.
  Proof.
    move => wfpdefs ?? hrecv hf Σ st st' n hrigid hc.
    iIntros "hΣ hΣΔ".
    inv hc.
    iIntros "[Hh #Hle]".
    iModIntro. (* keep the later *)
    iDestruct (expr_soundness with "hΣ hΣΔ Hle") as "#He" => //; try (by apply wfpdefs).
    rewrite interp_class_unfold //; first last.
    { by apply expr_has_ty_wf in hrecv. }
    { by apply wfpdefs. }
    iDestruct "He" as (?? def def0 σ0 ???) "[%H [#hmixed [#? [#hf0 [#hdyn H◯]]]]]".
    destruct H as ([= <-] & hdef & hdef0 & hlen & ? & hinherits & hfields & hidom).
    assert (hwf0: wf_ty (ClassT t σ)) by (by apply expr_has_ty_wf in hrecv).
    assert (hl0: length (generics def) = length σ0).
    { apply inherits_using_wf in hinherits; try (by apply wfpdefs).
      destruct hinherits as (?&?&?&hh).
      inv hh; by simplify_eq.
    }
    assert (hl1: length σ0 = length σ).
    { rewrite -hl0.
      rewrite /interp_list fmap_length in hlen.
      by rewrite hlen.
    }
    assert (hff: has_field name t1 Public (subst_ty σ0 fty) orig).
    { by apply has_field_inherits_using with (A := t1) (σB := σ0) in hf => //; try (by apply wfpdefs). }
    iAssert (⌜t0 = t1⌝ ∗ heap_models h ∗ ▷ interp_type (subst_ty σ0 fty) Σt v)%I with "[Hh]" as "[%Ht [Hh Hv]]".
    { iDestruct "Hh" as (sh) "(H● & %hdom & #Hh)".
      iDestruct (sem_heap_own_valid_2 with "H● H◯") as "#HΦ".
      iDestruct ("Hh" with "[//]") as (iFs) "[H H▷]".
      iRewrite "H" in "HΦ".
      rewrite option_equivI prod_equivI /=.
      iDestruct "HΦ" as "[%Ht HΦ]".
      fold_leibniz; subst.
      iSplitR; first done.
      iSplitL. { iExists _. iFrame. by iSplit. }
      iSpecialize ("hdyn" $! name Public (subst_ty σ0 fty) orig hff).
      iNext.
      iDestruct "H▷" as "[%hdf h]".
      iRewrite -"HΦ" in "hdyn".
      iSpecialize ("h" $! name _ with "[hdyn]"); first done.
      iDestruct "h" as (w) "[%hw hiw]".
      by simplify_eq.
    }
    subst; simpl.
    iNext.
    iFrame.
    destruct wfpdefs.
    iApply interp_local_tys_update => //.
    rewrite !interp_type_subst; first last.
    { apply has_field_bounded in hf => //.
      destruct hf as (?&?&hf); simplify_eq.
      by rewrite -hl0.
    }
    { apply has_field_bounded in hf => //.
      destruct hf as (?&?&hf); simplify_eq.
      by rewrite -hl1 -hl0.
    }
    iApply interp_with_mono => //.
    { apply has_field_mono in hf => //.
      destruct hf as (?&?&hh); simplify_eq.
      by destruct hh.
    }
    by apply has_field_wf in hf.
  Qed.
End proofs.
