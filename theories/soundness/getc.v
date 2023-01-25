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

From shack Require Import lang progdef subtype eval.
From shack Require Import heap modality interp typing.
From shack.soundness Require Import expr defs.

Section proofs.
  (* assume a given set of class definitions and their SDT annotations. *)
  Context `{SDTCVS: SDTClassVarianceSpec}.

  (* Iris semantic context *)
  Context `{!sem_heapGS Θ}.

  Notation "X ≡≡ Y" := (∀ (w: value), X w ∗-∗ Y w)%I (at level 50, no associativity).

  Lemma get_priv_soundness C Δ rigid Γ lhs name fty:
    wf_cdefs pdefs →
    wf_lty Γ →
    has_field name C Private fty C →
    ∀ t tdef Σt σ,
    pdefs !! t = Some tdef →
    length Σt = length tdef.(generics) →
    inherits_using t C σ →
    ∀ Σ st st' n,
    length Σ = rigid →
    cmd_eval C st (GetC lhs ThisE name) st' n →
    let Σthis := interp_exact_tag interp_type t Σt in
    ⌜interp_list interp_nothing Σt σ ≡ Σ⌝ -∗
    □ interp_as_mixed Σthis -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σthis Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σthis Σ (<[lhs:=fty]> Γ) st'.1.
  Proof.
    move => wfpdefs wflty hf.
    move => t tdef Σt σ htdef hlenΣt hin_t_C_σ.
    move => Σ st st' n hrigid hc /=.
    iIntros "%heq #hΣthis #hΣ #hΣΔ".
    elim/cmd_eval_getI: hc.
    move => {n}.
    move => Ω h l t0 vs v heval hheap hvs hvis.
    iIntros "[Hh Hle]".
    iModIntro. (* keep the later *)
    destruct Ω as [vthis Ω].
    case: heval => ->.
    simpl in *.
    iDestruct "Hle" as "[#Hthis #Hle]" => /=.
    iAssert (interp_exact_tag interp_type t Σt (LocV l)) as "#Hl"; first by done.
    rewrite {3}interp_exact_tag_unseal /interp_exact_tag_def /=.
    iDestruct "Hthis" as (l0 ? fields ifields H) "(#hconstr & #hf0 & #H◯)".
    destruct H as ([= <-] & ? & hfields & hidom); simplify_eq.
    assert (hlen: ∃ cdef, pdefs !! C = Some cdef ∧
      length σ = length cdef.(generics) ∧
      Forall (λ ty : lang_ty, no_this ty) σ).
    { destruct wfpdefs.
      apply inherits_using_wf in hin_t_C_σ => //.
      destruct hin_t_C_σ as (? & ?& ? & hh & ?).
      apply wf_tyI in hh as (? & ? & hlenC & ?); simplify_eq.
      by eauto.
    }
    destruct hlen as (cdef & hcdef & hlen & hnothis).
    iAssert (⌜t0 = t⌝ ∗ heap_models h ∗ ▷ interp_type fty (interp_exact_tag interp_type t Σt) Σ v)%I with "[Hh]" as "[%Ht [Hh Hv]]".
    { iDestruct "Hh" as (sh) "(H● & %hdom & #Hh)".
      iDestruct (sem_heap_own_valid_2 with "H● H◯") as "#HΦ".
      iDestruct ("Hh" with "[//]") as (iFs) "[H H▷]".
      iRewrite "H" in "HΦ".
      rewrite option_equivI prod_equivI /=.
      iDestruct "HΦ" as "[%Ht HΦ]".
      fold_leibniz; subst.
      iSplitR; first done.
      iSplitL. { iExists _. iFrame. by iSplit. }
      assert (hfC: has_field name t Private (subst_ty σ fty) C) by (destruct wfpdefs; by eapply has_field_inherits_using).
      iSpecialize ("hf0" $! name Private (subst_ty σ fty) C hfC).
      iDestruct "H▷" as "[hdf h]".
      rewrite later_equivI.
      iNext.
      iDestruct "hf0" as (iF) "[hf0 hiff]".
      iRewrite -"HΦ" in "hf0".
      iSpecialize ("h" $! name _ with "[hf0]"); first done.
      iDestruct "h" as (w) "[%hw hiw]".
      simplify_eq.
      iDestruct ("hiff" with "hiw") as "hiw_"; iClear "hiw".
      iAssert (interp_type (subst_ty σ fty) (interp_exact_tag interp_type t Σt) Σt v) with "[hiw_]" as "#hiw".
      { rewrite /subst_gen -hlenΣt.
        by iApply interp_type_subst_this.
      }
      iClear "hiw_".
      rewrite interp_type_subst; last first.
      { destruct wfpdefs.
        apply has_field_bounded in hf => //.
        destruct hf as (? & ? & ?); simplify_eq.
        by rewrite hlen.
      }
      assert (heq2: interp_list (interp_exact_tag interp_type t Σt) Σt σ ≡ Σ).
      { rewrite -heq.
        by apply interp_list_no_this.
      }
      by rewrite heq2.
    }
    subst.
    iNext.
    iFrame.
    iApply interp_local_tys_update => //.
    by iSplit.
  Qed.

  Lemma get_pub_soundness C Δ kd rigid Γ lhs recv exact_ t σ name fty orig:
    wf_cdefs pdefs →
    wf_lty Γ →
    Forall wf_constraint Δ →
    expr_has_ty Δ Γ rigid kd recv (ClassT exact_ t σ) →
    field_lookup exact_ t σ name Public fty orig →
    ∀ Σthis Σ st st' n,
    length Σ = rigid →
    cmd_eval C st (GetC lhs recv name) st' n →
    □ interp_as_mixed Σthis -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σthis Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σthis Σ (<[lhs:=subst_fty exact_ t σ fty]> Γ) st'.1.
  Proof.
    move => wfpdefs ?? hrecv hf Σthis Σ st st' n hrigid hc.
    iIntros "hΣthis hΣ hΣΔ".
    elim/cmd_eval_getI: hc.
    move => {n}.
    move => Ω h l t0 vs v heval hheap hvs hvis.
    iIntros "[Hh #Hle]".
    iModIntro. (* keep the later *)
    assert (hwf0: wf_ty (ClassT exact_ t σ)) by (by apply expr_has_ty_wf in hrecv).
    assert (hwf0_ := hwf0).
    apply wf_tyI in hwf0_ as (tdef & htdef & hlen & hfσ); simplify_eq.
    iDestruct (expr_soundness with "hΣthis hΣ hΣΔ Hle") as "He" => //; try (by apply wfpdefs).
    destruct hf as [hf hex].
    destruct exact_.
    (* receiver class is exact *)
    - rewrite interp_exact_tag_unfold interp_exact_tag_unseal /interp_exact_tag_def /=.
      iDestruct "He" as (l0 tdef' fields ifields H) "(#hconstr & #hf0 & #H◯)".
      destruct H as ([= <-] & htdef' & hfields & hidom); simplify_eq.
      simpl.
      iAssert (⌜t0 = t⌝ ∗ heap_models h ∗
        ▷ interp_type (subst_gen t tdef fty) interp_nothing (interp_list Σthis Σ σ) v)%I with "[Hh]" as "[%Ht [Hh Hv]]".
      { iDestruct "Hh" as (sh) "(H● & %hdom & #Hh)".
        iDestruct (sem_heap_own_valid_2 with "H● H◯") as "#HΦ".
        iDestruct ("Hh" with "[//]") as (iFs) "[H H▷]".
        iRewrite "H" in "HΦ".
        rewrite option_equivI prod_equivI /=.
        iDestruct "HΦ" as "[%Ht HΦ]".
        fold_leibniz; subst.
        iSplitR; first done.
        iSplitL. { iExists _. iFrame. by iSplit. }
        iSpecialize ("hf0" $! name Public fty orig hf).
        iDestruct "hf0" as (iF) "[hf0 hiff]".
        iNext.
        iDestruct "H▷" as "[%hdf h]".
        iRewrite -"HΦ" in "hf0".
        iSpecialize ("h" $! name _ with "[hf0]"); first done.
        iDestruct "h" as (w) "[%hw hiw]".
        iApply "hiff".
        by simplify_eq.
      }
      subst; simpl.
      iNext.
      iFrame.
      destruct wfpdefs.
      iApply interp_local_tys_update => //.
      assert (hlen2: length (interp_list Σthis Σ σ) = length tdef.(generics)) by by rewrite /interp_list fmap_length.
      rewrite /subst_gen /subst_fty -hlen2.
      rewrite interp_type_subst_this => //.
      rewrite interp_type_subst; last first.
      { apply has_field_bounded in hf => //.
        destruct hf as (?&?&hf); simplify_eq.
        apply bounded_subst_this.
        + by rewrite hlen.
        + constructor.
          by apply bounded_gen_targs.
      }
      rewrite hlen -hlen2.
      rewrite interp_type_subst_this; first last.
      { by rewrite /interp_list map_length. }
      { by assumption. }
      done.
    - (* receiver is not exact, so it can't call anything using the `this`
       * type yet.
       *)
      case: hex => // hnothis.
      rewrite interp_tag_unfold interp_tag_equiv //; first last.
      { by rewrite /interp_list fmap_length. }
      { by apply wfpdefs. }
      iDestruct "He" as (?? def def1 σ0 ???) "(%H & #hmixed & #? & #hf0 & #hdyn & #H◯)".
      destruct H as ([= <-] & hdef & hdef0 & hlenΣt & hinherits & hfields & hidom).
      assert (hl0: length (generics def) = length σ0).
      { apply inherits_using_wf in hinherits; try (by apply wfpdefs).
        destruct hinherits as (?&?&?&hh&?).
        apply wf_tyI in hh as (? & ? & ? & ?); by simplify_eq.
      }
      assert (hl1: length σ0 = length σ).
      { rewrite -hl0.
        apply wf_tyI in hwf0 as (? & ? & ? & ?); by simplify_eq.
      }
      assert (hff: has_field name t1 Public (subst_ty σ0 fty) orig).
      { by apply has_field_inherits_using with (A := t1) (σB := σ0) in hf => //; try (by apply wfpdefs). }
      iAssert (⌜t0 = t1⌝ ∗ heap_models h ∗
        ▷ interp_type (subst_gen t1 def1 (subst_ty σ0 fty)) interp_nothing Σt v)%I with "[Hh]" as "[%Ht [Hh Hv]]".
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
        iDestruct "hdyn" as (iF) "[hdyn hiff]".
        iRewrite -"HΦ" in "hdyn".
        iSpecialize ("h" $! name _ with "[hdyn]"); first done.
        iDestruct "h" as (w) "[%hw hiw]".
        iApply "hiff".
        by simplify_eq.
      }
      subst; simpl.
      iNext.
      iFrame.
      destruct wfpdefs.
      iApply interp_local_tys_update => //.
      rewrite /subst_gen -hlenΣt.
      rewrite interp_type_subst_this => //.
      rewrite interp_type_subst; last first.
      { apply has_field_bounded in hf => //.
        destruct hf as (?&?&hf); simplify_eq.
        by rewrite -hl0.
      }
      rewrite (interp_list_no_this _ _ (interp_exact_tag interp_type t1 Σt) interp_nothing); last first.
      { apply inherits_using_wf in hinherits => //.
        by destruct hinherits as (? & ? & ? & ? & hh); simplify_eq.
      }
      iAssert (interp_type fty (interp_exact_tag interp_type t1 Σt)
        (interp_list Σthis Σ σ) v) with "[Hv]" as "Hv".
      { iApply interp_with_mono => //.
        - apply has_field_mono in hf => //.
          destruct hf as (?&?&hh); simplify_eq.
          by destruct hh.
        - by apply has_field_wf in hf.
      }
      rewrite interp_type_subst; first last.
      { apply bounded_subst_this.
        - apply has_field_bounded in hf => //.
          destruct hf as (?&?&hf).
          apply wf_tyI in hwf0 as (? & ? & -> & ?).
          by simplify_eq.
        - constructor; by apply bounded_gen_targs.
      }
      rewrite subst_this_no_this_id; last done.
      by rewrite (interp_type_no_this _ _ _ _ Σthis); last done.
  Qed.
End proofs.
