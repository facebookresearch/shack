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
  (* assume a given set of class definitions *)
  Context `{PDC: ProgDefContext}.
  (* assume some SDT constraints and their properties *)
  Context `{SDTCS: SDTClassSpec}.

  (* Iris semantic context *)
  Context `{!sem_heapGS Θ}.

  (*
  Lemma get_priv_soundness C cdef Δ rigid Γ lhs name fty:
    wf_cdefs pdefs →
    wf_lty Γ →
    pdefs !! C = Some cdef →
    has_field name C Private fty C →
    ∀ Σthis Σ st st' n,
    length Σ = rigid →
    cmd_eval C st (GetC lhs ThisE name) st' n →
    □ interp_as_mixed Σthis -∗
    interp_inclusion Σthis (interp_tag_alt C Σ) -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σthis Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σthis Σ (<[lhs:=fty]> Γ) st'.1.
  Proof.
    move => wfpdefs wflty hcdef hf Σthis Σ st st' n hrigid hc.
    iIntros "#hΣthis hΣthis_incl #hΣ #hΣΔ".
    elim/cmd_eval_getI: hc.
    move => {n}.
    move => Ω h l t0 vs v heval hheap hvs hvis.
    iIntros "[Hh Hle]".
    iModIntro. (* keep the later *)
    destruct Ω as [vthis Ω].
    case: heval => ->.
    simpl in *.
    iDestruct "Hle" as "[Hthis #Hle]" => /=.
    iDestruct ("hΣthis_incl" with "Hthis") as "#h".
    iDestruct "h" as (???? σ0 ???) "(%H & #hmixed & #? & #hinst & #hdyn & H◯)".
    destruct H as ([= <-] & ? & htdef & hlen & hinherits & hidom & hfields).
    simplify_eq.
    iAssert (⌜t0 = t⌝ ∗ heap_models h ∗ ▷ interp_type (subst_gen C cdef fty) Σthis Σ v)%I with "[Hh]" as "[%Ht [Hh Hv]]".
    { iDestruct "Hh" as (sh) "(H● & %hdom & #Hh)".
      iDestruct (sem_heap_own_valid_2 with "H● H◯") as "#HΦ".
      iDestruct ("Hh" with "[//]") as (iFs) "[H H▷]".
      iRewrite "H" in "HΦ".
      rewrite option_equivI prod_equivI /=.
      iDestruct "HΦ" as "[%Ht HΦ]".
      fold_leibniz; subst.
      iSplitR; first done.
      iSplitL. { iExists _. iFrame. by iSplit. }
      assert (hfC: has_field name t Private (subst_ty σ0 fty) C) by (destruct wfpdefs; by eapply has_field_inherits_using).
      iSpecialize ("hdyn" $! name Private (subst_ty σ0 fty) C hfC).
      iDestruct "H▷" as "[hdf h]".
      rewrite later_equivI. iNext.
      iRewrite -"HΦ" in "hdyn".
      iSpecialize ("h" $! name _ with "[hdyn]"); first done.
      iDestruct "h" as (w) "[%hw hiw]".
      simplify_eq.

      iAssert (interp_type (subst_ty σ0 fty) (interp_exact_class interp_type t Σt) Σt v) as "#Ht".
      { by rewrite /subst_gen -hlen -interp_type_subst_this. }
      iClear "hiw".

      rewrite interp_type_subst; last first.
      { destruct wfpdefs.
        apply has_field_bounded in hf => //.
        destruct hf as (? & ? & ?).
        apply inherits_using_wf in hinherits => //.
        destruct hinherits as (? & ?& ? & hh & _).
        apply wf_tyI in hh as (? & ? & hlenC & ?); simplify_eq.
        by rewrite hlenC.
      }

      rewrite -hinst.
      rewrite -interp_type_subst //.
      destruct wfpdefs.
      apply has_field_bounded in hf => //.
      destruct hf as (? & ? & ?).
      apply inherits_using_wf in hinherits => //.
      destruct hinherits as (? & ?& ? & hh).
      apply wf_tyI in hh as (? & ? & hlen & ?); simplify_eq.
      by rewrite hlen.
    }
    subst.
    iNext.
    iFrame.
    iApply interp_local_tys_update => //.
    iSplit; last done.
    rewrite /type_of_this /interp_this_type interp_this_unseal.
    iExists l, t1, tdef, σ0, Σt, fields, ifields.
    by repeat iSplit.
  Qed.
   *)

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
    case: hex => [h_is_exact | hnothis_t ].
    (* receiver class is exact *)
    - rewrite /is_true in h_is_exact; simplify_eq.
      rewrite interp_exact_class_unfold; first last.
      { by assumption. }
      { by apply wfpdefs. }
      iDestruct "He" as (tdef' Σt H)"(#hmixed & #hinst & #htag)".
      destruct H as [htdef' hΣtlen]; simplify_eq.
      iDestruct "htag" as (l0 tdef' fields ifields H) "(#hconstr & hf0 & #H◯)".
      destruct H as ([= <-] & htdef' & hfields & hidom); simplify_eq.
      simpl.
      iAssert (⌜t0 = t⌝ ∗ heap_models h ∗
        ▷ interp_type (subst_gen t tdef fty) interp_nothing Σt v)%I with "[Hh]" as "[%Ht [Hh Hv]]".
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
        iNext.
        iDestruct "H▷" as "[%hdf h]".
        iRewrite -"HΦ" in "hf0".
        iSpecialize ("h" $! name _ with "[hf0]"); first done.
        iDestruct "h" as (w) "[%hw hiw]".
        by simplify_eq.
      }
      subst; simpl.
      iNext.
      iFrame.
      destruct wfpdefs.
      iApply interp_local_tys_update => //.
      rewrite /subst_gen /subst_fty -hΣtlen.
      rewrite interp_type_subst_this => //.
      rewrite interp_type_subst; last first.
      { apply has_field_bounded in hf => //.
        destruct hf as (?&?&hf); simplify_eq.
        apply bounded_subst_this.
        + by rewrite hlen.
        + constructor.
          by apply bounded_gen_targs.
      }
      replace (length σ) with (length (interp_list Σthis Σ σ)) by by rewrite /interp_list map_length.
      rewrite interp_type_subst_this; first last.
      { by rewrite /interp_list map_length. }
      { by assumption. }

      t tdef Σthis (interp_list Σthis Σ σ) fty v htdef).
      rewrite hlen interp_type_subst_this.
      rewrite (interp_list_no_this _ _ (interp_exact_class interp_type t1 Σt) interp_nothing); last done.
    iAssert (interp_type fty (interp_exact_class interp_type t1 Σt)
                (interp_list Σthis Σ σ) v) with "[Hv]" as "Hv".
    { iApply interp_with_mono => //.
      - apply has_field_mono in hf => //.
        destruct hf as (?&?&hh); simplify_eq.
        by destruct hh.
      - by apply has_field_wf in hf.
    }
    - destruct exact_; last done.
      clear h_is_exact.
      rewrite interp_type_subst; last first.
      { apply bounded_subst_this.
        - apply has_field_bounded in hf => //.
          destruct hf as (?&?&hf); simplify_eq.
          by rewrite -hl1 -hl0.
        - constructor.
          by apply bounded_gen_targs.
      }
      replace (length σ) with (length (interp_list Σthis Σ σ)) by by rewrite /interp_list map_length.
      rewrite (interp_type_subst_this t tdef); first last.
      { by rewrite /interp_list map_length hlen. }
      { done. }
      (* ARGL *)













    rewrite interp_tag_unfold interp_tag_equiv; first last.
    { by rewrite /interp_list fmap_length. }
    { done. }
    { by apply wfpdefs. }
    iDestruct "He" as (?? def def1 σ0 ???) "(%H & #hmixed & #? & #hf0 & #hdyn & #H◯)".
    destruct H as ([= <-] & hdef & hdef1 & hlenΣt & hinherits & hfields & hidom).
    assert (hl0: length (generics def) = length σ0 ∧ 
                 Forall (λ ty : lang_ty, no_this ty) σ0).
    { apply inherits_using_wf in hinherits; try (by apply wfpdefs).
      destruct hinherits as (?&?&?&hh&hnothis).
      apply wf_tyI in hh as (? & ? & ? & ?); by simplify_eq.
    }
    destruct hl0 as [hl0 hnothis].
    assert (hl1: length σ0 = length σ).
    { rewrite -hl0.
      apply wf_tyI in hwf0 as (? & ? & ? & ?); by simplify_eq.
    }
    assert (hff: has_field name t1 Public (subst_ty σ0 fty) orig).
    { by apply has_field_inherits_using with (A := t1) (σB := σ0) in hf => //; try (by apply wfpdefs). }
    simpl.
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
    rewrite /subst_gen /subst_fty -hlenΣt.
    rewrite interp_type_subst_this => //.
    rewrite interp_type_subst; last first.
    { apply has_field_bounded in hf => //.
      destruct hf as (?&?&hf); simplify_eq.
      by rewrite -hl0.
    }
    rewrite (interp_list_no_this _ _ (interp_exact_class interp_type t1 Σt) interp_nothing); last done.
    iAssert (interp_type fty (interp_exact_class interp_type t1 Σt)
                (interp_list Σthis Σ σ) v) with "[Hv]" as "Hv".
    { iApply interp_with_mono => //.
      - apply has_field_mono in hf => //.
        destruct hf as (?&?&hh); simplify_eq.
        by destruct hh.
      - by apply has_field_wf in hf.
    }
    - destruct exact_; last done.
      clear h_is_exact.
      rewrite interp_type_subst; last first.
      { apply bounded_subst_this.
        - apply has_field_bounded in hf => //.
          destruct hf as (?&?&hf); simplify_eq.
          by rewrite -hl1 -hl0.
        - constructor.
          by apply bounded_gen_targs.
      }
      replace (length σ) with (length (interp_list Σthis Σ σ)) by by rewrite /interp_list map_length.
      rewrite (interp_type_subst_this t tdef); first last.
      { by rewrite /interp_list map_length hlen. }
      { done. }
      (* ARGL *)


    (* ONLY WORKS if t has no this *)
    rewrite (interp_type_no_this _ _ _ Σthis interp_nothing); first last.
    { apply wf_tyI in hwf0.
      apply subst_ty_has_no_this.
      - apply subst_this_has_no_this => /=.
        simp
        rewrite subst_this_no_this_id.


    - assert (hfty_nothis: no_this fty) by admit.
      rewrite subst_this_no_this_id; last admit.
      rewrite subst_this_no_this_id; last done.
      rewrite !interp_type_subst; first last.
      { apply has_field_bounded in hf => //.
        destruct hf as (?&?&hf); simplify_eq.
        by rewrite -hl0.
      }
      { apply has_field_bounded in hf => //.
        destruct hf as (?&?&hf); simplify_eq.
        by rewrite -hl1 -hl0.
      }
      rewrite (interp_type_no_this _ fty v interp_nothing Σthis hfty_nothis).
      iApply interp_with_mono => //.
      { apply has_field_mono in hf => //.
        destruct hf as (?&?&hh); simplify_eq.
        by destruct hh.
      }
      by apply has_field_wf in hf.
  Qed.
End proofs.
