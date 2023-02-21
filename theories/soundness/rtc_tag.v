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

From shack Require Import lang progdef subtype ok.
From shack Require Import eval heap modality interp typing.
From shack.soundness Require Import expr defs.

Section proofs.
  (* assume a given set of class definitions and their SDT annotations. *)
  Context `{SDTCVS: SDTClassVarianceSpec}.

  (* Iris semantic context *)
  Context `{!sem_heapGS Θ}.

  (* Helping the inference with this notation that hides pdefs *)
  Local Notation "Δ ⊢ s <: t" := (@subtype _ _ Δ Plain s t) (at level 70, s at next level, no associativity).
  Local Notation "Δ ⊢ s <D: t" := (@subtype _ _ Δ Aware s t) (at level 70, s at next level, no associativity).

  Lemma rtc_tag_soundness C cdef Δ kd rigid Γ0 Γ1 v tv t def thn els:
    wf_cdefs →
    wf_lty Γ0 →
    bounded_lty rigid Γ0 →
    Forall wf_constraint Δ →
    Forall (bounded_constraint rigid) Δ →
    pdefs !! C = Some cdef →
    ∀ t0 t0def Σt0 σ0,
    pdefs !! t0 = Some t0def →
    length Σt0 = length t0def.(generics) →
    Γ0 !! v = Some tv →
    pdefs !! t = Some def →
    cmd_has_ty C (lift_constraints rigid (constraints def) ++ Δ) kd
         (rigid + length (generics def))
         (<[v:=InterT tv
                 (ClassT false t (map GenT (seq rigid (length (generics def)))))]>
            Γ0) thn Γ1 →
    cmd_has_ty C Δ kd rigid Γ0 els Γ1 →
    ∀ Σ st st' n,
    length Σ = rigid →
    rigid ≥ length cdef.(generics) →
    cmd_eval C st (RuntimeCheckC v (RCTag t) thn els) st' n →
    let Σthis0 := interp_exact_tag interp_type t0 Σt0 in
    ⌜interp_list interp_nothing Σt0 σ0 ≡ take (length cdef.(generics)) Σ⌝ -∗
    □ interp_env_as_mixed Σt0 -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis0 Σ Δ -∗

    □ ( ⌜wf_lty
          (<[v:=InterT tv
            (ClassT false t (map GenT (seq rigid (length (generics def)))))]>
            Γ0)⌝ →
        ⌜bounded_lty (rigid + length (generics def))
          (<[v:=InterT tv
            (ClassT false t
              (map GenT (seq rigid (length (generics def)))))]> Γ0)⌝ →
        ⌜Forall wf_constraint (lift_constraints rigid (constraints def) ++ Δ)⌝ →
        ⌜Forall (bounded_constraint (rigid + length (generics def)))
          (lift_constraints rigid (constraints def) ++ Δ)⌝ →
        ∀ Σ st st' n
          (_: length Σ = (rigid + length (generics def))%nat)
          (_: rigid + length def.(generics) ≥ length cdef.(generics))
          (_: cmd_eval C st thn st' n),
          ⌜interp_list interp_nothing Σt0 σ0 ≡ take (length cdef.(generics)) Σ⌝ -∗
          □ interp_env_as_mixed Σt0 -∗
          □ interp_env_as_mixed Σ -∗
          □ Σinterp Σthis0 Σ (lift_constraints rigid (constraints def) ++ Δ) -∗
          heap_models st.2 ∗
            interp_local_tys Σthis0 Σ
              (<[v:=InterT tv
                (ClassT false t (map GenT (seq rigid (length (generics def)))))]>
                Γ0) st.1 -∗
          |=▷^n heap_models st'.2 ∗ interp_local_tys Σthis0 Σ Γ1 st'.1) -∗
    □ ( ⌜wf_lty Γ0⌝ →
        ⌜bounded_lty rigid Γ0⌝ →
        ⌜Forall wf_constraint Δ⌝ →
        ⌜Forall (bounded_constraint rigid) Δ⌝ →
        ∀ Σ st st' n
          (_: length Σ = rigid)
          (_ : rigid ≥ length cdef.(generics))
          (_: cmd_eval C st els st' n),
          ⌜interp_list interp_nothing Σt0 σ0 ≡ take (length cdef.(generics)) Σ⌝ -∗
          □ interp_env_as_mixed Σt0 -∗
          □ interp_env_as_mixed Σ -∗
          □ Σinterp Σthis0 Σ Δ -∗
          heap_models st.2 ∗ interp_local_tys Σthis0 Σ Γ0 st.1 -∗
        |=▷^n heap_models st'.2 ∗ interp_local_tys Σthis0 Σ Γ1 st'.1) -∗
    heap_models st.2 ∗ interp_local_tys Σthis0 Σ Γ0 st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σthis0 Σ Γ1 st'.1.
  Proof.
    move => wfpdefs wflty blty ? hΔb hcdef.
    move => t0 t0def Σt0 σ0 ht0def hlenΣt0.
    move => hv hdef hthn hels Σ st st' n hrigid hge hc Σthis0.
    iIntros "%hΣeq #hΣt0 #hΣ #hΣΔ #Hthn #Hels".
    elim/cmd_eval_rtcI : hc; last first.
    { move => ??; iIntros "[Hh H]".
      iApply "Hels" => //.
      by iSplit.
    }
    move => n0 hmatch heval.
    iClear "Hels".
    iIntros "H".
    pose (Δthn := lift_constraints rigid def.(constraints) ++ Δ).
    pose (tc := ClassT false t (map GenT (seq rigid (length def.(generics))))).
    assert (hwf: wf_lty (<[v:=InterT tv tc]> Γ0)).
    { apply insert_wf_lty => //.
      constructor; first by apply wflty in hv.
      econstructor => //.
      - by rewrite map_length seq_length.
      - rewrite Forall_lookup => k ty hx.
        apply list_lookup_fmap_inv in hx.
        destruct hx as [ty' [ -> h]].
        by constructor.
    }
    assert (hbounded:
      bounded_lty (rigid + length (generics def)) (<[v:=InterT tv tc]> Γ0)).
    { apply insert_bounded_lty.
      - constructor.
        + apply bounded_ge with rigid; last by lia.
          by apply blty in hv.
        + by apply bounded_rigid.
      - apply bounded_lty_ge with rigid; last by lia.
        by apply blty.
    }
    destruct hmatch as (l & hl & t' & fields & hlt & hinherits).
    iDestruct "H" as "[H #Hle]".
    iDestruct "Hle" as "[Hthis Hle]".
    iDestruct ("Hle" $! v with "[//]") as (?) "[%Hlev Hv]".
    rewrite Hlev in hl; simplify_eq.
    iAssert (□ interp_as_mixed interp_nothing)%I as "#hnothing".
    { iModIntro; by iIntros (w) "hw". }
    iAssert (□ interp_as_mixed Σthis0)%I as "#hΣthis".
    { iModIntro; iIntros (w) "hw".
      iLeft; iRight; iRight.
      iExists t0, Σt0, t0def; iSplit; first done.
      by iApply (exact_subtype_is_inclusion_aux with "hΣt0 hw").
    }
    iAssert (heap_models st.2 ∗
      ∃ Σt σin,
        let Σex := interp_list interp_nothing Σt σin in
        interp_tag interp_type t Σex (LocV l) ∗
        ⌜length Σex = length def.(generics)⌝ ∗
        □ ▷ interp_env_as_mixed Σt ∗
        □ ▷ interp_env_as_mixed Σex ∗
        □ ▷ Σinterp Σthis0 Σex def.(constraints)
    )%I with "[H]" as "[Hh #Hv2]".
    { iAssert (interp_type MixedT Σthis0 Σ (LocV l)) as "Hmixed".
      { destruct wfpdefs.
        assert (hsub : Δ ⊢ tv <: MixedT) by apply SubMixed.
        iApply subtype_is_inclusion => //.
        by apply wflty in hv.
      }
      rewrite interp_mixed_unfold /=.
      iDestruct "Hmixed" as "[Hnonnull | Hnull]"; last first.
      { iDestruct "Hnull" as "%Hnull"; discriminate. }
      iDestruct "Hnonnull" as "[Hint | Hl]".
      { iDestruct "Hint" as "%Hint"; by destruct Hint. }
      iDestruct "Hl" as "[Hbool | Hl]".
      { iDestruct "Hbool" as "%Hbool"; by destruct Hbool. }
      iDestruct "Hl" as (exTag exΣ exdef [hexdef hlen]) "Hl".
      rewrite interp_tag_equiv //; last (by apply wfpdefs).
      iDestruct "Hl" as (k rt exdef' rtdef σ Σt exfields ifields)
        "(%H & #hmixed & #hΣt & #hinst & #hdyn & #Hl)".
      destruct H as ([= <-] & hexdef' & hrtdef & hlΣt
        & hinherits' & hfields' & hidom'); simplify_eq.
      iDestruct "H" as (sh) "(H● & %hdom & #Hh)".
      iDestruct (sem_heap_own_valid_2 with "H● Hl") as "#HΦ".
      iDestruct ("Hh" with "[//]") as (iFs) "[H H▷]".
      iRewrite "H" in "HΦ".
      rewrite option_equivI prod_equivI /=.
      iDestruct "HΦ" as "[%Ht HΦ]".
      fold_leibniz; subst.
      iSplitL. { iExists _. iFrame. by iSplit. }
      assert (hh: ∃ σ, inherits_using rt t σ ∧
        length σ = length def.(generics)).
      { move: hdef hinherits.
        clear => hdef.
        induction 1 as [ t | s t u hst htu hi ].
        - exists (gen_targs (length def.(generics))).
          split; first by constructor.
          by rewrite length_gen_targs.
        - destruct (hi hdef) as (σ & h0 & h1).
          destruct hst as [s t sdef σB hsdef hsuper].
          exists (subst_ty σB <$> σ); split.
          + eapply InheritsTrans.
            * by econstructor.
            * done.
          + by rewrite map_length.
      }
      destruct hh as (σin & hσin & heq).
      assert (hwfσin : Forall wf_ty σin).
      { destruct wfpdefs.
        apply inherits_using_wf in hσin => //.
        destruct hσin as (? & ? & ? & h & ?); simplify_eq.
        by apply wf_ty_classI in h.
      }
      assert (hexlen: length (interp_list interp_nothing Σt σin) =
                      length (generics def)).
      { by rewrite /interp_list map_length. }
      iExists Σt, σin.
      iSplit.
      { rewrite interp_tag_equiv //; last (by apply wfpdefs).
        iExists l, rt, def, rtdef, σin, Σt, exfields, ifields.
        iSplit; first done.
        iSplit => //.
        iSplit => //.
        iSplit; last by iSplit.
        iModIntro; iNext.
        iApply iForall3_interp_reflexive.
        by rewrite /interp_list map_length heq.
      }
      iSplit.
      { iPureIntro.
        by rewrite /interp_list fmap_length.
      }
      iSplit; first done.
      iSplit.
      { iModIntro; iNext.
        iIntros (k ϕ hϕ w) "#Hw".
        apply list_lookup_fmap_inv in hϕ as [ty [-> hty]].
        iAssert (interp_type MixedT interp_nothing Σt w) as "HH".
        { iApply (submixed_is_inclusion_aux _ _ ty) => //.
          rewrite Forall_lookup in hwfσin.
          by apply hwfσin in hty.
        }
        by rewrite interp_mixed_unfold.
      }
      { iModIntro; iNext.
        iIntros (k c hc w).
        destruct  wfpdefs.
        assert (hno: no_this_constraint c).
        { apply wf_constraints_no_this in hdef.
          rewrite /wf_cdef_constraints_no_this Forall_lookup in hdef.
          by apply hdef in hc as [].
        }
        destruct hno as [].
        iClear "Hv".
        rewrite (interp_type_no_this _ _ _ Σthis0 interp_nothing); last done.
        rewrite (interp_type_no_this _ _ _ Σthis0 interp_nothing); last done.
        rewrite -!interp_type_subst; first last.
        { apply wf_constraints_bounded in hdef.
          rewrite /wf_cdef_constraints_bounded Forall_lookup -heq in hdef.
          by apply hdef in hc as [].
        }
        { apply wf_constraints_bounded in hdef.
          rewrite /wf_cdef_constraints_bounded Forall_lookup -heq in hdef.
          by apply hdef in hc as [].
        }
        assert (hh := hσin).
        apply inherits_using_ok in hh => //.
        destruct hh as (? & ? & hok); simplify_eq.
        apply ok_tyI in hok as (? & ? & ? & hok); simplify_eq.
        assert (hc' := hc).
        apply hok in hc'.
        iApply (subtype_is_inclusion with "hnothing hmixed hΣt") => //.
        + by apply wf_constraints_wf in hrtdef.
        + apply wf_constraints_wf in hdef.
          rewrite /wf_cdef_constraints_wf Forall_lookup in hdef.
      apply hdef in hc as [].
      by apply wf_ty_subst.
      }
    }
    iDestruct "Hv2" as (Σt σin) "(Hv2 & %heq & #hΣt & #hΣex & #hΣexΔc)".
    (* We need the extra +1 to get that the existiential Σ
     * is correctly ⊆ mixed
     *)
    rewrite updN_S.
    iModIntro; iNext.
    pose (Σex := interp_list interp_nothing Σt σin).
    iAssert (interp_env_as_mixed (Σ ++ Σex)) as "hmixed".
    { iIntros (k ϕ hϕ w) "#hw".
      rewrite lookup_app in hϕ.
      destruct (Σ !! k) as [ty0 | ] eqn:h0.
      + case: hϕ => <-.
        by iApply "hΣ".
      + by iApply "hΣex".
    }
    iAssert (Σinterp Σthis0 (Σ ++ Σex) Δthn) as "hΣ_Δ".
    { iIntros (k c hc w) "#hw".
      rewrite Forall_lookup in hΔb.
      rewrite /Δthn lookup_app in hc.
      destruct (lift_constraints (length Σ) def.(constraints) !! k) as [c0 | ] eqn:hc0.
      + case : hc => <-.
        apply list_lookup_fmap_inv in hc0 as [c1 [-> hc1]].
        rewrite !interp_type_lift.
        by iApply "hΣexΔc".
      + rewrite -!interp_type_app.
        * by iApply "hΣΔ".
        * by apply hΔb in hc as [].
        * by apply hΔb in hc as [].
    }
    iAssert (|=▷^n0 heap_models st'.2 ∗
      interp_local_tys Σthis0 (Σ ++ Σex) Γ1 st'.1)%I with "[Hh]" as "H".
    { iApply "Hthn" => //.
      - iPureIntro.
        apply Forall_app; split.
        + apply lift_constraints_wf.
          by apply wf_constraints_wf in hdef.
        + assumption.
      - iPureIntro.
        apply Forall_app; split.
        + apply lift_constraints_bounded.
          by apply wf_constraints_bounded in hdef.
        + apply bounded_constraints_ge with (length Σ); first done.
          by lia.
      - by rewrite app_length heq.
      - iPureIntro; by lia.
      - iPureIntro.
        by rewrite take_app_le. 
      - iFrame.
        iSplit; first done.
        iIntros (w tw).
        rewrite lookup_insert_Some.
        iIntros "%Hw".
        destruct Hw as [[<- <-] | [hne hw]].
        + iExists (LocV l); rewrite Hlev; iSplitR; first done.
          rewrite interp_inter_unfold; iSplit.
          { rewrite -interp_type_app; first done.
            by apply blty in hv.
          }
          rewrite (interp_type_rigid _ Σ Σex); first by rewrite heq.
          { by destruct wfpdefs. }
          econstructor => //.
          { by rewrite map_length seq_length heq. }
          rewrite Forall_lookup => k ty h.
          apply list_lookup_fmap_inv in h as [? [-> h]].
          by constructor.
        + iDestruct ("Hle" $! w tw hw) as (z hz) "#Hz".
          iExists z; iSplit; first done.
          rewrite -interp_type_app; first done.
          by apply blty in hw.
    }
    iRevert "H".
    iApply updN_mono_I.
    iIntros "[Hm H]"; iFrame.
    rewrite -interp_local_app; first done.
    destruct wfpdefs.
    by eapply cmd_has_ty_bounded in hels.
  Qed.
End proofs.
