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

  Lemma set_priv_soundness C Δ kd cdef rigid Γ fld rhs fty:
    wf_cdefs →
    wf_lty Γ →
    Forall wf_constraint Δ →
    pdefs !! C = Some cdef →
    cdef.(classfields) !! fld = Some (Private, fty) →
    expr_has_ty Δ Γ rigid kd rhs fty →
    ∀ t tdef Σt σ,
    pdefs !! t = Some tdef →
    length Σt = length tdef.(generics) →
    inherits_using t C σ →
    ∀ Σ st st' n,
    length Σ = rigid →
    rigid ≥ length cdef.(generics) →
    cmd_eval C st (SetC ThisE fld rhs) st' n →
    let Σthis := interp_exact_tag interp_type t Σt in
    ⌜interp_list interp_nothing Σt σ ≡ take (length cdef.(generics)) Σ⌝ -∗
    □ interp_env_as_mixed Σt -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σthis Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σthis Σ Γ st'.1.
  Proof.
    move => wfpdefs.
    destruct wfpdefs.
    move => wflty ? hcdef hf hrhs.
    move => t tdef Σt σ htdef hlenΣt hin_t_C.
    move => Σ st st' n hrigid hge hc Σthis.
    elim/cmd_eval_setI : hc => {n}.
    move => Ω h vis fty0 orig l v t0 vs vs' heval heval_rhs hheap ->.
    move => hf0 hvis /=.
    iIntros "%hΣeq #hΣt #hΣ #hΣΔ".
    iIntros "[Hh #Hle]" => /=.
    iSplitL; last done.
    destruct Ω as [vthis Ω].
    case: heval heval_rhs => -> heval_rhs {vthis}.
    iAssert (□ interp_as_mixed Σthis)%I as "#hΣthis".
    { iModIntro; iIntros (w) "hw".
      iLeft; iRight; iRight.
      iExists t, Σt, tdef; iSplit; first done.
      by iApply (exact_subtype_is_inclusion_aux with "hΣt hw").
    }
    iApply (heap_models_update_priv _ _ _ _ t0 C $! hΣeq with "hΣt hΣ hΣΔ") => //.
    - by subst.
    - by iDestruct "Hle" as "[Hthis Hle]".
    - by iApply expr_soundness.
  Qed.

  Lemma set_pub_soundness C cdef Δ kd rigid Γ recv fld rhs fty exact_ t σ orig:
    wf_cdefs →
    wf_lty Γ →
    Forall wf_constraint Δ →
    pdefs !! C = Some cdef →
    expr_has_ty Δ Γ rigid kd recv (ClassT exact_ t σ) →
    has_field fld t Public fty orig →
    (is_true exact_ ∨ no_this fty) →
    expr_has_ty Δ Γ rigid kd rhs (subst_fty exact_ t σ fty) →
    ∀ t0 t0def Σt0 σ0,
    pdefs !! t0 = Some t0def →
    length Σt0 = length t0def.(generics) →
    inherits_using t0 C σ0 →
    ∀ Σ st st' n,
    length Σ = rigid →
    cmd_eval C st (SetC recv fld rhs) st' n →
    let Σthis0 := interp_exact_tag interp_type t0 Σt0 in
    ⌜interp_list interp_nothing Σt0 σ0 ≡ take (length cdef.(generics)) Σ⌝ -∗
    □ interp_env_as_mixed Σt0 -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis0 Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σthis0 Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σthis0 Σ Γ st'.1.
  Proof.
    move => wfpdefs wflty ? hcdef hrecv hf hex hrhs.
    move => t0 t0def Σt0 σ0 ht0def hlenΣt0 hin0.
    move => Σ st st' n hrigid hc.
    elim/cmd_eval_setI : hc => {n}.
    move => Ω h vis fty0 orig0 l v t1 vs vs' heval heval_rhs hheap ->.
    move => hf0 hvis Σthis0.
    iIntros "%heqΣ #hΣt0 #hΣ #hΣΔ".
    iIntros "[Hh #Hle]" => /=.
    iSplitL; last done.
    assert (ht: wf_ty (ClassT exact_ t σ)) by (by apply expr_has_ty_wf in hrecv).
    iAssert (□ interp_as_mixed Σthis0)%I as "#hΣthis".
    { iModIntro; iIntros (w) "hw".
      iLeft; iRight; iRight.
      iExists t0, Σt0, t0def; iSplit; first done.
      by iApply (exact_subtype_is_inclusion_aux with "hΣt0 hw").
    }
    iApply ((heap_models_update_pub _ _ _ _ _ _ exact_ t σ)
      with "hΣt0 hΣ") => //=; try (by apply wfpdefs).
    - iApply expr_soundness => //; by apply wfpdefs.
    - iApply expr_soundness => //; by apply wfpdefs.
  Qed.

  (* TODO: factorize the priv vs pub mechanics. This proof is using both *)
  Lemma set_this_soundness C cdef Δ kd rigid Γ recv fld rhs fty orig:
    wf_cdefs →
    wf_lty Γ →
    Forall wf_constraint Δ →
    pdefs !! C = Some cdef →
    expr_has_ty Δ Γ rigid kd recv ThisT →
    has_field fld C Public fty orig →
    expr_has_ty Δ Γ rigid kd rhs fty →
    ∀ t tdef Σt σ,
    pdefs !! t = Some tdef →
    length Σt = length tdef.(generics) →
    inherits_using t C σ →
    ∀ Σ st st' n,
    length Σ = rigid →
    rigid ≥ length cdef.(generics) →
    cmd_eval C st (SetC recv fld rhs) st' n →
    let Σthis := interp_exact_tag interp_type t Σt in
    ⌜interp_list interp_nothing Σt σ ≡ take (length cdef.(generics)) Σ⌝ -∗
    □ interp_env_as_mixed Σt -∗
    □ interp_env_as_mixed Σ -∗
    □ Σinterp Σthis Σ Δ -∗
    heap_models st.2 ∗ interp_local_tys Σthis Σ Γ st.1 -∗
    |=▷^n heap_models st'.2 ∗ interp_local_tys Σthis Σ Γ st'.1.
  Proof.
    move => wfpdefs.
    destruct wfpdefs.
    move => wflty ? hcdef hrecv hf hrhs.
    move => t tdef Σt σ htdef hlenΣt hin_t_C.
    move => Σ st st' n hrigid hge hc Σthis.
    elim/cmd_eval_setI : hc => {n}.
    move => Ω h vis fty0 orig0 l v t0 vs vs' heval heval_rhs hheap ->.
    move => hf0 hvis /=.
    iIntros "%hΣeq #hΣt #hΣ #hΣΔ".
    iIntros "[Hh #Hle]" => /=.
    (* TODO *)
    iAssert (□ interp_as_mixed Σthis)%I as "#hΣthis".
    { iModIntro; iIntros (w) "hw".
      iLeft; iRight; iRight.
      iExists t, Σt, tdef; iSplit; first done.
      by iApply (exact_subtype_is_inclusion_aux with "hΣt hw").
    }
    iAssert (□ interp_type fty Σthis Σ v)%I as "#hrhs".
    { by iApply (expr_soundness with "hΣthis hΣ hΣΔ Hle"). }
    iAssert (□ interp_type ThisT Σthis Σ (LocV l))%I as "#hrecv".
    { by iApply (expr_soundness with "hΣthis hΣ hΣΔ Hle"). }
    rewrite interp_this_unfold {5}/Σthis /=.
    rewrite interp_exact_tag_unseal /interp_exact_tag_def /=.
    iDestruct "hrecv" as (? tdef' fields ifields hpure) "(#hconstr & #hfields & hl)".
    destruct hpure as ([= <-] & htdef' & hfields & hdomfields); simplify_eq.
    iSplitL; last done.
    iDestruct "Hh" as (sh) "(hown & %hdom & #h)".
    iExists sh.
    iDestruct (sem_heap_own_valid_2 with "hown hl") as "#Hv".
    iSplitL "hown"; first by iFrame.
    iSplitR.
    { iPureIntro.
      by rewrite hdom dom_insert_lookup_L.
    }
    iModIntro.
    iIntros (l'' t'' vs'') "%Heq".
    rewrite lookup_insert_Some in Heq.
    destruct Heq as [[<- [= <- <-]] | [hne hl]]; last first.
    { iApply "h".
      by iPureIntro.
    }
    iSpecialize ("h" $! l t0 vs with "[//]").
    iDestruct "h" as (iFs) "[#hsh hmodels]".
    iExists iFs; iSplit; first done.
    iRewrite "Hv" in "hsh".
    rewrite !option_equivI prod_equivI /=.
    iDestruct "hsh" as "[%ht #hifs]".
    fold_leibniz; subst.
    assert (hf2 : has_field fld t0 Public (subst_ty σ fty) orig)
      by by eapply has_field_inherits_using.
    destruct (has_field_fun _ _ _ _ _ hf0 _ _ _ hf2) as (-> & -> & ->).
    iSpecialize ("hfields" $! fld Public (subst_ty σ fty) orig hf0).
    rewrite later_equivI.
    iNext.
    iDestruct "hfields" as (iF) "(#hiF & #hiff)".
    iAssert (⌜is_Some (iFs !! fld)⌝)%I as "%hiFs".
    { iRewrite -"hifs".
      by iRewrite "hiF".
    }
    rewrite /heap_models_fields.
    iDestruct "hmodels" as "[%hdomv #hmodfs]".
    iSplit.
    { iPureIntro.
      by rewrite -hdomv dom_insert_lookup // -elem_of_dom hdomv elem_of_dom.
    }
    iIntros (f' iF') "#hf'".
    destruct (decide (fld = f')) as [-> | hne]; last first.
    { rewrite lookup_insert_ne //.
      by iApply "hmodfs".
    }
    rewrite lookup_insert.
    iExists v; iSplitR; first done.
    iRewrite -"hifs" in "hf'".
    iRewrite "hiF" in "hf'".
    rewrite !option_equivI discrete_fun_equivI.
    iSpecialize ("hf'" $! v).
    iRewrite -"hf'".
    iApply "hiff".
    rewrite /subst_gen -hlenΣt.
    iAssert (interp_type (subst_ty σ fty) Σthis Σt v -∗
      interp_type (subst_this (ClassT true t0 (gen_targs (length Σt))) (subst_ty σ fty)) interp_nothing Σt v)%I as "Himpl".
    { rewrite interp_type_subst_this => //.
      by iIntros.
    }
    iApply "Himpl"; iClear "Himpl".
    assert (h0 := hin_t_C).
    apply inherits_using_wf in h0 => //.
    destruct h0 as (? & ? & ? & hwf & ?); simplify_eq.
    assert (bounded (length (generics cdef)) fty).
    { apply has_field_bounded in hf => //.
      destruct hf as (def' & hdef' & hfty).
      by simplify_eq.
    }
    rewrite interp_type_subst; last first.
    { apply wf_tyI in hwf as (? & ? & hlen & ?); simplify_eq.
      by rewrite hlen.
    }
    iClear "hconstr hiF hiff hl hifs hmodfs hf' Hv".
    rewrite {4}/Σthis.
    assert (heq : interp_list Σthis Σt σ ≡ interp_list interp_nothing Σt σ).
    { by apply interp_list_no_this. }
    rewrite (interp_type_equivI _ _ _ heq).
    rewrite (interp_type_equivI _ _ _ hΣeq).
    by rewrite interp_type_take.
  Qed.
End proofs.
