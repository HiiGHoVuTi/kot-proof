From iris.heap_lang Require Import lang proofmode notation.
From iris.bi Require Import derived_laws.

From Coq Require Import List.
Import ListNotations.

From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Deque Require Import common tick shared_ref deque_cost push_cost concat_cost pop_cost_lemmas.

Section proof.

  Context `{!heapGS Σ} `{!na_invG Σ}.
  Context {π : gname}.

  Lemma pop_spec_helper oD x (ℓ : loc) : forall depth,
    {{{ isDeque π depth (⋅x ++ oD) (SOMEV #ℓ) ∗ ⏱ time_for_pop ∗ Token π depth }}}
      pop_nonempty (#ℓ)
    {{{ d', RET (x, d')%V; isDeque π depth oD d' ∗ Token π depth }}}.
  Proof.
    Opaque isPopFiveTuple isUnsafePopFiveTuple prepare_pop naive_pop.
    iIntros (depth ψ) "(Hd & τ & O) Hψ".
    rewrite isDeque_unfold.
    rewrite /pop_nonempty.
    Opaque pop_nonempty.
    iLöb as "iH" forall (ℓ oD x depth ψ).
    iDestruct "Hd" as "[[%H _] | (%ℓ' & %Heqℓ & Hℓ)]". by inversion H.
    inversion Heqℓ as [H]. rewrite -H. clear Heqℓ H ℓ'.
    wp_pures.
    iDestruct (split_time 1 with "τ") as "[ι τ]". by lia.
    wp_apply (tick_spec with "ι") as "_".
    wp_pures.
    wp_apply (ssref_load_open with "[Hℓ O]") as "%d (O & πd & DONE)".
      { by iFrame. }
    iDestruct (safe_decidable depth (⋅x ++ oD) d with "πd") as "[Unsafe | Safe]".
    wp_pures.
    2: {
      wp_pures.
      iDestruct "Safe" as (kp ks) "(Hsafe & τ' & pop_safe)".
      iDestruct "Hsafe" as "#Hsafe".
      Ltac gather_t pot := iDestruct (time_combine with String.concat "" ["[τ "; pot; "]"]) as "τ"; [ iFrame |].
      gather_t "τ'".
      iAssert (isPersFiveTuple π depth (⋅x ++ oD) d) as "Hd".
      - Transparent isPopFiveTuple.
        iDestruct "Hsafe" as "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                            %kMd & %ltr & %rtr &
                            -> & %conf & #Hp & #Hl & #Hm & #Hr & #Hs &
                            #Hltr & #Hrtr & %Hoeq)".
        Opaque isPopFiveTuple.
        iExists p, l, m, r, s, op, ol, om, or, os, kp, kMd, ks, ltr, rtr.
        doneL.
        iSplit. iPureIntro. inversion conf; by easy_config.
        iFrame "#". iFrame.
        done.
      - wp_bind (naive_pop_safe d)%E.
        iApply (wp_wand with "pop_safe").
        iIntros (true_) "->".
        Opaque isPersFiveTuple.
        wp_pures.
        iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
        wp_bind (#ℓ <- d)%E.
        iApply (wp_wand with "[DONE ι O Hd]").
        {
          iApply ("DONE" with "[ι Hd]"); [| by iFrame].
          iNext.
          iApply strutcure_and_time.
          by iFrame.
        }
        iIntros (unit) "O".
        wp_pures; clear unit.
        wp_apply (safe_naive_pop with "[τ]") as (x' d' o') "(Hd' & %Heq)".
          { iFrame "#".
            split_t (kp ∘ ks); [| done].
            destruct (buffer_colour (kp-1));
            destruct (buffer_colour ks);
            destruct (buffer_colour kp);
            simpl; auto with arith.
          }
        inversion Heq.
        iApply "Hψ".
        by iFrame.
      Transparent isPersFiveTuple.
    }
    iDestruct "Unsafe" as "[Hunsafe pop_unsafe]".
    wp_bind (naive_pop_safe d)%E.
    iApply (wp_wand with "pop_unsafe").
    iIntros (false_) "->".
    wp_pures.
    wp_apply (prepare_pop_spec with "[τ O Hunsafe]").
    - iFrame.
      iIntros (ℓ' x' o') "Hℓ' τ O".
      Transparent pop_nonempty.
      rewrite /pop_nonempty.
      iApply ("iH" with "[Hℓ'] [τ] [O]"); iClear "iH"; try done.
      + rewrite -isDeque_unfold. ℓisDeque ℓ'. iExact "Hℓ'".
      + iNext.
        iIntros (d') "[Hd O]".
        iExists d'. iFrame. done.
    - iIntros (f' kp ks) "(Hf' & O & τ)". iClear "iH".
      wp_pures.
      wp_bind (#ℓ <- f')%E.
      Transparent isPopFiveTuple.
      iDestruct "Hf'" as "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                          %kMd & %ltr & %rtr &
                          -> & %conf & #Hp & #Hl & #Hm & #Hr & #Hs &
                          #Hltr & #Hrtr & %Hoeq)".
      split_t (kp ⋄ ks).
      iApply (wp_wand with "[DONE O ι]").
      {
        iApply ("DONE" with "[ι]"); [| done].
        iNext.
        iExists p, l, m, r, s, op, ol, om, or, os, kp, kMd, ks, ltr, rtr.
        doneL.
        iSplit. iPureIntro. inversion conf; by easy_config.
        iFrame "#". iFrame.
        iSplit. iApply (big_sepL2_mono with "Hltr"). by auto.
        iSplit. iApply (big_sepL2_mono with "Hrtr"). by auto.
        done.
      }
      iIntros (unit) "O". wp_pures; clear unit.
      wp_apply (safe_naive_pop with "[τ]").
      + split_t (kp ∘ ks).
        iFrame.
        iExists p, l, m, r, s, op, ol, om, or, os, kMd, ltr, rtr.
        doneL.
        iSplit. iPureIntro. inversion conf; by easy_config.
        iFrame "#". iFrame.
        iSplit. iApply (big_sepL2_mono with "Hltr"). by auto.
        iSplit. iApply (big_sepL2_mono with "Hrtr"). by auto.
        done.
      + iIntros (x' d' o') "[Hd %Heq]".
        inversion Heq.
        iApply "Hψ".
        iFrame.
  Qed.

  Definition pop_spec : forall x o d,
    {{{ IsDeque π (⋅x ++ o) d ∗ Token π 0 ∗ ⏱ time_for_pop }}}
      pop d
    {{{ d', RET (x, d')%V; IsDeque π o d' ∗ Token π 0 }}}.
  Proof.
    iIntros (x o d ψ) "(#Hd & O & τ) hψ".
    rewrite /pop.
    wp_pures.
    rewrite /IsDeque isDeque_unfold.
    iCombine "Hd Hd" as "[_ [[-> %Heq]|(%ℓ & -> & Hℓ)]]";
      rewrite -isDeque_unfold;
      [ inversion Heq |].
    wp_pures.
    wp_apply (pop_spec_helper with "[O τ]").
      by (iFrame; iFrame "#").
    done.
  Qed.

End proof.