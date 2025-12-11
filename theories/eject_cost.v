From iris.heap_lang Require Import lang proofmode notation.
From iris.bi Require Import derived_laws.

From Coq Require Import List.
Import ListNotations.

From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Deque Require Import common tick shared_ref deque_cost eject_cost_lemmas.

Section proof.

  Context `{!heapGS Σ} `{!na_invG Σ}.
  Context {π : gname}.

  Variable COST_ANALYSIS : TICK_COST = 1.

  Lemma eject_spec_helper oD x (ℓ : loc) : forall depth,
    {{{ isDeque π depth (oD ++ ⋅x) (SOMEV #ℓ) ∗ ⏱ time_for_pop ∗ Token π depth }}}
      eject_nonempty (#ℓ)
    {{{ d', RET (d', x)%V; isDeque π depth oD d' ∗ Token π depth }}}.
  Proof.
    Opaque isEjectFiveTuple isUnsafeEjectFiveTuple prepare_eject naive_eject.
    iIntros (depth ψ) "(Hd & τ & O) Hψ".
    rewrite isDeque_unfold.
    rewrite /eject_nonempty.
    Opaque eject_nonempty.
    iLöb as "iH" forall (ℓ oD x depth ψ).
    iDestruct "Hd" as "[[%H _] | (%ℓ' & %Heqℓ & Hℓ)]". by inversion H.
    inversion Heqℓ as [H]. rewrite -H. clear Heqℓ H ℓ'.
    wp_pures.
    iDestruct (split_time 1 with "τ") as "[ι τ]". by lia.
    rewrite -COST_ANALYSIS.
    wp_apply (tick_spec with "ι") as "_".
    rewrite COST_ANALYSIS.
    wp_pures.
    wp_apply (ssref_load_open with "[Hℓ O]") as "%d (O & πd & DONE)".
      { by iFrame. }
    iDestruct (safe_decidable depth (oD++⋅x) d with "πd") as "[Unsafe | Safe]".
    wp_pures.
    2: {
      wp_pures.
      iDestruct "Safe" as (kp ks) "(Hsafe & τ' & eject_safe)".
      iDestruct "Hsafe" as "#Hsafe".
      gather_t "τ'".
      iAssert (isPersFiveTuple π depth (oD ++ ⋅x) d) as "Hd".
      - Transparent isEjectFiveTuple.
        iDestruct "Hsafe" as "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                            %kMd & %ltr & %rtr &
                            -> & %conf & #Hp & #Hl & #Hm & #Hr & #Hs &
                            #Hltr & #Hrtr & %Hoeq)".
        Opaque isEjectFiveTuple.
        iExists p, l, m, r, s, op, ol, om, or, os, kp, kMd, ks, ltr, rtr.
        doneL.
        iSplit. iPureIntro. inversion conf; by easy_config.
        iFrame "#". iFrame.
        done.
      - wp_bind (naive_eject_safe d)%E.
        iApply (wp_wand with "eject_safe").
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
        wp_apply (safe_naive_eject COST_ANALYSIS with "[τ]") as (x' d' o') "(Hd' & %Heq)".
          { iFrame "#".
            split_t (kp ∘ ks); [| done].
            destruct (buffer_colour (ks-1));
            destruct (buffer_colour ks);
            destruct (buffer_colour kp);
            simpl; auto with arith.
          }
        destruct (app_sing_inv COST_ANALYSIS _ _ _ _ Heq) as [-> ->].
        iApply "Hψ".
        by iFrame.
      Transparent isPersFiveTuple.
    }
    iDestruct "Unsafe" as "[Hunsafe eject_unsafe]".
    wp_bind (naive_eject_safe d)%E.
    iApply (wp_wand with "eject_unsafe").
    iIntros (false_) "->".
    wp_pures.
    wp_apply (prepare_eject_spec with "[τ O Hunsafe]").
    - assumption.
    - iFrame.
      iIntros (ℓ' x' o') "Hℓ' τ O".
      Transparent eject_nonempty.
      rewrite /eject_nonempty.
      iApply ("iH" with "[Hℓ'] [τ] [O]"); iClear "iH"; try done.
      + rewrite -isDeque_unfold. ℓisDeque ℓ'. iExact "Hℓ'".
      + iNext.
        iIntros (d') "[Hd O]".
        iExists d'. iFrame. done.
    - iIntros (f' kp ks) "(Hf' & O & τ)". iClear "iH".
      wp_pures.
      wp_bind (#ℓ <- f')%E.
      Transparent isEjectFiveTuple.
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
      wp_apply (safe_naive_eject with "[τ]").
      + assumption.
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
        destruct (app_sing_inv COST_ANALYSIS _ _ _ _ Heq) as [-> ->].
        iApply "Hψ".
        iFrame.
  Qed.

  Definition eject_spec : forall x o d,
    {{{ IsDeque π (o++⋅x) d ∗ Token π 0 ∗ ⏱ time_for_pop }}}
      eject d
    {{{ d', RET (d', x)%V; IsDeque π o d' ∗ Token π 0 }}}.
  Proof.
    iIntros (x o d ψ) "(#Hd & O & τ) hψ".
    rewrite /eject.
    wp_pures.
    rewrite /IsDeque isDeque_unfold.
    iCombine "Hd Hd" as "[_ [[-> %Heq]|(%ℓ & -> & Hℓ)]]";
      rewrite -isDeque_unfold;
      [ destruct o; simpl in Heq; inversion Heq |].
    wp_pures.
    wp_apply (eject_spec_helper with "[O τ]").
      by (iFrame; iFrame "#").
    done.
  Qed.

End proof.
