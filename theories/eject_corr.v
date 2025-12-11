From iris.heap_lang Require Import lang proofmode notation.
From iris.bi Require Import derived_laws.

From Coq Require Import List.
Import ListNotations.

From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Deque Require Import common tick shared_ref deque_corr eject_corr_lemmas.

Section proof.

  Context `{!heapGS Σ}.

  Variable NO_COST_ANALYSIS : TICK_COST = 0.

  Lemma eject_spec_helper oD x (ℓ : loc) :
    {{{ isDeque (oD ++ ⋅x) (SOMEV #ℓ) }}}
      eject_nonempty (#ℓ)
    {{{ d', RET (d', x)%V; isDeque oD d' }}}.
  Proof.
    Transparent fiveTuple.
    Opaque isEjectFiveTuple isUnsafeEjectFiveTuple prepare_eject naive_eject.
    iIntros (ψ) "Hd Hψ".
    rewrite isDeque_unfold.
    rewrite /eject_nonempty.
    Opaque eject_nonempty.
    iLöb as "iH" forall (ℓ oD x ψ).
    iDestruct "Hd" as "[[%H _] | (%ℓ' & %Heqℓ & #Hℓ)]". by inversion H.
    inversion Heqℓ as [H]. rewrite -H. clear Heqℓ H ℓ'.
    wp_pures.
    wp_apply (tick_spec) as "_".
      { rewrite NO_COST_ANALYSIS time_zero //. }
    wp_pures.
    wp_apply (csref_load with "[Hℓ]") as (d) "πd". by apply fiveTuplePersistent.
      by iExact "Hℓ".
    iDestruct (safe_decidable (oD++⋅x) d with "πd") as "[Unsafe | Safe]".
    wp_pures.
    2: {
      wp_pures.
      iDestruct "Safe" as "(Hsafe & eject_safe)".
      iDestruct "Hsafe" as "#Hsafe".
      iAssert (fiveTuple (oD ++ ⋅x) d) as "Hd".
      - Transparent isEjectFiveTuple.
        iDestruct "Hsafe" as "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                            %kPr & %kMd & %kSf & %ltr & %rtr &
                            -> & %conf & #Hp & #Hl & #Hm & #Hr & #Hs &
                            #Hltr & #Hrtr & %Hoeq)".
        Opaque isEjectFiveTuple.
        iExists p, l, m, r, s, op, ol, om, or, os, kPr, kMd, kSf, ltr, rtr.
        doneL.
        iSplit. iPureIntro. inversion conf; by easy_config.
        iFrame "#". iFrame.
        done.
      - wp_bind (naive_eject_safe d)%E.
        iApply (wp_wand with "eject_safe").
        iIntros (true_) "->".
        Opaque fiveTuple.
        wp_pures.
        wp_bind (#ℓ <- d)%E.
        wp_apply (csref_store with "[Hℓ]") as "_".
        {
          iSplit. iExact "Hℓ".
          by iFrame.
        }
        wp_pures.
        wp_apply (safe_naive_eject NO_COST_ANALYSIS) as (x' d' o') "(Hd' & %Heq)".
          { iFrame "#". }
        destruct (app_sing_inv NO_COST_ANALYSIS _ _ _ _ Heq) as [-> ->].
        iApply "Hψ".
        by iFrame.
      Transparent fiveTuple.
    }
    iDestruct "Unsafe" as "[Hunsafe eject_unsafe]".
    wp_bind (naive_eject_safe d)%E.
    iApply (wp_wand with "eject_unsafe").
    iIntros (false_) "->".
    wp_pures.
    wp_apply (prepare_eject_spec with "[Hunsafe]").
    - assumption.
    - iFrame.
      iIntros (ℓ' x' o') "Hℓ'".
      Transparent eject_nonempty.
      rewrite /eject_nonempty.
      iApply ("iH" with "[Hℓ']"); iClear "iH"; try done.
      + rewrite -isDeque_unfold. ℓisDeque ℓ'. iExact "Hℓ'".
      + iNext.
        iIntros (d') "Hd".
        iExists d'. iFrame. done.
    - iIntros (f') "Hf'". iClear "iH".
      wp_pures.
      wp_bind (#ℓ <- f')%E.
      Transparent isEjectFiveTuple.
      iDestruct "Hf'" as "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                          %kp & %kMd & %ks & %ltr & %rtr &
                          -> & %conf & #Hp & #Hl & #Hm & #Hr & #Hs &
                          #Hltr & #Hrtr & %Hoeq)".
      wp_apply (csref_store with "[Hℓ]").
      {
        iSplit. iExact "Hℓ".
        iExists p, l, m, r, s, op, ol, om, or, os, kp, kMd, ks, ltr, rtr.
        doneL.
        iSplit. iPureIntro. inversion conf; by easy_config.
        iFrame "#". iFrame.
        done.
      }
      iIntros "_". wp_pures.
      wp_apply (safe_naive_eject).
      + assumption.
      + iFrame.
        iExists p, l, m, r, s, op, ol, om, or, os, kp, kMd, ks, ltr, rtr.
        doneL.
        iSplit. iPureIntro. inversion conf; by easy_config.
        iFrame "#". iFrame.
        iSplit. iApply (big_sepL2_mono with "Hltr"). by auto.
        iSplit. iApply (big_sepL2_mono with "Hrtr"). by auto.
        done.
      + iIntros (x' d' o') "[Hd %Heq]".
        destruct (app_sing_inv NO_COST_ANALYSIS _ _ _ _ Heq) as [-> ->].
        iApply "Hψ".
        iFrame.
  Qed.

  Definition eject_spec : forall x o d,
    {{{ IsDeque (o++⋅x) d }}}
      eject d
    {{{ d', RET (d', x)%V; IsDeque o d' }}}.
  Proof.
    iIntros (x o d ψ) "#Hd hψ".
    rewrite /eject.
    wp_pures.
    rewrite /IsDeque isDeque_unfold.
    iCombine "Hd Hd" as "[_ [[-> %Heq]|(%ℓ & -> & Hℓ)]]";
      rewrite -isDeque_unfold;
      [ destruct o; simpl in Heq; inversion Heq |].
    wp_pures.
    wp_apply (eject_spec_helper).
      by (iFrame; iFrame "#").
    done.
  Qed.

End proof.
