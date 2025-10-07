From iris.heap_lang Require Import lang proofmode notation.
From iris.bi Require Import derived_laws.

From Coq Require Import List.
Import ListNotations.

From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Deque Require Import common tick shared_ref deque_corr push_corr concat_corr pop_corr_lemmas.

Section proof.

  Context `{!heapGS Σ}.

  (* since this is a functional correction proof, we use a cheat that is confined to this section *)
  Let TIME_CHEAT : ∀ k, ⊢ (⏱ k : iProp Σ).
  Admitted.

  Lemma pop_spec_helper oD x (ℓ : loc) :
    {{{ isDeque (⋅x ++ oD) (SOMEV #ℓ) }}}
      pop_nonempty (#ℓ)
    {{{ d', RET (x, d')%V; isDeque oD d' }}}.
  Proof.
    Opaque isPopFiveTuple isUnsafePopFiveTuple prepare_pop naive_pop.
    iIntros (ψ) "Hd Hψ".
    rewrite isDeque_unfold.
    rewrite /pop_nonempty.
    Opaque pop_nonempty.
    iLöb as "iH" forall (ℓ oD x ψ).
    iDestruct "Hd" as "[[%H _] | (%ℓ' & %Heqℓ & #Hℓ)]". by inversion H.
    inversion Heqℓ as [H]. rewrite -H. clear Heqℓ H ℓ'.
    wp_pures.
    iDestruct (TIME_CHEAT) as "ι".
    wp_apply (tick_spec with "ι") as "_".
    wp_pures.
    wp_apply (csref_load with "Hℓ") as (d) "πd".
    iDestruct (safe_decidable (⋅x ++ oD) d with "πd") as "[Unsafe | Safe]".
    wp_pures.
    2: {
      wp_pures.
      iDestruct "Safe" as "(Hsafe & pop_safe)".
      iDestruct "Hsafe" as "#Hsafe".
      iAssert (fiveTuple (⋅x ++ oD) d) as "Hd".
      - Transparent isPopFiveTuple.
        iDestruct "Hsafe" as "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                            %kPr & %kMd & %kSf & %ltr & %rtr &
                            -> & %conf & #Hp & #Hl & #Hm & #Hr & #Hs &
                            #Hltr & #Hrtr & %Hoeq)".
        Opaque isPopFiveTuple.
        iExists p, l, m, r, s, op, ol, om, or, os, kPr, kMd, kSf, ltr, rtr.
        doneL.
        iSplit. iPureIntro. inversion conf; by easy_config.
        iFrame "#". iFrame.
        done.
      - wp_bind (naive_pop_safe d)%E.
        iApply (wp_wand with "pop_safe").
        iIntros (true_) "->".
        Opaque fiveTuple.
        wp_pures.
        wp_apply (csref_store with "[Hℓ]").
        {
          iSplit. iExact "Hℓ".
          by iFrame.
        }
        iIntros (unit).
        wp_pures; clear unit.
        wp_apply (safe_naive_pop with "[Hd]") as (x' d' o') "(Hd' & %Heq)".
        { iFrame "#".
        }
        inversion Heq.
        iApply "Hψ".
        by iFrame.
      Transparent fiveTuple.
    }
    iDestruct "Unsafe" as "[Hunsafe pop_unsafe]".
    wp_bind (naive_pop_safe d)%E.
    iApply (wp_wand with "pop_unsafe").
    iIntros (false_) "->".
    wp_pures.
    wp_apply (prepare_pop_spec with "[Hunsafe]").
    - iFrame.
      iIntros (ℓ' x' o') "Hℓ'".
      Transparent pop_nonempty.
      rewrite /pop_nonempty.
      iApply ("iH" with "[Hℓ']"); iClear "iH"; try done.
      + rewrite -isDeque_unfold. ℓisDeque ℓ'. iExact "Hℓ'".
      + iNext.
        iIntros (d') "Hd".
        iExists d'. iFrame. done.
    - iIntros (f') "Hf'". iClear "iH".
      wp_pures.
      wp_bind (#ℓ <- f')%E.
      Transparent isPopFiveTuple.
      iDestruct "Hf'" as "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                          %kPr & %kMd & %kSf & %ltr & %rtr &
                          -> & %conf & #Hp & #Hl & #Hm & #Hr & #Hs &
                          #Hltr & #Hrtr & %Hoeq)".
      wp_apply (csref_store with "[Hℓ]").
      {
        iSplit. iExact "Hℓ".
        iExists p, l, m, r, s, op, ol, om, or, os, kPr, kMd, kSf, ltr, rtr.
        doneL.
        iSplit. iPureIntro. inversion conf; by easy_config.
        iFrame "#". iFrame.
        done.
      }
      iIntros (unit). wp_pures; clear unit.
      wp_apply (safe_naive_pop).
      + iFrame.
        iExists p, l, m, r, s, op, ol, om, or, os, kPr, kMd, kSf, ltr, rtr.
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
    {{{ IsDeque (⋅x ++ o) d }}}
      pop d
    {{{ d', RET (x, d')%V; IsDeque o d' }}}.
  Proof.
    iIntros (x o d ψ) "#Hd hψ".
    rewrite /pop.
    wp_pures.
    rewrite /IsDeque isDeque_unfold.
    iCombine "Hd Hd" as "[_ [[-> %Heq]|(%ℓ & -> & Hℓ)]]";
      rewrite -isDeque_unfold;
      [ inversion Heq |].
    wp_pures.
    wp_apply (pop_spec_helper).
      by (iFrame; iFrame "#").
    done.
  Qed.

End proof.