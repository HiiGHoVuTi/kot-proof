From iris.heap_lang Require Import lang proofmode notation.
From iris.bi Require Import derived_laws.

From Coq Require Import List.
Import ListNotations.

From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Deque Require Import common tick shared_ref deque_corr.

Section proof.

  Context `{!heapGS Σ}.

  Variable NO_COST_ANALYSIS : TICK_COST = 0.

  Lemma push_spec_helper oD x d :
    {{{ isDeque oD d }}}
      push x d
    {{{ d', RET d'; isDeque (⋅x ++ oD) d' }}}.
  Proof.
    iLöb as "iH" forall (x d oD).
    iIntros (ψ) "Hd Hψ".
    rewrite /push.
    wp_pures.
    wp_apply (tick_spec) as "_".
      { rewrite NO_COST_ANALYSIS time_zero //. }
    wp_pures.
    rewrite {1} isDeque_unfold.
    iDestruct "Hd" as "[[-> ->] | (%ℓ & -> & #Hℓ)]".
    - wp_pures.
      rewrite /asingleton. wp_pures.
      wp_apply bpush_spec as "%b #Hb".
        { iApply bempty_spec. }
      wp_pures.
      wp_bind (ref _)%E.
      wp_apply (csref_alloc (fiveTuple (⋅x))) as "%ℓ #Hℓ".
      + rewrite app_nil_r. by iApply (singleton_deque_better).
      + wp_pures.
        iApply "Hψ".
        iFrame.
        ℓisDeque ℓ. iModIntro. rewrite !app_nil_r //.
    - wp_pures.
      wp_apply (csref_load (fiveTuple _)) as "%d #πd".
        { iFrame. iExact "Hℓ". }
      iCombine "πd πd" as "[_ Hv]".
      iDestruct "πd" as "
        (%pr & %ld & %md & %rd & %sf & %prC & %ldC & %mdC & %rdC & %sfC
            & %kPr & %kMd & %kSf & %ltr & %rtr & -> & %cfg
            & #Hpr & #Hld & #Hmd & #Hrd & #Hsf & #Hltr & #Hrtr & %Heq)".
      wp_pures.
      wp_bind (if: _ then _ else _)%E.
      wp_apply (bis_empty_spec with "Hmd") as "_".
      wp_pures.
      destruct (bool_decide (kMd = 0)) eqn:?.
      + apply bool_decide_eq_true_1 in Heqb as Heqmd.
        wp_pures.
        wp_bind (if: _ then _ else _)%E.
        wp_apply (bhas_length_8_spec with "Hsf") as "_".
        wp_pures.
        destruct (bool_decide (kSf = 8)) eqn:?.
        * apply bool_decide_eq_true_1 in Heqb0 as ->.
          inversion cfg; invert_all_in; destruct ldC; inversion H; destruct rdC; inversion H1.
          iDestruct (big_sepL2_nil_inv_l with "Hltr") as "->".
          iDestruct (big_sepL2_nil_inv_l with "Hrtr") as "->".
          iDestruct (buffer_length with "Hpr") as "%HlprC". destruct prC; [| inversion HlprC].
          iDestruct (buffer_length with "Hmd") as "%HlmdC". destruct mdC; [| inversion HlmdC].
          wp_pures.
          wp_apply (bsplit8_spec with "Hsf") as "%b1 %b2 %b3 %o1 %o2 %o3 (#Hb1 & #Hb2 & #Hb3 & %H123)".
          wp_pures.
          wp_bind (#ℓ <- _)%E.
          wp_apply (csref_store).
          {
            iSplit. iExact "Hℓ".
            iExists b1, ld, b2, rd, b3,
              o1, [], o2, [], o3,
              3, 2, 3, [], [].
            iFrame. iFrame "#".
            doneL.
            iSplitR. by easy_config.
            do 2 doneL.
            inversion cfg; [| exfalso; lia].
            iPureIntro.
            rewrite Heq //=.
          }
          iIntros (unit).
          wp_pures; clear unit.
          wp_bind (bpush _ _)%E.
          wp_apply (bpush_spec with "Hb1") as "%pr'' #Hpr''".
          rewrite /assemble_.
          wp_pures.
          wp_bind (ref _)%E.
          wp_apply (csref_alloc (fiveTuple (⋅x ++ oD))) as "%ℓ' #Hℓ'".
          -- iExists pr'', ld, b2, rd, b3,
              (⋅x ++ o1), [], o2, [], o3,
              4, 2, 3, [], [].
            iFrame. iFrame "#".
            doneL.
            iSplitR. by easy_config.
            do 2 doneL.
            inversion cfg; [| exfalso; lia].
            iPureIntro.
            rewrite Heq H123 //=.
          -- wp_pures.
            iApply "Hψ".
            iFrame.
            ℓisDeque ℓ'.
            iExact "Hℓ'".
        * wp_pures.
          apply bool_decide_eq_false_1 in Heqb0.
          wp_bind (#ℓ <- _)%E.
          wp_apply (csref_store).
          {
            iSplit. iExact "Hℓ".
            iFrame.
            iApply (laterInFiveTuple with "Hv").
          }
          iIntros (unit).
          wp_pures; clear unit.
          rewrite /assemble_.
          wp_apply (bpush_spec with "Hsf") as "%sf' #Hsf'".
          wp_pures.
          wp_apply (csref_alloc (fiveTuple (⋅x ++ oD))) as "%ℓ' #Hℓ'".
          -- iExists bempty, empty, bempty, empty, sf',
              [], [], [], [], (⋅x ++ sfC),
              0, 0, (S kSf), [], [].
            inversion cfg; [| exfalso; lia ].
            iDestruct (buffer_length with "Hpr") as "%HlprC". destruct prC; [| inversion HlprC].
            iDestruct (buffer_length with "Hmd") as "%HlmdC". destruct mdC; [| inversion HlmdC].
            symmetry in H; rewrite (nil_length_inv _ H) in Heq |- *.
            symmetry in H1; rewrite (nil_length_inv _ H1) in Heq |- *.
            iDestruct (big_sepL2_nil_inv_l with "Hltr") as "->".
            iDestruct (big_sepL2_nil_inv_l with "Hrtr") as "->".
            iFrame.
            doneL.
            iSplitR; [ iPureIntro; constructor; invert_all_in; list_elem_of |].
            iSplitR. by iApply bempty_spec.
            iSplitR. by isEmptyDeque.
            iSplitR. by iApply bempty_spec.
            iSplitR. by isEmptyDeque.
            assert (S kSf = kSf + 1) as -> by lia.
            doneL.
            aac_normalise in Heq.
            rewrite Heq.
            repeat doneL.
            iPureIntro; simpl; aac_reflexivity.
          -- wp_pures.
            iApply "Hψ".
            iFrame.
            ℓisDeque ℓ'.
            iExact "Hℓ'".
      + apply bool_decide_eq_false_1 in Heqb as Heqmd.
        wp_pures.
        wp_apply (bhas_length_6_spec with "Hpr") as "_".
        wp_pures.
        destruct (bool_decide (kPr = 6)) eqn:?.
        * apply bool_decide_eq_true_1 in Heqb0 as ->.
          wp_pures.
          wp_apply (bsplit642_spec with "Hpr") as "%b1 %b2 %o1 %o2 (#Ho1 & #Ho2 & %Heq12)".
          rewrite /abuffer /atriple_.
          iSpecialize ("iH" $! (b2, NONEV, bempty)%V ld ltr).
          do 16 wp_pure.
          wp_smart_apply ("iH") as "%ld' #Hld'"; iClear "iH".
            by iFrame "#".
          wp_pures.
          wp_bind (#ℓ <- _)%E.
          inversion cfg.
          wp_apply csref_store.
          {
            iSplit. iExact "Hℓ".
            iExists b1, ld', md, rd, sf,
              o1, (⋅o2 ++ ldC), mdC, rdC, sfC,
              4, 2, kSf, (⋅(b2, NONEV, bempty)%V ++ ltr), rtr.
            iFrame "#".
            iSplitR. done.
            iSplitR. { iPureIntro; constructor; list_elem_of. }
            iSplitL.
              { iApply (big_sepL2_app with "[Hltr]").
                - iApply (big_sepL2_singleton).
                  iNext. rewrite triple_unfold.
                  iExists b2, NONEV, bempty,
                    o2, [], [],
                    2, 0, [].
                  iSplitR. { iPureIntro; eapply left_leaning; list_elem_of.  }
                  do 2 doneL.
                  iSplitR. isEmptyDeque.
                  iSplitR. iApply bempty_spec.
                  doneL.
                  iPureIntro; simpl; aac_reflexivity.
                - iApply (big_sepL2_mono with "Hltr").
                  by auto.
              }
            iSplitR. iApply (big_sepL2_mono with "Hrtr"). by auto.
            iPureIntro.
            rewrite Heq Heq12 /=.
            aac_reflexivity.
          }
          iIntros (unit).
          rewrite /assemble_.
          wp_pures; clear unit.
          wp_apply (bpush_spec with "Ho1") as "%pr3 #Hpr3".
          wp_pures.
          wp_apply (csref_alloc (fiveTuple (⋅x ++ oD))) as "%ℓ' #Hℓ'". {
            iExists pr3, ld', md, rd, sf,
              (⋅x ++ o1), (⋅o2 ++ ldC), mdC, rdC, sfC,
              5, 2, kSf, (⋅ (b2, NONEV, bempty)%V ++ ltr), rtr.
            iFrame "#".
            iSplitR. done.
            iSplitR. { iPureIntro; constructor; list_elem_of. }
            (* TODO(Juliette): factor out this proof *)
            iSplitL.
              { iApply (big_sepL2_app with "[Hltr]").
                - iApply (big_sepL2_singleton).
                  iNext. rewrite triple_unfold.
                  iExists b2, NONEV, bempty,
                    o2, [], [],
                    2, 0, [].
                  iSplitR. { iPureIntro; eapply left_leaning; list_elem_of.  }
                  do 2 doneL.
                  iSplitR. isEmptyDeque.
                  iSplitR. iApply bempty_spec.
                  doneL.
                  iPureIntro; simpl; aac_reflexivity.
                - iApply (big_sepL2_mono with "Hltr").
                  by auto.
              }
            iSplitR. iApply (big_sepL2_mono with "Hrtr"). by auto.
            iPureIntro.
            rewrite Heq Heq12 /=.
            aac_reflexivity.
          }
          wp_pures.
          iApply "Hψ".
          iFrame.
          ℓisDeque ℓ'. iExact "Hℓ'".
        * apply bool_decide_eq_false_1 in Heqb0 as prNotFull.
          wp_pures.
          wp_bind (#ℓ <- _)%E.
          wp_apply csref_store.
          {
            iSplit. iExact "Hℓ".
            iFrame. by iApply (laterInFiveTuple with "Hv").
          }
          iIntros (unit).
          wp_pures; clear unit.
          wp_apply (bpush_spec with "Hpr") as "%pr' #Hpr'".
          rewrite /assemble_.
          wp_pures.
          wp_bind (ref _)%E.
          wp_apply (csref_alloc (fiveTuple (⋅x ++ oD))) as "%ℓ' #Hℓ'".
          -- iExists pr', ld, md, rd, sf,
              (⋅x ++ prC), ldC, mdC, rdC ,sfC,
              (S kPr), kMd, kSf, ltr, rtr.
            inversion cfg; [ exfalso; lia |].
            assert (S kPr = kPr + 1) as -> by lia.
            iFrame "#".
            iSplitR. done.
            iSplitR. { iPureIntro; constructor; invert_all_in; list_elem_of. }
            iSplitR. iApply (big_sepL2_mono with "Hltr"). by auto.
            iSplitR. iApply (big_sepL2_mono with "Hrtr"). by auto.
            iPureIntro; rewrite Heq; aac_reflexivity.
          -- wp_pures.
            iApply "Hψ".
            iFrame.
            ℓisDeque ℓ'.
            iExact "Hℓ'".
  Qed.

  Theorem push_spec oD (x : val) (d : val) :
    {{{ IsDeque oD d }}}
      push x d
    {{{ d', RET d'; IsDeque (⋅x ++ oD) d' }}}.
  Proof.
    iIntros (ψ) "HD Hψ".
    rewrite /IsDeque.
    wp_apply (push_spec_helper with "[HD]") as "%d' HD'".
      { iFrame. }
    by iApply "Hψ".
  Qed.

End proof.
