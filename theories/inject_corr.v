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

  Lemma inject_spec_helper oD x d :
    {{{ isDeque oD d }}}
      inject d x
    {{{ d', RET d'; isDeque (oD ++ ⋅x) d' }}}.
  Proof.
    iLöb as "iH" forall (x d oD).
    iIntros (ψ) "Hd Hψ".
    rewrite /inject.
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
          wp_apply csref_store.
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
          wp_bind (binject _ _)%E.
          wp_apply (binject_spec with "Hb3") as "%sf'' #Hsf''".
          rewrite /assemble_.
          wp_pures.
          wp_bind (ref _)%E.
          wp_apply (csref_alloc (fiveTuple (oD++⋅x))) as "%ℓ' #Hℓ'".
          -- iExists b1, ld, b2, rd, sf'',
              o1, [], o2, [], (o3++⋅x),
              3, 2, 4, [], [].
            iFrame. iFrame "#".
            doneL.
            iSplitR. by easy_config.
            do 2 doneL.
            inversion cfg; [| exfalso; lia].
            iPureIntro.
            rewrite Heq H123 //=.
            aac_reflexivity.
          -- wp_pures.
            iApply "Hψ".
            iFrame.
            ℓisDeque ℓ'.
            iExact "Hℓ'".
        * wp_pures.
          apply bool_decide_eq_false_1 in Heqb0.
          wp_bind (#ℓ <- _)%E.
          wp_apply (csref_store (fiveTuple _)).
          {
            iSplit. iExact "Hℓ".
            iApply (laterInFiveTuple with "Hv").
          }
          iIntros (unit).
          wp_pures; clear unit.
          rewrite /assemble_.
          wp_apply (binject_spec with "Hsf") as "%sf' #Hsf'".
          wp_pures.
          wp_apply (csref_alloc (fiveTuple (oD++⋅x))) as "%ℓ' #Hℓ'".
          -- iExists bempty, empty, bempty, empty, sf',
              [], [], [], [], (sfC++⋅x),
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
        wp_apply (bhas_length_6_spec with "Hsf") as "_".
        wp_pures.
        destruct (bool_decide (kSf = 6)) eqn:?.
        * apply bool_decide_eq_true_1 in Heqb0 as ->.
          wp_pures.
          wp_apply (bsplit624_spec with "Hsf") as "%b1 %b2 %o1 %o2 (#Ho1 & #Ho2 & %Heq12)".
          rewrite /abuffer /atriple_.
          iSpecialize ("iH" $! (b1, NONEV, bempty)%V rd rtr).
          do 16 wp_pure.
          wp_smart_apply ("iH") as "%ld' #Hld'"; iClear "iH". by iFrame "#".
          wp_pures.
          wp_bind (#ℓ <- _)%E.
          inversion cfg. lia.
          wp_apply (csref_store (fiveTuple _)).
          {
            iSplit. iExact "Hℓ".
            iExists pr, ld, md, ld', b2,
              prC, ldC, mdC, (rdC++⋅o1), o2,
              kPr, 2, 4, ltr, (rtr++⋅(b1, NONEV, bempty)%V).
            iFrame "#".
            iSplitR. done.
            iSplitR. { iPureIntro; constructor; list_elem_of. }
            iSplitR. iApply (big_sepL2_mono with "Hltr"). by auto.
            iSplitL.
              { iApply (big_sepL2_app with "[Hrtr]").
                - iApply (big_sepL2_mono with "Hrtr").
                  by auto.
                - iApply (big_sepL2_singleton).
                  iNext. rewrite triple_unfold.
                  iExists b1, NONEV, bempty,
                    o1, [], [],
                    2, 0, [].
                  iSplitR. { iPureIntro; eapply left_leaning; list_elem_of.  }
                  do 2 doneL.
                  iSplitR. isEmptyDeque.
                  iSplitR. iApply bempty_spec.
                  doneL.
                  iPureIntro; simpl; aac_reflexivity.
              }
            iPureIntro.
            rewrite Heq Heq12 /= concat_app /=.
            aac_reflexivity.
          }
          iIntros (unit).
          rewrite /assemble_.
          wp_pures; clear unit.
          wp_apply (binject_spec with "Ho2") as "%pr3 #Hpr3".
          wp_pures.
          wp_apply (csref_alloc (fiveTuple (oD++⋅x))) as "%ℓ' #Hℓ'". {
            iExists pr, ld, md, ld', pr3,
              prC, ldC, mdC, (rdC++⋅o1), (o2++⋅x),
              kPr, 2, 5, ltr, (rtr ++ ⋅ (b1, NONEV, bempty)%V).
            iFrame "#".
            iSplitR. done.
            iSplitR. { iPureIntro; constructor; list_elem_of. }
            iSplitR. iApply (big_sepL2_mono with "Hltr"). by auto.
            iSplitL.
              { iApply (big_sepL2_app with "[Hrtr]").
                - iApply (big_sepL2_mono with "Hrtr").
                  by auto.
                - iApply (big_sepL2_singleton).
                  iNext. rewrite triple_unfold.
                  iExists b1, NONEV, bempty,
                    o1, [], [],
                    2, 0, [].
                  iSplitR. { iPureIntro; eapply left_leaning; list_elem_of.  }
                  do 2 doneL.
                  iSplitR. isEmptyDeque.
                  iSplitR. iApply bempty_spec.
                  doneL.
                  iPureIntro; simpl; aac_reflexivity.
              }
            iPureIntro.
            rewrite Heq Heq12 /= concat_app /=.
            aac_reflexivity.
          }
          wp_pures.
          iApply "Hψ".
          iFrame.
          ℓisDeque ℓ'. iExact "Hℓ'".
        * apply bool_decide_eq_false_1 in Heqb0 as prNotFull.
          wp_pures.
          wp_bind (#ℓ <- _)%E.
          wp_apply (csref_store (fiveTuple _)).
          {
            iSplit. iExact "Hℓ".
            iFrame. by iApply (laterInFiveTuple with "Hv").
          }
          iIntros (unit).
          wp_pures; clear unit.
          wp_apply (binject_spec with "Hsf") as "%sf' #Hsf'".
          rewrite /assemble_.
          wp_pures.
          wp_bind (ref _)%E.
          wp_apply (csref_alloc (fiveTuple (oD++⋅x))) as "%ℓ' #Hℓ'".
          -- iExists pr, ld, md, rd, sf',
              prC, ldC, mdC, rdC, (sfC++⋅x),
              kPr, kMd, (S kSf), ltr, rtr.
            inversion cfg; [ exfalso; lia |].
            assert (S kSf = kSf + 1) as -> by lia.
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

  Theorem inject_spec oD (x : val) (d : val) :
    {{{ IsDeque oD d }}}
      inject d x
    {{{ d', RET d'; IsDeque (oD++⋅x) d' }}}.
  Proof.
    iIntros (ψ) "HD Hψ".
    rewrite /IsDeque.
    wp_apply (inject_spec_helper with "[HD]") as "%d' HD'".
      { iFrame. }
    by iApply "Hψ".
  Qed.

End proof.
