From iris.heap_lang Require Import lang proofmode notation.
From iris.bi Require Import derived_laws.

From Coq Require Import List.
Import ListNotations.

From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Deque Require Import common tick shared_ref deque_cost.

Section proof.

  Context `{!heapGS Σ} `{!na_invG Σ}.
  Context {π : gname}.

  Lemma push_spec_helper oD x d : forall depth,
    {{{ isDeque π depth oD d ∗ ⏱ time_for_push ∗ Token π depth }}}
      push x d
    {{{ d', RET d'; isDeque π depth (⋅x ++ oD) d' ∗ Token π depth }}}.
  Proof.
    iLöb as "iH" forall (x d oD).
    iIntros (depth ψ) "(Hd & τ & O) Hψ".
    rewrite /push.
    iDestruct (split_time 1 with "τ") as "[ι τ]". by auto with arith.
    wp_pures.
    wp_apply (tick_spec with "ι") as "_".
    wp_pures.
    rewrite {1} isDeque_unfold.
    iDestruct "Hd" as "[[-> ->] | (%ℓ & -> & #Hℓ)]".
    - wp_pures.
      rewrite /asingleton. wp_pures.
      wp_apply bpush_spec as "%b #Hb".
        { iApply bempty_spec. }
      wp_pures.
      wp_bind (ref _)%E.
      wp_apply (ssref_alloc π (fiveTuple _ depth (⋅x))) as "%ℓ #Hℓ".
      + rewrite app_nil_r. by iApply (singleton_deque_better).
      + wp_pures.
        iApply "Hψ".
        iFrame.
        ℓisDeque ℓ. iModIntro. rewrite !app_nil_r //.
    - wp_pures.
      wp_apply (ssref_load_open with "[O]") as "%d (O & πd & DONE)".
        { iFrame. iExact "Hℓ". }
      iDestruct (persist_structure with "πd") as "[#Hv
        (%pr & %ld & %md & %rd & %sf & %prC & %ldC & %mdC & %rdC & %sfC
            & %kPr & %kMd & %kSf & %ltr & %rtr & -> & %cfg & pot
            & #Hpr & #Hld & #Hmd & #Hrd & #Hsf & #Hltr & #Hrtr & %Heq)]".
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
          iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
          iApply (wp_wand with "[DONE ι O]").
          {
            iApply ("DONE" with "[ι]"); [| by iFrame].
            iNext.
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
          iIntros (unit) "O".
          wp_pures; clear unit.
          wp_bind (bpush _ _)%E.
          wp_apply (bpush_spec with "Hb1") as "%pr'' #Hpr''".
          rewrite /assemble_.
          wp_pures.
          wp_bind (ref _)%E.
          iDestruct (split_time 1 with "τ") as "[ι τ]". by lia.
          wp_apply (ssref_alloc π (fiveTuple _ depth (⋅x ++ oD)) with "[ι]") as "%ℓ' #Hℓ'".
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
          iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
          iApply (wp_wand with "[DONE ι O]").
          {
            iApply ("DONE" with "[ι]"); [| iFrame].
            iNext.
            iApply (strutcure_and_time with "[ι]").
            iFrame.
            iApply (laterInFiveTuple with "Hv").
          }
          iIntros (unit) "O".
          wp_pures; clear unit.
          rewrite /assemble_.
          wp_apply (bpush_spec with "Hsf") as "%sf' #Hsf'".
          wp_pures.
          iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
          wp_apply (ssref_alloc π (fiveTuple _ depth (⋅x ++ oD)) with "[ι]") as "%ℓ' #Hℓ'".
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
            iSplitL; [ iApply (three_time_enough with "ι") |].
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
          iSpecialize ("iH" $! (b2, NONEV, bempty)%V ld ltr (S depth)).
          iDestruct (time_combine with "[τ pot]") as "τ". by (rewrite /=; iFrame).
          iDestruct (split_time time_for_push with "τ") as "[ι τ]".
            { destruct (buffer_colour kSf); rewrite /=; auto. }
          do 16 wp_pure.
          wp_smart_apply ("iH" with "[ι O]") as "%ld' [#Hld' O]"; iClear "iH". {
            iFrame "#".
            (* rewrite /isElement triple_unfold !app_nil_r. *)
            by iFrame.
          }
          wp_pures.
          wp_bind (#ℓ <- _)%E.
          inversion cfg.
          iDestruct (split_time (4 ⋄ kSf) with "τ") as "[ι τ]".
            { invert_all_in; rewrite //=; auto. }
          iApply (wp_wand with "[DONE ι O]").
          {
            iApply ("DONE" with "[ι]"); [| iFrame].
            iNext.
            iExists b1, ld', md, rd, sf,
              o1, (⋅o2 ++ ldC), mdC, rdC, sfC,
              4, 2, kSf, (⋅(b2, NONEV, bempty)%V ++ ltr), rtr.
            iFrame "#".
            iSplitR. done.
            iSplitR. { iPureIntro; constructor; list_elem_of. }
            iSplitL.
              { rewrite {2}/five_tuple_potential.
                invert_all_in; rewrite //=; auto.
              }
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
          iIntros (unit) "O".
          rewrite /assemble_.
          wp_pures; clear unit.
          wp_apply (bpush_spec with "Ho1") as "%pr3 #Hpr3".
          wp_pures.
          iDestruct (split_time (5 ⋄ kSf) with "τ") as "[ι τ]".
            { invert_all_in; rewrite //=; auto. }
          wp_apply (ssref_alloc π (fiveTuple _ depth (⋅x ++ oD)) with "[ι]") as "%ℓ' #Hℓ'". {
            iExists pr3, ld', md, rd, sf,
              (⋅x ++ o1), (⋅o2 ++ ldC), mdC, rdC, sfC,
              5, 2, kSf, (⋅ (b2, NONEV, bempty)%V ++ ltr), rtr.
            iFrame "#".
            iSplitR. done.
            iSplitR. { iPureIntro; constructor; list_elem_of. }
            iSplitL.
              { rewrite {2}/five_tuple_potential.
                invert_all_in; rewrite //=; auto.
              }
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
          iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
          iApply (wp_wand with "[DONE ι O]").
          {
            iApply ("DONE" with "[ι]"); [| iFrame].
            iNext.
            iApply (strutcure_and_time with "[ι]").
            iFrame. by iApply (laterInFiveTuple with "Hv").
          }
          iIntros (unit) "O".
          wp_pures; clear unit.
          wp_apply (bpush_spec with "Hpr") as "%pr' #Hpr'".
          rewrite /assemble_.
          wp_pures.
          wp_bind (ref _)%E.
          iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
          wp_apply (ssref_alloc π (fiveTuple _ depth (⋅x ++ oD)) with "[ι]") as "%ℓ' #Hℓ'".
          -- iExists pr', ld, md, rd, sf,
              (⋅x ++ prC), ldC, mdC, rdC ,sfC,
              (S kPr), kMd, kSf, ltr, rtr.
            inversion cfg; [ exfalso; lia |].
            assert (S kPr = kPr + 1) as -> by lia.
            iFrame "#".
            iSplitR. done.
            iSplitR. { iPureIntro; constructor; invert_all_in; list_elem_of. }
            iSplitL. by iApply (three_time_enough with "ι").
            iSplitR. iApply (big_sepL2_mono with "Hltr"). by auto.
            iSplitR. iApply (big_sepL2_mono with "Hrtr"). by auto.
            iPureIntro; rewrite Heq; aac_reflexivity.
          -- wp_pures.
            iApply "Hψ".
            iFrame.
            ℓisDeque ℓ'.
            iExact "Hℓ'".
  Unshelve. all: by auto.
  Qed.

  Theorem push_spec oD (x : val) (d : val) :
    {{{ IsDeque π oD d ∗ ⏱ time_for_push ∗ Token π 0 }}}
      push x d
    {{{ d', RET d'; IsDeque π (⋅x ++ oD) d' ∗ Token π 0 }}}.
  Proof.
    iIntros (ψ) "(HD & τ & O) Hψ".
    rewrite /IsDeque.
    wp_apply (push_spec_helper with "[HD τ O]") as "%d' HD'".
      { iFrame. }
    by iApply "Hψ".
  Qed.

  Corollary inject_spec_helper oD x d : forall depth,
    {{{ isDeque π depth oD d ∗ ⏱ time_for_push ∗ Token π depth }}}
      inject d x
    {{{ d', RET d'; isDeque π depth (oD ++ ⋅x) d' ∗ Token π depth }}}.
 Admitted.

  Corollary inject_spec oD (x : val) (d : val) :
    {{{ IsDeque π oD d ∗ ⏱ time_for_push ∗ Token π 0 }}}
      inject d x
    {{{ d', RET d'; IsDeque π (oD ++ ⋅x) d' ∗ Token π 0 }}}.
  Admitted.

  (*
  (* NOTE(Juliette): Marked as 0 time cost, but runs in ⏱ (8 * time_for_push) constant time *)
  Corollary push_whole_spec : forall lvl b oB d oD size,
    {{{ buffer size oB b ∗ isDeque π lvl oD d ∗ Token π lvl }}}
      push_whole_buffer push b d
    {{{ d', RET d'; isDeque π lvl (oB ++ oD) d' ∗ Token π lvl }}}.
  Admitted.

  (* NOTE(Juliette): Marked as 0 time cost, but runs in ⏱ (8 * time_for_push) constant time *)
  Corollary binject_whole_spec : forall b oB d oD size size',
    {{{ buffer size oB b ∗ buffer size' oD d }}}
      inject_whole_buffer binject d b
    {{{ d', RET d'; buffer (size+size') (oD ++ oB) d' }}}.
  Admitted.

  (* TODO: move me *)
  Property inject_whole_spec : forall lvl b oB d oD size,
    {{{ buffer size oB b ∗ isDeque π lvl oD d ∗ Token π lvl }}}
      inject_whole_buffer inject d b
    {{{ d', RET d'; isDeque π lvl (oD ++ oB) d' ∗ Token π lvl }}}.
  Admitted.
  *)

End proof.
