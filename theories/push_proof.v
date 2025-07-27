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
  Variable π : gname.

  Lemma push_spec_helper oD x d : forall depth,
    {{{ isDeque π depth oD d ∗ ⏱ time_for_push ∗ Token π depth }}}
      push x d
    {{{ d', RET d'; isDeque π depth (⋅x ++ oD) d' ∗ Token π depth }}}.
  Proof.
  (*
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
      rewrite /singleton_deque. wp_pures.
      wp_apply bpush_spec as "%b #Hb".
        { iApply empty_is_buffer. }
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
      wp_apply (bsize_better_spec with "Hmd") as "_".
      wp_pures.
      destruct (bool_decide (kMd = 0)) eqn:?.
      + apply bool_decide_eq_true_1 in Heqb as Heqmd.
        apply bool_decide_code_true in Heqb as ->.
        wp_pures.
        wp_bind (if: _ then _ else _)%E.
        wp_apply (bsize_better_spec with "Hsf") as "_".
        wp_pures.
        destruct (bool_decide (kSf = 8)) eqn:?.
        * apply bool_decide_eq_true_1 in Heqb as ->.
          wp_pures.
          wp_apply (bpop_spec2 with "Hsf") as "%x1 %b1 %o1 (Hsf' & ->)".
          wp_pures.
          wp_apply (bpop_spec2 with "Hsf'") as "%x2 %b2 %o2 (Hsf' & ->)".
          wp_pures.
          wp_apply (bpop_spec2 with "Hsf'") as "%x3 %b3 %o3 (Hsf' & ->)".
          wp_pures.
          wp_apply (bpush_spec2) as "%bp3 Hbp".
            { by iApply empty_is_buffer_at. }
          wp_apply (bpush_spec2 with "Hbp") as "%bp2 Hbp".
          wp_apply (bpush_spec2 with "Hbp") as "%pr' #Hpr'".
          wp_pures.
          wp_apply (bpop_spec2 with "Hsf'") as "%x4 %b4 %o4 (Hsf' & ->)".
          wp_pures.
          wp_apply (bpop_spec2 with "Hsf'") as "%x5 %sf' %o5 (#Hsf' & ->)".
          wp_pures.
          wp_apply (bpush_spec2) as "%bp5 Hbm".
            { by iApply empty_is_buffer_at. }
          wp_apply (bpush_spec2 with "Hbm") as "%md' #Hmd'".
          wp_pures.
          rewrite !app_nil_r Heqmd.
          wp_bind (#ℓ <- _)%E.
          iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
          iApply (wp_wand with "[DONE ι O]").
          {
            iApply ("DONE" with "[ι]"); [| by iFrame].
            iNext.
            iExists pr', empty, md', empty, sf',
              (⋅x1 ++ ⋅x2 ++ ⋅x3), [], (⋅x4 ++ ⋅x5), [], o5,
              3, 2, 3, [], [].
            iFrame. iFrame "#".
            doneL.
            iSplitR. by easy_config.
            iSplitR. by isEmptyDeque.
            iSplitR. by isEmptyDeque.
            do 2 doneL.
            inversion cfg; [| exfalso; lia].
            iDestruct (empty_buffer_is_empty with "Hpr") as "->".
            iDestruct (empty_buffer_is_empty with "Hmd") as "->".
            destruct ldC; inversion H.
            destruct rdC; inversion H1.
            iPureIntro.
            rewrite Heq //.
          }
          iIntros (unit) "O".
          wp_pures; clear unit.
          wp_bind (bpush _ _)%E.
          wp_apply (bpush_spec2 with "Hpr'") as "%pr'' #Hpr''".
          wp_pures.
          wp_bind (ref _)%E.
          iDestruct (split_time 1 with "τ") as "[ι τ]". by lia.
          wp_apply (ssref_alloc π (fiveTuple _ depth (⋅x ++ oD)) with "[ι]") as "%ℓ' #Hℓ'".
          -- iExists pr'', empty, md', empty, sf',
              (⋅x ++ ⋅x1 ++ ⋅x2 ++ ⋅x3), [], (⋅x4 ++ ⋅x5), [], o5,
              4, 2, 3, [], [].
            iFrame. iFrame "#".
            doneL.
            iSplitR. by easy_config.
            iSplitR. by isEmptyDeque.
            iSplitR. by isEmptyDeque.
            do 2 doneL.
            inversion cfg; [| exfalso; lia].
            iDestruct (empty_buffer_is_empty with "Hpr") as "->".
            iDestruct (empty_buffer_is_empty with "Hmd") as "->".
            destruct ldC; inversion H.
            destruct rdC; inversion H1.
            iPureIntro.
            rewrite Heq //.
          -- wp_pures.
            iApply "Hψ".
            iFrame.
            ℓisDeque ℓ'.
            iExact "Hℓ'".
        * apply bool_decide_eq_false_1 in Heqb as sfNotFull.
          apply bool_decide_code_false in Heqb as ->.
          wp_pures.
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
          wp_apply (bpush_spec2 with "Hsf") as "%sf' #Hsf'".
          wp_pures.
          iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
          wp_apply (ssref_alloc π (fiveTuple _ depth (⋅x ++ oD)) with "[ι]") as "%ℓ' #Hℓ'".
          -- iExists pr, ld, md, rd, sf',
              [], [], [], [], (⋅x ++ oD),
              0, 0, (S kSf), [], [].
            inversion cfg; [| exfalso; lia ].
            iDestruct (empty_buffer_is_empty with "Hpr") as "->".
            iDestruct (empty_buffer_is_empty with "Hmd") as "->".
            symmetry in H; rewrite (nil_length_inv _ H) in Heq |- *.
            symmetry in H1; rewrite (nil_length_inv _ H1) in Heq |- *.
            iDestruct (big_sepL2_nil_inv_l with "Hltr") as "->".
            iDestruct (big_sepL2_nil_inv_l with "Hrtr") as "->".
            iFrame.
            doneL.
            iSplitR; [ iPureIntro; constructor; invert_all_in |].
            iSplitL; [ iApply (three_time_enough with "ι") |].
            doneL.
            aac_normalise in Heq.
            rewrite Heq.
            do 6 doneL.
            iPureIntro; simpl; aac_reflexivity.
          -- wp_pures.
            iApply "Hψ".
            iFrame.
            ℓisDeque ℓ'.
            iExact "Hℓ'".
      + apply bool_decide_eq_false_1 in Heqb as Heqmd.
        apply bool_decide_code_false in Heqb as Heqmd2.
        rewrite Heqmd2.
        wp_pures.
        wp_apply (bsize_better_spec with "Hpr") as "_".
        wp_pures.
        destruct (bool_decide (kPr = 6)) eqn:?.
        * apply bool_decide_eq_true_1 in Heqb0 as ->.
          wp_pures.
          wp_apply (beject_spec2 with "Hpr") as "%b6 %x6 %o6 (Hpr' & ->)".
          wp_pures.
          wp_apply (beject_spec2 with "Hpr'") as "%pr2 %x5 %o5 (#Hpr2 & ->)".
          wp_pures.
          wp_apply (bpush_spec2) as "%bs6 Hbp".
            { by iApply empty_is_buffer_at. }
          wp_apply (bpush_spec2 with "Hbp") as "%pr' #Hpr'".
          do 4 wp_pure.
          iSpecialize ("iH" $! (pr', NONEV, empty_buffer)%V ld ltr (S depth)).
          iDestruct (time_combine with "[τ pot]") as "τ". by (rewrite /=; iFrame).
          iDestruct (split_time time_for_push with "τ") as "[ι τ]".
            { destruct (buffer_colour kSf); rewrite /=; auto. }
          wp_apply ("iH" with "[ι O]") as "%ld' [#Hld' O]"; iClear "iH". {
            iFrame "#".
            (* rewrite /isElement triple_unfold !app_nil_r. *)
            iFrame.
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
            iExists pr2, ld', md, rd, sf,
              o5, ([⋅x5 ++ ⋅x6] ++ ldC), mdC, rdC, sfC,
              4, 2, kSf, (⋅(pr', NONEV, empty_buffer)%V ++ ltr), rtr.
            rewrite !app_nil_r.
            iFrame "#".
            iSplitR. done.
            iSplitR. { iPureIntro; constructor; auto with find_in_list. }
            iSplitL.
              { rewrite {2}/five_tuple_potential.
                invert_all_in; rewrite //=; auto.
              }
            iSplitL.
              { iApply (big_sepL2_app with "[Hltr]").
                - iApply (big_sepL2_singleton).
                  iNext. rewrite triple_unfold.
                  iExists pr', NONEV, empty_buffer,
                    (⋅x5 ++ ⋅x6), [], [],
                    2, 0, [].
                  iSplitR. { iPureIntro; eapply left_leaning; auto with find_in_list.  }
                  do 2 doneL.
                  iSplitR. isEmptyDeque.
                  iSplitR. iApply empty_is_buffer_at.
                  doneL.
                  iPureIntro; simpl; aac_reflexivity.
                - iApply (big_sepL2_mono with "Hltr").
                  by auto.
              }
            iSplitR. iApply (big_sepL2_mono with "Hrtr"). by auto.
            iPureIntro.
            rewrite Heq /= !cons_middle.
            aac_reflexivity.
          }
          iIntros (unit) "O".
          wp_pures; clear unit.
          wp_apply (bpush_spec2 with "Hpr2") as "%pr3 #Hpr3".
          wp_pures.
          iDestruct (split_time (5 ⋄ kSf) with "τ") as "[ι τ]".
            { invert_all_in; rewrite //=; auto. }
          wp_apply (ssref_alloc π (fiveTuple _ depth (⋅x ++ oD)) with "[ι]") as "%ℓ' #Hℓ'". {
            iExists pr3, ld', md, rd, sf,
              (⋅x ++ o5), ([⋅x5 ++ ⋅x6] ++ ldC), mdC, rdC, sfC,
              5, 2, kSf, (⋅ (pr', NONEV, empty_buffer)%V ++ ltr), rtr.
            iFrame "#".
            iSplitR. done.
            iSplitR. { iPureIntro; constructor; auto with find_in_list. }
            iSplitL.
              { rewrite {2}/five_tuple_potential.
                invert_all_in; rewrite //=; auto.
              }
            (* TODO(Juliette): factor out this proof *)
            iSplitL.
              { iApply (big_sepL2_app with "[Hltr]").
                - iApply (big_sepL2_singleton).
                  iNext. rewrite triple_unfold.
                  iExists pr', NONEV, empty_buffer,
                    (⋅x5 ++ ⋅x6), [], [],
                    2, 0, [].
                  iSplitR. { iPureIntro; eapply left_leaning; auto with find_in_list.  }
                  do 2 doneL.
                  iSplitR. isEmptyDeque.
                  iSplitR. iApply empty_is_buffer_at.
                  doneL.
                  iPureIntro; simpl; aac_reflexivity.
                - iApply (big_sepL2_mono with "Hltr").
                  by auto.
              }
            iSplitR. iApply (big_sepL2_mono with "Hrtr"). by auto.
            iPureIntro.
            rewrite Heq /= !cons_middle.
            aac_reflexivity.
          }
          wp_pures.
          iApply "Hψ".
          iFrame.
          ℓisDeque ℓ'. iExact "Hℓ'".
        * apply bool_decide_eq_false_1 in Heqb0 as prNotFull.
          apply bool_decide_code_false in Heqb0 as ->.
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
          wp_apply (bpush_spec2 with "Hpr") as "%pr' #Hpr'".
          wp_pures.
          wp_bind (ref _)%E.
          iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
          wp_apply (ssref_alloc π (fiveTuple _ depth (⋅x ++ oD)) with "[ι]") as "%ℓ' #Hℓ'".
          -- iExists pr', ld, md, rd, sf,
              (⋅x ++ prC), ldC, mdC, rdC ,sfC,
              (S kPr), kMd, kSf, ltr, rtr.
            inversion cfg; [ exfalso; lia |].
            iFrame "#".
            iSplitR. done.
            iSplitR. { iPureIntro; constructor; [invert_all_in | auto with find_in_list]. }
            iSplitL. by iApply (three_time_enough with "ι").
            iSplitR. iApply (big_sepL2_mono with "Hltr"). by auto.
            iSplitR. iApply (big_sepL2_mono with "Hrtr"). by auto.
            iPureIntro; rewrite Heq; aac_reflexivity.
          -- wp_pures.
            iApply "Hψ".
            iFrame.
            ℓisDeque ℓ'.
            iExact "Hℓ'".
  Qed.
  *)
  Admitted.

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

End proof.
