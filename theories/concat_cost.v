From iris.heap_lang Require Import lang proofmode notation.
From iris.bi Require Import derived_laws.

From Coq Require Import List.
Import ListNotations.

From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Deque Require Import common tick shared_ref deque_cost push_cost.

Section proof.

  Context `{!heapGS Σ} `{!na_invG Σ}.
  Context {π : gname}.

  Theorem dconcat_spec (d1 d2 : val) : forall o1 o2,
    {{{ IsDeque π o1 d1 ∗ IsDeque π o2 d2 ∗ ⏱ time_for_concat ∗ Token π 0 }}}
      dconcat d1 d2
    {{{ d', RET d'; IsDeque π (o1 ++ o2) d' ∗ Token π 0 }}}.
  Proof.
    iIntros (o1 o2 ψ) "(Hd1 & Hd2 & τ & O) Hψ".
    rewrite /dconcat /IsDeque.
    wp_pures.
    iDestruct (split_time 1 with "τ") as "[ι τ]". by lia.
    wp_apply (tick_spec with "ι") as "_".
    wp_pures.
    (* trivial cases *)
    rewrite {1} isDeque_unfold.
    iDestruct "Hd1" as "[[-> ->] | (%ℓ1 & -> & #Hℓ1)]".
    { wp_pures. iApply "Hψ". rewrite app_nil_l //. by iFrame. }
    rewrite {1} isDeque_unfold.
    iDestruct "Hd2" as "[[-> ->] | (%ℓ2 & -> & #Hℓ2)]".
    { wp_pures. iApply "Hψ". iFrame. ℓisDeque ℓ1. rewrite app_nil_r. iExact "Hℓ1". }
    wp_pures.
    wp_apply (ssref_read π _ (isPersFiveTuple _ _ _) with "[Hℓ1 O]") as "%v
      [(%pr1 & %ld1 & %md1 & %rd1 & %sf1 & %prC1 & %ldC1 & %mdC1 & %rdC1 & %sfC1
            & %kPr1 & %kMd1 & %kSf1 & %ltr1 & %rtr1 & -> & %cfg1
            & #Hpr1 & #Hld1 & #Hmd1 & #Hrd1 & #Hsf1 & #Hltr1 & #Hrtr1 & %Heq1)
      O]".
      { iFrame "#". iFrame.
        iIntros (v) "H".
        iApply (persist_structure with "H").
      }
    wp_pures.
    wp_apply (bsize_better_spec with "Hmd1") as "_".
    wp_pures.
    destruct (bool_decide (kMd1 = 0)) eqn:?.
    { (* d1 is suffix only *)
      apply bool_decide_eq_true_1 in Heqb as Heqmd.
      apply bool_decide_code_true in Heqb as ->.
      wp_pures.
      wp_apply (push_whole_spec with "[O]") as "%d' [#Hd' O]".
        { iSplitR. iExact "Hsf1". iFrame. ℓisDeque ℓ2. iExact "Hℓ2". }
      iApply "Hψ".
      iFrame.
      inversion cfg1; [| exfalso; lia].
      iDestruct (empty_buffer_is_empty with "Hpr1") as "->".
      iDestruct (empty_buffer_is_empty with "Hmd1") as "->".
      rewrite (nil_length_inv _ (eq_sym H)) in Heq1 |- *.
      rewrite (nil_length_inv _ (eq_sym H1)) in Heq1 |- *.
      aac_normalise in Heq1.
      rewrite Heq1 //.
      }
    apply bool_decide_eq_false_1 in Heqb as Heqmd1.
    apply bool_decide_code_false in Heqb as ->.
    wp_pures.
    wp_apply (ssref_read π _ (isPersFiveTuple _ _ _) with "[Hℓ2 O]") as "%v'
      [(%pr2 & %ld2 & %md2 & %rd2 & %sf2 & %prC2 & %ldC2 & %mdC2 & %rdC2 & %sfC2
            & %kPr2 & %kMd2 & %kSf2 & %ltr2 & %rtr2 & -> & %cfg2
            & #Hpr2 & #Hld2 & #Hmd2 & #Hrd2 & #Hsf2 & #Hltr2 & #Hrtr2 & %Heq2)
      O]".
      { iFrame "#". iFrame.
        iIntros (v) "H".
        iApply (persist_structure with "H").
      }
    wp_pures.
    wp_apply (bsize_better_spec with "Hmd2") as "_".
    wp_pures.
    destruct (bool_decide (kMd2 = 0)) eqn:?.
    { (* d2 is suffix only *)
      apply bool_decide_eq_true_1 in Heqb as Heqmd.
      apply bool_decide_code_true in Heqb as ->.
      wp_pures.
      wp_apply (inject_whole_spec with "[O]") as "%d' [#Hd' O]".
        { iSplitR. iExact "Hsf2". iFrame. ℓisDeque ℓ1. iExact "Hℓ1". }
      iApply "Hψ".
      iFrame.
      inversion cfg2; [| exfalso; by lia ].
      iDestruct (empty_buffer_is_empty with "Hpr2") as "->".
      iDestruct (empty_buffer_is_empty with "Hmd2") as "->".
      rewrite (nil_length_inv _ (eq_sym H)) in Heq2 |- *.
      rewrite (nil_length_inv _ (eq_sym H1)) in Heq2 |- *.
      aac_normalise in Heq2.
      rewrite Heq2 //.
    }
    apply bool_decide_eq_false_1 in Heqb as Heqmd2.
    apply bool_decide_code_false in Heqb as ->.
    wp_pures.
    inversion cfg1; [exfalso; by apply Heqmd2 |].
    inversion cfg2; [exfalso; by apply Heqmd2 |].
    change (kPr2 ∈ map S [2; 3; 4; 5]) in H6.
    apply decrease_in in H6 as (kPr2' & -> & HkPr2').
    wp_apply (bpop_spec2 with "Hpr2") as "%y %pr1' %oBY (Hpr2' & ->)".
    wp_pures.
    change (kSf1 ∈ map S [2; 3; 4; 5]) in H0.
    apply decrease_in in H0 as (kSf1' & -> & HkSf1').
    wp_apply (beject_spec2 with "Hsf1") as "%sf1' %x %oBX (Hsf1' & ->)".
    wp_pures.
    wp_apply (bpush_spec2) as "%bm Hbm".
      { by iApply empty_is_buffer_at. }
    wp_apply (bpush_spec2 with "Hbm") as "%md' #Hmd'".
    wp_pures.
    wp_apply (partition_buffer_left_better_spec with "[Hsf1']") as "%s1' %s1'' %os1' %os1'' %ks1' %ks1'' (#Hs1' & #Hs1'' & (%Hos1' & %Hos1'' & %Hos1eq))".
      { iFrame. iPureIntro. invert_all_in; list_elem_of. }
    wp_pures.
    iDestruct (na_own_acc _ _ _ (next_stage 0) with "O") as "[O A]".
    iDestruct (split_time time_for_push with "τ") as "[ι τ]". by lia.
    rewrite !app_nil_r.
    wp_apply (inject_spec_helper with "[Hld1 ι O]") as "%ld1' [#Hld1' O]".
      { iFrame "#". iFrame. }
    wp_pures.
    wp_bind (if: _ then _ else _)%E.
    iDestruct (split_time time_for_push with "τ") as "[ι τ]". by lia.
    iDestruct ("A" with "O") as "O".
    wp_apply (wp_strong_mono _ _ _ _ _
      (λ v, ∃ tr trC, isDeque _ 1 tr v ∗
        ⌜ List.concat trC = List.concat ldC1 ++ mdC1 ++ List.concat rdC1 ++ os1' ++ os1'' ⌝ ∗
        ([∗list] a;b ∈ trC; tr, ▷ triple π 1 a b) ∗
        Token π 0)%I
      with "[O ι]") as "%ld1'' (%tr1' & %trC1' & #Hld1'' & %HtrC1' & #trtrC1' & O)"; try done.
    {
     wp_apply (bsize_better_spec with "Hs1''") as "_".
      wp_pures.
      destruct (bool_decide (ks1'' = 0)) eqn:?.
      - apply bool_decide_eq_true_1 in Heqb as Heqs1.
        apply bool_decide_code_true in Heqb as ->.
        wp_pures.
        rewrite Heqs1.
        iDestruct (empty_buffer_is_empty with "Hs1''") as "->".
        rewrite !app_nil_r.
        iExists (ltr1 ++ ⋅(md1, rd1, s1')%V), (ldC1 ++ ⋅(mdC1 ++ List.concat rdC1 ++ os1')).
        iFrame "#". iFrame.
        iModIntro.
        iSplitL.
        + iPureIntro. rewrite !concat_app /= app_nil_r //.
        + iApply (big_sepL2_app with "[Hltr1]").
          * iApply (big_sepL2_mono with "Hltr1"). by auto.
          * simpl. doneR. iNext.
            rewrite triple_unfold.
            iExists md1, rd1, s1', mdC1, rdC1, os1', kMd1, ks1', rtr1.
            inversion cfg1; [ rewrite -H3 in H14; lia |].
            iSplitR. iPureIntro.
            destruct (length rdC1); [apply left_leaning | apply has_child];
              auto with arith; list_elem_of.
            iSplitR. done.
            iFrame "#".
            doneR.
            iApply (big_sepL2_mono with "Hrtr1"). by auto.
      - apply bool_decide_eq_false_1 in Heqb as Heqs1.
        apply bool_decide_code_false in Heqb as ->.
        wp_pures.
        iDestruct (na_own_acc _ _ _ (next_stage 0) with "O") as "[O A]".
        wp_apply (inject_spec_helper with "[Hld1' ι O]") as "%ld1'' [#Hld1'' O]".
          { iFrame "#". iFrame. }
        iDestruct ("A" with "O") as "O".
        iExists ((ltr1 ++ ⋅(md1, rd1, s1')%V) ++ ⋅(s1'', NONEV, empty_buffer)%V),
                ((ldC1 ++ ⋅(mdC1 ++ List.concat rdC1 ++ os1')) ++ ⋅os1'').
        iFrame. iFrame "#".
        iSplitL.
        + iPureIntro. rewrite /= !concat_app /=. aac_reflexivity.
        + iApply (big_sepL2_app with "[Hltr1]");
        [ iApply (big_sepL2_app with "[Hltr1]") |].
          * iApply (big_sepL2_mono with "Hltr1"). by auto.
          * simpl. doneR.
            (* TODO(Juliette): factor out *)
            rewrite triple_unfold.
            iExists md1, rd1, s1', mdC1, rdC1, os1', kMd1, ks1', rtr1.
            inversion cfg1; [ rewrite -H3 in H14; lia |].
            iSplitR. iPureIntro.
            destruct (length rdC1); [apply left_leaning | apply has_child];
              auto with arith; list_elem_of.
            iSplitR. done.
            iFrame "#".
            doneR.
            iApply (big_sepL2_mono with "Hrtr1"). by auto.
          * simpl. doneR.
            rewrite triple_unfold.
            iExists s1'', empty, empty_buffer, os1'', [], [], ks1'', 0, [].
            iSplitR. iPureIntro. constructor; invert_all_in; list_elem_of.
            iSplitR. done.
            iFrame "#".
            iSplitR. isEmptyDeque.
            iSplitR. rewrite /bufferPre. iSplitL. by iApply empty_is_buffer. done.
            iNext. doneL.
            iPureIntro; simpl; aac_reflexivity.
    }
    iModIntro. wp_pures.
    wp_apply (partition_buffer_right_better_spec with "[Hpr2']") as "%p2' %p2'' %op2' %op2'' %kp2' %kp2'' (#Hp2' & #Hp2'' & (%Hp21' & %Hp2'' & %Hop2eq))".
      { iFrame. iPureIntro. invert_all_in; list_elem_of. }
    wp_pures.
    iDestruct (na_own_acc _ _ _ (next_stage 0) with "O") as "[O A]".
    iDestruct (split_time time_for_push with "τ") as "[ι τ]". by lia.
    wp_apply (push_spec_helper with "[Hrd2 ι O]") as "%rd2' [#Hrd2' O]".
    { iFrame "#". iFrame. }
    iDestruct ("A" with "O") as "O".
    wp_pures.
    wp_bind (if: _ then _ else _)%E.
    iDestruct (split_time time_for_push with "τ") as "[ι τ]". by lia.
    wp_apply (wp_strong_mono _ _ _ _ _
      (λ v, ∃ tr trC, isDeque _ 1 tr v ∗
        ⌜ List.concat trC = op2' ++ op2'' ++ List.concat ldC2 ++ mdC2 ++ List.concat rdC2 ⌝ ∗
        ([∗list] a;b ∈ trC; tr, ▷ triple π 1 a b) ∗
        Token π 0)%I
      with "[ι O]") as "%rd2'' (%tr2' & %trC2' & #Hrd2'' & %HtrC2' & #trtrC2' & O)"; try done.
    {
      wp_apply (bsize_better_spec with "Hp2'") as "_".
      wp_pures.
      destruct (bool_decide (kp2' = 0)) eqn:?.
      + apply bool_decide_eq_true_1 in Heqb as Heqp2.
        apply bool_decide_code_true in Heqb as ->.
        wp_pures.
        iFrame.
        rewrite Heqp2.
        iDestruct (empty_buffer_is_empty with "Hp2'") as "->".
        rewrite !app_nil_l.
        iExists (⋅(p2'', ld2, md2)%V ++ rtr2), (⋅(op2'' ++ List.concat ldC2 ++ mdC2) ++ rdC2).
        iFrame "#".
        iSplitR.
        * iPureIntro. rewrite !concat_app /=. aac_reflexivity.
        * simpl.
          iSplitR.
          -- iModIntro. iNext.
            rewrite triple_unfold.
            iExists p2'', ld2, md2, op2'', ldC2, mdC2, kp2'', kMd2, ltr2.
            inversion cfg2.
            iSplitR. iPureIntro.
            destruct (length ldC2); [apply left_leaning | apply has_child];
              auto with arith; list_elem_of.
            iSplitR. done.
            iFrame "#".
            doneR.
            iApply (big_sepL2_mono with "Hltr2"). by auto.
          -- iApply (big_sepL2_mono with "Hrtr2"). by auto.
      + apply bool_decide_eq_false_1 in Heqb as Heqp2.
        apply bool_decide_code_false in Heqb as ->.
        wp_pures.
        iDestruct (na_own_acc _ _ _ (next_stage 0) with "O") as "[O A]".
        wp_apply (push_spec_helper with "[Hrd2' ι O]") as "%rd2'' [#Hrd2'' O]".
          { iFrame "#". iFrame. }
        iDestruct ("A" with "O") as "O".
        iFrame.
        iExists (⋅(p2', NONEV, empty_buffer)%V ++ ⋅(p2'', ld2, md2)%V ++ rtr2),
                (⋅op2' ++ ⋅(op2'' ++ concat ldC2 ++ mdC2) ++ rdC2).
        iFrame "#".
        iSplitL.
        * iPureIntro. rewrite !concat_app /=. aac_reflexivity.
        * iApply (big_sepL2_app with "[Hrtr2]");
        [| iApply (big_sepL2_app with "[Hrtr2]") ].
          -- simpl. doneR.
            rewrite triple_unfold. iNext.
            iExists p2', empty, empty_buffer, op2', [], [], kp2', 0, [].
            iSplitR. iPureIntro. constructor; invert_all_in; list_elem_of.
            iSplitR. done.
            iFrame "#".
            iSplitR. isEmptyDeque.
            iSplitR. rewrite /bufferPre. iSplitL. by iApply empty_is_buffer. done.
            doneL.
            iPureIntro; simpl; aac_reflexivity.
          -- simpl. doneR.
            (* TODO(Juliette): factor out *)
            rewrite triple_unfold.
            iExists p2'', ld2, md2, op2'', ldC2, mdC2, kp2'', kMd2, ltr2.
            inversion cfg2.
            iSplitR. iPureIntro.
            destruct (length ldC2); [apply left_leaning | apply has_child];
              auto with arith; list_elem_of.
            iSplitR. done.
            iFrame "#".
            doneR.
            iApply (big_sepL2_mono with "Hltr2"). by auto.
          -- iApply (big_sepL2_mono with "Hrtr2"). by auto.
    }
    iModIntro. wp_pures.
    wp_apply (ssref_alloc π (fiveTuple _ 0 (o1 ++ o2)) with "[τ]") as (ℓ') "Hℓ'".
    { iExists pr1, ld1'', md', rd2'', sf2,
      prC1, trC1', (⋅x ++ ⋅y), trC2', sfC2,
      kPr1, 2, kSf2, tr1', tr2'.
      iSplitR. done.
      iSplitR. iPureIntro. constructor; list_elem_of.
      iSplitL "τ". iApply three_time_enough. iDestruct (split_time 3 with "τ") as "[ι _]"; [lia | auto].
      iFrame "#".
      iSplitL. iApply (big_sepL2_mono with "trtrC1'"). by auto.
      iSplitL. iApply (big_sepL2_mono with "trtrC2'"). by auto.
      iPureIntro.
      rewrite Heq1 Heq2 -Hos1eq -Hop2eq HtrC1' HtrC2'.
      aac_reflexivity.
    }
    wp_pures.
    iApply "Hψ".
    iFrame.
    ℓisDeque ℓ'. iExact "Hℓ'".
    Unshelve. all: by auto.
  Qed.

End proof.
