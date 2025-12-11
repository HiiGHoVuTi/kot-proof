From iris.heap_lang Require Import lang proofmode notation.
From iris.bi Require Import derived_laws.

From Coq Require Import List.
Import ListNotations.

From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Deque Require Import common tick shared_ref deque_corr push_corr inject_corr.

Section proof.

  Context `{!heapGS Σ}.

  Variable NO_COST_ANALYSIS : TICK_COST = 0.

  Lemma safe_inject_whole :
    ∀ sC dC d, isDeque dC d -∗
    fold.safe_fold id inject d sC (isDeque (dC ++ sC)).
  Proof.
    intro.
    iInduction sC as [| x sC ].
    all: iIntros (dC d) "#Hd".
    all: rewrite /fold.safe_fold.
    - iFrame. rewrite app_nil_r //.
    - iApply (inject_spec_helper).
        { assumption. }
        { iFrame. iExact "Hd". }
      iNext.
      iIntros (d') "Hd'".
      iSpecialize ("IHsC").
      iSpecialize ("IHsC" $! (dC ++ ⋅x) d' with "Hd'").
      assert (dC ++ x :: sC = ((dC ++ [x]) ++ sC)) as ->
        by rewrite cons_middle app_assoc //.
      done.
  Qed.

  Lemma inject_whole_spec : forall s d k sC dC,
    {{{ buffer k sC s ∗ isDeque dC d }}}
      bfold_left inject d s
    {{{ d', RET d'; isDeque (dC ++ sC) d' }}}.
  Proof.
    intros. iIntros "(#Hs & #Hd) Hϕ".
    wp_apply (bfold_left_spec _ _ _ _ (isDeque (dC ++ sC))%I).
    - iFrame "#".
      iDestruct (buffer_length with "Hs") as "<-".
      by iApply (safe_inject_whole sC).
    - by iApply "Hϕ".
  Qed.

  Lemma safe_push_whole :
    ∀ sC dC d, isDeque dC d -∗
    fold.safe_fold fold.fflip push d (rev sC) (isDeque (sC ++ dC)).
  Proof.
    intro.
    rewrite -{2}(rev_involutive sC).
    set (l := rev sC).
    assert (l = rev sC) by done.
    move: sC l H => sC l.
    move: l sC => l.
    iInduction l as [| x l].
    all: iIntros (sC Heq dC d) "#Hd".
    - iFrame.
      rewrite //.
    - rewrite /fold.safe_fold.
      wp_pures.
      iApply (push_spec_helper).
        { assumption. }
        { iFrame. iExact "Hd". }
      iNext.
      iIntros (d') "Hd'".
      assert (l = rev (rev l)) as Hinv by rewrite rev_involutive //.
      iSpecialize ("IHl" $! (rev l) Hinv).
      iSpecialize ("IHl" $! (⋅x ++ dC) d' with "Hd'").
      assert (rev (x::l) ++ dC = rev l ++ ⋅x ++ dC) as ->.
        { assert (x::l = ⋅x ++ l) as -> by rewrite //.
          rewrite rev_app_distr.
          assert (rev [x] = [x]) as -> by rewrite //.
          aac_reflexivity. }
      done.
  Qed.

 Lemma push_whole_spec : forall s d k sC dC,
    {{{ buffer k sC s ∗ isDeque dC d }}}
      bfold_right push s d
    {{{ d', RET d'; isDeque (sC ++ dC) d' }}}.
  Proof.
    intros. iIntros "(#Hs & #Hd) Hϕ".
    wp_apply (bfold_right_spec _ _ _ _ (isDeque (sC ++ dC))%I).
    - iFrame "#".
      iDestruct (buffer_length with "Hs") as "<-".
      by iApply (safe_push_whole sC).
    - by iApply "Hϕ".
  Qed.

  Theorem dconcat_spec_helper (d1 d2 : val) : forall o1 o2,
    {{{ isDeque o1 d1 ∗ isDeque o2 d2 }}}
      dconcat d1 d2
    {{{ d', RET d'; isDeque (o1 ++ o2) d' }}}.
  Proof.
    iIntros (o1 o2 ψ) "(Hd1 & Hd2) Hψ".
    rewrite /dconcat /IsDeque.
    wp_pures.
    wp_apply (tick_spec) as "_".
      { rewrite NO_COST_ANALYSIS time_zero //. }
    wp_pures.
    (* trivial cases *)
    rewrite {1} isDeque_unfold.
    iDestruct "Hd1" as "[[-> ->] | (%ℓ1 & -> & #Hℓ1)]".
    { wp_pures. iApply "Hψ". rewrite app_nil_l //. }
    rewrite {1} isDeque_unfold.
    iDestruct "Hd2" as "[[-> ->] | (%ℓ2 & -> & #Hℓ2)]".
    { wp_pures. iApply "Hψ". iFrame. ℓisDeque ℓ1. rewrite app_nil_r. iExact "Hℓ1". }
    wp_pures.
    wp_apply (csref_load with "Hℓ1") as "%v
      (%pr1 & %ld1 & %md1 & %rd1 & %sf1 & %prC1 & %ldC1 & %mdC1 & %rdC1 & %sfC1
            & %kPr1 & %kMd1 & %kSf1 & %ltr1 & %rtr1 & -> & %cfg1
            & #Hpr1 & #Hld1 & #Hmd1 & #Hrd1 & #Hsf1 & #Hltr1 & #Hrtr1 & %Heq1)
      ".
    wp_pures.
    wp_apply (csref_load with "Hℓ2") as "%v'
      (%pr2 & %ld2 & %md2 & %rd2 & %sf2 & %prC2 & %ldC2 & %mdC2 & %rdC2 & %sfC2
            & %kPr2 & %kMd2 & %kSf2 & %ltr2 & %rtr2 & -> & %cfg2
            & #Hpr2 & #Hld2 & #Hmd2 & #Hrd2 & #Hsf2 & #Hltr2 & #Hrtr2 & %Heq2)
      ".
    wp_pures.
    wp_apply (bis_empty_spec with "Hmd1") as "_".
    wp_pures.
    destruct (bool_decide (kMd1 = 0)) eqn:?.
    { (* d1 is suffix only *)
      apply bool_decide_eq_true_1 in Heqb as Heqmd.
      inversion cfg1; [| exfalso; lia].
      wp_pures.
      wp_apply (push_whole_spec).
      - iFrame "#". iFrame.
        ℓisDeque ℓ2. iExact "Hℓ2".
      - iDestruct (buffer_length with "Hpr1") as "%Hpr1L";
          destruct prC1; [| inversion Hpr1L].
        iDestruct (buffer_length with "Hmd1") as "%Hmd1L";
          destruct mdC1; [| inversion Hmd1L].
        rewrite (nil_length_inv _ (eq_sym H)) in Heq1 |- *.
        rewrite (nil_length_inv _ (eq_sym H1)) in Heq1 |- *.
        aac_normalise in Heq1.
        rewrite Heq1.
        by iApply "Hψ".
      }
    apply bool_decide_eq_false_1 in Heqb as Heqmd1.
    wp_pures.
    wp_apply (bis_empty_spec with "Hmd2") as "_".
    wp_pures.
    destruct (bool_decide (kMd2 = 0)) eqn:?.
    { (* d2 is suffix only *)
      apply bool_decide_eq_true_1 in Heqb0 as Heqmd.
      inversion cfg2; [| exfalso; lia].
      wp_pures.
      wp_apply (inject_whole_spec).
      - iFrame "#". iFrame.
        ℓisDeque ℓ1. iExact "Hℓ1".
      - iDestruct (buffer_length with "Hpr2") as "%Hpr2L";
          destruct prC2; [| inversion Hpr2L].
        iDestruct (buffer_length with "Hmd2") as "%Hmd2L";
          destruct mdC2; [| inversion Hmd2L].
        rewrite (nil_length_inv _ (eq_sym H)) in Heq2 |- *.
        rewrite (nil_length_inv _ (eq_sym H1)) in Heq2 |- *.
        aac_normalise in Heq2.
        rewrite Heq2.
        by iApply "Hψ".
    }
    apply bool_decide_eq_false_1 in Heqb0 as Heqmd2.
    wp_pures.
    inversion cfg1; [exfalso; by apply Heqmd2 |].
    inversion cfg2; [exfalso; by apply Heqmd2 |].
    change (kSf1 ∈ map S [2; 3; 4; 5]) in H0.
    apply decrease_in in H0 as (kSf1' & -> & HkSf1').
    wp_apply (beject_spec with "Hsf1") as "%sf1' %x %oBX (Hsf1' & ->)".
    wp_pures.
    change (kPr2 ∈ map S [2; 3; 4; 5]) in H6.
    apply decrease_in in H6 as (kPr2' & -> & HkPr2').
    wp_apply (bpop_spec with "Hpr2") as "%y %pr1' %oBY (Hpr2' & ->)".
    wp_pures.
    wp_apply (bdoubleton_spec) as "%md' #Hmd'". { done. }
    wp_pures.
    wp_apply (bsplit23l_spec with "[Hsf1']") as "%s1' %s1'' %os1' %os1'' %ks1' %ks1'' (#Hs1' & #Hs1'' & (%Hks1' & %Hks1'' & %Heqos1))".
      { iFrame. iPureIntro. invert_all_in; list_elem_of. }
    rewrite /atriple_.
    wp_pures.
    wp_apply (inject_spec_helper with "Hld1") as "%ld1' #Hld1'".
      { assumption. }
    wp_pures.
    wp_bind (if: _ then _ else _)%E.
    wp_apply (wp_strong_mono _ _ _ _ _
      (λ v, ∃ tr trC, isDeque tr v ∗
        ⌜ List.concat trC = List.concat ldC1 ++ mdC1 ++ List.concat rdC1 ++ os1' ++ os1'' ⌝ ∗
        ([∗list] a;b ∈ trC; tr, ▷ triple a b))%I
      ) as "%ld1'' (%tr1' & %trC1' & #Hld1'' & %HtrC1' & #trtrC1')"; try done.
    {
     wp_apply (bis_empty_spec with "Hs1''") as "_".
      wp_pures.
      destruct (bool_decide (ks1'' = 0)) eqn:?.
      - apply bool_decide_eq_true_1 in Heqb1 as Heqs1.
        wp_pures.
        rewrite Heqs1.
        iDestruct (buffer_length with "Hs1''") as "%Hs1''L".
        destruct os1''; [| inversion Hs1''L].
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
              auto with arith; try list_elem_of.
            iSplitR. done.
            iFrame "#".
            doneR.
            iApply (big_sepL2_mono with "Hrtr1"). by auto.
      - apply bool_decide_eq_false_1 in Heqb1 as Heqs1.
        wp_pures.
        wp_apply (abuffer_spec with "Hs1''") as "%ts1'' #Hts1''".
          { inversion Hks1''; [lia | list_elem_of]. }
        wp_apply (inject_spec_helper with "Hld1'") as "%ld1'' #Hld1''".
          { assumption. }
        iExists ((ltr1 ++ ⋅(md1, rd1, s1')%V) ++ ⋅ts1''%V),
                ((ldC1 ++ ⋅(mdC1 ++ List.concat rdC1 ++ os1')) ++ ⋅os1'').
        iFrame. iFrame "#".
        iSplitL.
        + iPureIntro. rewrite /= !concat_app /=. aac_reflexivity.
        + doneR.
          iApply (big_sepL2_app with "[Hltr1]").
          * iApply (big_sepL2_mono with "Hltr1"). by auto.
          * simpl. doneR.
            iNext.
            rewrite !triple_unfold.
            iExists md1, rd1, s1', mdC1, rdC1, os1', kMd1, ks1', rtr1.
            inversion cfg1; [ rewrite -H3 in H14; lia |].
            iSplitR. iPureIntro.
            destruct (length rdC1); [apply left_leaning | apply has_child];
              auto with arith; list_elem_of.
            iSplitR. done.
            iFrame "#".
            doneR.
            iApply (big_sepL2_mono with "Hrtr1"). by auto.
    }
    iModIntro. wp_pures.
    wp_apply (bsplit23r_spec with "[Hpr2']") as "%p2' %p2'' %op2' %op2'' %kp2' %kp2'' (#Hp2' & #Hp2'' & (%Hp21' & %Hp2'' & %Hop2eq))".
      { iFrame. iPureIntro. clear HkSf1' Hks1' Hks1''. invert_all_in; list_elem_of. }
    wp_pures.
    wp_apply (push_spec_helper with "Hrd2") as "%rd2' #Hrd2'".
      { assumption. }
    wp_pures.
    wp_bind (if: _ then _ else _)%E.
    wp_apply (wp_strong_mono _ _ _ _ _
      (λ v, ∃ tr trC, isDeque tr v ∗
        ⌜ List.concat trC = op2' ++ op2'' ++ List.concat ldC2 ++ mdC2 ++ List.concat rdC2 ⌝ ∗
        ([∗list] a;b ∈ trC; tr, ▷ triple a b))%I
      ) as "%rd2'' (%tr2' & %trC2' & #Hrd2'' & %HtrC2' & #trtrC2')"; try done.
    {
      wp_apply (bis_empty_spec with "Hp2'") as "_".
      wp_pures.
      destruct (bool_decide (kp2' = 0)) eqn:?.
      + apply bool_decide_eq_true_1 in Heqb1 as Heqp2.
        wp_pures.
        iFrame.
        rewrite Heqp2.
        iDestruct (buffer_length with "Hp2'") as "%Hp2'L".
        destruct op2'; [| inversion Hp2'L].
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
            { iDestruct (buffer_length with "Hpr2") as "%Habsurd". inversion Habsurd. }
            iSplitR. iPureIntro.
            destruct (length ldC2); [apply left_leaning | apply has_child];
              try lia; list_elem_of.
            iSplitR. done.
            iFrame "#".
            doneR.
            iApply (big_sepL2_mono with "Hltr2"). by auto.
          -- iApply (big_sepL2_mono with "Hrtr2"). by auto.
      + apply bool_decide_eq_false_1 in Heqb1 as Heqp2.
        wp_pures.
        wp_apply (abuffer_spec with "Hp2'") as "%tp2' #Htp2'".
          { inversion Hp21'; [lia | list_elem_of]. }
        wp_apply (push_spec_helper with "Hrd2'") as "%rd2'' #Hrd2''".
          { assumption. }
        iFrame.
        iExists (⋅tp2' ++ ⋅(p2'', ld2, md2)%V ++ rtr2),
                (⋅op2' ++ ⋅(op2'' ++ concat ldC2 ++ mdC2) ++ rdC2).
        iFrame "#".
        iSplitL.
        * iPureIntro. rewrite !concat_app /=. aac_reflexivity.
        * doneL.
          iApply (big_sepL2_app with "[Hrtr2]").
          -- simpl. doneR.
            iNext.
            rewrite !triple_unfold.
            iExists p2'', ld2, md2, op2'', ldC2, mdC2, kp2'', kMd2, ltr2.
            inversion cfg2.
            { iDestruct (buffer_length with "Hpr2") as "%Habsurd". inversion Habsurd. }
            iSplitR. iPureIntro.
            destruct (length ldC2); [apply left_leaning | apply has_child];
              auto with arith; list_elem_of.
            iSplitR. done.
            iFrame "#".
            doneR.
            iApply (big_sepL2_mono with "Hltr2"). by auto.
          -- iApply (big_sepL2_mono with "Hrtr2"). by auto.
    }
    rewrite /assemble_.
    iModIntro. wp_pures.
    wp_apply (csref_alloc (fiveTuple (o1 ++ o2))) as (ℓ') "Hℓ'".
    { iExists pr1, ld1'', md', rd2'', sf2,
      prC1, trC1', (⋅oBX ++ ⋅pr1'), trC2', sfC2,
      kPr1, 2, kSf2, tr1', tr2'.
      iSplitR. done.
      iSplitR. iPureIntro. constructor; list_elem_of.
      iFrame "#".
      iSplitL. iApply (big_sepL2_mono with "trtrC1'"). by auto.
      iSplitL. iApply (big_sepL2_mono with "trtrC2'"). by auto.
      iPureIntro.
      rewrite Heq1 Heq2 Heqos1 Hop2eq HtrC1' HtrC2'.
      aac_reflexivity.
    }
    wp_pures.
    iApply "Hψ".
    iFrame.
    ℓisDeque ℓ'. iExact "Hℓ'".
    Unshelve. all: by auto.
  Qed.

  Definition dconcat_spec d1 d2 : forall o1 o2,
    {{{ isDeque o1 d1 ∗ isDeque o2 d2 }}}
      dconcat d1 d2
    {{{ d', RET d'; IsDeque (o1 ++ o2) d' }}}
  :=
    dconcat_spec_helper d1 d2.

End proof.
