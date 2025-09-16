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
    iIntros (depth ψ) "(Hd & τ & O) Hψ".
    rewrite isDeque_unfold.
    rewrite /pop_nonempty.
    iLöb as "iH" forall (ℓ oD x depth).
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
      (* NOTE(Juliette): pourquoi nommer la première hypothèse casse tout ????? je ne comprends rien *)
      iDestruct "Safe" as "[Hsafe pop_safe]".
      wp_bind (naive_pop_safe d)%E.
      iApply (wp_wand with "pop_safe").
      iIntros (true_) "->".
      wp_apply (naive_pop_safe with "Hd").

    }
    (*
    iDestruct (persist_structure with "πd") as "[#Hv
        (%pr & %ld & %md & %rd & %sf & %prC & %ldC & %mdC & %rdC & %sfC
            & %kPr & %kMd & %kSf & %ltr & %rtr & -> & %cfg & pot
            & #Hpr & #Hld & #Hmd & #Hrd & #Hsf & #Hltr & #Hrtr & %Heq)]".
    wp_pures.
    *)
    (* START HERE *)

    (*
    wp_bind (if: _ then _ else _)%E.
    wp_apply (wp_strong_mono _ _ _ _ _
      (λ v, isPopFiveTuple π depth (⋅x ++ oD) v ∗ Token π (S depth))%I
      with "[O τ]"); [easy | easy | |]. {
    wp_apply (bsize_better_spec with "Hmd") as "_".
    wp_pures.
    destruct (bool_decide (kMd = 0)) eqn:?.
    { (* apply bool_decide_eq_true_1 in Heqb as Heqmd.
      apply bool_decide_code_true in Heqb as ->.
      wp_pures.
      iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
      iFrame.
      inversion cfg; [| exfalso; lia].
      destruct ldC; inversion H.
      destruct rdC; inversion H1.
      iDestruct (big_sepL2_nil_inv_l with "Hltr") as "->".
      iDestruct (big_sepL2_nil_inv_l with "Hrtr") as "->".
      iExists pr,ld,md,rd,sf,prC,[],mdC,[],sfC,0,0,kSf,[],[].
      iFrame "#".
      iSplitR. done.
      iSplitR.
        { iPureIntro.
          rewrite Heqmd in cfg |- *.
          invert_all_in; constructor; list_elem_of.
        }
      iSplitL. by iApply three_time_enough.
      do 2 doneL.
      done.
      *)
      admit.
    }
    apply bool_decide_eq_false_1 in Heqb as Heqmd.
    apply bool_decide_code_false in Heqb as ->.
    wp_pures.
    wp_apply (bsize_better_spec with "Hpr") as "_".
    wp_pures.
    destruct (bool_decide (kPr = 3)) eqn:?.
    2: { (*
      apply bool_decide_eq_false_1 in Heqb as Heqpr.
      apply bool_decide_code_false in Heqb as ->.
      wp_pures.
      iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
      iFrame.
      iExists pr,ld,md,rd,sf,prC,ldC,mdC,rdC,sfC,kPr,kMd,kSf,ltr,rtr.
      iFrame "#".
      iSplitR. done.
      iSplitR.
        { iPureIntro.
          inversion cfg; [exfalso; lia |].
          invert_all_in; constructor; list_elem_of.
        }
      iSplitL. by iApply three_time_enough.
      iSplitR. iApply (big_sepL2_mono with "Hltr"). by auto.
      iSplitR. iApply (big_sepL2_mono with "Hrtr"). by auto.
      done.
      *)
      admit.
    }
    apply bool_decide_eq_true_1 in Heqb as Heqpr.
    apply bool_decide_code_true in Heqb as ->.
    wp_pures.
    rewrite {1}isDeque_unfold {1}isDeque_unfold.
    iDestruct "Hld" as "[[-> ->] | (%ℓld & -> & Hld)]";
    iDestruct "Hrd" as "[[-> ->] | (%ℓrd & -> & Hrd)]";
    wp_pures.
    - (* wp_apply (bsize_better_spec with "Hsf") as "_".
      wp_pures.
      destruct (bool_decide (kSf = 3)) eqn:?.
      + apply bool_decide_eq_true_1 in Heqb as Heqsf.
        apply bool_decide_code_true in Heqb as ->.
        wp_pures.
        wp_bind (inject_whole_buffer _ _ _).
        wp_apply (binject_whole_spec with "[Hmd Hsf]") as "%sf' #Hsf'".
          by iFrame "#".
        wp_apply (binject_whole_spec with "[Hmd Hsf']") as "%sf'' #Hsf''".
          by iFrame "#".
        wp_pures.
        iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
        iModIntro.
        iFrame.
        iExists empty_buffer,NONEV,empty_buffer,NONEV,sf'',[],[],[],[],(prC ++ mdC ++ sfC),0,0,(kSf+kMd+kPr),[],[].
        iFrame "#".
        iSplitR. done.
        iSplitR.
          { iPureIntro.
            inversion cfg; constructor; simpl; list_elem_of.
            - rewrite !Nat.add_0_r //.
            - rewrite Heqpr Heqsf. list_elem_of.
           }
        iSplitL. by iApply three_time_enough.
        iSplitR. by iApply empty_is_buffer_at.
        iSplitR. by isEmptyDeque.
        iSplitR. by iApply empty_is_buffer_at.
        iSplitR. by isEmptyDeque.
        do 2 doneL.
        iDestruct (big_sepL2_nil_inv_r with "Hltr") as "->".
        iDestruct (big_sepL2_nil_inv_r with "Hrtr") as "->".
        iPureIntro.
        rewrite Heq //.
      + apply bool_decide_eq_false_1 in Heqb as Heqsf.
        apply bool_decide_code_false in Heqb as ->.
        wp_pures.
        inversion cfg. symmetry in H2; by contradiction.
        wp_apply (bpop_spec2 with "Hmd") as "%a %m %oM (#hM' & %HmdC)".
        wp_pures.
        wp_apply (binject_spec2 with "Hpr") as "%p' #Hp'".
        wp_pures.
        change (kSf ∈ map S [2; 3; 4; 5]) in H0.
        apply decrease_in in H0 as (kSf' & -> & HkSf').
        wp_apply (bpop_spec2 with "Hsf") as "%b %s' %oS' (#hS' & %HsfC)".
        wp_pures.
        wp_apply (binject_spec2 with "hM'") as "%md' #Hmd'".
        wp_pures.
        iModIntro.
        iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
        iFrame.
        iExists p', NONEV, md', NONEV, s',
          (prC++⋅a), [], (oM++⋅b), [], oS', (S kPr), 2, kSf', [], [].
        iFrame "#".
        iSplitR. done.
        iSplitR.
          { iPureIntro.
            constructor;
            [rewrite Heqpr | invert_all_in];
            list_elem_of;
            exfalso; apply Heqsf; by auto.
          }
        iSplitL. by iApply three_time_enough.
        iSplitR. by isEmptyDeque.
        iSplitR. by isEmptyDeque.
        iDestruct (big_sepL2_nil_inv_r with "Hltr") as "->".
        iDestruct (big_sepL2_nil_inv_r with "Hrtr") as "->".
        do 2 doneL.
        iPureIntro.
        aac_rewrite Heq.
        aac_rewrite HsfC.
        aac_rewrite HmdC.
        rewrite /= !cons_middle. aac_reflexivity.
        *)
      admit.
    - wp_apply (ssref_read π _ (isPersFiveTuple _ _ _) with "[Hrd O]") as "%right
        [(%pr1 & %ld1 & %md1 & %rd1 & %sf1 & %prC1 & %ldC1 & %mdC1 & %rdC1 & %sfC1
            & %kPr1 & %kMd1 & %kSf1 & %ltr1 & %rtr1 & -> & %cfg1
            & #Hpr1 & #Hld1 & #Hmd1 & #Hrd1 & #Hsf1 & #Hltr1 & #Hrtr1 & %Heq1)
        O]".
        {
          iSplitR. iExact "Hrd".
          iFrame.
          iIntros (v) "H".
          iApply (persist_structure with "H").
        }
        rewrite /inspect_first /naive_pop.
        remember (S depth) as sDepth.
        wp_pures.
        wp_apply (bsize_better_spec with "Hmd1") as "_".
        wp_pures.
        destruct (bool_decide (kMd1 = 0)) eqn:?.
        + apply bool_decide_eq_true_1 in Heqb as Heqmd1.
          apply bool_decide_code_true in Heqb as ->.
          wp_pures.
          inversion cfg1; [| exfalso; lia].
          change (kSf1 ∈ map S [0;1;2;3;4;5;6;7]) in H3.
          apply decrease_in in H3 as (kSf' & -> & HkSf').
          iCombine "Hsf1 Hsf1" as "[_ #sHsf1]".
          rewrite {11}HeqsDepth /=.
          wp_apply (bpop_spec2 with "Hsf1") as "%x' %str' %rstr (#Hstr' & ->)".
          wp_pures.
          wp_alloc _ignored as "_". wp_pures. clear _ignored.
          assert (x' ∈ rtr) as Hx'.
            { rewrite Heq1.
              do 4 (apply elem_of_list_app; right).
              apply elem_of_list_app; left.
              by list_elem_of. }
          iDestruct (lookup_triple (S depth) _ _ _ Hx' with "Hrtr") as "(%xC' & Hx')".
          rewrite triple_unfold.
          iDestruct "Hx'" as "(%fst & %child & %last & %fstC & %childC & %lastC & %kFst & %kLst & %chTr & %bCfg & -> & #Hfst & #Hch & #Hlst & #chCchT & ->)".
          wp_pures.
          wp_bind (first_nonempty _)%E.
          wp_apply (wp_strong_mono _ _ _ _ _ (λ v, ⌜ v = SOMEV fst ⌝)%I); [ done | done | | ].
          {
            rewrite /first_nonempty. wp_pures.
            wp_apply (bsize_better_spec with "Hfst") as "_".
            wp_pures.
            assert (bool_decide (#kFst = #0%nat) = false) as ->.
              { inversion bCfg; invert_all_in. }
            wp_pures.
            done.
          }
          iIntros "%TMP ->". iModIntro.
          wp_pures.
          wp_apply (bsize_better_spec with "Hfst") as "_".
          wp_pures.
          destruct (bool_decide (kFst = 3%nat)) eqn:?.
          * (* *) apply bool_decide_eq_true_1 in Heqb as Heqkfst.
            apply bool_decide_code_true in Heqb as deckfst.
            rewrite deckfst.
            wp_pures.
            wp_apply (bsize_better_spec with "Hmd1") as "_".
            wp_pures.
            iDestruct "sHsf1" as "[#rHsf1 %lHsf1]".
            wp_apply (bpop_spec with "rHsf1") as "%str'' #Hstr''".
            wp_pures.
            wp_alloc ℓr as "Hℓr".
            wp_pures.
            wp_apply (bsize_better_spec with "Hfst") as "_". wp_pures.
            wp_apply (bsize_better_spec with "Hlst") as "_". wp_pures.
            rewrite deckfst.
            wp_pures.
            inversion cfg. { exfalso. apply Heqmd. done. }
            wp_apply (bpop_spec2 with "Hmd") as "%a %m %oM (Hm & %HmdC)".
            wp_pures.
            wp_apply (binject_spec2 with "Hpr") as "%p' #Hp'".
            wp_pures.
            rewrite Heqkfst.
            wp_apply (bpop_spec2 with "Hfst") as "%b %x' %oX' (#Hx' & %HfstC)".
            wp_pures.
            wp_apply (binject_spec2 with "Hm") as "%m' #Hm'".
            wp_pures.
            wp_bind (push _)%E.
            rewrite /push.
            wp_pures.
            iDestruct (split_time 1 with "τ") as "[ι τ]". by lia.
            wp_apply (tick_spec with "ι") as "_".
            wp_pures.
            wp_load.
            wp_pures.
            wp_apply (bsize_better_spec with "Hmd1") as "_".
            wp_pures.
            wp_apply (bsize_spec with "Hstr''") as "_".
            simpl in lHsf1. inversion lHsf1.
            rewrite H12.
            wp_pures.
            assert (bool_decide (#kSf' = #8%nat) = false) as ->.
              { apply bool_decide_code_false, bool_decide_eq_false_2.
                intro; clear H3 H5.
                invert_all_in; lia.
              }
            wp_pures.
            wp_store.
            wp_bind (bpush _ _).
            wp_apply (bpush_spec with "Hstr''") as "%str''' #Hstr'''".
            wp_pures.
            iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
            wp_bind (ref _)%E.
            wp_apply (ssref_alloc π (fiveTuple π (S depth) _) with "[ι]") as "%ℓ'' #Hℓ''".
            { iExists pr1, ld1, md1, rd1, str''', oPr1, oLd1, oMd1, oRd1, _,
                kPr1, kMd1, (S kSf').
              rewrite -H -H0 -H1 -H2 -HeqsDepth.
              iFrame "#". iFrame.
              rewrite HeqsDepth.
              iSplitR. done.
              iSplitR.
              {
                iPureIntro.
                constructor.
                invert_all_in; list_elem_of.
              }
              iSplitL. by iApply three_time_enough.
              iSplitL.
              - iExists ((x',child,last)%V::str), ((oX'++childC++lastC)::strC).
                iSplitL. iExact "Hstr'''".
                iSplitL. iPureIntro. split.
                + done.
                + rewrite -Hlstr. by simpl.
                + iApply big_sepL2_cons.
                  iSplitL.
                  * rewrite -HeqsDepth. iNext.
                    rewrite triple_unfold.
                    iExists x', child, last, oX', childC, lastC, 2, kLst.
                    iSplitR.
                      { iPureIntro.
                        clear HkSf' H3 H5.
                        inversion bCfg; constructor; invert_all_in;
                        list_elem_of.
                      }
                    iSplitR. done.
                    rewrite HeqsDepth.
                    iFrame "#".
                    iPureIntro. done.
                  * iApply (big_sepL2_mono with "Hstrrest").
                    intros. iIntros "H". by iNext.
              - iPureIntro. done.
            }
            wp_pures.
            iFrame.
            iExists p', NONEV, m', (SOMEV #ℓ''), sf,
              (prC ++ oA), [], (oM ++ oB), _, sfC,
              (S kPr), 2, kSf.
            iModIntro.
            iFrame "#"; iFrame.
            iSplitR. done.
            iSplitR.
              { iPureIntro.
                clear HkSf'.
                constructor; invert_all_in; list_elem_of;
                exfalso; lia.
              }
            iSplitL. iApply three_time_enough.
              iDestruct (split_time 3 with "τ") as "[A _]"; by [lia | done].
            iSplitR. by isEmptyDeque.
            iSplitR. ℓisDeque ℓ''. by iExact "Hℓ''".
            iDestruct (empty_buffer_is_empty with "Hpr1") as "->".
            iDestruct (empty_buffer_is_empty with "Hmd1") as "->".
            destruct oLd1; [| inversion H].
            destruct oRd1; [| inversion H1].
            iPureIntro.
            rewrite Heq HmdC Ho1 Hos1 HoB HfstC /=.
            aac_reflexivity.
            *)
            admit.
          * apply bool_decide_eq_false_1 in Heqb as Heqkfst.
            apply bool_decide_code_false in Heqb as deckfst.
            rewrite deckfst.
            wp_pures.
            iDestruct (isDeque_unfold with "Hch") as "[[-> ->] | (%ℓi & -> & Hch')]"; wp_pures.
            --

End proof.
From iris.heap_lang Require Import lang proofmode notation.
From iris.bi Require Import derived_laws.

From Coq Require Import List.
Import ListNotations.

From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Deque Require Import common tick shared_ref deque_cost push_cost concat_cost.

Section proof.

  Context `{!heapGS Σ} `{!na_invG Σ}.
  Context {π : gname}.

  (* TODO: start here*)
  Lemma pop_spec_helper oD x ℓ : forall depth,
    {{{ isDeque π depth (⋅x ++ oD) (SOMEV #ℓ) ∗ ⏱ time_for_pop ∗ Token π depth }}}
      pop (SOMEV #ℓ)
    {{{ d', RET (x, d')%V; isDeque π depth oD d' ∗ Token π depth }}}.
  Proof.
    iIntros (depth ψ) "(Hd & τ & O) Hψ".
    rewrite isDeque_unfold.
    rewrite /pop.
    iLöb as "iH" forall (ℓ oD x depth).
    iDestruct "Hd" as "[[%H _] | (%ℓ' & -> & Hℓ)]". by inversion H.
    wp_pures.
    iDestruct (split_time 1 with "τ") as "[ι τ]". by lia.
    wp_apply (tick_spec with "ι") as "_".
    wp_pures.
    wp_apply (ssref_load_open with "[Hℓ O]") as "%d (O & πd & DONE)". by iFrame.
    iDestruct (persist_structure with "πd") as "[#Hv
        (%pr & %ld & %md & %rd & %sf & %prC & %ldC & %mdC & %rdC & %sfC
            & %kPr & %kMd & %kSf & %ltr & %rtr & -> & %cfg & pot
            & #Hpr & #Hld & #Hmd & #Hrd & #Hsf & #Hltr & #Hrtr & %Heq)]".
    wp_pures.
    wp_bind (if: _ then _ else _)%E.
    wp_apply (wp_strong_mono _ _ _ _ _
      (λ v, isPopFiveTuple π depth (⋅x ++ oD) v ∗ Token π (S depth))%I
      with "[O τ]"); [easy | easy | |]. {
    wp_apply (bsize_better_spec with "Hmd") as "_".
    wp_pures.
    destruct (bool_decide (kMd = 0)) eqn:?.
    { (* apply bool_decide_eq_true_1 in Heqb as Heqmd.
      apply bool_decide_code_true in Heqb as ->.
      wp_pures.
      iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
      iFrame.
      inversion cfg; [| exfalso; lia].
      destruct ldC; inversion H.
      destruct rdC; inversion H1.
      iDestruct (big_sepL2_nil_inv_l with "Hltr") as "->".
      iDestruct (big_sepL2_nil_inv_l with "Hrtr") as "->".
      iExists pr,ld,md,rd,sf,prC,[],mdC,[],sfC,0,0,kSf,[],[].
      iFrame "#".
      iSplitR. done.
      iSplitR.
        { iPureIntro.
          rewrite Heqmd in cfg |- *.
          invert_all_in; constructor; list_elem_of.
        }
      iSplitL. by iApply three_time_enough.
      do 2 doneL.
      done.
      *)
      admit.
    }
    apply bool_decide_eq_false_1 in Heqb as Heqmd.
    apply bool_decide_code_false in Heqb as ->.
    wp_pures.
    wp_apply (bsize_better_spec with "Hpr") as "_".
    wp_pures.
    destruct (bool_decide (kPr = 3)) eqn:?.
    2: { (*
      apply bool_decide_eq_false_1 in Heqb as Heqpr.
      apply bool_decide_code_false in Heqb as ->.
      wp_pures.
      iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
      iFrame.
      iExists pr,ld,md,rd,sf,prC,ldC,mdC,rdC,sfC,kPr,kMd,kSf,ltr,rtr.
      iFrame "#".
      iSplitR. done.
      iSplitR.
        { iPureIntro.
          inversion cfg; [exfalso; lia |].
          invert_all_in; constructor; list_elem_of.
        }
      iSplitL. by iApply three_time_enough.
      iSplitR. iApply (big_sepL2_mono with "Hltr"). by auto.
      iSplitR. iApply (big_sepL2_mono with "Hrtr"). by auto.
      done.
      *)
      admit.
    }
    apply bool_decide_eq_true_1 in Heqb as Heqpr.
    apply bool_decide_code_true in Heqb as ->.
    wp_pures.
    rewrite {1}isDeque_unfold {1}isDeque_unfold.
    iDestruct "Hld" as "[[-> ->] | (%ℓld & -> & Hld)]";
    iDestruct "Hrd" as "[[-> ->] | (%ℓrd & -> & Hrd)]";
    wp_pures.
    - (* wp_apply (bsize_better_spec with "Hsf") as "_".
      wp_pures.
      destruct (bool_decide (kSf = 3)) eqn:?.
      + apply bool_decide_eq_true_1 in Heqb as Heqsf.
        apply bool_decide_code_true in Heqb as ->.
        wp_pures.
        wp_bind (inject_whole_buffer _ _ _).
        wp_apply (binject_whole_spec with "[Hmd Hsf]") as "%sf' #Hsf'".
          by iFrame "#".
        wp_apply (binject_whole_spec with "[Hmd Hsf']") as "%sf'' #Hsf''".
          by iFrame "#".
        wp_pures.
        iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
        iModIntro.
        iFrame.
        iExists empty_buffer,NONEV,empty_buffer,NONEV,sf'',[],[],[],[],(prC ++ mdC ++ sfC),0,0,(kSf+kMd+kPr),[],[].
        iFrame "#".
        iSplitR. done.
        iSplitR.
          { iPureIntro.
            inversion cfg; constructor; simpl; list_elem_of.
            - rewrite !Nat.add_0_r //.
            - rewrite Heqpr Heqsf. list_elem_of.
           }
        iSplitL. by iApply three_time_enough.
        iSplitR. by iApply empty_is_buffer_at.
        iSplitR. by isEmptyDeque.
        iSplitR. by iApply empty_is_buffer_at.
        iSplitR. by isEmptyDeque.
        do 2 doneL.
        iDestruct (big_sepL2_nil_inv_r with "Hltr") as "->".
        iDestruct (big_sepL2_nil_inv_r with "Hrtr") as "->".
        iPureIntro.
        rewrite Heq //.
      + apply bool_decide_eq_false_1 in Heqb as Heqsf.
        apply bool_decide_code_false in Heqb as ->.
        wp_pures.
        inversion cfg. symmetry in H2; by contradiction.
        wp_apply (bpop_spec2 with "Hmd") as "%a %m %oM (#hM' & %HmdC)".
        wp_pures.
        wp_apply (binject_spec2 with "Hpr") as "%p' #Hp'".
        wp_pures.
        change (kSf ∈ map S [2; 3; 4; 5]) in H0.
        apply decrease_in in H0 as (kSf' & -> & HkSf').
        wp_apply (bpop_spec2 with "Hsf") as "%b %s' %oS' (#hS' & %HsfC)".
        wp_pures.
        wp_apply (binject_spec2 with "hM'") as "%md' #Hmd'".
        wp_pures.
        iModIntro.
        iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
        iFrame.
        iExists p', NONEV, md', NONEV, s',
          (prC++⋅a), [], (oM++⋅b), [], oS', (S kPr), 2, kSf', [], [].
        iFrame "#".
        iSplitR. done.
        iSplitR.
          { iPureIntro.
            constructor;
            [rewrite Heqpr | invert_all_in];
            list_elem_of;
            exfalso; apply Heqsf; by auto.
          }
        iSplitL. by iApply three_time_enough.
        iSplitR. by isEmptyDeque.
        iSplitR. by isEmptyDeque.
        iDestruct (big_sepL2_nil_inv_r with "Hltr") as "->".
        iDestruct (big_sepL2_nil_inv_r with "Hrtr") as "->".
        do 2 doneL.
        iPureIntro.
        aac_rewrite Heq.
        aac_rewrite HsfC.
        aac_rewrite HmdC.
        rewrite /= !cons_middle. aac_reflexivity.
        *)
      admit.
    - wp_apply (ssref_read π _ (isPersFiveTuple _ _ _) with "[Hrd O]") as "%right
        [(%pr1 & %ld1 & %md1 & %rd1 & %sf1 & %prC1 & %ldC1 & %mdC1 & %rdC1 & %sfC1
            & %kPr1 & %kMd1 & %kSf1 & %ltr1 & %rtr1 & -> & %cfg1
            & #Hpr1 & #Hld1 & #Hmd1 & #Hrd1 & #Hsf1 & #Hltr1 & #Hrtr1 & %Heq1)
        O]".
        {
          iSplitR. iExact "Hrd".
          iFrame.
          iIntros (v) "H".
          iApply (persist_structure with "H").
        }
        rewrite /inspect_first /naive_pop.
        remember (S depth) as sDepth.
        wp_pures.
        wp_apply (bsize_better_spec with "Hmd1") as "_".
        wp_pures.
        destruct (bool_decide (kMd1 = 0)) eqn:?.
        + apply bool_decide_eq_true_1 in Heqb as Heqmd1.
          apply bool_decide_code_true in Heqb as ->.
          wp_pures.
          inversion cfg1; [| exfalso; lia].
          change (kSf1 ∈ map S [0;1;2;3;4;5;6;7]) in H3.
          apply decrease_in in H3 as (kSf' & -> & HkSf').
          iCombine "Hsf1 Hsf1" as "[_ #sHsf1]".
          rewrite {11}HeqsDepth /=.
          wp_apply (bpop_spec2 with "Hsf1") as "%x' %str' %rstr (#Hstr' & ->)".
          wp_pures.
          wp_alloc _ignored as "_". wp_pures. clear _ignored.
          assert (x' ∈ rtr) as Hx'.
            { rewrite Heq1.
              do 4 (apply elem_of_list_app; right).
              apply elem_of_list_app; left.
              by list_elem_of. }
          iDestruct (lookup_triple (S depth) _ _ _ Hx' with "Hrtr") as "(%xC' & Hx')".
          rewrite triple_unfold.
          iDestruct "Hx'" as "(%fst & %child & %last & %fstC & %childC & %lastC & %kFst & %kLst & %chTr & %bCfg & -> & #Hfst & #Hch & #Hlst & #chCchT & ->)".
          wp_pures.
          wp_bind (first_nonempty _)%E.
          wp_apply (wp_strong_mono _ _ _ _ _ (λ v, ⌜ v = SOMEV fst ⌝)%I); [ done | done | | ].
          {
            rewrite /first_nonempty. wp_pures.
            wp_apply (bsize_better_spec with "Hfst") as "_".
            wp_pures.
            assert (bool_decide (#kFst = #0%nat) = false) as ->.
              { inversion bCfg; invert_all_in. }
            wp_pures.
            done.
          }
          iIntros "%TMP ->". iModIntro.
          wp_pures.
          wp_apply (bsize_better_spec with "Hfst") as "_".
          wp_pures.
          destruct (bool_decide (kFst = 3%nat)) eqn:?.
          * (* *) apply bool_decide_eq_true_1 in Heqb as Heqkfst.
            apply bool_decide_code_true in Heqb as deckfst.
            rewrite deckfst.
            wp_pures.
            wp_apply (bsize_better_spec with "Hmd1") as "_".
            wp_pures.
            iDestruct "sHsf1" as "[#rHsf1 %lHsf1]".
            wp_apply (bpop_spec with "rHsf1") as "%str'' #Hstr''".
            wp_pures.
            wp_alloc ℓr as "Hℓr".
            wp_pures.
            wp_apply (bsize_better_spec with "Hfst") as "_". wp_pures.
            wp_apply (bsize_better_spec with "Hlst") as "_". wp_pures.
            rewrite deckfst.
            wp_pures.
            inversion cfg. { exfalso. apply Heqmd. done. }
            wp_apply (bpop_spec2 with "Hmd") as "%a %m %oM (Hm & %HmdC)".
            wp_pures.
            wp_apply (binject_spec2 with "Hpr") as "%p' #Hp'".
            wp_pures.
            rewrite Heqkfst.
            wp_apply (bpop_spec2 with "Hfst") as "%b %x' %oX' (#Hx' & %HfstC)".
            wp_pures.
            wp_apply (binject_spec2 with "Hm") as "%m' #Hm'".
            wp_pures.
            wp_bind (push _)%E.
            rewrite /push.
            wp_pures.
            iDestruct (split_time 1 with "τ") as "[ι τ]". by lia.
            wp_apply (tick_spec with "ι") as "_".
            wp_pures.
            wp_load.
            wp_pures.
            wp_apply (bsize_better_spec with "Hmd1") as "_".
            wp_pures.
            wp_apply (bsize_spec with "Hstr''") as "_".
            simpl in lHsf1. inversion lHsf1.
            rewrite H12.
            wp_pures.
            assert (bool_decide (#kSf' = #8%nat) = false) as ->.
              { apply bool_decide_code_false, bool_decide_eq_false_2.
                intro; clear H3 H5.
                invert_all_in; lia.
              }
            wp_pures.
            wp_store.
            wp_bind (bpush _ _).
            wp_apply (bpush_spec with "Hstr''") as "%str''' #Hstr'''".
            wp_pures.
            iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
            wp_bind (ref _)%E.
            wp_apply (ssref_alloc π (fiveTuple π (S depth) _) with "[ι]") as "%ℓ'' #Hℓ''".
            { iExists pr1, ld1, md1, rd1, str''', oPr1, oLd1, oMd1, oRd1, _,
                kPr1, kMd1, (S kSf').
              rewrite -H -H0 -H1 -H2 -HeqsDepth.
              iFrame "#". iFrame.
              rewrite HeqsDepth.
              iSplitR. done.
              iSplitR.
              {
                iPureIntro.
                constructor.
                invert_all_in; list_elem_of.
              }
              iSplitL. by iApply three_time_enough.
              iSplitL.
              - iExists ((x',child,last)%V::str), ((oX'++childC++lastC)::strC).
                iSplitL. iExact "Hstr'''".
                iSplitL. iPureIntro. split.
                + done.
                + rewrite -Hlstr. by simpl.
                + iApply big_sepL2_cons.
                  iSplitL.
                  * rewrite -HeqsDepth. iNext.
                    rewrite triple_unfold.
                    iExists x', child, last, oX', childC, lastC, 2, kLst.
                    iSplitR.
                      { iPureIntro.
                        clear HkSf' H3 H5.
                        inversion bCfg; constructor; invert_all_in;
                        list_elem_of.
                      }
                    iSplitR. done.
                    rewrite HeqsDepth.
                    iFrame "#".
                    iPureIntro. done.
                  * iApply (big_sepL2_mono with "Hstrrest").
                    intros. iIntros "H". by iNext.
              - iPureIntro. done.
            }
            wp_pures.
            iFrame.
            iExists p', NONEV, m', (SOMEV #ℓ''), sf,
              (prC ++ oA), [], (oM ++ oB), _, sfC,
              (S kPr), 2, kSf.
            iModIntro.
            iFrame "#"; iFrame.
            iSplitR. done.
            iSplitR.
              { iPureIntro.
                clear HkSf'.
                constructor; invert_all_in; list_elem_of;
                exfalso; lia.
              }
            iSplitL. iApply three_time_enough.
              iDestruct (split_time 3 with "τ") as "[A _]"; by [lia | done].
            iSplitR. by isEmptyDeque.
            iSplitR. ℓisDeque ℓ''. by iExact "Hℓ''".
            iDestruct (empty_buffer_is_empty with "Hpr1") as "->".
            iDestruct (empty_buffer_is_empty with "Hmd1") as "->".
            destruct oLd1; [| inversion H].
            destruct oRd1; [| inversion H1].
            iPureIntro.
            rewrite Heq HmdC Ho1 Hos1 HoB HfstC /=.
            aac_reflexivity.
            *)
            admit.
          * apply bool_decide_eq_false_1 in Heqb as Heqkfst.
            apply bool_decide_code_false in Heqb as deckfst.
            rewrite deckfst.
            wp_pures.
            iDestruct (isDeque_unfold with "Hch") as "[[-> ->] | (%ℓi & -> & Hch')]"; wp_pures.
            --

End proof.
