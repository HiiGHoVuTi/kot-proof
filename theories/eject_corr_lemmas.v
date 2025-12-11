From iris.heap_lang Require Import lang proofmode notation.
From iris.bi Require Import derived_laws.

From Coq Require Import List.
Import ListNotations.

From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Deque Require Import common tick shared_ref deque_corr push_corr concat_corr pop_corr_lemmas.

Section lemmas.

  Context `{!heapGS Σ}.

  Variable NO_COST_ANALYSIS : TICK_COST = 0.

  (* Five-tuple configuration for calling naive_eject *)
  Inductive eject_configuration : nat -> nat -> nat -> nat -> nat -> Prop :=
    | eject_suffix_only : forall s, s ∈ [1..8] -> eject_configuration 0 0 0 0 s
    | eject_has_middle : forall p ld rd s, p ∈ [3..6] -> s ∈ [4..6] -> eject_configuration p ld 2 rd s.

 Definition isEjectFiveTuple := (
    λ o d, ∃ (pr ld md rd sf : val)
      pr_content left_content md_content right_content sf_content
      (kPr kMd kSf : nat) left_triples right_triples,
      ⌜ d = (pr, ld, md, rd, sf)%V ⌝ ∗
      ⌜ eject_configuration kPr (length left_content) kMd (length right_content) kSf ⌝ ∗
      buffer kPr pr_content pr ∗
      isDeque left_triples ld ∗
      buffer kMd md_content md ∗
      isDeque right_triples rd ∗
      buffer kSf sf_content sf ∗
      ([∗list] c;tr ∈ left_content;left_triples, ▷ triple c tr) ∗
      ([∗list] c;tr ∈ right_content;right_triples, ▷ triple c tr) ∗
      ⌜ o = pr_content ++ List.concat left_content ++ md_content ++ List.concat right_content ++ sf_content ⌝
  )%I.

 Definition isUnsafeEjectFiveTuple := (
    λ o d, ∃ (pr ld md rd sf : val)
      pr_content left_content md_content right_content sf_content
      (kPr : nat) left_triples right_triples,
      ⌜ d = (pr, ld, md, rd, sf)%V ⌝ ∗
      ⌜ five_tuple_configuration kPr (length left_content) 2 (length right_content) 3 ⌝ ∗
      buffer kPr pr_content pr ∗
      isDeque left_triples ld ∗
      buffer 2 md_content md ∗
      isDeque right_triples rd ∗
      buffer 3 sf_content sf ∗
      ([∗list] c;tr ∈ left_content;left_triples, ▷ triple c tr) ∗
      ([∗list] c;tr ∈ right_content;right_triples, ▷ triple c tr) ∗
      ⌜ o = pr_content ++ List.concat left_content ++ md_content ++ List.concat right_content ++ sf_content ⌝
  )%I.

  Lemma safe_decidable : forall o f,
    fiveTuple o f -∗
      (isUnsafeEjectFiveTuple o f ∗ WP naive_eject_safe f {{ x, ⌜ x = #false ⌝ }})
    ∨ isEjectFiveTuple o f ∗ WP naive_eject_safe f {{ x, ⌜ x = #true ⌝ }}.
  Proof.
    iIntros (o f) "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                      %kPr & %kMd & %kSf & %ltr & %rtr &
                      %Heq & %conf & #Hp & #Hl & #Hm & #Hr & #Hs &
                      #Hltr & #Hrtr & %Hoeq)".
    inversion conf.
    - iRight.
      iFrame.
      iSplitL.
      + iExists p, l, m, r, s, op, ol, om, or, os, 0, 0, kSf, ltr, rtr.
        iFrame "#".
        doneL.
        iSplit. iPureIntro. rewrite -H -H1. by easy_config.
        done.
      + rewrite /naive_eject_safe.
        rewrite Heq.
        wp_pures.
        wp_apply (bis_empty_spec with "Hm") as "_".
        wp_pures.
        done.
    - destruct (dec_eq_nat kSf 3) as [-> | HkSf]; [iLeft | iRight].
      + iSplitL.
        * iExists p, l, m, r, s, op, ol, om, or, os, kPr, ltr, rtr.
          iFrame "#". iFrame.
          doneL.
          rewrite {3}H3.
          iSplit; done.
        * rewrite /naive_eject_safe Heq.
          wp_pures.
          wp_apply (bis_empty_spec with "Hm") as "_".
          wp_pures.
          wp_apply (blength_spec with "Hs") as "_".
          wp_pures.
          done.
      + iSplitR.
        * iExists p, l, m, r, s, op, ol, om, or, os, kPr, kMd, kSf, ltr, rtr.
          rewrite -H3.
          iFrame. iFrame "#".
          doneL.
          iSplit. iPureIntro. apply eject_has_middle; invert_all_in.
          done.
        * rewrite /naive_eject_safe Heq.
          iFrame.
          wp_pures.
          wp_apply (bis_empty_spec with "Hm") as "_".
          wp_pures.
          wp_apply (blength_spec with "Hs") as "_".
          invert_all_in; wp_pures; done.
  Qed.

  Ltac suffix_only_incantation op om H H1 Hoeq :=
    iDestruct (buffer_length with "Hp") as "%LprC";
    destruct op; [| inversion LprC];
    iDestruct (buffer_length with "Hm") as "%LmdC";
    destruct om; [| inversion LmdC];
    symmetry in H; rewrite (nil_length_inv _ H) in Hoeq |- *;
    symmetry in H1; rewrite (nil_length_inv _ H1) in Hoeq |- *;
    iDestruct (big_sepL2_nil_inv_l with "Hltr") as "->";
    iDestruct (big_sepL2_nil_inv_l with "Hrtr") as "->".

  Lemma safe_naive_eject : forall o f,
    {{{ isEjectFiveTuple o f }}}
      naive_eject f
    {{{ x d o', RET (d, x)%V; isDeque o' d ∗ ⌜ o = o' ++ ⋅x ⌝ }}}.
  Proof.
    iIntros (o f ψ) "Hf Hψ".
    iDestruct "Hf" as "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                      %kPr & %kMd & %kSf & %ltr & %rtr &
                      -> & %conf & #Hp & #Hl & #Hm & #Hr & #Hs &
                      #Hltr & #Hrtr & %Hoeq)".
    rewrite /naive_eject.
    wp_pures.
    inversion conf; wp_pures.
    - suffix_only_incantation op om H H1 Hoeq.
      change (kSf ∈ map S [0;1;2;3;4;5;6;7]) in H3.
      assert (∃ kSf', kSf = kSf' + 1) as (kSf' & ->)
        by (invert_all_in;
        match goal with
        | |- ∃ kSf', S ?x = kSf' + 1 => exists x; lia
        end).
      wp_apply (beject_spec with "Hs") as "%b' %o' %x (#Hb & ->)".
      rewrite /assemble /assemble_.
      wp_pures.
      wp_apply (bis_empty_spec with "Hm") as "_". wp_pures.
      wp_apply (bis_empty_spec with "Hb") as "_".
      destruct kSf'; wp_pures.
      + iApply "Hψ".
        iDestruct (buffer_length with "Hb") as "%LbC".
        destruct o'; [| inversion LbC].
        iModIntro.
        iSplit.
        * by isEmptyDeque.
        * iPureIntro.
          rewrite Hoeq //.
      + wp_bind (ref _)%E.
        wp_apply (csref_alloc (fiveTuple o')) as "%ℓ'' #Hℓ''".
        * iExists p,l,m,r,b',[],[],[],[],o',0,0,(S kSf'),[],[].
          rewrite /concat !app_nil_l in Hoeq.
          iFrame. iFrame "#".
          doneL.
          assert (S kSf' ∈ [1..7]).
            { assert (S kSf' + 1 = S (S kSf')) as Heq by lia.
              rewrite Heq in H3.
              invert_all_in; list_elem_of.
            }
          clear H3.
          iSplit. iPureIntro. by constructor; invert_all_in; list_elem_of.
          do 2 doneL.
          iPureIntro.
          rewrite //.
        * wp_pures.
          iModIntro.
          iApply "Hψ".
          iSplit. by ℓisDeque ℓ''.
          iPureIntro. rewrite Hoeq //.
    - change (kSf ∈ map S [3;4;5]) in H0.
      apply decrease_in in H0 as (kS & -> & H0).
      wp_apply (beject_spec with "Hs") as "%b' %o' %x (#Hb' & ->)".
      rewrite /assemble.
      wp_pures.
      wp_apply (bis_empty_spec with "Hm") as "_".
      rewrite /assemble_.
      wp_pures.
      wp_apply (csref_alloc (fiveTuple _)) as "%ℓ'' #Hℓ''".
      + iExists p,l,m,r,b',op,ol,om,or,o',kPr,kMd,kS,ltr,rtr.
        rewrite -H3.
        iFrame. iFrame "#".
        doneL.
        iSplit. iPureIntro. by constructor; invert_all_in; list_elem_of.
        iSplit. iApply (big_sepL2_mono with "Hltr"). by auto.
        iSplit. iApply (big_sepL2_mono with "Hrtr"). by auto.
        done.
      + wp_pures.
        iModIntro.
        iApply "Hψ".
        iSplit. by ℓisDeque ℓ''.
        iPureIntro. rewrite Hoeq. aac_reflexivity.
  Qed.

  Lemma unsafe_naive_eject : forall o f,
    {{{ fiveTuple o f }}}
      naive_eject f
    {{{ x (d : val) o', RET (d, x)%V;
      ⌜ o = o' ++ ⋅x ⌝ ∗
      ∀ y : val,
        WP inject d y {{ d, isDeque (o' ++ ⋅y) d }}
    }}}.
  Proof.
    iIntros (o f ψ) "Hf Hψ".
    iDestruct "Hf" as "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                      %kPr & %kMd & %kSf & %ltr & %rtr &
                      -> & %conf & #Hp & #Hl & #Hm & #Hr & #Hs &
                      #Hltr & #Hrtr & %Hoeq)".
    rewrite /naive_eject.
    wp_pures.
    inversion conf; wp_pures.
    - suffix_only_incantation op om H H1 Hoeq.
      iClear "Hl Hr".
      change (kSf ∈ map S [0;1;2;3;4;5;6;7]) in H3.
      apply decrease_in in H3 as (ks & -> & Hks).
      wp_apply (beject_spec with "Hs") as (b' o' x) "[#Hb' %Hoeq']".
      rewrite /assemble.
      wp_pures.
      wp_apply (bis_empty_spec with "Hm") as "_".
      wp_pures.
      wp_apply (bis_empty_spec with "Hb'") as "_".
      inversion Hks; wp_pures.
      + iApply "Hψ".
        iModIntro.
        iSplit.
        * iPureIntro.
          aac_rewrite Hoeq.
          rewrite //.
        * iIntros (y).
          rewrite /inject.
          wp_pures.
          wp_apply (tick_spec) as "_".
            { rewrite NO_COST_ANALYSIS time_zero //. }
          rewrite /asingleton.
          wp_pures.
          wp_apply (bpush_spec) as (b) "Hb". by iApply bempty_spec.
          wp_pures.
          wp_apply (csref_alloc (fiveTuple [y]) with "[Hb]") as (ℓ) "Hℓ".
            { iExists bempty, NONEV, bempty, NONEV, b, [], [], [], [], [y], 0, 0, 1, [], [].
              iFrame. iFrame "#".
              repeat doneL.
              iSplit. by easy_config.
              repeat (iSplit; [iApply bempty_spec || isEmptyDeque |]).
              do 2 doneL.
              done.
            }
          wp_pures.
          iModIntro.
          rewrite /=.
          iDestruct (buffer_length with "Hs") as "%Hos".
          destruct os; [inversion Hos |].
          destruct os; [| inversion Hos].
          destruct o'; [| inversion Hoeq'].
          -- ℓisDeque ℓ.
            iExact "Hℓ".
          -- exfalso.
            symmetry in H9.
            apply app_nil_r_inv in H9.
            inversion H9.
      + clear Hks.
        assert (bool_decide (ks = 0%nat) = false) as -> by invert_all_in.
        rewrite /assemble_.
        wp_pures.
        wp_alloc ℓ as "Hℓ".
        wp_pures.
        iModIntro.
        iApply "Hψ".
        iSplit. iPureIntro; aac_rewrite Hoeq; by rewrite //.
        iIntros (y').
        rewrite /inject.
        wp_pures.
        wp_apply (tick_spec) as "_".
          { rewrite NO_COST_ANALYSIS time_zero //. }
        wp_pures.
        wp_load.
        wp_pures.
        wp_apply (bis_empty_spec with "Hm") as "_".
        wp_pures.
        wp_apply (bhas_length_8_spec with "Hb'") as "_".
        assert (bool_decide (ks = 8%nat) = false) as -> by invert_all_in.
        wp_pures.
        wp_store.
        rewrite /assemble_.
        wp_apply (binject_spec with "Hb'") as (b) "Hb".
        wp_pures.
        wp_apply (csref_alloc (fiveTuple (o' ++ ⋅y')) with "[Hb]") as (ℓ') "Hℓ'".
          { iExists bempty, NONEV, bempty, NONEV, b, [], [], [], [], (o'++⋅y'), 0, 0, (ks+1), [], [].
            iFrame. iFrame "#".
            repeat doneL.
            iSplit. rewrite H H1 -H0 -H2 in conf. done.
            repeat (iSplit; [iApply bempty_spec || isEmptyDeque |] || doneL).
            done.
          }
        wp_pures.
        iModIntro.
        rewrite /=.
        ℓisDeque ℓ'.
        iExact "Hℓ'".
    - change (kSf ∈ map S [2; 3; 4; 5]) in H0.
      apply decrease_in in H0 as (ks & -> & Hks).
      wp_apply (beject_spec with "Hs") as "%b' %o' %x (#Hb' & ->)".
      rewrite /assemble.
      wp_pures.
      wp_apply (bis_empty_spec with "Hm") as "_".
      rewrite /assemble_.
      wp_pures.
      wp_alloc ℓ as "Hℓ".
      wp_pures.
      iModIntro.
      iApply ("Hψ" $! x (SOMEV #ℓ) (op ++ concat ol ++ om ++ concat or ++ o')).
      iSplit. iPureIntro. rewrite Hoeq. aac_reflexivity.
      iIntros (y).
      rewrite /inject.
      wp_pures.
      wp_apply (tick_spec) as "_".
        { rewrite NO_COST_ANALYSIS time_zero //. }
      wp_pures.
      wp_load.
      wp_pures.
      wp_apply (bis_empty_spec with "Hm") as "_".
      wp_pures.
      wp_apply (bhas_length_6_spec with "Hb'") as "_".
      assert (bool_decide (ks = 6%nat) = false) as  -> by invert_all_in.
      wp_pures.
      wp_store.
      rewrite /assemble_.
      wp_apply (binject_spec with "Hb'") as "%p' #Hp'".
      wp_pures.
      wp_apply (csref_alloc (fiveTuple (op ++ concat ol ++ om ++ concat or ++ o' ++ ⋅y))) as "%ℓ' Hℓ'".
      + iExists p,l,m,r,p',op,ol,om,or,(o'++⋅y),kPr,2,(ks+1),ltr,rtr.
        iFrame "#".
        doneL.
        iSplit. iPureIntro. rewrite H3. done.
        iSplit. iApply (big_sepL2_mono with "Hltr"). by auto.
        iSplit. iApply (big_sepL2_mono with "Hrtr"). by auto.
        repeat doneL.
        done.
      + wp_pures.
        iModIntro.
        rewrite -!app_assoc.
        ℓisDeque ℓ'.
        iExact "Hℓ'".
  Qed.

  Lemma destruct_end {A} : forall (θ : list A),
    θ = [] ∨ ∃ θ' e, θ = θ' ++ ⋅e.
  Proof.
    induction θ.
    - by left.
    - assert (a :: θ = ⋅a ++ θ) as -> by reflexivity.
      right.
      destruct IHθ as [-> | (o & e & ->)].
      + by exists [], a.
      + by exists (⋅a++o), e.
  Qed.

  Lemma inspect_last_spec : forall o f,
    {{{ fiveTuple o f }}}
      inspect_last f
    {{{ o' t, RET t; ⌜ o = o' ++ ⋅t ⌝  }}}.
  Proof.
    iIntros (o f ψ) "Hf Hψ".
    iDestruct "Hf" as "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                      %kPr & %kMd & %kSf & %ltr & %rtr &
                      -> & %conf & #Hp & #Hl & #Hm & #Hr & #Hs &
                      #Hltr & #Hrtr & %Hoeq)".
    rewrite /inspect_last. wp_pures.
    inversion conf; wp_pures.
    - change (kSf ∈ map S [0;1;2;3;4;5;6;7]) in H3.
      apply decrease_in in H3 as (kS & -> & HkS).
      destruct (destruct_end os) as [-> | (os' & x & ->)].
        { iDestruct (buffer_length with "Hs") as "%abs".
          simpl in abs; lia. }
      wp_apply (blast_spec with "Hs") as "_".
      iApply "Hψ".
      suffix_only_incantation op om H H1 Hoeq.
      iPureIntro.
      rewrite Hoeq //.
    - change (kSf ∈ map S [2;3;4;5]) in H0.
      apply decrease_in in H0 as (kS & -> & HkS).
      destruct (destruct_end os) as [-> | (os' & x & ->)].
        { iDestruct (buffer_length with "Hs") as "%abs".
          simpl in abs; lia. }
      wp_apply (blast_spec with "Hs") as "_".
      iApply "Hψ".
      iPureIntro.
      rewrite Hoeq !app_assoc //.
  Qed.

  Inductive special_triple_configuration : nat -> nat -> nat -> Prop :=
    | is_special_three : forall x, x ∈ [0; 2; 3] -> special_triple_configuration x 0 3
    | is_special_child : forall x o y, x ∈ [2; 3] -> o > 0 -> y ∈ [2; 3] -> special_triple_configuration x o y
    | is_special_first : forall x o y, x ∈ [2; 3] -> y ∈ [2; 3] -> special_triple_configuration x o y.

  Inductive not_special_triple_configuration : nat -> nat -> nat -> Prop :=
    | is_bad : not_special_triple_configuration 0 0 2.

  Definition isSpecialTriple := (
    λ o t,
      ∃ (fst ch lst : val)
        fst_content child_content lst_content
        (kFst kLst : nat) triples,
        ⌜ special_triple_configuration kFst (length child_content) kLst ⌝ ∗
        ⌜ t = (fst, ch, lst)%V ⌝ ∗
        buffer kFst fst_content fst ∗
        isDeque triples ch ∗
        buffer kLst lst_content lst ∗
        ([∗list] c;tr ∈ child_content;triples, ▷ triple c tr) ∗
        ⌜ o = fst_content ++ List.concat child_content ++ lst_content ⌝
  )%I.

  Definition isNotSpecialTriple := (
    λ o t,
      ∃ (fst ch lst : val)
        fst_content child_content lst_content
        (kFst kLst : nat) triples,
        ⌜ not_special_triple_configuration kFst (length child_content) kLst ⌝ ∗
        ⌜ t = (fst, ch, lst)%V ⌝ ∗
        buffer kFst fst_content fst ∗
        isDeque triples ch ∗
        buffer kLst lst_content lst ∗
        ([∗list] c;tr ∈ child_content;triples, ▷ triple c tr) ∗
        ⌜ o = fst_content ++ List.concat child_content ++ lst_content ⌝
  )%I.

  Lemma antinormalize_special_spec : forall o t,
    {{{ @pop_corr_lemmas.isSpecialTriple Σ _  o t }}}
      antinormalize t
    {{{ t', RET t'; isSpecialTriple o t' }}}.
  Proof.
    iIntros (o t ψ) "Ht Hψ".
    iDestruct "Ht" as (f c l fc cc lc kFst kLst tr) "(%conf & -> & #Hf & #Hc & #Hl & Htr & %Hoeq)".
    rewrite /antinormalize.
    inversion conf; wp_pures; wp_apply (bis_empty_spec with "Hl") as "_"; wp_pures.
    - inversion H1.
      + wp_pures.
        iApply "Hψ". iModIntro.
        iDestruct (buffer_length with "Hl") as "%H'".
        destruct lc; [| inversion H'].
        destruct cc; [| inversion H].
        iDestruct (big_sepL2_nil_inv_l with "Htr") as "->".
        iExists bempty, c, f, [], [], fc, 0, kFst, [].
        rewrite -H0.
        iFrame "#".
        iSplitR. iPureIntro. simpl. by easy_config.
        doneL.
        iSplitR. by iApply bempty_spec.
        doneL.
        iPureIntro.
        rewrite Hoeq /= app_nil_r //.
      + assert (bool_decide (kLst = 0%nat) = false) as -> by invert_all_in.
        wp_pures.
        iApply "Hψ". iModIntro.
        destruct cc; [| inversion H].
        iDestruct (big_sepL2_nil_inv_l with "Htr") as "->".
        iExists f, c, l, fc, [], lc, kFst, kLst, [].
        rewrite -H0.
        iFrame "#".
        iSplitR. iPureIntro. simpl. by easy_config.
        doneL.
        doneL.
        done.
    - assert (bool_decide (kLst = 0%nat) = false) as -> by invert_all_in.
      wp_pures.
      iApply "Hψ". iModIntro.
      iExists f, c, l, fc, cc, lc, kFst, kLst, tr.
      iFrame "#".
      iSplitR. iPureIntro. simpl. by easy_config.
      doneL.
      iSplitL. iApply (big_sepL2_mono with "Htr"). by auto.
      done.
    - assert (bool_decide (kLst = 0%nat) = false) as -> by invert_all_in.
      wp_pures.
      iApply "Hψ". iModIntro.
      iExists f, c, l, fc, cc, lc, kFst, kLst, tr.
      iFrame "#".
      iSplitR. iPureIntro. simpl. by easy_config.
      doneL.
      iSplitL. iApply (big_sepL2_mono with "Htr"). by auto.
      done.
  Qed.

  Lemma antinormalize_not_special_spec : forall o t,
    {{{ @pop_corr_lemmas.isNotSpecialTriple Σ _ o t }}}
      antinormalize t
    {{{ t', RET t'; isNotSpecialTriple o t' }}}.
  Proof.
    iIntros (o t ψ) "Ht Hψ".
    iDestruct "Ht" as (f c l fc cc lc kFst kLst tr) "(%conf & -> & #Hf & #Hc & #Hl & Htr & %Hoeq)".
    rewrite /antinormalize.
    inversion conf; wp_pures; wp_apply (bis_empty_spec with "Hl") as "_"; wp_pures.
    iModIntro.
    iApply "Hψ".
    iDestruct (buffer_length with "Hl") as "%H'".
    destruct lc; [| inversion H'].
    destruct cc; [| inversion H1].
    iDestruct (big_sepL2_nil_inv_l with "Htr") as "->".
    iExists bempty, c, f, [], [], fc, 0, kFst, [].
    rewrite -H.
    iFrame "#".
    iSplitR. iPureIntro. simpl. by easy_config.
    doneL.
    iSplitR. by iApply bempty_spec.
    doneL.
    iPureIntro.
    rewrite Hoeq /= app_nil_r //.
  Qed.

  Definition isPersFiveTupleLaterRemoved := (
    λ o d, ∃ (pr ld md rd sf : val)
      pr_content left_content md_content right_content sf_content
      (kPr kMd kSf : nat) left_triples right_triples,
      ⌜ d = (pr, ld, md, rd, sf)%V ⌝ ∗
      ⌜ five_tuple_configuration kPr (length left_content) kMd (length right_content) kSf ⌝ ∗
      buffer kPr pr_content pr ∗
      isDeque left_triples ld ∗
      buffer kMd md_content md ∗
      isDeque right_triples rd ∗
      buffer kSf sf_content sf ∗
      ([∗list] c;tr ∈ left_content;left_triples, triple c tr) ∗
      ([∗list] c;tr ∈ right_content;right_triples, triple c tr) ∗
      ⌜ o = pr_content ++ List.concat left_content ++ md_content ++ List.concat right_content ++ sf_content ⌝
  )%I.

  Lemma add_later : forall o d, isPersFiveTupleLaterRemoved o d -∗ fiveTuple o d.
  Proof.
    iIntros (o d) "Hd".
    iDestruct "Hd" as (p l m r s op ol om or os kp km ks ltr rtr)
      "(-> & conf & hp & hl & hm & hr & hs & hltr & hrtr & heq)".
    iExists p, l, m, r, s, op, ol, om, or, os, kp, km, ks, ltr, rtr.
    iFrame.
    doneL.
    iSplitL "hltr".
    - iApply (big_sepL2_mono with "hltr"). by auto.
    - iApply (big_sepL2_mono with "hrtr"). by auto.
  Qed.

  Lemma app_sing_inv {A} : forall (o o' : list A) (x y : A),
    o ++ ⋅x = o' ++ ⋅y -> o = o' ∧ x = y.
  Proof.
    induction o; intros.
    - rewrite app_nil_l in H.
      apply (f_equal length) in H as H'.
      rewrite length_app /= in H'.
      assert (length o' = 0) by lia.
      destruct o'.
      + by inversion H.
      + simpl in H0. lia.
    - destruct o'. inversion H.
      + apply (f_equal length) in H2.
        rewrite length_app /= in H2.
        lia.
      + rewrite -!app_comm_cons in H.
        inversion H.
        by specialize (IHo o' x y H2) as [-> ->].
  Qed.

  Lemma eject_triple_spec : forall os tr ℓ,
    {{{ ℓ ⤇ fiveTuple tr
      ∗ ([∗list] x;y ∈ os;tr, triple x y)
      ∗ (∀ ℓ x o,
          ℓ ⤇ fiveTuple (o ++ ⋅x) -∗
          WP eject_nonempty #ℓ
            {{ r, ∃ d, ⌜ r = (d, x)%V ⌝ ∗ isDeque o d }})
    }}}
      subst "eject_nonempty" eject_nonempty (eject_triple #ℓ)
    {{{ t' t o tr' os' (d' : val), RET (d', t)%V;
      ⌜ tr = tr' ++ ⋅t' ∧ os = os' ++ ⋅o ⌝ ∗
      ([∗list] x;y ∈ os';tr', triple x y) ∗
      ( isSpecialTriple o t ∗ (∀ x : val, WP inject d' x {{ d'', isDeque (tr' ++ ⋅x) d'' }})
      ∨ isNotSpecialTriple o t ∗ isDeque tr' d'
      )
    }}}.
  Proof.
    iIntros (os tr d Hψ) "(#Hd & Htr & iH) Hψ".
    rewrite /pop_triple.
    wp_pures.
    Opaque fiveTuple.
    wp_apply (csref_load with "Hd").
    iIntros (f) "#Hf".
    wp_pures.
    wp_apply (inspect_last_spec with "[Hf]").
      { iExact "Hf". }
    iIntros (o t) "->".
    wp_pures.
    destruct (destruct_end os) as [-> | (os' & l &  ->)].
      iDestruct (big_sepL2_nil_inv_l with "Htr") as "%No".
        apply app_nil_r_inv in No.
        inversion No.
    rename os' into os.
    iDestruct (big_sepL2_app_inv with "Htr") as "(Htr & Ht)". by right.
    iAssert (triple l t) with "[Ht]" as "Ht".
      { simpl. iDestruct "Ht" as "[A _]". done. }
    iDestruct (pop_corr_lemmas.special_decidable NO_COST_ANALYSIS with "Ht") as "[#Ht' | #Ht']";
    iCombine "Ht' Ht'" as "[Ht! Ht!']";
    iDestruct "Ht!'" as (fi c la fc cc lc kF kL tr) "(%conf & -> & Hf' & Hc & Hl & Htrtr & %Hleq)";
    inversion conf.
    Opaque pop_corr_lemmas.isSpecialTriple pop_corr_lemmas.isNotSpecialTriple isSpecialTriple isNotSpecialTriple.
    + rewrite isDeque_unfold.
      iDestruct "Hc" as "[[-> ->] | (%ℓ & -> & Hℓ)]".
      2: {
        wp_bind (Fst _)%V.
        iInv "Hℓ" as "(%v' & Hv' & Hℓ')".
        wp_pure.
        iExFalso.
        iDestruct "Hv'" as (pr' ld' md' rd' sf' pc' lc' mc' rc' sc' kp' km' ks' lt rt) "(_ & %conf' & _ & _ & _ & _ & Hs & _ & _ & ->)".
        iDestruct (big_sepL2_length with "Htrtr") as "%Hlen".
        rewrite Hlen in H.
        iDestruct (buffer_length with "Hs") as "%Hslen".
        assert (ks' > 0) as Hslen' by (inversion conf'; invert_all_in; lia).
        rewrite !length_app in H.
        lia.
      }
      wp_pures.
      wp_apply (bhas_length_3_spec with "Hf'") as "_".
      wp_pures.
      wp_apply (unsafe_naive_eject).
        { iFrame.
              by iExact "Hf". }
      iIntros (x' d' o') "(%Hoeq' & Hpush)".
      wp_pures.
      apply app_sing_inv in Hoeq' as [-> <-].
      wp_apply (antinormalize_special_spec with "Ht!") as (t') "Ht''".
      wp_pures. iModIntro.
      iApply "Hψ".
      doneL.
      iSplit. iExact "Htr".
      iLeft.
      iSplitL "Ht''".
      * iExact "Ht''".
      * iExact "Hpush".
    + (* NOTE(Juliette): dedup *)
      wp_pures.
      rewrite isDeque_unfold.
      iDestruct "Hc" as "[[-> ->] | (%ℓ & -> & Hℓ)]".
        { iDestruct (big_sepL2_nil_inv_r with "Htrtr") as "->". inversion H0. }
      wp_pures.
      wp_apply (bhas_length_3_spec with "Hf'") as "_".
      assert (kF = 2 ∨ kF = 3) as [-> | ->] by invert_all_in; wp_pures.
      * wp_apply (bis_empty_spec with "Hl") as "_".
        assert (bool_decide (kL = 0%nat) = false) as -> by invert_all_in.
        wp_pures.
        wp_apply (unsafe_naive_eject).
          { iFrame.
                by iExact "Hf". }
        iIntros (x' d' o') "(%Hoeq' & Hpush)".
        wp_pures.
        apply app_sing_inv in Hoeq' as [-> <-].
        wp_apply (antinormalize_special_spec with "Ht!") as (t') "Ht''".
        wp_pures. iModIntro.
        iApply "Hψ".
        iFrame.
        doneL.
        iLeft.
        iSplitL "Ht''".
        -- iExact "Ht''".
        -- iExact "Hpush".
      * wp_apply (unsafe_naive_eject).
          { iFrame.
                by iExact "Hf". }
        iIntros (x' d' o') "(%Hoeq' & Hpush)".
        wp_pures.
        apply app_sing_inv in Hoeq' as [-> <-].
        wp_apply (antinormalize_special_spec with "Ht!") as (t') "Ht''".
        wp_pures. iModIntro.
        iApply "Hψ".
        iFrame.
        doneL.
        iLeft.
        iSplitL "Ht''".
        -- iExact "Ht''".
        -- iExact "Hpush".
    + wp_pures.
      rewrite isDeque_unfold.
      wp_pures.
      wp_apply (bhas_length_3_spec with "Hf'") as "_".
      wp_pures.
      assert (kF = 2 ∨ kF = 3) as [-> | ->] by invert_all_in; wp_pures.
      * wp_apply (bis_empty_spec with "Hl") as "_".
        wp_pures.
        assert (bool_decide (kL = 0%nat) = false) as -> by invert_all_in.
        wp_pures.
        wp_apply (unsafe_naive_eject).
          { iFrame.
                by iExact "Hf". }
        iIntros (x' d' o') "(%Hoeq' & Hpush)".
        wp_pures.
        apply app_sing_inv in Hoeq' as [-> <-].
        wp_apply (antinormalize_special_spec with "Ht!") as (t') "Ht''".
        wp_pures. iModIntro.
        iApply "Hψ".
        iFrame.
        doneL.
        iLeft.
        iSplitL "Ht''".
        -- iExact "Ht''".
        -- iExact "Hpush".
      * wp_apply (unsafe_naive_eject).
          { iFrame.
                by iExact "Hf". }
        iIntros (x' d' o') "(%Hoeq' & Hpush)".
        wp_pures.
        apply app_sing_inv in Hoeq' as [-> <-].
        wp_apply (antinormalize_special_spec with "Ht!") as (t') "Ht''".
        wp_pures. iModIntro.
        iApply "Hψ".
        iFrame.
        doneL.
        iLeft.
        iSplitL "Ht''".
        -- iExact "Ht''".
        -- iExact "Hpush".
    + wp_pures.
      wp_apply (bhas_length_3_spec with "Hf'") as "_".
      wp_pures.
      wp_apply (bis_empty_spec with "Hl") as "_".
      wp_pures.
      wp_bind  (eject_nonempty _)%E.
      iApply (wp_strong_mono with "[iH]").
        { auto. } { reflexivity. }
      * iApply ("iH" with "[]"). iExact "Hd".
      * iIntros (v) "(%d' & -> & Hd')". iModIntro.
        wp_pures.
        wp_apply (antinormalize_not_special_spec with "Ht!") as (t') "Ht''".
        wp_pures. iModIntro.
        iApply "Hψ".
        iFrame. doneL.
        iRight.
        iFrame.
  Qed.

  Lemma prepare_eject_spec : forall o f,
    {{{ isUnsafeEjectFiveTuple o f ∗
      ∀ ℓ x o', ℓ ⤇ fiveTuple (o' ++ ⋅x) -∗
        WP eject_nonempty #ℓ {{ r, ∃ d, ⌜ r = (d, x)%V ⌝ ∗ isDeque o' d }}
    }}}
      subst "eject_nonempty" eject_nonempty (prepare_eject f)
    {{{ f', RET f'; isEjectFiveTuple o f' }}}.
  Proof.
    Opaque eject_triple.
    iIntros (o f ψ) "(Hf & iH) Hψ".
    rewrite /isUnsafeEjectFiveTuple.
    iDestruct "Hf" as "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                      %kPr & %ltr & %rtr &
                      -> & %conf & #Hp & #Hl & #Hm & #Hr & #Hs &
                      #Hltr & #Hrtr & %Hoeq)".
    rewrite /prepare_eject.
    wp_pures.
    inversion conf.
    do 2 rewrite isDeque_unfold.
    Notation selpat := "[[-> ->] | (%ℓ & -> & Hℓ)]".
    iDestruct "Hr" as selpat;
    [iDestruct "Hl" as selpat |].
    - wp_pures.
      wp_apply (bhas_length_3_spec with "Hp") as "_".
      iDestruct (big_sepL2_nil_inv_r with "Hltr") as "->";
      iDestruct (big_sepL2_nil_inv_r with "Hrtr") as "->".
      inversion H; wp_pures.
      + wp_apply (bconcat323_spec with "[Hp Hm Hs]") as "%b' Hb8". by iFrame "#".
        wp_pures.
        iApply "Hψ".
        iModIntro.
        * iExists bempty, NONEV, bempty, NONEV, b', [], [], [], [], (op++om++os),
            0, 0, 8, [], [].
          iFrame. iFrame "#".
          doneL.
          iSplit. by easy_config.
          iSplit. by (iApply bempty_spec).
          iSplit. by isEmptyDeque.
          iSplit. by (iApply bempty_spec).
          iSplit. by isEmptyDeque.
          repeat doneL.
          iPureIntro.
          aac_rewrite Hoeq.
          by rewrite //.
      + assert (bool_decide (kPr = 3%nat) = false) as ->.
        { clear H H0. invert_all_in. }
        wp_pures.
        change (kPr ∈ map S [3;4;5]) in H7.
        apply decrease_in in H7 as (k & -> & Hk).
        clear H H0 H6.
        wp_apply (bdouble_move_right_spec with "[Hp Hm Hs]"). by iFrame "#".
        iIntros (b1 b2 b3 o1 o2 o3) "(#H1 & #H2 & #H3 & %Heq)".
        wp_pures.
        iModIntro.
        iApply "Hψ".
        iExists b1, NONEV, b2, NONEV, b3, o1, [], o2, [], o3,
          k, 2, 4, [], [].
        iFrame. iFrame "#".
        doneL.
        iSplit. iPureIntro. constructor; invert_all_in; list_elem_of.
        iSplit. by isEmptyDeque.
        iSplit. by isEmptyDeque.
        repeat doneL.
        iPureIntro.
        aac_rewrite Hoeq.
        rewrite //.
    - wp_pures.
      iDestruct (big_sepL2_nil_inv_r with "Hrtr") as "->".
      wp_bind (let: "f" := _ in _)%E.
      wp_apply (eject_triple_spec with "[iH]").
      + iSplit. iExact "Hℓ".
        iSplit. iExact "Hltr".
        iApply "iH".
      + Transparent isSpecialTriple.
        iIntros (t' t o' rtr' os' d') "([-> ->] & Htr' & [(#Ht & Hd') | (Ht & Hd')])".
          (* appeler la spec de pop_case_2_special *)
        * iDestruct "Ht" as (fi c la fc cc lc kF kL tr) "(%tconf & -> & #Hfi & #Hc & #Hla & #Htrtr & %Hleq)".
          wp_pures.
          wp_apply (bhas_length_3_spec with "Hla") as "_".
          inversion tconf; wp_pures.
          -- wp_apply (bdouble_move_right_spec) as (b1 b2 b3 o1 o2 o3) "(#H1 & #H2 & #H3 & %Hoeq')".
            { assert (3 = 2 + 1) as -> by reflexivity.
              iFrame "#". }
            rewrite /atriple.
            wp_pures.
            wp_apply (bis_empty_spec with "Hfi") as "_".
            inversion H7; rewrite /atriple_.
            ++ wp_pures.
              wp_bind (inject _ _)%E.
              iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
              iIntros (l') "Hl'".
              iModIntro. wp_pures.
              iModIntro.
              iApply "Hψ".
              iExists p, l', b2, NONEV, b3,
                op, (os' ++ ⋅(o1++List.concat cc)), o2, [], o3, kPr, 2, 4,
                (rtr' ++ ⋅(b1, c, bempty)%V), [].
              doneL.
              iFrame "#". iFrame.
              iSplit. iPureIntro. by easy_config.
              iSplit. by isEmptyDeque.
              iSplit; [ iApply (big_sepL2_app) |].
              ** iDestruct (big_sepL2_app_inv with "Hltr") as "[Hrtr' _]". by right.
                iApply (big_sepL2_mono with "Hrtr'"). by auto.
              ** simpl; doneR.
                iNext. iClear "Hrtr".
                rewrite triple_unfold.
                iExists b1, c, bempty, o1, cc, [], 2, 0, tr.
                iSplit. iPureIntro. rewrite -H3. by easy_config.
                doneL. iFrame "#".
                iSplit. by iApply bempty_spec.
                iSplit. iApply (big_sepL2_mono with "Htrtr"). by auto.
                iPureIntro.
                rewrite app_nil_r //.
              ** doneL.
                iDestruct (buffer_length with "Hfi") as "%Hlfi".
                destruct fc; [| inversion Hlfi].
                destruct cc; [| inversion H3].
                iPureIntro.
                rewrite Hoeq /= Hleq !concat_app /= app_nil_r.
                aac_rewrite Hoeq'.
                aac_reflexivity.
            ++ assert (bool_decide (kF = 0%nat) = false) as -> by invert_all_in.
              wp_pures.
              wp_bind (inject _ _)%E.
              iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
              iIntros (l') "Hl'".
              iModIntro. wp_pures.
              iModIntro.
              iApply "Hψ".
              iExists p, l', b2, NONEV, b3,
                op, (os' ++ ⋅(fc ++ List.concat cc ++ o1)), o2, [], o3, kPr, 2, 4,
                (rtr' ++ ⋅(fi, c, b1)%V), [].
              doneL.
              iFrame "#". iFrame.
              iSplit. iPureIntro. by easy_config.
              iSplit. by isEmptyDeque.
              iSplit; [ iApply (big_sepL2_app) |].
              ** iDestruct (big_sepL2_app_inv with "Hltr") as "[Hrtr' _]". by right.
                iApply (big_sepL2_mono with "Hrtr'"). by auto.
              ** simpl; doneR.
                iNext. iClear "Hrtr".
                rewrite triple_unfold.
                iExists fi, c, b1, fc, cc, o1, kF, 2, tr.
                iSplit. iPureIntro. rewrite -H3. by easy_config.
                doneL. iFrame "#".
                iSplit. iApply (big_sepL2_mono with "Htrtr"). by auto.
                iPureIntro.
                rewrite //.
              ** doneL.
                iDestruct (buffer_length with "Hfi") as "%Hlfi".
                destruct cc; [| inversion H3].
                iPureIntro.
                rewrite Hoeq /= Hleq !concat_app /= app_nil_r.
                aac_rewrite Hoeq'.
                aac_reflexivity.
          -- assert (kL = 2 ∨ kL = 3) as HkL by (clear H H0 H8; invert_all_in).
            destruct HkL as [-> | ->]; wp_pures.
            ++ wp_apply (bconcat23_spec with "[Hm Hs]") as (b') "Hb'". by iFrame "#".
              wp_pures.
              rewrite isDeque_unfold.
              iDestruct "Hc" as "[[_ ->] | (%ℓc & -> & Hℓc)]".
                { iDestruct (big_sepL2_nil_inv_r with "Htrtr") as "->". inversion H6. }
              wp_pures.
              wp_apply (abuffer_spec_explicit with "Hfi") as "Ht". by assumption.
              wp_pures.
              wp_bind (inject _ _)%E.
              iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
              iIntros (l') "Hl'".
              iModIntro. wp_pures.
              wp_apply (dconcat_spec_helper with "[Hℓc Hl']") as (l) "Hl".
                { assumption. }
                { iFrame. ℓisDeque ℓc. iExact "Hℓc". }
              wp_pures.
              iModIntro.
              iApply "Hψ".
              iExists p, l, la, NONEV, b', op, ((os'++⋅fc)++cc), lc, [], (om++os),
                kPr, 2, 5, ((rtr'++⋅(fi, NONEV, bempty)%V)++tr), [].
              doneL.
              iSplit. iPureIntro. by easy_config.
              iFrame. iFrame "#".
              iSplit. by isEmptyDeque.
              iSplit.
              ** iSplit. doneR.
                iApply (big_sepL2_mono with "Htr'"). by auto.
                iApply (big_sepL2_mono with "Htrtr"). by auto.
              ** doneL. iPureIntro.
                rewrite !concat_app Hoeq Hleq /= !app_nil_r !concat_app /=.
                aac_reflexivity.
            ++ wp_apply (bdouble_move_right_spec with "[Hla Hm Hs]").
                { iFrame "#". assert (3 = 2 + 1) as -> by reflexivity. done. }
             iIntros (b1 b2 b3 o1 o2 o3) "(H1 & H2 & #H3 & %Hnoeq)".
              rewrite /atriple.
              wp_pures.
              wp_apply (bis_empty_spec with "Hfi") as "_".
              assert (bool_decide (kF = 0%nat) = false) as -> by invert_all_in.
              rewrite /atriple_.
              wp_pures.
              wp_bind (inject _ _)%E.
              iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
              iIntros (l') "Hl'".
              iModIntro.
              wp_pures.
              iModIntro. iApply "Hψ".
              iExists p, l', b2, NONEV, b3,
                op, (os'++⋅(fc++List.concat cc++o1)), o2, [], o3,
                kPr, 2, 4, (rtr'++⋅(fi, c, b1)%V), [].
              doneL.
              iSplit. iPureIntro. simpl. by easy_config.
              iFrame "#". iFrame.
              iSplit. by isEmptyDeque.
              iSplit; [ iApply (big_sepL2_app with "[Htr']") | doneL ].
              ** iApply (big_sepL2_mono with "Htr'"). by auto.
              ** simpl. doneR. iNext.
                rewrite !triple_unfold.
                iExists fi, c, b1, fc, cc, o1, kF, 2, tr.
                iSplit. iPureIntro. by easy_config.
                doneL.
                iFrame . iFrame "#".
                iSplit. iApply (big_sepL2_mono with "Htrtr"). by auto.
                done.
              ** iPureIntro.
                rewrite !concat_app Hoeq Hleq /= !app_nil_r concat_app /=.
                aac_rewrite Hnoeq.
                aac_reflexivity.
          -- assert (kL = 2 ∨ kL = 3) as HkL by (clear H H0 H8; invert_all_in).
            destruct HkL as [-> | ->]; wp_pures.
            ++ wp_apply (bconcat23_spec with "[Hm Hs]") as (b') "Hb'". by iFrame "#".
              wp_pures.
              destruct (bool_decide (c = NONEV)); wp_pures.
              ** wp_apply (bis_empty_spec with "Hfi") as "_".
                assert (bool_decide (kF = 0%nat) = false) as -> by invert_all_in.
                wp_pures.
                wp_apply (abuffer_spec_explicit with "Hfi") as "Ht". by assumption.
                wp_pures.
                wp_bind (inject _ _)%E.
                iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
                iIntros (l') "Hl'".
                iModIntro. wp_pures.
                wp_apply (dconcat_spec_helper with "[Hc Hl']") as (l) "Hl".
                  { assumption. }
                  { iFrame. by iFrame "#". }
                wp_pures.
                iModIntro.
                iApply "Hψ".
                iExists p, l, la, NONEV, b', op, ((os'++⋅fc)++cc), lc, [], (om++os),
                kPr, 2, 5, ((rtr'++⋅(fi, NONEV, bempty)%V)++tr), [].
                doneL.
                iSplit. iPureIntro. by easy_config.
                iFrame. iFrame "#".
                iSplit. by isEmptyDeque.
                iSplit.
                --- iSplit. doneR.
                  iApply (big_sepL2_mono with "Htr'"). by auto.
                  iApply (big_sepL2_mono with "Htrtr"). by auto.
                --- doneL. iPureIntro.
                  rewrite !concat_app Hoeq Hleq /= !app_nil_r !concat_app /=.
                  aac_reflexivity.
              ** wp_apply (abuffer_spec_explicit with "Hfi") as "Ht". by assumption.
                wp_pures.
                wp_bind (inject _ _)%E.
                iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
                iIntros (l') "Hl'".
                iModIntro. wp_pures.
                wp_apply (dconcat_spec_helper with "[Hc Hl']") as (l) "Hl".
                  { assumption. }
                  { iFrame. by iFrame "#". }
                wp_pures.
                iModIntro.
                iApply "Hψ".
                iExists p, l, la, NONEV, b', op, ((os'++⋅_)++cc), lc, [], (om++os),
                  kPr, 2, 5, ((rtr'++⋅(fi, NONEV, bempty)%V)++tr), [].
                doneL.
                iSplit. iPureIntro. by easy_config.
                iFrame. iFrame "#".
                iSplit. by isEmptyDeque.
                iSplit; [| doneL].
                --- iSplit. doneR.
                  iApply (big_sepL2_mono with "Htr'"). by auto.
                  iApply (big_sepL2_mono with "Htrtr"). by auto.
                --- iPureIntro.
                  rewrite !concat_app Hoeq Hleq /= !app_nil_r concat_app /=.
                  aac_reflexivity.
            ++ wp_apply (bdouble_move_right_spec) as (b1 b2 b3 o1 o2 o3) "(#H1 & #H2 & #H3 & %Hoeq')".
            { assert (3 = 2 + 1) as -> by reflexivity.
              iFrame "#". }
            rewrite /atriple.
            wp_pures.
            wp_apply (bis_empty_spec with "Hfi") as "_".
            assert (bool_decide (kF = 0%nat) = false) as -> by invert_all_in.
            rewrite /atriple_.
            wp_pures.
            wp_bind (inject _ _)%E.
            iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
            iIntros (l') "Hl'".
            iModIntro. wp_pures.
            iModIntro.
            iApply "Hψ".
            iExists p, l', b2, NONEV, b3,
                op, (os'++⋅(fc++List.concat cc++o1)), o2, [], o3,
                kPr, 2, 4, (rtr'++⋅(fi, c, b1)%V), [].
            doneL.
            iSplit. iPureIntro. simpl. by easy_config.
            iFrame "#". iFrame.
            iSplit. by isEmptyDeque.
            iSplit; [ iApply (big_sepL2_app with "[Htr']") | doneL ].
            ** iApply (big_sepL2_mono with "Htr'"). by auto.
            ** simpl. doneR. iNext.
              rewrite !triple_unfold.
              iExists fi, c, b1, fc, cc, o1, kF, 2, tr.
              iSplit. iPureIntro. destruct (length cc); constructor; (list_elem_of || lia).
              doneL.
              iFrame . iFrame "#".
              iSplit. iApply (big_sepL2_mono with "Htrtr"). by auto.
              done.
            ** iPureIntro.
              rewrite !concat_app Hoeq Hleq /= !app_nil_r concat_app /=.
              aac_rewrite Hoeq'.
              aac_reflexivity.
        Opaque isSpecialTriple.
        * Transparent isNotSpecialTriple. wp_pures.
          (* appeler la spec de pop_case_2_not_special *)
          rewrite /prepare_pop_case_2.
          iDestruct "Ht" as (fi c la fc cc lc kF kL tr) "(%tconf & -> & #Hfi & #Hc & #Hla & #Htrtr & %Hleq)".
          wp_pures.
          wp_apply (bhas_length_3_spec with "Hla") as "_".
          inversion tconf; wp_pures.
          wp_apply (bconcat23_spec with "[Hm Hs]") as (b') "Hb'". by iFrame "#".
          rewrite isDeque_unfold.
          iDestruct "Hc" as "[[-> ->] | (%ℓ' & -> & Hℓ')]".
          2: {
            rewrite /abuffer.
            do 4 wp_pure.
            wp_bind (_ = _)%E.
            iInv "Hℓ'" as "(%v' & Hv' & Hℓ'')".
            wp_pure.
            iExFalso.
            iDestruct "Hv'" as (pr' ld' md' rd' sf' pc' lc' mc' rc' sc' kp' km' ks' lt rt) "(_ & %conf' & _ & _ & _ & _ & Hs' & _ & _ & ->)".
            iDestruct (big_sepL2_length with "Htrtr") as "%Hlen".
            rewrite Hlen in H7.
            iDestruct (buffer_length with "Hs'") as "%Hslen".
            assert (ks' > 0) as Hslen' by (inversion conf'; invert_all_in; lia).
            rewrite !length_app in H7.
            lia.
          }
          wp_pures.
          wp_apply (bis_empty_spec with "Hfi") as "_".
          wp_pures.
          (*
          assert (kL = 0 ∨ kL ∈ [2; 3]) as Hkl. by invert_all_in.
          destruct Hkl as [-> | Hkl]; wp_pures.
          -- *)
            iModIntro. iApply "Hψ".
            iExists p, d', la, NONEV, b', op, os', lc, [], (om++os),
              kPr, 2, 5, rtr', [].
            doneL.
            iSplit. iPureIntro. by easy_config.
            iFrame "#". iFrame.
            iSplit. by isEmptyDeque.
            iSplit. iApply (big_sepL2_mono with "Htr'"). by auto.
            doneL.
            destruct fc; [| iDestruct (buffer_length with "Hfi") as "%No"; by inversion No ].
            destruct cc; [| by inversion H6 ].
            iPureIntro.
            rewrite Hoeq Hleq /= concat_app /=.
            aac_reflexivity.
        Opaque isNotSpecialTriple.
    - wp_pures.
      wp_bind (let: "f" := _ in _)%E.
      wp_apply (eject_triple_spec with "[iH]").
      + iSplit. iExact "Hℓ".
        iSplit. iExact "Hrtr".
        iApply "iH".
      + Transparent isSpecialTriple.
        iIntros (t' t o' rtr' os' d') "([-> ->] & Htr' & [(#Ht & Hd') | (Ht & Hd')])".
        * (* appeler la spec de pop_case_1_special *)
          iDestruct "Ht" as (fi c la fc cc lc kF kL tr) "(%tconf & -> & #Hfi & #Hc & #Hla & #Htrtr & %Hleq)".
          wp_pures.
          wp_apply (bhas_length_3_spec with "Hla") as "_".
          inversion tconf; wp_pures.
          -- wp_apply (bmove_right_1_33_spec with "[Hla Hs]"). by iFrame "#".
            iIntros (b1 b2 o1 o2) "(#H1 & #H2 & %Honeq)".
            rewrite /atriple.
            wp_pures.
            wp_apply (bis_empty_spec with "Hfi") as "_".
            inversion H7; rewrite /atriple_.
            ++ wp_pures.
              wp_bind (inject _ _)%E.
              iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
              iIntros (r') "Hr'".
              iModIntro. wp_pures.
              iModIntro. iApply "Hψ".
              iExists p, l, m, r', b2, op, ol, om, (os'++⋅(fc++List.concat cc++o1)), o2,
                kPr, 2, 4, ltr, (rtr' ++ ⋅(b1, c, bempty)%V).
              doneL.
              iSplit. iPureIntro. by easy_config.
              rewrite -isDeque_unfold.
              iFrame. iFrame "#".
              iSplit. iApply (big_sepL2_mono with "Hltr"). by auto.
              iSplit. iApply (big_sepL2_app with "[Htr']"). iApply (big_sepL2_mono with "Htr'"). by auto.
              simpl. doneR. iNext.
                iClear "Hltr".
                rewrite triple_unfold.
                iExists b1, c, bempty, o1, cc, [], 2, 0, tr.
                iSplit. iPureIntro. inversion H3. by easy_config.
                doneL.
                iFrame "#".
                iSplit. by iApply bempty_spec.
                iSplit. iApply (big_sepL2_mono with "Htrtr"). by auto.
                destruct fc; [| iDestruct (buffer_length with "Hfi") as "%No"; by inversion No ].
                destruct cc; [| by inversion H6 ].
                iPureIntro. rewrite /= app_nil_r //.
              iPureIntro.
                rewrite Hoeq /= Hleq !concat_app /=.
                aac_rewrite Honeq.
                aac_reflexivity.
            ++ assert (bool_decide (kF = 0%nat) = false) as -> by invert_all_in.
              wp_pures.
              wp_bind (inject _ _)%E.
              iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
              iIntros (r') "Hr'".
              iModIntro. wp_pures.
              iModIntro. iApply "Hψ".
              iExists p, l, m, r', b2, op, ol, om, (os'++⋅(fc++List.concat cc++o1)), o2,
                kPr, 2, 4, ltr, (rtr' ++ ⋅(fi, c, b1)%V).
              doneL.
              iSplit. iPureIntro. by easy_config.
              rewrite -isDeque_unfold.
              iFrame. iFrame "#".
              iSplit. iApply (big_sepL2_mono with "Hltr"). by auto.
              iSplit. iApply (big_sepL2_app with "[Htr']"). iApply (big_sepL2_mono with "Htr'"). by auto.
              simpl. doneR. iNext.
                iClear "Hltr".
                rewrite triple_unfold.
                iExists fi, c, b1, fc, cc, o1, kF, 2, tr.
                iSplit. iPureIntro. inversion H3. by easy_config.
                doneL.
                iFrame "#".
                iSplit. iApply (big_sepL2_mono with "Htrtr"). by auto.
                destruct fc; [| iDestruct (buffer_length with "Hfi") as "%No"; by inversion No ].
                destruct cc; [| by inversion H6 ].
                iPureIntro. rewrite //.
              iPureIntro.
                rewrite Hoeq /= Hleq !concat_app /=.
                aac_rewrite Honeq.
                aac_reflexivity.
          -- assert (kL = 2 ∨ kL = 3) as [-> | ->] by invert_all_in; wp_pures.
            ++ wp_apply (bconcat23_spec with "[Hla Hs]") as (b') "Hb'". by iFrame "#".
              wp_pures.
              rewrite !isDeque_unfold.
              iDestruct "Hc" as "[[-> ->] | (%ℓc & -> & Hℓc)]".
                { iDestruct (big_sepL2_nil_inv_r with "Htrtr") as "->". inversion H6. }
              wp_pures.
              wp_apply (abuffer_spec_explicit with "Hfi") as "Ht". by assumption.
              wp_pures.
              wp_bind (inject _ _)%E.
              iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
              iIntros (r') "Hr'".
              iModIntro. wp_pures.
              wp_apply (dconcat_spec_helper with "[Hℓc Hr']") as (r) "Hr".
                { assumption. }
                { iFrame. ℓisDeque ℓc. iExact "Hℓc". }
              wp_pures.
              iModIntro.
              iApply "Hψ".
              iExists p, l, m, r, b', op, ol, om, ((os' ++ ⋅fc) ++ cc), (lc ++ os),
                kPr, 2, 5, ltr, ((rtr'++⋅(fi, NONEV, bempty)%V)++tr).
              doneL.
              iSplit. iPureIntro. simpl. by easy_config.
              rewrite -isDeque_unfold.
              iFrame "#". iFrame.
              iSplit; [| iSplit; [iSplit; [iSplit; [| done] |] |]].
              ** iApply (big_sepL2_mono with "Hltr"). by auto.
              ** iApply (big_sepL2_mono with "Htr'"). by auto.
              ** iApply (big_sepL2_mono with "Htrtr"). by auto.
              ** iPureIntro.
                rewrite Hoeq Hleq !concat_app /=.
                aac_reflexivity.
            ++ wp_apply (bmove_right_1_33_spec with "[Hla Hs]"). by iFrame "#".
              iIntros (b1 b2 o1 o2) "(#H1 & #H2 & %Hnoeq)".
              rewrite /atriple.
              wp_pures.
              wp_apply (bis_empty_spec with "Hfi") as "_".
              assert (bool_decide (kF = 0%nat) = false) as -> by invert_all_in.
              rewrite /atriple_.
              wp_pures.
              wp_bind (inject _ _)%E.
              iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
              iIntros (r') "Hr'".
              iModIntro. wp_pures.
              iApply "Hψ".
              iModIntro.
              iExists p, l, m, r', b2, op, ol, om, (os'++⋅(fc++List.concat cc++o1)), o2,
                kPr, 2, 4, ltr, (rtr'++⋅(fi, c, b1)%V).
              doneL.
              iSplit. iPureIntro. simpl. by easy_config.
              rewrite -isDeque_unfold.
              iFrame "#". iFrame.
              iSplit. iApply (big_sepL2_mono with "Hltr"). by auto.
              iSplit. iApply (big_sepL2_app with "[Htr']"). iApply (big_sepL2_mono with "Htr'"). by auto.
              iSplit.
                iClear "Hltr".
                rewrite triple_unfold.
                iExists fi, c, b1, fc, cc, o1, kF, 2, tr.
                iSplitL. iPureIntro. destruct (length cc); [inversion H6 |]; by easy_config.
                doneL.
                iFrame "#".
                iSplit. iApply (big_sepL2_mono with "Htrtr"). by auto.
                done.
              done.
              iPureIntro.
                rewrite Hoeq Hleq !concat_app /=.
                aac_rewrite Hnoeq.
                aac_reflexivity.
          -- assert (kL = 2 ∨ kL = 3) as [-> | ->] by invert_all_in; wp_pures.
            ++ wp_apply (bconcat23_spec with "[Hla Hs]") as (b') "Hb'". by iFrame "#".
              wp_pures.
              wp_bind (if: _ then _ else #false)%E.
              iApply (wp_strong_mono _ _ _ _ _ (λ v, ⌜ v = #false ⌝)%I). { auto. } { auto. }
                { destruct (bool_decide (c = NONEV)); wp_pures.
                - wp_apply (bis_empty_spec with "Hfi") as "_".
                  assert (bool_decide (kF = 0%nat) = false) as -> by invert_all_in.
                  done.
                - done.
                }
              iIntros (v) "->". iModIntro. wp_pures.
              wp_apply (abuffer_spec_explicit with "Hfi") as "Ht". by assumption.
              wp_pures.
              wp_bind (inject _ _)%E.
              iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
              iIntros (r') "Hr'".
              iModIntro. wp_pures.
              wp_apply (dconcat_spec_helper with "[Hc Hr']") as (r) "Hr".
                { assumption. }
                { iFrame. iExact "Hc". }
              wp_pures.
              iModIntro.
              iApply "Hψ".
              iExists p, l, m, r, b', op, ol, om, ((os' ++ ⋅fc) ++ cc), (lc ++ os),
                kPr, 2, 5, ltr, ((rtr'++⋅(fi, NONEV, bempty)%V)++tr).
              doneL.
              iSplit. iPureIntro. simpl. by easy_config.
              rewrite -isDeque_unfold.
              iFrame "#". iFrame.
              iSplit; [| iSplit; [iSplit; [iSplit; [| done] |] |]].
              ** iApply (big_sepL2_mono with "Hltr"). by auto.
              ** iApply (big_sepL2_mono with "Htr'"). by auto.
              ** iApply (big_sepL2_mono with "Htrtr"). by auto.
              ** iPureIntro.
                rewrite Hoeq Hleq !concat_app /=.
                aac_reflexivity.
            ++ wp_apply (bmove_right_1_33_spec with "[Hla Hs]"). by iFrame "#".
              iIntros (b1 b2 o1 o2) "(#H1 & #H2 & %Hnoeq)".
              rewrite /atriple.
              wp_pures.
              wp_apply (bis_empty_spec with "Hfi") as "_".
              assert (bool_decide (kF = 0%nat) = false) as -> by invert_all_in.
              rewrite /atriple_.
              wp_pures.
              wp_bind (inject _ _)%E.
              iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
              iIntros (r') "Hr'".
              iModIntro. wp_pures.
              iApply "Hψ".
              iModIntro.
              iExists p, l, m, r', b2, op, ol, om, (os'++⋅(fc++List.concat cc++o1)), o2,
                kPr, 2, 4, ltr, (rtr' ++ ⋅(fi, c, b1)%V).
              doneL.
              iSplit. iPureIntro. by easy_config.
              rewrite -isDeque_unfold.
              iFrame. iFrame "#".
              iSplit. iApply (big_sepL2_mono with "Hltr"). by auto.
              iSplit. iApply (big_sepL2_app with "[Htr']"). iApply (big_sepL2_mono with "Htr'"). by auto.
              simpl. doneR. iNext.
                iClear "Hltr".
                rewrite triple_unfold.
                iExists fi, c, b1, fc, cc, o1, kF, 2, tr.
                iSplit. iPureIntro. destruct (length cc); constructor; by (lia || list_elem_of).
                doneL.
                iFrame "#".
                iSplit. iApply (big_sepL2_mono with "Htrtr"). by auto.
                destruct fc; [| iDestruct (buffer_length with "Hfi") as "%No"; by inversion No ].
                destruct cc; [| by inversion H6 ].
                iPureIntro. rewrite //.
              iPureIntro.
                rewrite Hoeq /= Hleq !concat_app /=.
                aac_rewrite Hnoeq.
                aac_reflexivity.
        Opaque isSpecialTriple.
        * Transparent isNotSpecialTriple.
          (* appeler la spec de pop_case_1_not_special *)
          iDestruct "Ht" as (fi c la fc cc lc kF kL tr) "(%tconf & -> & #Hfi & #Hc & #Hla & #Htrtr & %Hleq)".
          wp_pures.
          wp_apply (bhas_length_3_spec with "Hla") as "_".
          inversion tconf; wp_pures.
          wp_apply (bconcat23_spec with "[Hm Hs]") as (b') "Hb'". by iFrame "#".
          rewrite !isDeque_unfold.
          iDestruct "Hc" as "[[-> ->] | (%ℓ' & -> & Hℓ')]".
          2: {
            do 2 wp_pure.
            wp_bind (_ = _)%E.
            iInv "Hℓ'" as "(%v' & Hv' & Hℓ'')".
            wp_pure.
            iExFalso.
            iDestruct "Hv'" as (pr' ld' md' rd' sf' pc' lc' mc' rc' sc' kp' km' ks' lt rt) "(_ & %conf' & _ & _ & _ & _ & Hs' & _ & _ & ->)".
            iDestruct (big_sepL2_length with "Htrtr") as "%Hlen".
            rewrite Hlen in H7.
            iDestruct (buffer_length with "Hs'") as "%Hslen".
            assert (ks' > 0) as Hslen' by (inversion conf'; invert_all_in; lia).
            rewrite !length_app in H7.
            lia.
          }
          wp_pures.
          wp_apply (bis_empty_spec with "Hfi") as "_".
          wp_pures.
          iModIntro. iApply "Hψ".
          iExists p, l, m, d', b', op, ol, om, os', (lc++os),
            kPr, 2, 5, ltr, rtr'.
          rewrite -!isDeque_unfold.
          doneL.
          iSplit. iPureIntro. by easy_config.
          iFrame "#". iFrame.
          iSplit. iApply (big_sepL2_mono with "Hltr"). by auto.
          iSplit. iApply (big_sepL2_mono with "Htr'"). by auto.
          destruct fc; [| iDestruct (buffer_length with "Hfi") as "%No"; by inversion No ].
          destruct cc; [| by inversion H6 ].
          iPureIntro.
          rewrite Hoeq Hleq /= concat_app /=.
          aac_reflexivity.
        Opaque isNotSpecialTriple.
    Qed.

  Global Instance isPopFiveTuplePersistent o d : Persistent (isEjectFiveTuple o d).
  Proof.
    rewrite /isEjectFiveTuple.
    repeat (apply bi.exist_persistent; intro).
    repeat (apply bi.sep_persistent; apply _).
  Qed.

End lemmas.
