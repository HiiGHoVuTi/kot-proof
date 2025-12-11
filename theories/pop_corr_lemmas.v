From iris.heap_lang Require Import lang proofmode notation.
From iris.bi Require Import derived_laws.

From Coq Require Import List.
Import ListNotations.

From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Deque Require Import common tick shared_ref deque_corr push_corr concat_corr.

Section lemmas.

  Context `{!heapGS Σ}.

  Variable NO_COST_ANALYSIS : TICK_COST = 0.

  (* Five-tuple configuration for calling naive_pop *)
  Inductive pop_configuration : nat -> nat -> nat -> nat -> nat -> Prop :=
    | pop_suffix_only : forall s, s ∈ [1..8] -> pop_configuration 0 0 0 0 s
    | pop_has_middle : forall p ld rd s, p ∈ [4..6] -> s ∈ [3..6] -> pop_configuration p ld 2 rd s.

 Definition isPopFiveTuple := (
    λ o d, ∃ (pr ld md rd sf : val)
      pr_content left_content md_content right_content sf_content
      (kPr kMd kSf : nat) left_triples right_triples,
      ⌜ d = (pr, ld, md, rd, sf)%V ⌝ ∗
      ⌜ pop_configuration kPr (length left_content) kMd (length right_content) kSf ⌝ ∗
      buffer kPr pr_content pr ∗
      isDeque left_triples ld ∗
      buffer kMd md_content md ∗
      isDeque right_triples rd ∗
      buffer kSf sf_content sf ∗
      ([∗list] c;tr ∈ left_content;left_triples, ▷ triple c tr) ∗
      ([∗list] c;tr ∈ right_content;right_triples, ▷ triple c tr) ∗
      ⌜ o = pr_content ++ List.concat left_content ++ md_content ++ List.concat right_content ++ sf_content ⌝
  )%I.

 Definition isUnsafePopFiveTuple := (
    λ o d, ∃ (pr ld md rd sf : val)
      pr_content left_content md_content right_content sf_content
      (kMd kSf : nat) left_triples right_triples,
      ⌜ d = (pr, ld, md, rd, sf)%V ⌝ ∗
      ⌜ five_tuple_configuration 3 (length left_content) kMd (length right_content) kSf ⌝ ∗
      buffer 3 pr_content pr ∗
      isDeque left_triples ld ∗
      buffer kMd md_content md ∗
      isDeque right_triples rd ∗
      buffer kSf sf_content sf ∗
      ([∗list] c;tr ∈ left_content;left_triples, ▷ triple c tr) ∗
      ([∗list] c;tr ∈ right_content;right_triples, ▷ triple c tr) ∗
      ⌜ o = pr_content ++ List.concat left_content ++ md_content ++ List.concat right_content ++ sf_content ⌝
  )%I.

  Lemma safe_decidable : forall o f,
    fiveTuple o f -∗
      (isUnsafePopFiveTuple o f ∗ WP naive_pop_safe f {{ x, ⌜ x = #false ⌝ }})
    ∨ isPopFiveTuple o f ∗ WP naive_pop_safe f {{ x, ⌜ x = #true ⌝ }}.
  Proof.
    iIntros (o f) "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                      %kPr & %kMd & %kSf & %ltr & %rtr &
                      %Heq & %conf & #Hp & #Hl & #Hm & #Hr & #Hs &
                      #Hltr & #Hrtr & %Hoeq)".
    destruct (dec_eq_nat kPr 3) as [-> | HkPr]; [iLeft | iRight].
    - iSplitL.
      + iExists p, l, m, r, s, op, ol, om, or, os, kMd, kSf, ltr, rtr.
        iFrame "#". iFrame.
        doneL.
        iSplit; done.
      + rewrite /naive_pop_safe Heq.
        wp_pures.
        inversion conf.
        wp_apply (bis_empty_spec with "Hm") as "_".
        wp_pures.
        wp_apply (blength_spec with "Hp") as "_".
        wp_pures.
        done.
    - iSplitR.
      + iExists p, l, m, r, s, op, ol, om, or, os, kPr, kMd, kSf, ltr, rtr.
        iFrame. iFrame "#".
        doneL. doneR.
        iPureIntro.
        inversion conf.
        * by easy_config.
        * inversion H; [ exfalso; lia |].
          by easy_config.
      + rewrite /naive_pop_safe Heq.
        iFrame.
        wp_pures.
        wp_apply (bis_empty_spec with "Hm") as "_".
        inversion conf; wp_pures.
        * done.
        * wp_apply (blength_spec with "Hp") as "_".
          clear H0.
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

  Lemma safe_naive_pop : forall o f,
    {{{ isPopFiveTuple o f }}}
      naive_pop f
    {{{ x d o', RET (x, d)%V; isDeque o' d ∗ ⌜ o = ⋅x ++ o' ⌝ }}}.
  Proof.
    iIntros (o f ψ) "Hf Hψ".
    iDestruct "Hf" as "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                      %kPr & %kMd & %kSf & %ltr & %rtr &
                      -> & %conf & #Hp & #Hl & #Hm & #Hr & #Hs &
                      #Hltr & #Hrtr & %Hoeq)".
    rewrite /naive_pop.
    wp_pures.
    wp_apply (bis_empty_spec with "Hm") as "_".
    inversion conf; wp_pures.
    - suffix_only_incantation op om H H1 Hoeq.
      change (kSf ∈ map S [0;1;2;3;4;5;6;7]) in H3.
      assert (∃ kSf', kSf = kSf' + 1) as (kSf' & ->)
        by (invert_all_in;
        match goal with
        | |- ∃ kSf', S ?x = kSf' + 1 => exists x; lia
        end).
      wp_apply (bpop_spec with "Hs") as "%b' %x %o' (#Hb & ->)".
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
    - change (kPr ∈ map S [3;4;5]) in H.
      apply decrease_in in H as (kP & -> & H).
      wp_apply (bpop_spec with "Hp") as "%b' %x %o' (#Hb' & ->)".
      rewrite /assemble_.
      wp_pures.
      wp_apply (csref_alloc (fiveTuple _)) as "%ℓ'' #Hℓ''".
      + iExists b',l,m,r,s,o',ol,om,or,os,kP,kMd,kSf,ltr,rtr.
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

  Lemma unsafe_naive_pop : forall o f,
    {{{ fiveTuple o f }}}
      naive_pop f
    {{{ x (d : val) o', RET (x, d)%V;
      ⌜ o = ⋅ x ++ o' ⌝ ∗
      ∀ y : val,
        WP push y d {{ d, isDeque (⋅ y ++ o') d }}
    }}}.
  Proof.
    iIntros (o f ψ) "Hf Hψ".
    iDestruct "Hf" as "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                      %kPr & %kMd & %kSf & %ltr & %rtr &
                      -> & %conf & #Hp & #Hl & #Hm & #Hr & #Hs &
                      #Hltr & #Hrtr & %Hoeq)".
    rewrite /naive_pop.
    wp_pures.
    wp_apply (bis_empty_spec with "Hm") as "_".
    inversion conf; wp_pures.
    - suffix_only_incantation op om H H1 Hoeq.
      iClear "Hl Hr".
      change (kSf ∈ map S [0;1;2;3;4;5;6;7]) in H3.
      apply decrease_in in H3 as (ks & -> & Hks).
      wp_apply (bpop_spec with "Hs") as (b' x o') "[#Hb' %Hoeq']".
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
          rewrite /push.
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
          ℓisDeque ℓ.
          iExact "Hℓ".
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
        rewrite /push.
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
        wp_apply (bpush_spec with "Hb'") as (b) "Hb".
        wp_pures.
        wp_apply (csref_alloc (fiveTuple (⋅y' ++ o')) with "[Hb]") as (ℓ') "Hℓ'".
          { iExists bempty, NONEV, bempty, NONEV, b, [], [], [], [], (⋅y' ++ o'), 0, 0, (ks+1), [], [].
            iFrame. iFrame "#".
            repeat doneL.
            iSplit. rewrite H H1 -H0 -H2 in conf. done.
            repeat (iSplit; [iApply bempty_spec || isEmptyDeque |]).
            do 2 doneL.
            done.
          }
        wp_pures.
        iModIntro.
        rewrite /=.
        ℓisDeque ℓ'.
        iExact "Hℓ'".
    - change (kPr ∈ map S [2; 3; 4; 5]) in H.
      apply decrease_in in H as (kp & -> & Hkp).
      wp_apply (bpop_spec with "Hp") as "%b' %x %o' (#Hb' & ->)".
      rewrite /assemble_.
      wp_pures.
      wp_alloc ℓ as "Hℓ".
      wp_pures.
      iModIntro.
      iApply ("Hψ" $! x (SOMEV #ℓ) (o' ++ concat ol ++ om ++ concat or ++ os)).
      iSplit. iPureIntro. rewrite Hoeq. aac_reflexivity.
      iIntros (y).
      rewrite /push.
      wp_pures.
      wp_apply (tick_spec) as "_".
        { rewrite NO_COST_ANALYSIS time_zero //. }
      wp_pures.
      wp_load.
      wp_pures.
      wp_apply (bis_empty_spec with "Hm") as "_".
      wp_pures.
      wp_apply (bhas_length_6_spec with "Hb'") as "_".
      assert (bool_decide (kp = 6%nat) = false) as  -> by invert_all_in.
      wp_pures.
      wp_store.
      rewrite /assemble_.
      wp_apply (bpush_spec with "Hb'") as "%p' #Hp'".
      wp_pures.
      wp_apply (csref_alloc (fiveTuple (⋅y ++ o' ++ concat ol ++ om ++ concat or ++ os))) as "%ℓ' Hℓ'".
      + iExists p',l,m,r,s,(⋅y++o'),ol,om,or,os,(kp+1),2,kSf,ltr,rtr.
        iFrame "#".
        doneL.
        iSplit. iPureIntro. rewrite H3. done.
        iSplit. iApply (big_sepL2_mono with "Hltr"). by auto.
        iSplit. iApply (big_sepL2_mono with "Hrtr"). by auto.
        done.
      + wp_pures.
        iModIntro.
        ℓisDeque ℓ'.
        iExact "Hℓ'".
  Qed.

  Lemma inspect_first_spec : forall o f,
    {{{ fiveTuple o f }}}
      inspect_first f
    {{{ o' t, RET t; ⌜ o = ⋅ t ++ o' ⌝  }}}.
  Proof.
    iIntros (o f ψ) "Hf Hψ".
    iDestruct "Hf" as "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                      %kPr & %kMd & %kSf & %ltr & %rtr &
                      -> & %conf & #Hp & #Hl & #Hm & #Hr & #Hs &
                      #Hltr & #Hrtr & %Hoeq)".
    rewrite /inspect_first. wp_pures.
    wp_apply (bis_empty_spec with "Hm") as "_".
    inversion conf; wp_pures.
    - change (kSf ∈ map S [0;1;2;3;4;5;6;7]) in H3.
      apply decrease_in in H3 as (kS & -> & HkS).
      destruct os.
        { iDestruct (buffer_length with "Hs") as "%abs".
          simpl in abs; lia. }
      wp_apply (bfirst_spec with "Hs") as "_".
      iApply "Hψ".
      suffix_only_incantation op om H H1 Hoeq.
      iPureIntro.
      rewrite Hoeq //.
    - change (kPr ∈ map S [2;3;4;5]) in H.
      apply decrease_in in H as (kP & -> & HkP).
      destruct op.
        { iDestruct (buffer_length with "Hp") as "%abs".
          simpl in abs; lia. }
      wp_apply (bfirst_spec with "Hp") as "_".
      iApply "Hψ".
      iPureIntro.
      rewrite Hoeq //.
  Qed.

  Inductive special_triple_configuration : nat -> nat -> nat -> Prop :=
    | is_special_three : forall y, y ∈ [0; 2; 3] -> special_triple_configuration 3 0 y
    | is_special_child : forall x o y, x ∈ [2; 3] -> o > 0 -> y ∈ [2; 3] -> special_triple_configuration x o y
    | is_special_last : forall x o y, x ∈ [2; 3] -> y ∈ [2; 3] -> special_triple_configuration x o y.

  Inductive not_special_triple_configuration : nat -> nat -> nat -> Prop :=
    (* | is_bad : forall y, y ∈ [0; 2; 3] -> not_special_triple_configuration 2 0 y. *)
    | is_bad : not_special_triple_configuration 2 0 0.

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

  Lemma special_decidable : forall o t,
    triple o t -∗
      isSpecialTriple o t
    ∨ isNotSpecialTriple o t.
  Proof.
    iIntros (o t) "Ht".
    rewrite triple_unfold.
    iDestruct "Ht" as (f c l fc cc lc kFst kLst tr) "(%conf & -> & Hf & Hc & Hl & Htr & %Hoeq)".
    inversion conf.
    - inversion H0.
      + inversion H2.
        * iRight.
          iExists f, c, l, fc, cc, lc, kFst, 0, tr.
          rewrite H6.
          iFrame.
          iSplit; [| iSplit]; iPureIntro; auto.
          rewrite -H. constructor; done.
        * iLeft.
          iExists f, c, l, fc, cc, lc, kFst, kLst, tr.
          rewrite H6.
          iFrame.
          iSplit; [| iSplit]; iPureIntro; auto.
          rewrite -H. apply is_special_last; by list_elem_of.
      + clear H0. assert (kFst = 3) as H' by (clear H2; invert_all_in).
        iLeft.
        iExists f, c, l, fc, cc, lc, kFst, kLst, tr.
        iFrame.
        iSplit; [| iSplit]; iPureIntro; auto.
        rewrite -H H'. constructor; done.
    - inversion H; [| inversion H]; [| clear H H1; invert_all_in; lia |].
      + iLeft.
        iExists f, c, l, fc, cc, lc, kFst, kLst, tr.
        rewrite H7.
        iFrame.
        iSplit; [| iSplit]; iPureIntro; auto.
        -- constructor; auto; list_elem_of.
      + iLeft.
        iExists f, c, l, fc, cc, lc, kFst, kLst, tr.
        assert (kFst = 3) as -> by (clear H H1; invert_all_in).
        iFrame.
        iSplit; [| iSplit]; iPureIntro; auto.
        constructor; auto.
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

  Lemma pop_triple_spec : forall os tr ℓ,
    {{{ ℓ ⤇ fiveTuple tr
      ∗ ([∗list] x;y ∈ os;tr, triple x y)
      ∗ (∀ ℓ x o,
          ℓ ⤇ fiveTuple (⋅ x ++ o) -∗
          WP pop_nonempty #ℓ
            {{ r, ∃ d, ⌜ r = (x, d)%V ⌝ ∗ isDeque o d }})
    }}}
      subst "pop_nonempty" pop_nonempty (pop_triple #ℓ)
    {{{ t o tr' os' (d' : val), RET (t, d')%V;
      ⌜ tr = ⋅t ++ tr' ∧ os = ⋅o ++ os' ⌝ ∗
      ([∗list] x;y ∈ os';tr', triple x y) ∗
      ( isSpecialTriple o t ∗ (∀ x : val, WP push x d' {{ d'', isDeque (⋅x ++ tr') d'' }})
      ∨ isNotSpecialTriple o t ∗ isDeque tr' d'
      )
    }}}.
  Proof.
    iIntros (os tr d Hψ) "(#Hd & Htr & iH) Hψ".
    rewrite /pop_triple.
    wp_pures.
    wp_apply (csref_load with "Hd").
    iIntros (f) "#Hf".
    wp_pures.
    wp_apply (inspect_first_spec with "[Hf]").
      { iApply add_later.
        iExact "Hf".
      }
    iIntros (o t) "->".
    wp_pures.
    destruct os. iDestruct (big_sepL2_nil_inv_l with "Htr") as "%No". inversion No.
    assert (l :: os = ⋅ l ++ os) as -> by auto.
    iDestruct (big_sepL2_app_inv with "Htr") as "(Ht & Htr)". by left.
    iAssert (triple l t) with "[Ht]" as "Ht".
      { simpl. iDestruct "Ht" as "[A _]". done. }
    iDestruct (special_decidable with "Ht") as "[#Ht' | #Ht']";
    iCombine "Ht' Ht'" as "[Ht! Ht!']";
    iDestruct "Ht!'" as (fi c la fc cc lc kF kL tr) "(%conf & -> & Hf' & Hc & Hl & Htrtr & %Hleq)";
    inversion conf.
    Opaque isSpecialTriple isNotSpecialTriple.
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
      wp_apply (unsafe_naive_pop).
        { iFrame.
          iApply add_later.
          by iExact "Hf". }
      iIntros (x d' o') "(%Hoeq' & Hpush)".
      inversion Hoeq'.
      iApply "Hψ".
      doneL.
      iSplit. iExact "Htr".
      iLeft.
      iSplitR.
      * assert (x = (fi, NONEV, la)%V) as -> by by inversion Hoeq'.
        iExact "Ht!".
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
        wp_apply (unsafe_naive_pop).
          { iFrame.
            iApply add_later.
            iExact "Hf". }
        iIntros (x' d' o') "(%Hoeq' & Hpush)".
        inversion Hoeq'.
        iApply "Hψ".
        iFrame.
        doneL.
        iLeft.
        iSplitR.
        -- assert (x' = (fi, SOMEV #ℓ, la)%V) as -> by by inversion Hoeq'.
          iExact "Ht!".
        -- iExact "Hpush".
      * wp_apply (unsafe_naive_pop).
          { iFrame.
            iApply add_later.
            by iExact "Hf". }
        iIntros (x' d' o') "(%Hoeq' & Hpush)".
        inversion Hoeq'.
        iApply "Hψ".
        iFrame.
        doneL.
        iLeft.
        iSplitR.
        -- assert (x' = (fi, SOMEV #ℓ, la)%V) as -> by by inversion Hoeq'.
          iExact "Ht!".
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
        wp_apply (unsafe_naive_pop).
          { iFrame.
            iApply add_later.
            iExact "Hf". }
        iIntros (x' d' o') "(%Hoeq' & Hpush)".
        inversion Hoeq'.
        iApply "Hψ".
        iFrame.
        doneL.
        iLeft.
        iSplitR.
        -- assert (x' = (fi, c, la)%V) as -> by by inversion Hoeq'.
          iExact "Ht!".
        -- iExact "Hpush".
      * wp_apply (unsafe_naive_pop).
          { iApply add_later.
            by iExact "Hf". }
        iIntros (x' d' o') "(%Hoeq' & Hpush)".
        inversion Hoeq'.
        iApply "Hψ".
        iFrame.
        doneL.
        iLeft.
        iSplitR.
        -- assert (x' = (fi, c, la)%V) as -> by by inversion Hoeq'.
          iExact "Ht!".
        -- iExact "Hpush".
    + wp_pures.
      wp_apply (bhas_length_3_spec with "Hf'") as "_".
      wp_pures.
      wp_apply (bis_empty_spec with "Hl") as "_".
      wp_pures.
      iApply (wp_strong_mono with "[iH]").
        { auto. } { reflexivity. }
      * iApply ("iH"). iExact "Hd".
      * iIntros (v) "(%d' & -> & Hd')".
        iApply "Hψ".
        iModIntro. iFrame. doneL.
        iRight.
        iFrame. iExact "Ht!".
  Qed.

  Lemma prepare_pop_spec : forall o f,
    {{{ isUnsafePopFiveTuple o f ∗
      ∀ ℓ x o', ℓ ⤇ fiveTuple (⋅x ++ o') -∗
        WP pop_nonempty #ℓ {{ r, ∃ d, ⌜ r = (x, d)%V ⌝ ∗ isDeque o' d }}
    }}}
      subst "pop_nonempty" pop_nonempty (prepare_pop f)
    {{{ f', RET f'; isPopFiveTuple o f' }}}.
  Proof.
    iIntros (o f ψ) "(Hf & iH) Hψ".
    rewrite /isUnsafePopFiveTuple.
    iDestruct "Hf" as "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                      %kMd & %kSf & %ltr & %rtr &
                      -> & %conf & #Hp & #Hl & #Hm & #Hr & #Hs &
                      #Hltr & #Hrtr & %Hoeq)".
    rewrite /prepare_pop.
    wp_pures.
    inversion conf.
    rewrite isDeque_unfold.
    Notation selpat := "[[-> ->] | (%ℓ & -> & Hℓ)]".
    iDestruct "Hl" as selpat;
    [rewrite isDeque_unfold; iDestruct "Hr" as selpat |].
    - wp_pures.
      wp_apply (bhas_length_3_spec with "Hs") as "_".
      iDestruct (big_sepL2_nil_inv_r with "Hltr") as "->";
      iDestruct (big_sepL2_nil_inv_r with "Hrtr") as "->".
      inversion H0; wp_pures.
      + wp_apply (bconcat323_spec with "[Hp Hm Hs]") as "%b' Hb8". by iFrame "#".
        wp_pures.
        iApply "Hψ".
        iModIntro.
        * iExists bempty, NONEV, bempty, NONEV, b', [], [], [], [], (op++om++os),
            0, 0, 8, [], [].
          iFrame. iFrame "#".
          doneL.
          iSplit. simpl. iPureIntro. constructor. invert_all_in; list_elem_of.
          iSplit. by (iApply bempty_spec).
          iSplit. by isEmptyDeque.
          iSplit. by (iApply bempty_spec).
          iSplit. by isEmptyDeque.
          repeat doneL.
          iPureIntro.
          aac_rewrite Hoeq.
          by rewrite //.
      + assert (bool_decide (kSf = 3%nat) = false) as ->.
        { clear H H0. invert_all_in. }
        wp_pures.
        change (kSf ∈ map S [3;4;5]) in H8.
        apply decrease_in in H8 as (k & -> & Hk).
        clear H0.
        wp_apply (bdouble_move_left_spec with "[Hp Hm Hs]"). by iFrame "#".
        iIntros (b1 b2 b3 o1 o2 o3) "(#H1 & #H2 & #H3 & %Heq)".
        wp_pures.
        iModIntro.
        iApply "Hψ".
        iExists b1, NONEV, b2, NONEV, b3, o1, [], o2, [], o3,
          4, 2, k, [], [].
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
      iDestruct (big_sepL2_nil_inv_r with "Hltr") as "->".
      wp_bind (let: "f" := _ in _)%E.
      wp_apply (pop_triple_spec with "[iH]").
      + iSplit. iExact "Hℓ".
        iSplit. iExact "Hrtr".
        iApply "iH".
      + Transparent isSpecialTriple.
        iIntros (t o' rtr' os' d') "([-> ->] & Htr' & [(#Ht & Hd') | (Ht & Hd')])".
          (* appeler la spec de pop_case_2_special *)
        * rewrite /prepare_pop_case_2.
          iDestruct "Ht" as (fi c la fc cc lc kF kL tr) "(%tconf & -> & #Hfi & #Hc & #Hla & #Htrtr & %Hleq)".
          wp_pures.
          wp_apply (bhas_length_3_spec with "Hfi") as "_".
          inversion tconf; wp_pures.
          -- wp_apply (bdouble_move_left_spec) as (b1 b2 b3 o1 o2 o3) "(#H1 & #H2 & #H3 & %Hoeq')".
            { assert (3 = 2 + 1) as -> by reflexivity.
              iFrame "#". }
            rewrite /atriple_.
            wp_pures.
            wp_bind (push _ _)%E.
            iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
            iIntros (r') "Hr'".
            iModIntro. wp_pures.
            iModIntro.
            iApply "Hψ".
            iExists b1, NONEV, b2, r', s, o1, [], o2,
              (⋅(o3 ++ List.concat cc ++ lc) ++ os'), os, 4, 2, kSf,
              [], (⋅(b3, c, la)%V ++ rtr').
            doneL.
            iFrame "#". iFrame.
            iSplit. iPureIntro. by easy_config.
            iSplit. by isEmptyDeque.
            doneL.
            iSplit; [ iApply (big_sepL2_app) |].
            ++ simpl; doneR.
              iNext. iClear "Hrtr".
              rewrite triple_unfold.
              iExists b3, c, la, o3, cc, lc, 2, kL, tr.
              iSplit. iPureIntro. rewrite -H6. by easy_config.
              doneL. iFrame "#".
              iSplit. iApply (big_sepL2_mono with "Htrtr"). by auto.
              iPureIntro.
              done.
            ++ iDestruct (big_sepL2_app_inv with "Hrtr") as "[_ Hrtr']". by left.
              iApply (big_sepL2_mono with "Hrtr'"). by auto.
            ++ iPureIntro.
              rewrite Hoeq /= -!app_assoc Hleq.
              aac_rewrite Hoeq'.
              aac_reflexivity.
          -- assert (kF = 2 ∨ kF = 3) as HkF by (clear H H0 H8; invert_all_in).
            destruct HkF as [-> | ->]; wp_pures.
            ++ wp_apply (bconcat32_spec with "[Hp Hm]") as (b') "Hb'". by iFrame "#".
              wp_pures.
              rewrite isDeque_unfold.
              iDestruct "Hc" as "[[_ ->] | (%ℓc & -> & Hℓc)]".
                { iDestruct (big_sepL2_nil_inv_r with "Htrtr") as "->". inversion H7. }
              wp_pures.
              wp_apply (abuffer_spec_explicit with "Hla") as "Ht". by assumption.
              wp_pures.
              wp_bind (push _ _)%E.
              iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
              iIntros (r') "Hr'".
              iModIntro. wp_pures.
              wp_apply (dconcat_spec_helper with "[Hℓc Hr']") as (r) "Hr".
                { assumption. }
                { iFrame. ℓisDeque ℓc. iExact "Hℓc". }
              wp_pures.
              iModIntro.
              iApply "Hψ".
              iExists b', NONEV, fi, r, s, (op++om), [], fc, (cc++⋅lc++os'), os,
                5, 2, kSf, [], (tr++⋅(la, NONEV, bempty)%V++rtr').
              doneL.
              iSplit. iPureIntro. by easy_config.
              iFrame. iFrame "#".
              iSplit. by isEmptyDeque.
              doneL.
              iSplit.
              ** iSplit. iApply (big_sepL2_mono with "Htrtr"). by auto.
                doneL.
                iApply (big_sepL2_mono with "Htr'"). by auto.
              ** iPureIntro.
                rewrite !concat_app Hoeq Hleq /= !app_nil_r.
                aac_reflexivity.
            ++ wp_apply (bdouble_move_left_spec with "[Hp Hm Hfi]").
                { iFrame "#". assert (3 = 2 + 1) as -> by reflexivity. done. }
             iIntros (b1 b2 b3 o1 o2 o3) "(H1 & H2 & #H3 & %Hnoeq)".
              rewrite /atriple_.
              wp_pures.
              wp_bind (push _ _)%E.
              iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
              iIntros (r') "Hr'".
              iModIntro.
              wp_pures.
              iModIntro. iApply "Hψ".
              iExists b1, NONEV, b2, r', s, o1, [], o2, (⋅(o3++List.concat cc++lc) ++ os'), os,
                4, 2, kSf, [], (⋅(b3, c, la)%V ++ rtr').
              doneL.
              iSplit. iPureIntro. simpl. by easy_config.
              iFrame "#". iFrame.
              iSplit. by isEmptyDeque.
              doneL.
              iSplit; [ iApply (big_sepL2_app) |].
              ** simpl. doneR. iNext.
                rewrite !triple_unfold.
                iExists b3, c, la, o3, cc, lc, 2, kL, tr.
                iSplit. iPureIntro. by easy_config.
                doneL.
                iFrame . iFrame "#".
                iSplit. iApply (big_sepL2_mono with "Htrtr"). by auto.
                done.
              ** iApply (big_sepL2_mono with "Htr'"). by auto.
              ** iPureIntro.
                rewrite !concat_app Hoeq Hleq /= !app_nil_r.
                aac_rewrite Hnoeq.
                aac_reflexivity.
          -- assert (kF = 2 ∨ kF = 3) as HkF by (clear H H0 H8; invert_all_in).
            destruct HkF as [-> | ->]; wp_pures.
            ++ wp_apply (bconcat32_spec with "[Hp Hm]") as (b') "Hb'". by iFrame "#".
              wp_pures.
              destruct (bool_decide (c = NONEV)); wp_pures.
              ** wp_apply (bis_empty_spec with "Hla") as "_".
                assert (bool_decide (kL = 0%nat) = false) as -> by invert_all_in.
                wp_pures.
                wp_apply (abuffer_spec_explicit with "Hla") as "Ht". by assumption.
                wp_pures.
                wp_bind (push _ _)%E.
                iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
                iIntros (r') "Hr'".
                iModIntro. wp_pures.
                wp_apply (dconcat_spec_helper with "[Hc Hr']") as (r) "Hr".
                  { assumption. }
                  { iFrame. by iFrame "#". }
                wp_pures.
                iModIntro.
                iApply "Hψ".
                iExists b', NONEV, fi, r, s, (op++om), [], fc, (cc++⋅lc++os'), os,
                  5, 2, kSf, [], (tr++⋅(la, NONEV, bempty)%V++rtr').
                doneL.
                iSplit. iPureIntro. by easy_config.
                iFrame. iFrame "#".
                iSplit. by isEmptyDeque.
                doneL.
                iSplit.
                --- iSplit. iApply (big_sepL2_mono with "Htrtr"). by auto.
                  doneL.
                  iApply (big_sepL2_mono with "Htr'"). by auto.
                --- iPureIntro.
                  rewrite !concat_app Hoeq Hleq /= !app_nil_r.
                  aac_reflexivity.
              ** wp_apply (abuffer_spec_explicit with "Hla") as "Ht". by assumption.
                wp_pures.
                wp_bind (push _ _)%E.
                iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
                iIntros (r') "Hr'".
                iModIntro. wp_pures.
                wp_apply (dconcat_spec_helper with "[Hc Hr']") as (r) "Hr".
                  { assumption. }
                  { iFrame. by iFrame "#". }
                wp_pures.
                iModIntro.
                iApply "Hψ".
                iExists b', NONEV, fi, r, s, (op++om), [], fc, (cc++⋅lc++os'), os,
                  5, 2, kSf, [], (tr++⋅(la, NONEV, bempty)%V++rtr').
                doneL.
                iSplit. iPureIntro. by easy_config.
                iFrame. iFrame "#".
                iSplit. by isEmptyDeque.
                doneL.
                iSplit.
                --- iSplit. iApply (big_sepL2_mono with "Htrtr"). by auto.
                  doneL.
                  iApply (big_sepL2_mono with "Htr'"). by auto.
                --- iPureIntro.
                  rewrite !concat_app Hoeq Hleq /= !app_nil_r.
                  aac_reflexivity.
            ++ wp_apply (bdouble_move_left_spec) as (b1 b2 b3 o1 o2 o3) "(#H1 & #H2 & #H3 & %Hoeq')".
            { assert (3 = 2 + 1) as -> by reflexivity.
              iFrame "#". }
            rewrite /atriple_.
            wp_pures.
            wp_bind (push _ _)%E.
            iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
            iIntros (r') "Hr'".
            iModIntro. wp_pures.
            iModIntro.
            iApply "Hψ".
            iExists b1, NONEV, b2, r', s, o1, [], o2,
              (⋅(o3 ++ List.concat cc ++ lc) ++ os'), os,
              4, 2, kSf,
              [], (⋅(b3, c, la)%V ++ rtr').
            doneL.
            iSplit. iPureIntro. by easy_config.
            iFrame. iFrame "#".
            iSplit. by isEmptyDeque.
            doneL.
            iSplit; [ iApply (big_sepL2_app) |].
            ** simpl; doneR.
              iNext. iClear "Hrtr".
              rewrite triple_unfold.
              iExists b3, c, la, o3, cc, lc, 2, kL, tr.
              iSplit. iPureIntro. destruct (length cc); constructor; clear H H0; invert_all_in; by (list_elem_of || auto with arith).
              doneL. iFrame "#".
              iSplit. iApply (big_sepL2_mono with "Htrtr"). by auto.
              iPureIntro.
              done.
            ** iDestruct (big_sepL2_app_inv with "Hrtr") as "[_ Hrtr']". by left.
              iApply (big_sepL2_mono with "Hrtr'"). by auto.
            ** iPureIntro.
              rewrite Hoeq /= -!app_assoc Hleq.
              aac_rewrite Hoeq'.
              aac_reflexivity.
        Opaque isSpecialTriple.
        * Transparent isNotSpecialTriple. wp_pures.
          (* appeler la spec de pop_case_2_not_special *)
          rewrite /prepare_pop_case_2.
          iDestruct "Ht" as (fi c la fc cc lc kF kL tr) "(%tconf & -> & #Hfi & #Hc & #Hla & #Htrtr & %Hleq)".
          wp_pures.
          wp_apply (bhas_length_3_spec with "Hfi") as "_".
          inversion tconf; wp_pures.
          wp_apply (bconcat32_spec with "[Hp Hm]") as (b') "Hb'". by iFrame "#".
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
            rewrite Hlen in H8.
            iDestruct (buffer_length with "Hs'") as "%Hslen".
            assert (ks' > 0) as Hslen' by (inversion conf'; invert_all_in; lia).
            rewrite !length_app in H8.
            lia.
          }
          wp_pures.
          wp_apply (bis_empty_spec with "Hla") as "_".
          wp_pures.
          (*
          assert (kL = 0 ∨ kL ∈ [2; 3]) as Hkl. by invert_all_in.
          destruct Hkl as [-> | Hkl]; wp_pures.
          -- *)
            iModIntro. iApply "Hψ".
            iExists b', NONEV, fi, d', s, (op ++ om), [], fc, os', os,
              5, 2, kSf, [], rtr'.
            doneL.
            iSplit. iPureIntro. by easy_config.
            iFrame "#". iFrame.
            iSplit. by isEmptyDeque.
            doneL.
            iSplit. iApply (big_sepL2_mono with "Htr'"). by auto.
            destruct lc; [| iDestruct (buffer_length with "Hla") as "%No"; by inversion No ].
            destruct cc; [| by inversion H6 ].
            iPureIntro.
            rewrite Hoeq Hleq /= app_nil_r.
            aac_reflexivity.
        Opaque isNotSpecialTriple.
    - wp_pures.
      wp_bind (let: "f" := _ in _)%E.
      wp_apply (pop_triple_spec with "[iH]").
      + iSplit. iExact "Hℓ".
        iSplit. iExact "Hltr".
        iApply "iH".
      + Transparent isSpecialTriple.
        iIntros (t o' ltr' os' d') "([-> ->] & Htr' & [(#Ht & Hd') | (Ht & Hd')])".
        * (* appeler la spec de pop_case_1_special *)
          rewrite /prepare_pop_case_1.
          iDestruct "Ht" as (fi c la fc cc lc kF kL tr) "(%tconf & -> & #Hfi & #Hc & #Hla & #Htrtr & %Hleq)".
          wp_pures.
          wp_apply (bhas_length_3_spec with "Hfi") as "_".
          inversion tconf; wp_pures.
          -- wp_apply (bmove_left_1_33_spec with "[Hp Hfi]"). by iFrame "#".
            iIntros (b1 b2 o1 o2) "(#H1 & #H2 & %Honeq)".
            rewrite /atriple_.
            wp_pures.
            wp_bind (push _ _)%E.
            iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
            iIntros (l') "Hl'".
            iModIntro. wp_pures.
            iModIntro. iApply "Hψ".
            iExists b1, l', m, r, s, o1, (⋅(o2++List.concat cc++lc) ++ os'), om, or, os,
              4, 2, kSf, (⋅(b2, c, la)%V ++ ltr'), rtr.
            doneL.
            iSplit. iPureIntro. by easy_config.
            iFrame. iFrame "#".
            iSplit; [iApply big_sepL2_app; [simpl| ] | iSplit].
            ++ doneR. iNext.
              iClear "Hltr".
              rewrite triple_unfold.
              iExists b2, c, la, o2, cc, lc, 2, kL, tr.
              iSplit. iPureIntro. inversion H6. by easy_config.
              doneL.
              iFrame "#".
              iSplit. iApply (big_sepL2_mono with "Htrtr"). by auto.
              done.
            ++ iApply (big_sepL2_mono with "Htr'"). by auto.
            ++ iApply (big_sepL2_mono with "Hrtr"). by auto.
            ++ iPureIntro.
              rewrite Hoeq /= -!app_assoc Hleq.
              aac_rewrite Honeq.
              aac_reflexivity.
          -- assert (kF = 2 ∨ kF = 3) as [-> | ->] by invert_all_in; wp_pures.
            ++ wp_apply (bconcat32_spec with "[Hp Hfi]") as (b') "Hb'". by iFrame "#".
              wp_pures.
              rewrite !isDeque_unfold.
              iDestruct "Hc" as "[[-> ->] | (%ℓc & -> & Hℓc)]".
                { iDestruct (big_sepL2_nil_inv_r with "Htrtr") as "->". inversion H7. }
              wp_pures.
              wp_apply (abuffer_spec_explicit with "Hla") as "Ht". by assumption.
              wp_pures.
              wp_bind (push _ _)%E.
              iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
              iIntros (l') "Hl'".
              iModIntro. wp_pures.
              wp_apply (dconcat_spec_helper with "[Hℓc Hl']") as (l) "Hl".
                { assumption. }
                { iFrame. ℓisDeque ℓc. iExact "Hℓc". }
              wp_pures.
              iModIntro.
              iApply "Hψ".
              iExists b', l, m, r, s, (op ++ fc), (cc ++ ⋅lc ++ os'), om, or, os,
                5, 2, kSf, (tr ++ ⋅(la, NONEV, bempty)%V ++ ltr'), rtr.
              doneL.
              iSplit. iPureIntro. simpl. by easy_config.
              rewrite -isDeque_unfold.
              iFrame "#". iFrame.
              iSplit; [iSplit; [| iSplit; [done |]] | iSplit].
              ** iApply (big_sepL2_mono with "Htrtr"). by auto.
              ** iApply (big_sepL2_mono with "Htr'"). by auto.
              ** iApply (big_sepL2_mono with "Hrtr"). by auto.
              ** iPureIntro.
                rewrite Hoeq Hleq !concat_app {1 6}/concat.
                aac_reflexivity.
            ++ wp_apply (bmove_left_1_33_spec with "[Hp Hfi]"). by iFrame "#".
              iIntros (b1 b2 o1 o2) "(#H1 & #H2 & %Hnoeq)".
              rewrite /atriple_.
              wp_pures.
              wp_bind (push _ _)%E.
              iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
              iIntros (l') "Hl'".
              iModIntro. wp_pures.
              iApply "Hψ".
              iModIntro.
              iExists b1, l', m, r, s, o1, (⋅(o2++List.concat cc++lc)++os'), om, or, os,
                4, 2, kSf, (⋅(b2, c, la)%V++ltr'), rtr.
              doneL.
              iSplit. iPureIntro. simpl. by easy_config.
              iFrame "#". iFrame.
              iSplit; [iApply big_sepL2_app; [simpl |]| iSplit].
              ** doneR. iNext.
                iClear "Hltr".
                rewrite triple_unfold.
                iExists b2, c, la, o2, cc, lc, 2, kL, tr.
                iSplitL. iPureIntro. destruct (length cc); [inversion H7 |]; by easy_config.
                doneL.
                iFrame "#".
                iSplit. iApply (big_sepL2_mono with "Htrtr"). by auto.
                done.
              ** iApply (big_sepL2_mono with "Htr'"). by auto.
              ** iApply (big_sepL2_mono with "Hrtr"). by auto.
              ** iPureIntro.
                rewrite Hoeq Hleq !concat_app /=.
                aac_rewrite Hnoeq.
                aac_reflexivity.
          -- assert (kF = 2 ∨ kF = 3) as [-> | ->] by invert_all_in; wp_pures.
            ++ wp_apply (bconcat32_spec with "[Hp Hfi]") as (b') "Hb'". by iFrame "#".
              wp_pures.
              wp_bind (if: _ then _ else #false)%E.
              iApply (wp_strong_mono _ _ _ _ _ (λ v, ⌜ v = #false ⌝)%I). { auto. } { auto. }
                { destruct (bool_decide (c = NONEV)); wp_pures.
                - wp_apply (bis_empty_spec with "Hla") as "_".
                  assert (bool_decide (kL = 0%nat) = false) as -> by invert_all_in.
                  done.
                - done.
                }
              iIntros (v) "->". iModIntro. wp_pures.
              wp_apply (abuffer_spec_explicit with "Hla") as "Ht". by assumption.
              wp_pures.
              wp_bind (push _ _)%E.
              iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
              iIntros (l') "Hl'".
              iModIntro. wp_pures.
              wp_apply (dconcat_spec_helper with "[Hc Hl']") as (l) "Hl".
                { assumption. }
                { iFrame. iExact "Hc". }
              wp_pures.
              iModIntro.
              iApply "Hψ".
              iExists b', l, m, r, s, (op ++ fc), (cc ++ ⋅lc ++ os'), om, or, os,
                5, 2, kSf, (tr ++ ⋅(la, NONEV, bempty)%V ++ ltr'), rtr.
              doneL.
              iSplit. iPureIntro. simpl. by easy_config.
              iFrame "#". iFrame.
              iSplit; [iSplit; [| iSplit; [done |]] | iSplit].
              ** iApply (big_sepL2_mono with "Htrtr"). by auto.
              ** iApply (big_sepL2_mono with "Htr'"). by auto.
              ** iApply (big_sepL2_mono with "Hrtr"). by auto.
              ** iPureIntro.
                rewrite Hoeq Hleq !concat_app {1 6}/concat.
                aac_reflexivity.
            ++ wp_apply (bmove_left_1_33_spec with "[Hp Hfi]"). by iFrame "#".
              iIntros (b1 b2 o1 o2) "(#H1 & #H2 & %Hnoeq)".
              rewrite /atriple_.
              wp_pures.
              wp_bind (push _ _)%E.
              iApply (wp_strong_mono with "Hd'"). { auto. } { auto. }
              iIntros (l') "Hl'".
              iModIntro. wp_pures.
              iApply "Hψ".
              iModIntro.
              iExists b1, l', m, r, s, o1, (⋅(o2++List.concat cc++lc)++os'), om, or, os,
                4, 2, kSf, (⋅(b2, c, la)%V++ltr'), rtr.
              doneL.
              iSplit. iPureIntro. simpl. by easy_config.
              iFrame "#". iFrame.
              iSplit; [iApply big_sepL2_app; [simpl |]| iSplit].
              ** doneR. iNext.
                iClear "Hltr".
                rewrite triple_unfold.
                iExists b2, c, la, o2, cc, lc, 2, kL, tr.
                iSplitL. iPureIntro.
                  destruct (length cc); constructor; clear H6 H0;
                  invert_all_in; (lia || list_elem_of).
                doneL.
                iFrame "#".
                iSplit. iApply (big_sepL2_mono with "Htrtr"). by auto.
                done.
              ** iApply (big_sepL2_mono with "Htr'"). by auto.
              ** iApply (big_sepL2_mono with "Hrtr"). by auto.
              ** iPureIntro.
                rewrite Hoeq Hleq !concat_app /=.
                aac_rewrite Hnoeq.
                aac_reflexivity.
        Opaque isSpecialTriple.
        * Transparent isNotSpecialTriple.
          (* appeler la spec de pop_case_1_not_special *)
          rewrite /prepare_pop_case_1.
          iDestruct "Ht" as (fi c la fc cc lc kF kL tr) "(%tconf & -> & #Hfi & #Hc & #Hla & #Htrtr & %Hleq)".
          wp_pures.
          wp_apply (bhas_length_3_spec with "Hfi") as "_".
          inversion tconf; wp_pures.
          wp_apply (bconcat32_spec with "[Hp Hm]") as (b') "Hb'". by iFrame "#".
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
            rewrite Hlen in H8.
            iDestruct (buffer_length with "Hs'") as "%Hslen".
            assert (ks' > 0) as Hslen' by (inversion conf'; invert_all_in; lia).
            rewrite !length_app in H8.
            lia.
          }
          wp_pures.
          wp_apply (bis_empty_spec with "Hla") as "_".
          wp_pures.
          iModIntro. iApply "Hψ".
          iExists b', d', m, r, s, (op ++ fc), os', om, or, os,
            5, 2, kSf, ltr', rtr.
          rewrite -!isDeque_unfold.
          doneL.
          iSplit. iPureIntro. by easy_config.
          iFrame "#". iFrame.
          iSplit. iApply (big_sepL2_mono with "Htr'"). by auto.
          iSplit. iApply (big_sepL2_mono with "Hrtr"). by auto.
          destruct lc; [| iDestruct (buffer_length with "Hla") as "%No"; by inversion No ].
          destruct cc; [| by inversion H6 ].
          iPureIntro.
          rewrite Hoeq Hleq /= app_nil_r.
          aac_reflexivity.
        Opaque isNotSpecialTriple.
    Qed.

  Global Instance isPopFiveTuplePersistent o d : Persistent (isPopFiveTuple o d).
  Proof.
    rewrite /isPopFiveTuple.
    repeat (apply bi.exist_persistent; intro).
    repeat (apply bi.sep_persistent; apply _).
  Qed.

End lemmas.
