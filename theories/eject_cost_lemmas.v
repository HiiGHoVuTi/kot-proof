From iris.heap_lang Require Import lang proofmode notation.
From iris.bi Require Import derived_laws.

From Coq Require Import List.
Import ListNotations.

From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Deque Require Import common tick shared_ref deque_cost push_cost concat_cost pop_cost_lemmas.

Section lemmas.

  Context `{!heapGS Σ} `{!na_invG Σ}.
  Context {π : gname}.

  Notation "kp ∘ ks" := (kp ⋄ ks - 1).
  Definition Δ (kp ks : nat) := (kp ∘ ks) - (kp ⋄ ks).
  Notation "kp ⊻ ks" := ((kp ∘ ks) + (kp ⋄ ks)) (at level 60).

  Variable COST_ANALYSIS : TICK_COST = 1.

  (* Five-tuple configuration for calling naive_eject *)
  Inductive eject_configuration : nat -> nat -> nat -> nat -> nat -> Prop :=
    | eject_suffix_only : forall s, s ∈ [1..8] -> eject_configuration 0 0 0 0 s
    | eject_has_middle : forall p ld rd s, p ∈ [3..6] -> s ∈ [4..6] -> eject_configuration p ld 2 rd s.

 Definition isEjectFiveTuple := (
    λ n o kPr kSf d, ∃ (pr ld md rd sf : val)
      pr_content left_content md_content right_content sf_content
      (kMd : nat) left_triples right_triples,
      ⌜ d = (pr, ld, md, rd, sf)%V ⌝ ∗
      ⌜ eject_configuration kPr (length left_content) kMd (length right_content) kSf ⌝ ∗
      buffer kPr pr_content pr ∗
      isDeque π (S n) left_triples ld ∗
      buffer kMd md_content md ∗
      isDeque π (S n) right_triples rd ∗
      buffer kSf sf_content sf ∗
      ([∗list] c;tr ∈ left_content;left_triples, ▷ triple π (S n) c tr) ∗
      ([∗list] c;tr ∈ right_content;right_triples, ▷ triple π (S n) c tr) ∗
      ⌜ o = pr_content ++ List.concat left_content ++ md_content ++ List.concat right_content ++ sf_content ⌝
  )%I.

 Definition isUnsafeEjectFiveTuple := (
    λ π n o d, ∃ (pr ld md rd sf : val)
      pr_content left_content md_content right_content sf_content
      (kPr : nat) left_triples right_triples,
      ⌜ d = (pr, ld, md, rd, sf)%V ⌝ ∗
      ⌜ five_tuple_configuration kPr (length left_content) 2 (length right_content) 3 ⌝ ∗
      five_tuple_potential kPr 3 ∗
      buffer kPr pr_content pr ∗
      isDeque π (S n) left_triples ld ∗
      buffer 2 md_content md ∗
      isDeque π (S n) right_triples rd ∗
      buffer 3 sf_content sf ∗
      ([∗list] c;tr ∈ left_content;left_triples, ▷ triple π (S n) c tr) ∗
      ([∗list] c;tr ∈ right_content;right_triples, ▷ triple π (S n) c tr) ∗
      ⌜ o = pr_content ++ List.concat left_content ++ md_content ++ List.concat right_content ++ sf_content ⌝
  )%I.

  Lemma safe_decidable : forall n o f,
    fiveTuple π n o f -∗
      (isUnsafeEjectFiveTuple π n o f ∗ WP naive_eject_safe f {{ x, ⌜ x = #false ⌝ }})
    ∨ ∃ kp ks, isEjectFiveTuple n o kp ks f ∗ ⏱ (kp ⋄ ks) ∗ WP naive_eject_safe f {{ x, ⌜ x = #true ⌝ }}.
  Proof.
    iIntros (n o f) "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                      %kPr & %kMd & %kSf & %ltr & %rtr &
                      %Heq & %conf & pot & #Hp & #Hl & #Hm & #Hr & #Hs &
                      #Hltr & #Hrtr & %Hoeq)".
    inversion conf.
    - iRight.
      iExists 0, kSf.
      iFrame.
      iSplitL.
      + iExists p, l, m, r, s, op, ol, om, or, os, 0, ltr, rtr.
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
      + iExists kPr, kSf. iSplitR.
        * iExists p, l, m, r, s, op, ol, om, or, os, kMd, ltr, rtr.
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

  Ltac split_t τ := iDestruct (split_time τ with "τ") as "[ι τ]"; [ try lia |].
  Ltac split_ti kp ks := iDestruct (split_time (kp ⊻ ks) with "τ") as "[ι τ]"; [ invert_all_in; simpl; try lia |].
  Ltac split_Δ kp ks := split_t (Z.to_nat (Δ kp ks)); [ try (invert_all_in; rewrite /Δ /=; lia) |].
  Ltac gather_t pot := iDestruct (time_combine with String.concat "" ["[τ "; pot; "]"]) as "τ"; [ iFrame |].

  Lemma safe_naive_eject : forall n o kp ks f,
    {{{ isEjectFiveTuple n o kp ks f ∗ ⏱ (kp ∘ ks) }}}
      naive_eject f
    {{{ x d o', RET (d, x)%V; isDeque π n o' d ∗ ⌜ o = o' ++ ⋅x ⌝ }}}.
  Proof.
    iIntros (n o kPr kSf f ψ) "[Hf τ] Hψ".
    iDestruct "Hf" as "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                      %kMd & %ltr & %rtr &
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
        wp_apply (ssref_alloc π (fiveTuple π n o') with "[τ]") as "%ℓ'' #Hℓ''".
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
          iSplit. rewrite /five_tuple_potential /=.
            iDestruct (split_time (0 ⋄ S kSf') with "τ") as "[ι _]".
              { invert_all_in; auto with arith. }
            iExact "ι".
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
      split_t (kPr ⋄ kS). by invert_all_in.
      wp_apply (bis_empty_spec with "Hm") as "_".
      rewrite /assemble_.
      wp_pures.
      wp_apply (ssref_alloc π (fiveTuple π n _) with "[ι]") as "%ℓ'' #Hℓ''".
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

  Lemma unsafe_naive_eject : forall n o f,
    {{{ fiveTuple π n o f ∗ ⏱ 1 }}}
      naive_eject f
    {{{ x (d : val) o', RET (d, x)%V;
      ⌜ o = o' ++ ⋅x ⌝ ∗
      ∀ y : val,
        WP inject d y {{ d, isDeque π n (o' ++ ⋅y) d }}
    }}}.
  Proof.
    iIntros (n o f ψ) "[Hf τ] Hψ".
    iDestruct "Hf" as "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                      %kPr & %kMd & %kSf & %ltr & %rtr &
                      -> & %conf & pot & #Hp & #Hl & #Hm & #Hr & #Hs &
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
          rewrite -COST_ANALYSIS.
          wp_apply (tick_spec with "τ") as "_".
          rewrite COST_ANALYSIS.
          rewrite /asingleton.
          wp_pures.
          wp_apply (bpush_spec) as (b) "Hb". by iApply bempty_spec.
          wp_pures.
          wp_apply (ssref_alloc _ (fiveTuple π n [y]) with "[Hb]") as (ℓ) "Hℓ".
            { iExists bempty, NONEV, bempty, NONEV, b, [], [], [], [], [y], 0, 0, 1, [], [].
              rewrite !app_nil_r /five_tuple_potential /=.
              iFrame. iFrame "#".
              repeat doneL.
              iSplit. by easy_config.
              iSplit. by iApply time_zero.
              repeat (iSplit; [iApply bempty_spec || isEmptyDeque |]).
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
        rewrite -COST_ANALYSIS.
        wp_apply (tick_spec with "τ") as "_".
        rewrite COST_ANALYSIS.
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
        wp_apply (ssref_alloc _ (fiveTuple π n (o' ++ ⋅y')) with "[Hb pot]") as (ℓ') "Hℓ'".
          { iExists bempty, NONEV, bempty, NONEV, b, [], [], [], [], (o'++⋅y'), 0, 0, (ks+1), [], [].
            rewrite /five_tuple_potential /=.
            iFrame. iFrame "#".
            repeat doneL.
            iSplit. rewrite H H1 -H0 -H2 in conf. done.
            repeat (iSplit; [iApply bempty_spec || isEmptyDeque |]).
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
      rewrite -COST_ANALYSIS.
      wp_apply (tick_spec with "τ") as "_".
      rewrite COST_ANALYSIS.
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
      wp_apply (ssref_alloc π (fiveTuple π n (op ++ concat ol ++ om ++ concat or ++ o' ++ ⋅y)) with "[pot]") as "%ℓ' Hℓ'".
      + iExists p,l,m,r,p',op,ol,om,or,(o'++⋅y),kPr,2,(ks+1),ltr,rtr.
        iFrame "#".
        doneL.
        iSplit. iPureIntro. rewrite H3. done.
        iSplit. iExact "pot".
        iSplit. iApply (big_sepL2_mono with "Hltr"). by auto.
        iSplit. iApply (big_sepL2_mono with "Hrtr"). by auto.
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

  Lemma inspect_last_spec : forall n o f,
    {{{ isPersFiveTuple π n o f }}}
      inspect_last f
    {{{ o' t, RET t; ⌜ o = o' ++ ⋅t ⌝  }}}.
  Proof.
    iIntros (n o f ψ) "Hf Hψ".
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
    λ n o t,
      ∃ (fst ch lst : val)
        fst_content child_content lst_content
        (kFst kLst : nat) triples,
        ⌜ special_triple_configuration kFst (length child_content) kLst ⌝ ∗
        ⌜ t = (fst, ch, lst)%V ⌝ ∗
        buffer kFst fst_content fst ∗
        isDeque π n triples ch ∗
        buffer kLst lst_content lst ∗
        ([∗list] c;tr ∈ child_content;triples, ▷ triple π n c tr) ∗
        ⌜ o = fst_content ++ List.concat child_content ++ lst_content ⌝
  )%I.

  Definition isNotSpecialTriple := (
    λ n o t,
      ∃ (fst ch lst : val)
        fst_content child_content lst_content
        (kFst kLst : nat) triples,
        ⌜ not_special_triple_configuration kFst (length child_content) kLst ⌝ ∗
        ⌜ t = (fst, ch, lst)%V ⌝ ∗
        buffer kFst fst_content fst ∗
        isDeque π n triples ch ∗
        buffer kLst lst_content lst ∗
        ([∗list] c;tr ∈ child_content;triples, ▷ triple π n c tr) ∗
        ⌜ o = fst_content ++ List.concat child_content ++ lst_content ⌝
  )%I.

  Lemma antinormalize_special_spec : forall n o t,
    {{{ @pop_cost_lemmas.isSpecialTriple Σ _ _ π  n o t }}}
      antinormalize t
    {{{ t', RET t'; isSpecialTriple n o t' }}}.
  Proof.
    iIntros (n o t ψ) "Ht Hψ".
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

  Lemma antinormalize_not_special_spec : forall n o t,
    {{{ @pop_cost_lemmas.isNotSpecialTriple Σ _ _ π n o t }}}
      antinormalize t
    {{{ t', RET t'; isNotSpecialTriple n o t' }}}.
  Proof.
    iIntros (n o t ψ) "Ht Hψ".
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
    λ n o d, ∃ (pr ld md rd sf : val)
      pr_content left_content md_content right_content sf_content
      (kPr kMd kSf : nat) left_triples right_triples,
      ⌜ d = (pr, ld, md, rd, sf)%V ⌝ ∗
      ⌜ five_tuple_configuration kPr (length left_content) kMd (length right_content) kSf ⌝ ∗
      buffer kPr pr_content pr ∗
      isDeque π (S n) left_triples ld ∗
      buffer kMd md_content md ∗
      isDeque π (S n) right_triples rd ∗
      buffer kSf sf_content sf ∗
      ([∗list] c;tr ∈ left_content;left_triples, triple π (S n) c tr) ∗
      ([∗list] c;tr ∈ right_content;right_triples, triple π (S n) c tr) ∗
      ⌜ o = pr_content ++ List.concat left_content ++ md_content ++ List.concat right_content ++ sf_content ⌝
  )%I.

  Lemma add_later : forall n o d, isPersFiveTupleLaterRemoved n o d -∗ isPersFiveTuple π n o d.
  Proof.
    iIntros (n o d) "Hd".
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

  Lemma eject_triple_spec : forall n os tr ℓ,
    {{{ ℓ ⤇{π, n} fiveTuple π n tr ∗ Token π n
      ∗ ⏱ time_for_pop ∗ ([∗list] x;y ∈ os;tr, triple π n x y)
      ∗ (∀ ℓ x o,
          ℓ ⤇{π, n} fiveTuple π n (o ++ ⋅x) -∗
          ⏱ time_for_pop -∗
          Token π n -∗
          WP eject_nonempty #ℓ
            {{ r, ∃ d, ⌜ r = (d, x)%V ⌝ ∗ isDeque π n o d ∗ Token π n }})
    }}}
      subst "eject_nonempty" eject_nonempty (eject_triple #ℓ)
    {{{ t' t o tr' os' (d' : val), RET (d', t)%V; Token π n ∗
      ⌜ tr = tr' ++ ⋅t' ∧ os = os' ++ ⋅o ⌝ ∗
      ([∗list] x;y ∈ os';tr', triple π n x y) ∗
      ( isSpecialTriple n o t ∗ ⏱ (time_for_pop-4) ∗ (∀ x : val, WP inject d' x {{ d'', isDeque π n (tr' ++ ⋅x) d'' }})
      ∨ isNotSpecialTriple n o t ∗ isDeque π n tr' d'
      )
    }}}.
  Proof.
    iIntros (n os tr d Hψ) "(#Hd & O & τ & Htr & iH) Hψ".
    rewrite /pop_triple.
    wp_pures.
    wp_apply (ssref_read _ _ _ with "[O]").
    { iFrame "#". iFrame.
      iIntros (v) "Hv".
      by iApply persist_structure.
    }
    Opaque isPersFiveTuple.
    iIntros (f) "[#Hf O]".
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
    iAssert (triple π n l t) with "[Ht]" as "Ht".
      { simpl. iDestruct "Ht" as "[A _]". done. }
    iDestruct (pop_cost_lemmas.special_decidable COST_ANALYSIS with "Ht") as "[#Ht' | #Ht']";
    iCombine "Ht' Ht'" as "[Ht! Ht!']";
    iDestruct "Ht!'" as (fi c la fc cc lc kF kL tr) "(%conf & -> & Hf' & Hc & Hl & Htrtr & %Hleq)";
    inversion conf.
    Opaque pop_cost_lemmas.isSpecialTriple pop_cost_lemmas.isNotSpecialTriple isSpecialTriple isNotSpecialTriple.
    + rewrite isDeque_unfold.
      iDestruct "Hc" as "[[-> ->] | (%ℓ & -> & Hℓ)]".
      2: {
        iDestruct (na_own_acc (↑ W n) with "O") as "[O A]". by apply access_stage.
        iInv "Hℓ" as "[(%v' & Hv' & Hℓ') O]".
        wp_pure.
        iExFalso.
        iDestruct "Hv'" as (pr' ld' md' rd' sf' pc' lc' mc' rc' sc' kp' km' ks' lt rt) "(_ & %conf' & _ & _ & _ & _ & _ & Hs & _ & _ & ->)".
        iDestruct (big_sepL2_length with "Htrtr") as "%Hlen".
        rewrite Hlen in H.
        iDestruct (buffer_length with "Hs") as "%Hslen".
        assert (ks' > 0) as Hslen' by (inversion conf'; invert_all_in; lia).
        rewrite !length_app in H.
        lia.
      }
      wp_pures.
      iDestruct (split_time 1 with "τ") as "[ι τ]". by lia.
      iDestruct (split_time 3 with "τ") as "[ι' τ]". by lia.
      wp_apply (bhas_length_3_spec with "Hf'") as "_".
      wp_pures.
      wp_apply (unsafe_naive_eject with "[ι ι']").
        { iFrame.
          iDestruct (strutcure_and_time with "[ι']") as "H".
            { iFrame.
              by iExact "Hf". }
          iExact "H". }
      iIntros (x' d' o') "(%Hoeq' & Hpush)".
      wp_pures.
      apply app_sing_inv in Hoeq' as [-> <-].
      wp_apply (antinormalize_special_spec with "Ht!") as (t') "Ht''".
      wp_pures. iModIntro.
      iApply "Hψ".
      iSplitL "O". done.
      doneL.
      iSplit. iExact "Htr".
      iLeft.
      iSplitL "Ht''"; [| iSplitL "τ"].
      * iExact "Ht''".
      * by iDestruct (split_time (time_for_pop - 4) with "[τ]") as "[ι _]".
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
        iDestruct (split_time 1 with "τ") as "[ι τ]". by lia.
        iDestruct (split_time 3 with "τ") as "[ι' τ]". by lia.
        wp_apply (unsafe_naive_eject with "[ι ι']").
          { iFrame.
            iDestruct (strutcure_and_time with "[ι']") as "H".
              { iFrame.
                by iExact "Hf". }
            iExact "H". }
        iIntros (x' d' o') "(%Hoeq' & Hpush)".
        wp_pures.
        apply app_sing_inv in Hoeq' as [-> <-].
        wp_apply (antinormalize_special_spec with "Ht!") as (t') "Ht''".
        wp_pures. iModIntro.
        iApply "Hψ".
        iFrame.
        doneL.
        iLeft.
        iSplitL "Ht''"; [| iSplitL "τ"].
        -- iExact "Ht''".
        -- by iDestruct (split_time (time_for_pop - 4) with "[τ]") as "[ι _]".
        -- iExact "Hpush".
      * iDestruct (split_time 1 with "τ") as "[ι τ]". by lia.
        iDestruct (split_time 3 with "τ") as "[ι' τ]". by lia.
        wp_apply (unsafe_naive_eject with "[ι ι']").
          { iFrame.
            iDestruct (strutcure_and_time with "[ι']") as "H".
              { iFrame.
                by iExact "Hf". }
            iExact "H". }
        iIntros (x' d' o') "(%Hoeq' & Hpush)".
        wp_pures.
        apply app_sing_inv in Hoeq' as [-> <-].
        wp_apply (antinormalize_special_spec with "Ht!") as (t') "Ht''".
        wp_pures. iModIntro.
        iApply "Hψ".
        iFrame.
        doneL.
        iLeft.
        iSplitL "Ht''"; [| iSplitL "τ"].
        -- iExact "Ht''".
        -- by iDestruct (split_time (time_for_pop - 4) with "[τ]") as "[ι _]".
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
        iDestruct (split_time 1 with "τ") as "[ι τ]". by lia.
        iDestruct (split_time 3 with "τ") as "[ι' τ]". by lia.
        wp_apply (unsafe_naive_eject with "[ι ι']").
          { iFrame.
            iDestruct (strutcure_and_time with "[ι']") as "H".
              { iFrame.
                by iExact "Hf". }
            iExact "H". }
        iIntros (x' d' o') "(%Hoeq' & Hpush)".
        wp_pures.
        apply app_sing_inv in Hoeq' as [-> <-].
        wp_apply (antinormalize_special_spec with "Ht!") as (t') "Ht''".
        wp_pures. iModIntro.
        iApply "Hψ".
        iFrame.
        doneL.
        iLeft.
        iSplitL "Ht''"; [| iSplitL "τ"].
        -- iExact "Ht''".
        -- by iDestruct (split_time (time_for_pop - 4) with "[τ]") as "[ι _]".
        -- iExact "Hpush".
      * iDestruct (split_time 1 with "τ") as "[ι τ]". by lia.
        iDestruct (split_time 3 with "τ") as "[ι' τ]". by lia.
        wp_apply (unsafe_naive_eject with "[ι ι']").
          { iFrame.
            iDestruct (strutcure_and_time with "[ι']") as "H".
              { iFrame.
                by iExact "Hf". }
            iExact "H". }
        iIntros (x' d' o') "(%Hoeq' & Hpush)".
        wp_pures.
        apply app_sing_inv in Hoeq' as [-> <-].
        wp_apply (antinormalize_special_spec with "Ht!") as (t') "Ht''".
        wp_pures. iModIntro.
        iApply "Hψ".
        iFrame.
        doneL.
        iLeft.
        iSplitL "Ht''"; [| iSplitL "τ"].
        -- iExact "Ht''".
        -- by iDestruct (split_time (time_for_pop - 4) with "[τ]") as "[ι _]".
        -- iExact "Hpush".
    + wp_pures.
      wp_apply (bhas_length_3_spec with "Hf'") as "_".
      wp_pures.
      wp_apply (bis_empty_spec with "Hl") as "_".
      wp_pures.
      wp_bind  (eject_nonempty _)%E.
      iApply (wp_strong_mono with "[iH τ O]").
        { auto. } { reflexivity. }
      * iApply ("iH" with "[] [τ]"); [| auto | auto]. iExact "Hd".
      * iIntros (v) "(%d' & -> & Hd' & O)". iModIntro.
        wp_pures.
        wp_apply (antinormalize_not_special_spec with "Ht!") as (t') "Ht''".
        wp_pures. iModIntro.
        iApply "Hψ".
        iFrame. doneL.
        iRight.
        iFrame.
  Unshelve.
    simpl. apply fiveTuplePersistent.
  Qed.

  Lemma prepare_eject_spec : forall n o f,
    {{{ isUnsafeEjectFiveTuple π n o f ∗ ⏱ (time_for_pop - 1) ∗ Token π (S n) ∗
      ∀ ℓ x o', ℓ ⤇{π , S n} fiveTuple π (S n) (o' ++ ⋅x) -∗
        ⏱ time_for_pop -∗
        Token π (S n) -∗
        WP eject_nonempty #ℓ {{ r, ∃ d, ⌜ r = (d, x)%V ⌝ ∗ isDeque π (S n) o' d ∗ Token π (S n) }}
    }}}
      subst "eject_nonempty" eject_nonempty (prepare_eject f)
    {{{ f' kp ks, RET f'; isEjectFiveTuple n o kp ks f' ∗ Token π (S n) ∗ ⏱ (kp ⊻ ks) }}}.
  Proof.
    Opaque eject_triple.
    iIntros (n o f ψ) "(Hf & τ & O & iH) Hψ".
    rewrite /isUnsafeEjectFiveTuple.
    iDestruct "Hf" as "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                      %kPr & %ltr & %rtr &
                      -> & %conf & pot & #Hp & #Hl & #Hm & #Hr & #Hs &
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
        iModIntro. iSplitR "O τ"; [| iSplitL "O"; [done | ]].
        * iExists bempty, NONEV, bempty, NONEV, b', [], [], [], [], (op++om++os),
            0, [], [].
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
        * simpl. by split_t 3.
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
        split_ti k 4.
        iApply "Hψ". iSplitR "O ι"; [| by iFrame].
        iExists b1, NONEV, b2, NONEV, b3, o1, [], o2, [], o3,
          2, [], [].
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
      iDestruct (time_combine with "[τ pot]") as "τ". by iFrame.
      iDestruct (split_time time_for_pop with "τ") as "[ι τ']".
      invert_all_in; simpl; try lia.
      wp_apply (eject_triple_spec with "[ι O iH]").
      + iSplit. iExact "Hℓ".
        iSplitL "O". done.
        iSplitL "ι". done.
        iSplit. iExact "Hltr".
        iApply "iH".
      + Transparent isSpecialTriple.
        iIntros (t' t o' rtr' os' d') "(O & [-> ->] & Htr' & [(#Ht & τ & Hd') | (Ht & Hd')])".
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
              split_ti kPr 4.
              iSplitR "O ι"; [| by iFrame].
              iExists p, l', b2, NONEV, b3,
                op, (os' ++ ⋅(o1++List.concat cc)), o2, [], o3, 2,
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
              split_ti kPr 4.
              iSplitR "O ι"; [| by iFrame].
              iExists p, l', b2, NONEV, b3,
                op, (os' ++ ⋅(fc ++ List.concat cc ++ o1)), o2, [], o3, 2,
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
              iDestruct (split_time time_for_concat with "τ") as "[ι τ]". by lia.
              wp_apply (dconcat_spec_helper with "[Hℓc Hl' ι O]") as (l) "[Hl O]".
                { assumption. }
                { iFrame. ℓisDeque ℓc. iExact "Hℓc". }
              wp_pures.
              iModIntro.
              iApply "Hψ".
              split_ti kPr 5.
              iSplitR "O ι"; [| by iFrame].
              iExists p, l, la, NONEV, b', op, ((os'++⋅fc)++cc), lc, [], (om++os),
                2, ((rtr'++⋅(fi, NONEV, bempty)%V)++tr), [].
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
              split_ti kPr 4.
              iSplitR "O ι"; [| by iFrame].
              iExists p, l', b2, NONEV, b3,
                op, (os'++⋅(fc++List.concat cc++o1)), o2, [], o3,
                2, (rtr'++⋅(fi, c, b1)%V), [].
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
                iDestruct (split_time time_for_concat with "τ") as "[ι τ]". by lia.
                wp_apply (dconcat_spec_helper with "[Hc Hl' ι O]") as (l) "[Hl O]".
                  { assumption. }
                  { iFrame. by iFrame "#". }
                wp_pures.
                iModIntro.
                iApply "Hψ".
                split_ti kPr 5.
                iSplitR "O ι"; [| by iFrame].
                iExists p, l, la, NONEV, b', op, ((os'++⋅fc)++cc), lc, [], (om++os),
                2, ((rtr'++⋅(fi, NONEV, bempty)%V)++tr), [].
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
                iDestruct (split_time time_for_concat with "τ") as "[ι τ]". by lia.
                wp_apply (dconcat_spec_helper with "[Hc Hl' ι O]") as (l) "[Hl O]".
                  { assumption. }
                  { iFrame. by iFrame "#". }
                wp_pures.
                iModIntro.
                iApply "Hψ".
                split_ti kPr 5.
                iSplitR "O ι"; [| by iFrame].
                iExists p, l, la, NONEV, b', op, ((os'++⋅_)++cc), lc, [], (om++os),
                  2, ((rtr'++⋅(fi, NONEV, bempty)%V)++tr), [].
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
            split_ti kPr 4.
            iSplitR "O ι"; [| by iFrame].
            iExists p, l', b2, NONEV, b3,
                op, (os'++⋅(fc++List.concat cc++o1)), o2, [], o3,
                2, (rtr'++⋅(fi, c, b1)%V), [].
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
          iDestruct "τ'" as "τ".
          iDestruct "Ht" as (fi c la fc cc lc kF kL tr) "(%tconf & -> & #Hfi & #Hc & #Hla & #Htrtr & %Hleq)".
          wp_pures.
          wp_apply (bhas_length_3_spec with "Hla") as "_".
          inversion tconf; wp_pures.
          wp_apply (bconcat23_spec with "[Hm Hs]") as (b') "Hb'". by iFrame "#".
          rewrite isDeque_unfold.
          iDestruct "Hc" as "[[-> ->] | (%ℓ' & -> & Hℓ')]".
          2: {
            iDestruct (na_own_acc (↑ W (S n)) with "O") as "[O A]". by apply access_stage.
            iInv "Hℓ'" as "[(%v' & Hv' & Hℓ'') O]".
            wp_pure.
            iExFalso.
            iDestruct "Hv'" as (pr' ld' md' rd' sf' pc' lc' mc' rc' sc' kp' km' ks' lt rt) "(_ & %conf' & _ & _ & _ & _ & _ & Hs' & _ & _ & ->)".
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
            split_ti kPr 5.
            iSplitR "O ι"; [| by iFrame].
            iExists p, d', la, NONEV, b', op, os', lc, [], (om++os),
              2, rtr', [].
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
      iDestruct (time_combine with "[τ pot]") as "τ". by iFrame.
      iDestruct (split_time time_for_pop with "τ") as "[ι τ']".
      invert_all_in; simpl; lia.
      wp_apply (eject_triple_spec with "[ι O iH]").
      + iSplit. iExact "Hℓ".
        iSplitL "O". done.
        iSplitL "ι". done.
        iSplit. iExact "Hrtr".
        iApply "iH".
      + Transparent isSpecialTriple.
        iIntros (t' t o' rtr' os' d') "(O & [-> ->] & Htr' & [(#Ht & τ & Hd') | (Ht & Hd')])".
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
              split_ti kPr 4.
              iSplitR "O ι"; [| by iFrame].
              iExists p, l, m, r', b2, op, ol, om, (os'++⋅(fc++List.concat cc++o1)), o2,
                2, ltr, (rtr' ++ ⋅(b1, c, bempty)%V).
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
              split_ti kPr 4.
              iSplitR "O ι"; [| by iFrame].
              iExists p, l, m, r', b2, op, ol, om, (os'++⋅(fc++List.concat cc++o1)), o2,
                2, ltr, (rtr' ++ ⋅(fi, c, b1)%V).
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
              iDestruct (split_time time_for_concat with "τ") as "[ι τ]". by lia.
              wp_apply (dconcat_spec_helper with "[Hℓc Hr' ι O]") as (r) "[Hr O]".
                { assumption. }
                { iFrame. ℓisDeque ℓc. iExact "Hℓc". }
              wp_pures.
              iModIntro.
              iApply "Hψ".
              split_ti kPr 5.
              iSplitR "O ι"; [| by iFrame].
              iExists p, l, m, r, b', op, ol, om, ((os' ++ ⋅fc) ++ cc), (lc ++ os),
                2, ltr, ((rtr'++⋅(fi, NONEV, bempty)%V)++tr).
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
              split_ti kPr 4.
              iSplitR "O ι"; [| by iFrame].
              iModIntro.
              iExists p, l, m, r', b2, op, ol, om, (os'++⋅(fc++List.concat cc++o1)), o2,
                2, ltr, (rtr'++⋅(fi, c, b1)%V).
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
              iDestruct (split_time time_for_concat with "τ") as "[ι τ]". by lia.
              wp_apply (dconcat_spec_helper with "[Hc Hr' ι O]") as (r) "[Hr O]".
                { assumption. }
                { iFrame. iExact "Hc". }
              wp_pures.
              iModIntro.
              iApply "Hψ".
              split_ti kPr 5.
              iSplitR "O ι"; [| by iFrame].
              iExists p, l, m, r, b', op, ol, om, ((os' ++ ⋅fc) ++ cc), (lc ++ os),
                2, ltr, ((rtr'++⋅(fi, NONEV, bempty)%V)++tr).
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
              split_ti kPr 4.
              iSplitR "O ι"; [| by iFrame].
              iModIntro.
              iExists p, l, m, r', b2, op, ol, om, (os'++⋅(fc++List.concat cc++o1)), o2,
                2, ltr, (rtr' ++ ⋅(fi, c, b1)%V).
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
          wp_pures.
          rewrite !isDeque_unfold.
          iDestruct "Hc" as "[[-> ->] | (%ℓ' & -> & Hℓ')]".
          2: {
            iDestruct (na_own_acc (↑ W (S n)) with "O") as "[O A]". by apply access_stage.
            iInv "Hℓ'" as "[(%v' & Hv' & Hℓ'') O]".
            wp_pure.
            iExFalso.
            iDestruct "Hv'" as (pr' ld' md' rd' sf' pc' lc' mc' rc' sc' kp' km' ks' lt rt) "(_ & %conf' & _ & _ & _ & _ & _ & Hs' & _ & _ & ->)".
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
          iDestruct "τ'" as "τ".
          split_ti kPr 5.
          iSplitR "O ι"; [| by iFrame].
          iExists p, l, m, d', b', op, ol, om, os', (lc++os),
            2, ltr, rtr'.
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

  Global Instance isPopFiveTuplePersistent n o kp ks d : Persistent (isEjectFiveTuple n o kp ks d).
  Proof.
    rewrite /isEjectFiveTuple.
    repeat (apply bi.exist_persistent; intro).
    repeat (apply bi.sep_persistent; apply _).
  Qed.

End lemmas.

Notation "kp ∘ ks" := (kp ⋄ ks - 1).
Notation "kp ⊻ ks" := ((kp ∘ ks) + (kp ⋄ ks)) (at level 60).

Ltac split_t τ := iDestruct (split_time τ with "τ") as "[ι τ]"; [ try lia |].
Ltac split_ti kp ks := iDestruct (split_time (kp ⊻ ks) with "τ") as "[ι τ]"; [ invert_all_in; simpl; try lia |].
Ltac split_Δ kp ks := split_t (Z.to_nat (Δ kp ks)); [ try (invert_all_in; rewrite /Δ /=; lia) |].
Ltac gather_t pot := iDestruct (time_combine with String.concat "" ["[τ "; pot; "]"]) as "τ"; [ iFrame |].
