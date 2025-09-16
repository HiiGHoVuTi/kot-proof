From iris.heap_lang Require Import lang proofmode notation.
From iris.bi Require Import derived_laws.

From Coq Require Import List.
Import ListNotations.

From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Deque Require Import common tick shared_ref deque_cost push_cost concat_cost.

Section lemmas.

  Context `{!heapGS Σ} `{!na_invG Σ}.
  Context {π : gname}.

 (* TODO(Juliette): move me *)
 Definition isUnsafePopFiveTuple := (
    λ π n o d, ∃ (pr ld md rd sf : val)
      pr_content left_content md_content right_content sf_content
      (kMd kSf : nat) left_triples right_triples,
      ⌜ d = (pr, ld, md, rd, sf)%V ⌝ ∗
      ⌜ five_tuple_configuration 3 (length left_content) kMd (length right_content) kSf ⌝ ∗
      five_tuple_potential 3 kSf ∗
      buffer 3 pr_content pr ∗
      isDeque π (S n) left_triples ld ∗
      buffer kMd md_content md ∗
      isDeque π (S n) right_triples rd ∗
      buffer kSf sf_content sf ∗
      ([∗list] c;tr ∈ left_content;left_triples, ▷ triple π (S n) c tr) ∗
      ([∗list] c;tr ∈ right_content;right_triples, ▷ triple π (S n) c tr) ∗
      ⌜ o = pr_content ++ List.concat left_content ++ md_content ++ List.concat right_content ++ sf_content ⌝
  )%I.

  Lemma safe_decidable : forall n o f,
    fiveTuple π n o f -∗
      isUnsafePopFiveTuple π n o f ∧ WP naive_pop_safe f {{ x, ⌜ x = #false ⌝ }}
    ∨ isPopFiveTuple π n o f ∧ WP naive_pop_safe f {{ x, ⌜ x = #true ⌝ }}.
  Proof.
    iIntros (n o f) "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                      %kPr & %kMd & %kSf & %ltr & %rtr &
                      %Heq & %conf & pot & Hp & Hl & Hm & Hr & Hs &
                      Hltr & Hrtr & %Hoeq)".
    destruct (dec_eq_nat kPr 3) as [-> | HkPr]; [iLeft | iRight].
    - iSplit.
      + iExists p, l, m, r, s, op, ol, om, or, os, kMd, kSf, ltr, rtr.
        iFrame.
        iSplit; done.
      + rewrite /naive_pop_safe Heq.
        wp_pures.
        inversion conf.
        wp_apply (bis_empty_spec with "Hm") as "_".
        wp_pures.
        wp_apply (blength_spec with "Hp") as "_".
        wp_pures.
        done.
    - iSplit.
      + iExists p, l, m, r, s, op, ol, om, or, os, kPr, kMd, kSf, ltr, rtr.
        iFrame.
        doneL. doneR.
        iPureIntro.
        inversion conf.
        * by easy_config.
        * inversion H; [ exfalso; lia |].
          by easy_config.
      + rewrite /naive_pop_safe Heq.
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

  Lemma safe_naive_pop : forall n o f,
    {{{ isPopFiveTuple π n o f ∗ ⏱ 2 }}}
      naive_pop f
    {{{ x d o', RET (x, d)%V; isDeque π n o' d ∗ ⌜ o = ⋅x ++ o' ⌝ }}}.
  Proof.
    iIntros (n o f ψ) "[Hf τ] Hψ".
    iDestruct "Hf" as "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                      %kPr & %kMd & %kSf & %ltr & %rtr &
                      -> & %conf & pot & #Hp & #Hl & #Hm & #Hr & #Hs &
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
        wp_apply (ssref_alloc π (fiveTuple π n o') with "[pot]") as "%ℓ'' #Hℓ''".
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
            iDestruct (split_time (0 ⋄ S kSf') with "pot") as "[ι _]".
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
    - change (kPr ∈ map S [3;4;5]) in H.
      apply decrease_in in H as (kP & -> & H).
      wp_apply (bpop_spec with "Hp") as "%b' %x %o' (#Hb' & ->)".
      rewrite /assemble_.
      wp_pures.
      wp_apply (ssref_alloc π (fiveTuple π n _) with "[pot τ]") as "%ℓ'' #Hℓ''".
      + iExists b',l,m,r,s,o',ol,om,or,os,kP,kMd,kSf,ltr,rtr.
        rewrite -H3.
        iFrame. iFrame "#".
        doneL.
        iSplit. iPureIntro. by constructor; invert_all_in; list_elem_of.
        iSplit.
          { rewrite /five_tuple_potential.
            iDestruct (time_combine with "[τ pot]") as "τ". by iFrame.
            iDestruct (split_time (kP ⋄ kSf) with "τ") as "[ι _]".
              { invert_all_in; simpl; lia. }
            iExact "ι".
          }
        iSplit. iApply (big_sepL2_mono with "Hltr"). by auto.
        iSplit. iApply (big_sepL2_mono with "Hrtr"). by auto.
        done.
      + wp_pures.
        iModIntro.
        iApply "Hψ".
        iSplit. by ℓisDeque ℓ''.
        iPureIntro. rewrite Hoeq. aac_reflexivity.
  Qed.

  Lemma unsafe_naive_pop : forall n o f,
    {{{ isUnsafePopFiveTuple π n o f ∗ ⏱ 1 }}}
      naive_pop f
    {{{ x (d : val) o', RET (x, d)%V;
      ⌜ o = ⋅ x ++ o' ⌝ ∗
      ∀ y : val,
        WP push y d {{ d, isDeque π n (⋅ y ++ o') d }}
    }}}.
  Proof.
    iIntros (n o f ψ) "[Hf τ] Hψ".
    iDestruct "Hf" as "(%p & %l & %m & %r & %s & %op & %ol & %om & %or & %os &
                      %kMd & %kSf & %ltr & %rtr &
                      -> & %conf & pot & #Hp & #Hl & #Hm & #Hr & #Hs &
                      #Hltr & #Hrtr & %Hoeq)".
    rewrite /naive_pop.
    wp_pures.
    wp_apply (bis_empty_spec with "Hm") as "_".
    inversion conf; wp_pures.
    assert (3 = 2 + 1) as -> by rewrite //.
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
    wp_apply (tick_spec with "τ") as "_".
    wp_pures.
    wp_load.
    wp_pures.
    wp_apply (bis_empty_spec with "Hm") as "_".
    wp_pures.
    wp_apply (bhas_length_6_spec with "Hb'") as "_".
    wp_pures.
    wp_store.
    rewrite /assemble_.
    wp_apply (bpush_spec with "Hb'") as "%p' #Hp'".
    wp_pures.
    wp_apply (ssref_alloc π (fiveTuple π n (⋅y ++ o' ++ concat ol ++ om ++ concat or ++ os)) with "[pot]") as "%ℓ' Hℓ'".
    + iExists p',l,m,r,s,(⋅y++o'),ol,om,or,os,3,2,kSf,ltr,rtr.
      iFrame "#".
      doneL.
      iSplit. iPureIntro. by easy_config.
      iSplit. iExact "pot".
      iSplit. iApply (big_sepL2_mono with "Hltr"). by auto.
      iSplit. iApply (big_sepL2_mono with "Hrtr"). by auto.
      done.
    + wp_pures.
      iModIntro.
      ℓisDeque ℓ'.
      iExact "Hℓ'".
  Qed.

  Lemma inspect_first_spec : forall n o f,
    {{{ isPersFiveTuple π n o f }}}
      inspect_first f
    {{{ o' t, RET t; ⌜ o = ⋅ t ++ o' ⌝  }}}.
  Proof.
    iIntros (n o f ψ) "Hf Hψ".
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

End lemmas.