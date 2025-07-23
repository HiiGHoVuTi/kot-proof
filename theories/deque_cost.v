From iris.heap_lang Require Import lang proofmode notation.
From iris.bi Require Import derived_laws.

From Coq Require Import List.
Import ListNotations.

From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Deque Require Import common tick shared_ref.

Section potential_deques.
  (* This section describes the structure used for the proof of the time-complexity bounds *)

  Context `{!heapGS Σ} `{!na_invG Σ}.
  Variable π : gname.

  Let isDequeType := nat -d> list val -d> val -d> iProp Σ.

  (* Buffer unwinding: abstract content depends on level *)
  Definition bufferPre (size : nat) : list val -d> val -d> iProp Σ := (
    λ content buf, raw_buffer content buf ∗ ⌜ length content = size ⌝
  )%I.
  (*
  λ self_triple n content buf,
    match n with
    | 0 => raw_buffer content buf ∗ ⌜ length content = size ⌝
    | S n =>
        ∃ (triples : list val) (triple_contents : list (list val)),
          raw_buffer triples buf ∗
          ⌜ content = List.concat triple_contents ∧ length triples = size ⌝ ∗
          [∗ list] tri; c ∈ triples; triple_contents, ▷ self_triple n c tri
    end
  )%I.
  *)

  (*
  Global Instance bufferPreContractive size : Contractive (bufferPre size).
  Proof.
    rewrite /bufferPre.
    intros k f1 f2 Hdist n c b.
    repeat (f_contractive || f_equiv).
    (*
    apply (Hdist _ _ _).
    *)
  Qed.
  *)

  Definition five_tuple_potential : nat -> nat -> iProp Σ :=
    λ pre suf, ⏱ (pre ⋄ suf).

  Let fFiveTuple (triple_pred : isDequeType) (deque_pred : isDequeType) : isDequeType := (
    λ n o d, ∃ (pr ld md rd sf : val)
      pr_content left_content md_content right_content sf_content
      (kPr kMd kSf : nat) left_triples right_triples,
      ⌜ d = (pr, ld, md, rd, sf)%V ⌝ ∗
      ⌜ five_tuple_configuration kPr (length left_content) kMd (length right_content) kSf ⌝ ∗
      five_tuple_potential kPr kSf ∗
      bufferPre kPr pr_content pr ∗
      deque_pred (S n) left_triples ld ∗
      bufferPre kMd md_content md ∗
      deque_pred (S n) right_triples rd ∗
      bufferPre kSf sf_content sf ∗
      ([∗list] c;tr ∈ left_content;left_triples, ▷ triple_pred (S n) c tr) ∗
      ([∗list] c;tr ∈ right_content;right_triples, ▷ triple_pred (S n) c tr) ∗
      ⌜ o = pr_content ++ List.concat left_content ++ md_content ++ List.concat right_content ++ sf_content ⌝
  )%I.

  (* Define the mutual fixpoint functions *)
  Let fDeque (triple_pred : isDequeType) (deque_pred : isDequeType) : isDequeType := (
    λ n o d,
      (⌜ d = NONEV ∧ o = [] ⌝) ∨
      (∃ ℓ : loc, ⌜ d = SOMEV #ℓ ⌝ ∗
        ℓ ⤇{π . n} fFiveTuple triple_pred deque_pred n o)
  )%I.

  Let fTriple (triple_pred : isDequeType) (deque_pred : isDequeType) : isDequeType := (
    λ n o t,
      ∃ (fst ch lst : val)
        fst_content child_content lst_content
        (kFst kLst : nat) triples,
        ⌜ triple_configuration kFst (length child_content) kLst ⌝ ∗
        ⌜ t = (fst, ch, lst)%V ⌝ ∗
        bufferPre kFst fst_content fst ∗
        deque_pred n triples ch ∗
        bufferPre kLst lst_content lst ∗
        ([∗list] c;tr ∈ child_content;triples, ▷ triple_pred n c tr) ∗
        ⌜ o = fst_content ++ List.concat child_content ++ lst_content ⌝
  )%I.

  (* Prove contractivity *)
  Local Instance fDeque_contractive :
    ∀ n, Proper (dist_later n ==> dist_later n ==> dist n) fDeque.
  Proof.
    intros k deque1 deque2 Hdist_cad triple1 triple2 Hdist_tri.
    intros n o d.
    rewrite /fDeque.
    do 4 (f_contractive || f_equiv).
    rewrite /ssref.
    do 4 (f_contractive || f_equiv).
    rewrite /fFiveTuple.
    do 34 (f_contractive || f_equiv).
    f_equiv. by apply (Hdist_tri _ _ _).
    f_equiv.
    f_equiv. by apply (Hdist_tri _ _ _).
    f_equiv.
    do 6 f_equiv. by apply (Hdist_cad _ _ _).
    f_equiv. by apply (Hdist_cad _ _ _).
    (*
    do 30 (f_contractive || f_equiv). apply bufferPreContractive, dist_dist_later, Hdist_cad.
    f_equiv. by apply (Hdist_tri _ _ _).
    f_equiv. by apply bufferPreContractive, dist_dist_later, Hdist_cad.
    f_equiv. apply (Hdist_tri _ _ _).
    f_equiv. apply bufferPreContractive, dist_dist_later, Hdist_cad.
    *)
  Qed.

  Local Instance fTriple_contractive :
    ∀ n, Proper (dist_later n ==> dist n ==> dist n) fTriple.
  Proof.
    intros k tr1 tr2 Hdist_tri de1 de2 Hdist_cad.
    intros n o t.
    rewrite /fTriple.
    do 21 (f_contractive || f_equiv).
    - f_equiv. by apply (Hdist_cad _ _ _).
      f_equiv.
    do 5 f_equiv. f_contractive. by apply (Hdist_tri _ _ _).
  Qed.

  Definition triple := fixpoint_A fTriple fDeque.
  Definition isDeque := fixpoint_B fTriple fDeque.
  Definition fiveTuple := fFiveTuple triple isDeque.
  Definition isElement n o e := match n with 0 => ⌜ o = [e] ⌝%I | S n => triple n o e end.
  Definition buffer size := bufferPre size.
  Definition IsDeque o d := isDeque 0 o d.

  Definition isPersFiveTuple : isDequeType := (
    λ n o d, ∃ (pr ld md rd sf : val)
      pr_content left_content md_content right_content sf_content
      (kPr kMd kSf : nat) left_triples right_triples,
      ⌜ d = (pr, ld, md, rd, sf)%V ⌝ ∗
      ⌜ five_tuple_configuration kPr (length left_content) kMd (length right_content) kSf ⌝ ∗
      buffer kPr pr_content pr ∗
      isDeque (S n) left_triples ld ∗
      bufferPre kMd md_content md ∗
      isDeque (S n) right_triples rd ∗
      buffer kSf sf_content sf ∗
      ([∗list] c;tr ∈ left_content;left_triples, ▷ triple (S n) c tr) ∗
      ([∗list] c;tr ∈ right_content;right_triples, ▷ triple (S n) c tr) ∗
      ⌜ o = pr_content ++ List.concat left_content ++ md_content ++ List.concat right_content ++ sf_content ⌝
  )%I.

  Definition isLaterPersFiveTuple : isDequeType := (
    λ n o d, ∃ (pr ld md rd sf : val)
      pr_content left_content md_content right_content sf_content
      (kPr kMd kSf : nat) left_triples right_triples,
      ⌜ d = (pr, ld, md, rd, sf)%V ⌝ ∗
      ⌜ five_tuple_configuration kPr (length left_content) kMd (length right_content) kSf ⌝ ∗
      buffer kPr pr_content pr ∗
      isDeque (S n) left_triples ld ∗
      bufferPre kMd md_content md ∗
      isDeque (S n) right_triples rd ∗
      buffer kSf sf_content sf ∗
      ([∗list] c;tr ∈ left_content;left_triples, triple (S n) c tr) ∗
      ([∗list] c;tr ∈ right_content;right_triples, triple (S n) c tr) ∗
      ⌜ o = pr_content ++ List.concat left_content ++ md_content ++ List.concat right_content ++ sf_content ⌝
  )%I.

 Definition isPopFiveTuple : isDequeType := (
    λ n o d, ∃ (pr ld md rd sf : val)
      pr_content left_content md_content right_content sf_content
      (kPr kMd kSf : nat) left_triples right_triples,
      ⌜ d = (pr, ld, md, rd, sf)%V ⌝ ∗
      ⌜ pop_configuration kPr (length left_content) kMd (length right_content) kSf ⌝ ∗
      five_tuple_potential kPr kSf ∗
      buffer kPr pr_content pr ∗
      isDeque (S n) left_triples ld ∗
      bufferPre kMd md_content md ∗
      isDeque (S n) right_triples rd ∗
      buffer kSf sf_content sf ∗
      ([∗list] c;tr ∈ left_content;left_triples, ▷ triple (S n) c tr) ∗
      ([∗list] c;tr ∈ right_content;right_triples, ▷ triple (S n) c tr) ∗
      ⌜ o = pr_content ++ List.concat left_content ++ md_content ++ List.concat right_content ++ sf_content ⌝
  )%I.

  (* Unfolding lemmas come directly from the fixpoint theory *)
  Lemma isDeque_unfold n o d :
    isDeque n o d ⊣⊢ fDeque triple isDeque n o d.
  Proof.
    symmetry.
    apply (fixpoint_B_unfold fTriple fDeque _ _ _).
  Qed.

  Lemma triple_unfold n o t :
    triple n o t ⊣⊢ fTriple triple isDeque n o t.
  Proof.
    symmetry.
    apply (fixpoint_A_unfold fTriple fDeque _ _ _).
  Qed.

  (* Persistence instances *)
  Global Instance bufferPersistent s b c :
    Persistent (bufferPre s b c).
  Proof.
    apply _.
  Qed.

  Global Instance isDequePersistent n o d : Persistent (isDeque n o d).
  Proof.
    rewrite isDeque_unfold /fDeque.
    apply _.
  Qed.

  Global Instance triplePersistent n o t : Persistent (triple n o t).
  Proof.
    rewrite /triple /fixpoint_A /ofe.fixpoint_AB.
    revert n o t. apply fixpoint_ind.
    - intros f1 f2 H P n o t. rewrite -(H _ _ _) //.
    - exists (λ _ _ _, emp)%I. apply _.
    - intros.
      rewrite /ofe.fixpoint_AA /fTriple /ofe.fixpoint_AB.
      assert (forall a b, Persistent (fixpoint (fDeque x) n a b)); [| apply _].
      intros. apply fixpoint_ind.
        + intros f1 f2 H' P'. rewrite -(H' _ _ _) //.
        + exists (λ _ _ _, emp)%I. apply _.
        + apply _.
        + apply bi.limit_preserving_Persistent.
          intros k f1 f2 Hdist. apply (Hdist _ _ _).
    - apply limit_preserving_forall => n.
      apply limit_preserving_forall => o.
      apply limit_preserving_forall => t.
      apply bi.limit_preserving_Persistent.
      intros k f1 f2 Hdist. apply (Hdist _ _ _).
  Qed.

  Global Instance fiveTuplePersistent n o d : Persistent (isPersFiveTuple n o d).
  Proof.
    apply _.
  Qed.

  Global Instance isElementPersistent n o e : Persistent (isElement n o e).
  Proof.
    destruct n; apply _.
  Qed.

  Property persist_structure : forall n o d, fiveTuple n o d -∗ isPersFiveTuple n o d ∗ fiveTuple n o d.
  Proof.
    iIntros (n o d) "(%pr & %ld & %md & %rd & %sf & %prC & %ldC & %mdC & %rdC & %sfC
            & %kPr & %kMd & %kSf & %ltr & %rtr & -> & %cfg & pot
            & #Hpr & #Hld & #Hmd & #Hrd & #Hsf & #Hltr & #Hrtr & #Heq)".
    iSplitR; iExists pr, ld, md, rd, sf, prC, ldC, mdC, rdC, sfC, kPr, kMd, kSf, ltr, rtr; iFrame "#"; iFrame;
    iSplitR; done.
  Qed.

  Lemma laterInFiveTuple : forall n o d, isLaterPersFiveTuple n o d ⊢ isPersFiveTuple n o d.
  Proof.
    iIntros (n o d) "(%pr & %ld & %md & %rd & %sf & %prC & %ldC & %mdC & %rdC & %sfC
            & %kPr & %kMd & %kSf & %ltr & %rtr & -> & %cfg
            & #Hpr & #Hld & #Hmd & #Hrd & #Hsf & #Hltr & #Hrtr & #Heq)".
    iExists pr, ld, md, rd, sf, prC, ldC, mdC, rdC, sfC, kPr, kMd, kSf, ltr, rtr; iFrame "#"; iFrame.
    do 2 (iSplitR; [ done |]).
    iSplitL "Hltr". iApply (big_sepL2_mono with "Hltr"). by auto.
                    iApply (big_sepL2_mono with "Hrtr"). by auto.
  Qed.

  Lemma three_time_enough : forall a b, ⏱ 3 ⊢ five_tuple_potential a b : iProp Σ.
  Proof.
    iIntros (a b) "H".
    rewrite /five_tuple_potential.
    destruct (buffer_colour a), (buffer_colour b); auto;
    iDestruct (split_time 1 with "H") as "[A _]"; auto;
    iApply time_zero; auto.
  Qed.

  Lemma strutcure_and_time : forall depth o d, isPersFiveTuple depth o d ∗ ⏱ 3 ⊢ fiveTuple depth o d.
  Proof.
    iIntros (n o d) "[(%pr & %ld & %md & %rd & %sf & %prC & %ldC & %mdC & %rdC & %sfC
            & %kPr & %kMd & %kSf & %ltr & %rtr & -> & %cfg
            & #Hpr & #Hld & #Hmd & #Hrd & #Hsf & #Hltr & #Hrtr & #Heq) τ]".
    iExists pr, ld, md, rd, sf, prC, ldC, mdC, rdC, sfC, kPr, kMd, kSf, ltr, rtr; iFrame "#"; iFrame.
    do 2 (iSplitR; [done |]).
    iApply (three_time_enough with "τ").
  Qed.

End potential_deques.

Section proofs.

  Context `{!heapGS Σ} `{!na_invG Σ}.
  Variable π : gname.

  Ltac ℓisDeque ℓ := rewrite !isDeque_unfold; iRight; iExists ℓ; iSplitR; [done |].

  Ltac isEmptyDeque := rewrite !isDeque_unfold; iLeft; iPureIntro; done.

  Lemma bool_decide_code_true (a : nat) (b : nat) : bool_decide (a = b) = true -> bool_decide (#a = #b) = true.
  Proof.
    intro.
    apply bool_decide_eq_true_1 in H.
    by apply bool_decide_eq_true_2, f_equal, f_equal, f_equal.
  Qed.

  Lemma bool_decide_code_false (a : nat) (b : nat) : bool_decide (a = b) = false -> bool_decide (#a = #b) = false.
  Proof.
    intro.
    apply bool_decide_eq_false_1 in H.
    apply bool_decide_eq_false_2.
    intro. apply H.
    inversion H0.
    by apply Nat2Z.inj'.
  Qed.

  Example singleton_deque_spec : forall x : val,
    {{{ emp }}} singleton_deque x {{{ d, RET d; IsDeque π (⋅x) d }}}.
  Proof.
    iIntros (x Φ) "_ Hψ".
    rewrite /singleton_deque. wp_pures.
    wp_bind (bpush _ _)%E.
    wp_apply (bpush_spec) as "%b #Hb".
      { iApply empty_is_buffer. }
    wp_pures.
    wp_bind (ref _)%E.
    wp_apply (ssref_alloc _ (fiveTuple π 0 (⋅ x))) as "%ℓ Hℓ".
      { rewrite /fiveTuple.
        iExists empty_buffer, empty, empty_buffer, empty, b,
                []          , []   , []          , []    , (⋅x),
                0, 0, 1, [], [].
        rewrite //=.
        iSplitL. rewrite //.
        iSplitL. iPureIntro. constructor. by auto with find_in_list.
        iSplitL. rewrite /five_tuple_potential //. by iApply time_zero.
        iSplitL. iSplitL. iApply empty_is_buffer. done.
        iSplitL. isEmptyDeque.
        iSplitL. iSplitL. iApply empty_is_buffer. done.
        iSplitL. isEmptyDeque.
        iFrame "#". done.
      }
    wp_pures.
    iApply "Hψ".
    iModIntro.
    rewrite /IsDeque. ℓisDeque ℓ.
    done.
  Qed.

  Ltac isEmptyBufferAtDepth depth :=
  destruct depth;
  [ iSplitL; [by iApply empty_is_buffer | rewrite //]
  | iExists [], []; iSplitL; try iSplitL; rewrite //; by iApply empty_is_buffer ].

  Lemma bsize_better_spec k o b :
    {{{ buffer k o b }}}
      bsize b
    {{{ RET #k; True }}}.
  Proof.
    iIntros (ψ) "Hb Hψ".
    iDestruct "Hb" as "[Hb <-]".
    by iApply (bsize_spec with "Hb").
  Qed.

  Lemma empty_is_buffer_at : ⊢ buffer 0 [] empty_buffer.
  Proof.
    iSplitR; [ by iApply empty_is_buffer | done ].
  Qed.

  Lemma singleton_deque_better : forall depth x b, raw_buffer (⋅x) b -∗ fiveTuple π depth (⋅ x) (empty_buffer, NONEV, empty_buffer, NONEV, b)%V.
  Proof.
    iIntros (depth x b) "#Hb".
    iExists empty_buffer, empty, empty_buffer, empty, b,
            []          , []   , []          , []   , (⋅x),
            0, 0, 1, [], [].
    rewrite /=.
    iSplitR. rewrite //.
    iSplitR. iPureIntro. constructor. auto with find_in_list.
    iSplitR. by iApply time_zero.
    iSplitR. by iApply empty_is_buffer_at.
    iSplitR. isEmptyDeque.
    iSplitR. by iApply empty_is_buffer_at.
    iSplitR. isEmptyDeque.
    iSplitL; [| done].
    rewrite /bufferPre.
    destruct depth.
    - iSplitL; rewrite //.
    - rewrite /isElement.
      iFrame. by auto.
  Qed.

  Lemma empty_buffer_is_empty : forall b o, buffer 0 o b ⊢ ⌜ o = [] ⌝.
  Proof.
    iIntros (b o) "H".
    iDestruct "H" as "[_ %Heq]". iPureIntro; by apply nil_length_inv.
  Qed.

  (*
  Lemma push_buffer_element_spec x b : forall n o oX size,
    {{{ isElement π n oX x ∗ buffer π size n o b }}}
      bpush x b
    {{{ b', RET b'; buffer π (S size) n (oX ++ o) b' }}}.
  Proof.
    destruct n; iIntros (o oX size ψ) "[Hx Hb] Hψ".
    - iCombine "Hx Hb" as "[-> [Hb %sEqL]]".
      wp_apply (bpush_spec with "Hb") as "%b' Hb'".
      iApply "Hψ".
      iSplitL. done.
      iPureIntro. simpl; auto.
    - rewrite /isElement.
      iDestruct "Hb" as "(%triples & %triples_content & Hb & [%Ho %lenEqSz] & areTriples)".
      wp_apply (bpush_spec with "Hb") as "%b' Hb'".
      iApply "Hψ".
      rewrite /buffer /bufferPre.
      iExists (⋅ x ++ triples), (⋅ oX ++ triples_content).
      iFrame. iSplitR.
      + iPureIntro; split.
        * rewrite /= Ho //.
        * rewrite /= lenEqSz //.
      + iSplitR. done.
        iApply (big_sepL2_mono with "areTriples").
        intros. iIntros "t". by iNext.
  Qed.

  Corollary inject_buffer_element_spec x b : forall n o oX size,
    {{{ isElement π n oX x ∗ buffer π size n o b }}}
      binject b x
    {{{ b', RET b'; buffer π (S size) n (o ++ oX) b' }}}.
  Admitted.

  Lemma pop_buffer_element_spec b : forall n o size,
    {{{ buffer π (S size) n o b }}}
      bpop b
    {{{ x b', RET (x, b'); ∃ oX o', buffer π size n o' b' ∗ ⌜ o = oX ++ o' ⌝ ∗ isElement π n oX x }}}.
  Proof.
    destruct n; iIntros (o size ψ) "Hb Hψ".
    - iDestruct "Hb" as "[Hb %sEqL]".
      destruct o. by inversion sEqL.
      wp_apply (bpop_spec with "Hb") as "%b' Hb'".
      iApply "Hψ".
      iExists (⋅ v).
      iFrame. iSplit; iPureIntro.
      + by inversion sEqL.
      + auto.
    - iDestruct "Hb" as "(%triples & %triples_content & Hb & [%Ho %lenEqSz] & areTriples)".
      destruct triples. by inversion lenEqSz.
      iDestruct (big_sepL2_length with "areTriples") as "%Hlen".
      destruct triples_content. by rewrite lenEqSz // in Hlen.
      wp_apply (bpop_spec with "Hb") as "%b' Hb'".
      iApply "Hψ".
      iDestruct (big_sepL2_cons with "areTriples") as "[tri Hrest]".
      iExists l, (List.concat triples_content).
      iSplitL "Hb' Hrest".
      + iExists triples, triples_content.
        iSplitL "Hb'". done.
        iSplitR.
        * iPureIntro; split; [trivial |].
          by inversion lenEqSz.
        * iApply (big_sepL2_mono with "Hrest").
          intros. iIntros "t". by iNext.
      + iSplitR.
        * iPureIntro. by rewrite Ho //.
        * done.
  Qed.

   Corollary eject_buffer_element_spec b : forall n o size,
    {{{ buffer π (S size) n o b }}}
      beject b
    {{{ b' x, RET (b', x); ∃ oX o', buffer π size n o' b' ∗ ⌜ o = o' ++ oX ⌝ ∗ isElement π n oX x }}}.
  Admitted.

  Ltac solve_no_middle Heq H H1 :=
  iSplitR; [done |];
  iSplitR; [iPureIntro; constructor; auto with find_in_list |];
  iSplitL "ι"; [iExact "ι" |];
  iSplitR; [trivial |];
  iSplitR; [isEmptyDeque |];
  iSplitR; [trivial |];
  iSplitR; [isEmptyDeque |];
  iSplitR; [trivial |];
  inversion cfg;
  [ rewrite Heq;
    symmetry in H, H1;
    iDestruct (empty_buffer_is_empty with "Hpr") as "->";
    iDestruct (empty_buffer_is_empty with "Hmd") as "->";
    rewrite (nil_length_inv _ H);
    rewrite (nil_length_inv _ H1);
    iPureIntro;
    aac_reflexivity
  | inversion H0; inversion H8; inversion H12; inversion H16; inversion H20
  ].
  *)

  Lemma bpush_spec2 x b : forall o size,
    {{{ buffer size o b }}}
      bpush x b
    {{{ b', RET b'; buffer (S size) (⋅x ++ o) b' }}}.
  Proof.
    iIntros (o size ψ) "[Hb %Heq] Hψ".
    wp_apply (bpush_spec with "Hb") as "%b' Hb'".
    iApply "Hψ".
    iFrame. iPureIntro. simpl. by rewrite Heq //.
  Qed.

  Corollary binject_spec2 b x : forall o size,
    {{{ buffer size o b }}}
      binject b x
    {{{ b', RET b'; buffer (S size) (o ++ ⋅x) b' }}}.
  Admitted.

  Lemma bpop_spec2 b : forall o size,
    {{{ buffer (S size) o b }}}
      bpop b
    {{{ x b' o', RET (x, b'); buffer size o' b' ∗ ⌜ o = ⋅x ++ o' ⌝ }}}.
  Proof.
    iIntros (o size ψ) "[Hb %Heq] Hψ".
    destruct o. by inversion Heq.
    wp_apply (bpop_spec with "Hb") as "%b' Hb'".
    iApply "Hψ". iFrame.
    iPureIntro. by inversion Heq.
  Qed.

  Corollary beject_spec2 b : forall o size,
    {{{ buffer (S size) o b }}}
      beject b
    {{{ b' x o', RET (b', x); buffer size o' b' ∗ ⌜ o = o' ++ ⋅x ⌝ }}}.
  Admitted.

  Ltac invert_all_in :=
  repeat match goal with
  | H : _ ∈ _ |- _ =>
    first
    [ inversion H; clear H; auto 10 with find_in_list
    | inversion H; clear H; [ by contradiction |]
    | by inversion H
    ];
    try contradiction
  end.

  Ltac doneL := iSplitR; [done |].
  Ltac doneR := iSplitL; [| done].

  Ltac easy_config := try iPureIntro; constructor; auto with find_in_list.

  Notation time_for_push := 7.

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

  Notation time_for_concat := (4 * time_for_push + 1 + 3).

  Lemma decrease_in : forall n o, n ∈ map S o -> ∃ k, n = S k ∧ k ∈ o.
  Proof.
    induction o; intros.
    - inversion H.
    - rewrite /= in H.
      inversion H.
      + exists a. split; auto with find_in_list.
      + specialize (IHo H2) as (k & G1 & G2).
        exists k. split; auto with find_in_list.
  Qed.

  Property partition_buffer_left_better_spec : forall k o b,
    {{{ buffer k o b ∗ ⌜ k ∈ [2..6] ⌝ }}}
      partition_buffer_left b
    {{{ b1 b2 o1 o2 k1 k2, RET (b1, b2)%V;
        buffer k1 o1 b1 ∗ buffer k2 o2 b2 ∗
        ⌜ k1 ∈ [2; 3] ∧ k2 ∈ [0; 2; 3] ∧ o1 ++ o2 = o ⌝ }}}.
  Proof.
    iIntros (k o b ψ) "[[#Hb <-] %Hk] Hψ".
      wp_apply partition_buffer_left_spec as (b1 b2) "(%o1 & %o2 & Hb1 & Hb2 & (%Hl1 & %Hl2 & <-))".
        by iFrame "#".
      iApply "Hψ".
      by iFrame.
  Qed.

  Property partition_buffer_right_better_spec : forall k o b,
    {{{ buffer k o b ∗ ⌜ k ∈ [2..6] ⌝ }}}
      partition_buffer_right b
    {{{ b1 b2 o1 o2 k1 k2, RET (b1, b2)%V;
        buffer k1 o1 b1 ∗ buffer k2 o2 b2 ∗
        ⌜ k1 ∈ [0; 2; 3] ∧ k2 ∈ [2; 3] ∧ o1 ++ o2 = o ⌝ }}}.
  Admitted.

  Theorem dconcat_spec (d1 d2 : val) : forall o1 o2,
    {{{ IsDeque π o1 d1 ∗ IsDeque π o2 d2 ∗ ⏱ time_for_concat ∗ Token π 0 }}}
      dconcat d1 d2
    {{{ d', RET d'; IsDeque π (o1 ++ o2) d' ∗ Token π 0 }}}.
  Proof.
  (*
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
      { iFrame. iPureIntro. invert_all_in. }
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
              auto with find_in_list arith.
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
              auto with find_in_list arith.
            iSplitR. done.
            iFrame "#".
            doneR.
            iApply (big_sepL2_mono with "Hrtr1"). by auto.
          * simpl. doneR.
            rewrite triple_unfold.
            iExists s1'', empty, empty_buffer, os1'', [], [], ks1'', 0, [].
            iSplitR. iPureIntro. constructor; invert_all_in.
            iSplitR. done.
            iFrame "#".
            iSplitR. isEmptyDeque.
            iSplitR. rewrite /bufferPre. iSplitL. by iApply empty_is_buffer. done.
            iNext. doneL.
            iPureIntro; simpl; aac_reflexivity.
    }
    iModIntro. wp_pures.
    wp_apply (partition_buffer_right_better_spec with "[Hpr2']") as "%p2' %p2'' %op2' %op2'' %kp2' %kp2'' (#Hp2' & #Hp2'' & (%Hp21' & %Hp2'' & %Hop2eq))".
      { iFrame. iPureIntro. invert_all_in. }
    wp_pures.
    iDestruct (na_own_acc _ _ _ (next_stage 0) with "O") as "[O A]".
    iDestruct (split_time time_for_push with "τ") as "[ι τ]". by lia.
    wp_apply (push_spec_helper with "[Hrd2 ι O]") as "%rd2' [#Hrd2' O]".
    { iFrame "#". iFrame. }
    (* USE ME rewrite /isElement triple_unfold.

    }
      *)
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
              auto with find_in_list arith.
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
            iSplitR. iPureIntro. constructor; invert_all_in.
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
              auto with find_in_list arith.
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
      iSplitR. iPureIntro. constructor; auto with find_in_list.
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
  Qed.
  *)
  Admitted.

  Notation time_for_pop := (3 * time_for_concat).

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
          invert_all_in; constructor; auto 10 with find_in_list.
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
          invert_all_in; constructor; auto 10 with find_in_list.
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
            inversion cfg; constructor; simpl; auto with find_in_list.
            - rewrite !Nat.add_0_r //.
            - rewrite Heqpr Heqsf. auto 10 with find_in_list.
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
            auto with find_in_list;
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
          Lemma lookup_triple depth (L : list (list val)) (M : list val) y : y ∈ M -> ([∗ list] x;y ∈ L;M, triple π depth x y) ⊢ ∃ x, triple π depth x y.
          Proof.
            revert M. induction L; iIntros (M H) "LM".
            - iExFalso.
              iDestruct (big_sepL2_nil_inv_l with "LM") as "->".
              inversion H.
            - destruct M. by inversion H.
              iDestruct (big_sepL2_cons with "LM") as "[t LM]".
              inversion H.
              + by iExists a.
              + by iApply (IHL M H2).
          Qed.
          assert (x' ∈ rtr) as Hx'.
            { rewrite Heq1.
              do 4 (apply elem_of_list_app; right).
              by auto with find_in_list. }
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
                invert_all_in; auto 10 with find_in_list.
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
                        auto with find_in_list.
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
                constructor; invert_all_in; auto with find_in_list;
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

End proofs.
