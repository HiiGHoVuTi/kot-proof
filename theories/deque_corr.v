From iris.heap_lang Require Import lang proofmode notation.
From iris.bi Require Import derived_laws.

From Coq Require Import List.
Import ListNotations.

From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Deque Require Import common tick shared_ref.

Section concurrent_deques.
  (* This section describes the structure used for the proof of the concurrent correction *)

  Context `{!heapGS Σ}.

  Let isDequeType := list val -d> val -d> iProp Σ.

  Let fFiveTuple (triple_pred : isDequeType) (deque_pred : isDequeType) : isDequeType := (
    λ o d, ∃ (pr ld md rd sf : val)
      pr_content left_content md_content right_content sf_content
      (kPr kMd kSf : nat) left_triples right_triples,
      ⌜ d = (pr, ld, md, rd, sf)%V ⌝ ∗
      ⌜ five_tuple_configuration kPr (length left_content) kMd (length right_content) kSf ⌝ ∗
      buffer kPr pr_content pr ∗
      deque_pred left_triples ld ∗
      buffer kMd md_content md ∗
      deque_pred right_triples rd ∗
      buffer kSf sf_content sf ∗
      ([∗list] c;tr ∈ left_content;left_triples, ▷ triple_pred c tr) ∗
      ([∗list] c;tr ∈ right_content;right_triples, ▷ triple_pred c tr) ∗
      ⌜ o = pr_content ++ List.concat left_content ++ md_content ++ List.concat right_content ++ sf_content ⌝
  )%I.

  (* Define the mutual fixpoint functions *)
  Let fDeque (triple_pred : isDequeType) (deque_pred : isDequeType) : isDequeType := (
    λ o d,
      (⌜ d = NONEV ∧ o = [] ⌝) ∨
      (∃ ℓ : loc, ⌜ d = SOMEV #ℓ ⌝ ∗
        ℓ ⤇ fFiveTuple triple_pred deque_pred o)
  )%I.

  Let fTriple (triple_pred : isDequeType) (deque_pred : isDequeType) : isDequeType := (
    λ o t,
      ∃ (fst ch lst : val)
        fst_content child_content lst_content
        (kFst kLst : nat) triples,
        ⌜ triple_configuration kFst (length child_content) kLst ⌝ ∗
        ⌜ t = (fst, ch, lst)%V ⌝ ∗
        buffer kFst fst_content fst ∗
        deque_pred triples ch ∗
        buffer kLst lst_content lst ∗
        ([∗list] c;tr ∈ child_content;triples, ▷ triple_pred c tr) ∗
        ⌜ o = fst_content ++ List.concat child_content ++ lst_content ⌝
  )%I.

  (* Prove contractivity *)
  Local Instance fDeque_contractive :
    ∀ n, Proper (dist_later n ==> dist_later n ==> dist n) fDeque.
  Proof.
    intros k deque1 deque2 Hdist_cad triple1 triple2 Hdist_tri.
    intros o d.
    rewrite /fDeque.
    do 4 (f_contractive || f_equiv).
    rewrite /csref.
    do 4 (f_contractive || f_equiv).
    rewrite /fFiveTuple.
    do 33 (f_contractive || f_equiv).
    f_equiv. by apply (Hdist_tri _ _).
    f_equiv.
    f_equiv. by apply (Hdist_tri _ _).
    f_equiv.
    do 6 f_equiv. by apply (Hdist_cad _ _).
    f_equiv. by apply (Hdist_cad _ _).
  Qed.

  Local Instance fTriple_contractive :
    ∀ n, Proper (dist_later n ==> dist n ==> dist n) fTriple.
  Proof.
    intros k tr1 tr2 Hdist_tri de1 de2 Hdist_cad.
    intros o t.
    rewrite /fTriple.
    do 21 (f_contractive || f_equiv).
    - f_equiv. by apply (Hdist_cad _ _).
      f_equiv.
    do 5 f_equiv. f_contractive. by apply (Hdist_tri _ _).
  Qed.

  Definition triple := fixpoint_A fTriple fDeque.
  Definition isDeque := fixpoint_B fTriple fDeque.
  Definition fiveTuple := fFiveTuple triple isDeque.
  Definition IsDeque o d := isDeque o d.

  Definition isLaterFiveTuple : isDequeType := (
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

  (* Unfolding lemmas come directly from the fixpoint theory *)
  Lemma isDeque_unfold o d :
    isDeque o d ⊣⊢ fDeque triple isDeque o d.
  Proof.
    symmetry.
    apply (fixpoint_B_unfold fTriple fDeque _ _).
  Qed.

  Lemma triple_unfold o t :
    triple o t ⊣⊢ fTriple triple isDeque o t.
  Proof.
    symmetry.
    apply (fixpoint_A_unfold fTriple fDeque _ _).
  Qed.

  Global Instance isDequePersistent o d : Persistent (isDeque o d).
  Proof.
    rewrite isDeque_unfold /fDeque.
    apply _.
  Qed.

  Global Instance triplePersistent o t : Persistent (triple o t).
  Proof.
    rewrite /triple /fixpoint_A /ofe.fixpoint_AB.
    revert o t. apply fixpoint_ind.
    - intros f1 f2 H P o t. rewrite -(H _ _) //.
    - exists (λ _ _, emp)%I. apply _.
    - intros.
      rewrite /ofe.fixpoint_AA /fTriple /ofe.fixpoint_AB.
      assert (forall a b, Persistent (fixpoint (fDeque x) a b)); [| apply _].
      intros. apply fixpoint_ind.
        + intros f1 f2 H' P'. rewrite -(H' _ _) //.
        + exists (λ _ _, emp)%I. apply _.
        + apply _.
        + apply bi.limit_preserving_Persistent.
          intros k f1 f2 Hdist. apply (Hdist _ _).
    - apply limit_preserving_forall => o.
      apply limit_preserving_forall => t.
      apply bi.limit_preserving_Persistent.
      intros k f1 f2 Hdist. apply (Hdist _ _).
  Qed.

  Global Instance fiveTuplePersistent o d : Persistent (fiveTuple o d).
  Proof.
    apply _.
  Qed.

  Lemma laterInFiveTuple : forall o d, isLaterFiveTuple o d ⊢ fiveTuple o d.
  Proof.
    iIntros (o d) "(%pr & %ld & %md & %rd & %sf & %prC & %ldC & %mdC & %rdC & %sfC
            & %kPr & %kMd & %kSf & %ltr & %rtr & -> & %cfg
            & #Hpr & #Hld & #Hmd & #Hrd & #Hsf & #Hltr & #Hrtr & #Heq)".
    iExists pr, ld, md, rd, sf, prC, ldC, mdC, rdC, sfC, kPr, kMd, kSf, ltr, rtr; iFrame "#"; iFrame.
    do 2 (iSplitR; [ done |]).
    iSplitL "Hltr". iApply (big_sepL2_mono with "Hltr"). by auto.
                    iApply (big_sepL2_mono with "Hrtr"). by auto.
  Qed.

End concurrent_deques.

(* Useful tactics used throughout proofs (out of a section to be exported) *)
Ltac ℓisDeque ℓ := rewrite !isDeque_unfold; iRight; iExists ℓ; iSplitR; [done |].
Ltac isEmptyDeque := rewrite !isDeque_unfold; iLeft; iPureIntro; done.
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
Ltac easy_config := try iPureIntro; constructor; list_elem_of.

Section proofs.
  (* This section contains lemmas used for the three main proofs, found in separate files. *)

  Context `{!heapGS Σ}.

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
    {{{ emp }}} asingleton x {{{ d, RET d; IsDeque (⋅x) d }}}.
  Proof.
    iIntros (x Φ) "_ Hψ".
    rewrite /asingleton. wp_pures.
    wp_bind (bpush _ _)%E.
    wp_apply (bpush_spec) as "%b #Hb".
      { iApply bempty_spec. }
    wp_pures.
    wp_bind (ref _)%E.
    wp_apply (csref_alloc (fiveTuple (⋅ x))) as "%ℓ Hℓ".
      { rewrite /fiveTuple.
        iExists bempty, empty, bempty, empty, b,
                []          , []   , []          , []    , (⋅x),
                0, 0, 1, [], [].
        rewrite //=.
        iSplitL. rewrite //.
        iSplitL. iPureIntro. constructor. list_elem_of.
        iSplitL. iApply bempty_spec.
        iSplitL. isEmptyDeque.
        iSplitL. iApply bempty_spec.
        iSplitL. isEmptyDeque.
        iFrame "#". done.
      }
    wp_pures.
    iApply "Hψ".
    iModIntro.
    rewrite /IsDeque. ℓisDeque ℓ.
    done.
  Qed.

  Lemma singleton_deque_better : forall x b, buffer 1 (⋅x) b -∗ fiveTuple (⋅ x) (bempty, NONEV, bempty, NONEV, b)%V.
  Proof.
    iIntros (x b) "#Hb".
    iExists bempty, empty, bempty, empty, b,
            []           , []    , []   , [], (⋅x),
            0, 0, 1, [], [].
    rewrite /=.
    iSplitR. rewrite //.
    iSplitR. iPureIntro. constructor. list_elem_of.
    iSplitR. by iApply bempty_spec.
    iSplitR. isEmptyDeque.
    iSplitR. by iApply bempty_spec.
    iSplitR. isEmptyDeque.
    iSplitL; done.
  Qed.

  Lemma lookup_triple (L : list (list val)) (M : list val) y :
    y ∈ M -> ([∗ list] x;y ∈ L;M, triple x y)
    ⊢ ∃ x, triple x y.
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

  Lemma abuffer_spec_explicit : forall n o b,
    n ∈ [2; 3] -> {{{ buffer n o b }}} abuffer b {{{ RET (b, NONEV, bempty)%V; triple o (b, NONEV, bempty)%V }}}.
  Proof.
    iIntros (n o b Hn ψ) "Hb Hψ".
    rewrite /abuffer /atriple_.
    wp_pures.
    iApply "Hψ".
    rewrite triple_unfold.
    iExists b, NONEV, bempty, o, [], [], n, 0, [].
    iFrame.
    iModIntro.
    iSplitR. iPureIntro. constructor; list_elem_of.
    repeat doneL.
    iSplitL. rewrite isDeque_unfold. by iLeft.
    iSplitL. by iApply bempty_spec.
    repeat doneL.
    iPureIntro. rewrite !app_nil_r //=.
  Qed.

  Lemma abuffer_spec : forall n o b,
    n ∈ [2; 3] -> {{{ buffer n o b }}} abuffer b {{{ t, RET t; triple o t }}}.
  Proof.
    iIntros (n o k H ψ) "Hb Hψ".
    wp_apply (abuffer_spec_explicit with "Hb") as "H". by assumption.
    iApply "Hψ".
    done.
  Qed.


End proofs.
