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

  Definition five_tuple_potential : nat -> nat -> iProp Σ :=
    λ pre suf, ⏱ (pre ⋄ suf).

  Let fFiveTuple (triple_pred : isDequeType) (deque_pred : isDequeType) : isDequeType := (
    λ n o d, ∃ (pr ld md rd sf : val)
      pr_content left_content md_content right_content sf_content
      (kPr kMd kSf : nat) left_triples right_triples,
      ⌜ d = (pr, ld, md, rd, sf)%V ⌝ ∗
      ⌜ five_tuple_configuration kPr (length left_content) kMd (length right_content) kSf ⌝ ∗
      five_tuple_potential kPr kSf ∗
      buffer kPr pr_content pr ∗
      deque_pred (S n) left_triples ld ∗
      buffer kMd md_content md ∗
      deque_pred (S n) right_triples rd ∗
      buffer kSf sf_content sf ∗
      ([∗list] c;tr ∈ left_content;left_triples, ▷ triple_pred (S n) c tr) ∗
      ([∗list] c;tr ∈ right_content;right_triples, ▷ triple_pred (S n) c tr) ∗
      ⌜ o = pr_content ++ List.concat left_content ++ md_content ++ List.concat right_content ++ sf_content ⌝
  )%I.

  (* Define the mutual fixpoint functions *)
  Let fDeque (triple_pred : isDequeType) (deque_pred : isDequeType) : isDequeType := (
    λ n o d,
      (⌜ d = NONEV ∧ o = [] ⌝) ∨
      (∃ ℓ : loc, ⌜ d = SOMEV #ℓ ⌝ ∗
        ℓ ⤇{π, n} fFiveTuple triple_pred deque_pred n o)
  )%I.

  Let fTriple (triple_pred : isDequeType) (deque_pred : isDequeType) : isDequeType := (
    λ n o t,
      ∃ (fst ch lst : val)
        fst_content child_content lst_content
        (kFst kLst : nat) triples,
        ⌜ triple_configuration kFst (length child_content) kLst ⌝ ∗
        ⌜ t = (fst, ch, lst)%V ⌝ ∗
        buffer kFst fst_content fst ∗
        deque_pred n triples ch ∗
        buffer kLst lst_content lst ∗
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
    do 30 (f_contractive || f_equiv). apply bufferContractive, dist_dist_later, Hdist_cad.
    f_equiv. by apply (Hdist_tri _ _ _).
    f_equiv. by apply bufferContractive, dist_dist_later, Hdist_cad.
    f_equiv. apply (Hdist_tri _ _ _).
    f_equiv. apply bufferContractive, dist_dist_later, Hdist_cad.
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
  Definition IsDeque o d := isDeque 0 o d.

  Definition isPersFiveTuple : isDequeType := (
    λ n o d, ∃ (pr ld md rd sf : val)
      pr_content left_content md_content right_content sf_content
      (kPr kMd kSf : nat) left_triples right_triples,
      ⌜ d = (pr, ld, md, rd, sf)%V ⌝ ∗
      ⌜ five_tuple_configuration kPr (length left_content) kMd (length right_content) kSf ⌝ ∗
      buffer kPr pr_content pr ∗
      isDeque (S n) left_triples ld ∗
      buffer kMd md_content md ∗
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
      buffer kMd md_content md ∗
      isDeque (S n) right_triples rd ∗
      buffer kSf sf_content sf ∗
      ([∗list] c;tr ∈ left_content;left_triples, triple (S n) c tr) ∗
      ([∗list] c;tr ∈ right_content;right_triples, triple (S n) c tr) ∗
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

(* The number of (amortized) calls to any of [push], [dconcat] or [pop]. *)
Notation time_for_push := 7.
Notation time_for_concat := (8 * time_for_push + 1).
Notation time_for_pop := (3 * time_for_concat).

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

  Context `{!heapGS Σ} `{!na_invG Σ}.
  Context {π : gname}.

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
    {{{ emp }}} asingleton x {{{ d, RET d; IsDeque π (⋅x) d }}}.
  Proof.
    iIntros (x Φ) "_ Hψ".
    rewrite /asingleton. wp_pures.
    wp_bind (bpush _ _)%E.
    wp_apply (bpush_spec) as "%b #Hb".
      { iApply bempty_spec. }
    wp_pures.
    wp_bind (ref _)%E.
    wp_apply (ssref_alloc _ (fiveTuple π 0 (⋅ x))) as "%ℓ Hℓ".
      { rewrite /fiveTuple.
        iExists bempty, empty, bempty, empty, b,
                []          , []   , []          , []    , (⋅x),
                0, 0, 1, [], [].
        rewrite //=.
        iSplitL. rewrite //.
        iSplitL. iPureIntro. constructor. list_elem_of.
        iSplitL. rewrite /five_tuple_potential //. by iApply time_zero.
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

  Lemma singleton_deque_better : forall depth x b, buffer 1 (⋅x) b -∗ fiveTuple π depth (⋅ x) (bempty, NONEV, bempty, NONEV, b)%V.
  Proof.
    iIntros (depth x b) "#Hb".
    iExists bempty, empty, bempty, empty, b,
            []           , []    , []   , [], (⋅x),
            0, 0, 1, [], [].
    rewrite /=.
    iSplitR. rewrite //.
    iSplitR. iPureIntro. constructor. list_elem_of.
    iSplitR. by iApply time_zero.
    iSplitR. by iApply bempty_spec.
    iSplitR. isEmptyDeque.
    iSplitR. by iApply bempty_spec.
    iSplitR. isEmptyDeque.
    iSplitL; done.
  Qed.

  (* NOTE(Juliette): bring back?
  Lemma bempty_is_empty : forall b o, buffer 0 o b ⊢ ⌜ o = [] ⌝.
  Proof.
    iIntros (b o) "H".
    iDestruct "H" as "[_ %Heq]". iPureIntro; by apply nil_length_inv.
  Qed.
  *)

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
      rewrite /buffer /buffer.
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
  iSplitR; [iPureIntro; constructor; list_elem_of |];
  iSplitL "ι"; [iExact "ι" |];
  iSplitR; [trivial |];
  iSplitR; [isEmptyDeque |];
  iSplitR; [trivial |];
  iSplitR; [isEmptyDeque |];
  iSplitR; [trivial |];
  inversion cfg;
  [ rewrite Heq;
    symmetry in H, H1;
    iDestruct (bempty_is_empty with "Hpr") as "->";
    iDestruct (bempty_is_empty with "Hmd") as "->";
    rewrite (nil_length_inv _ H);
    rewrite (nil_length_inv _ H1);
    iPureIntro;
    aac_reflexivity
  | inversion H0; inversion H8; inversion H12; inversion H16; inversion H20
  ].
  *)

  (*
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
  *)

  Lemma decrease_in : forall n o, n ∈ map S o -> ∃ k, n = k + 1 ∧ k ∈ o.
  Proof.
    induction o; intros.
    - inversion H.
    - rewrite /= in H.
      inversion H.
      + exists a. split; [ auto | list_elem_of ]. lia.
      + specialize (IHo H2) as (k & G1 & G2).
        exists k. split; [ auto | list_elem_of ].
  Qed.

  (*
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
  *)

  Lemma lookup_triple depth (L : list (list val)) (M : list val) y :
    y ∈ M -> ([∗ list] x;y ∈ L;M, triple π depth x y)
    ⊢ ∃ x, triple π depth x y.
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

  Lemma abuffer_spec_explicit : forall n k o b,
    n ∈ [2; 3] -> {{{ buffer n o b }}} abuffer b {{{ RET (b, NONEV, bempty)%V; triple π k o (b, NONEV, bempty)%V }}}.
  Proof.
    iIntros (n k o b Hn ψ) "Hb Hψ".
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

  Lemma abuffer_spec : forall n k o b,
    n ∈ [2; 3] -> {{{ buffer n o b }}} abuffer b {{{ t, RET t; triple π k o t }}}.
  Proof.
    iIntros (n k' o k H ψ) "Hb Hψ".
    wp_apply (abuffer_spec_explicit with "Hb") as "H". by assumption.
    iApply "Hψ".
    done.
  Qed.


End proofs.
