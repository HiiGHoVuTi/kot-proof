From iris.heap_lang Require Import lang proofmode notation.
From iris.bi Require Import derived_laws.

From Deque Require Import tick.
From Coq Require Import List.
Import ListNotations.

From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Deque Require Import shared_ref.

(* Section notations *)
Notation "⋅ x" := [x] (at level 60).
Definition nonempty {A : Type} (x : list A) := ~(x = []).
Notation "[3..6]" := [3; 4; 5; 6].
Notation "[2..6]" := [2; 3; 4; 5; 6].
Notation "[1..7]" := [1; 2; 3; 4; 5; 6; 7].
Notation "[1..8]" := [1; 2; 3; 4; 5; 6; 7; 8].
(* End notations *)

Section assumptions.
  Context `{!heapGS Σ}.

  (* All functions in this section are assumed to run in O(1) time and space. *)

  Section buffers.
    (* Buffers will have bounded size, guaranteeing O(1) time and space complexity *)

    Definition raw_buffer (o : list val) : val -> iProp Σ.
    Admitted.

    Global Instance raw_bufferPersistent o v : Persistent (raw_buffer o v).
    Admitted.

    Definition empty_buffer : val.
    Admitted.

    Axiom empty_is_buffer : ⊢ raw_buffer [] empty_buffer.

    Definition bpush : val.
    Admitted.

    Property bpush_spec : forall o b x,
      {{{ raw_buffer o b }}}
        bpush x b
      {{{ b', RET b'; raw_buffer (⋅x ++ o) b' }}}.
    Admitted.

    Definition bpop : val.
    Admitted.

    Property bpop_spec : forall o b x,
      {{{ raw_buffer (⋅x ++ o) b }}}
        bpop b
      {{{ b', RET (x, b')%V; raw_buffer o b' }}}.
    Admitted.

    Definition binject : val.
    Admitted.

    Property binject_spec : forall o b x,
      {{{ raw_buffer o b }}}
        binject x b
      {{{ b', RET b'; raw_buffer (o ++ ⋅x) b' }}}.
    Admitted.

    Definition beject : val.
    Admitted.

    Property beject_spec : forall o b x,
      {{{ raw_buffer (o ++ ⋅x) b }}}
        beject b
      {{{ b', RET (x, b')%V; raw_buffer o b' }}}.
    Admitted.

    Definition bsize : val.
    Admitted.

    Property bsize_spec : forall o b,
      {{{ raw_buffer o b }}}
        bsize b
      {{{ RET #(length o); emp }}}.
    Admitted.

    Definition partition_buffer_left : val.
    Admitted.

    Property partition_buffer_left_spec : forall o b,
      {{{ raw_buffer o b ∗ ⌜ length o ∈ [2..6] ⌝ }}}
        partition_buffer_left b
      {{{ b1 b2, RET (b1, b2)%V;
        ∃ o1 o2, raw_buffer o1 b1 ∗ raw_buffer o2 b2 ∗
          ⌜ length o1 ∈ [2; 3] ∧ length o2 ∈ [0; 2; 3] ∧ o1 ++ o2 = o ⌝ }}}.
    Admitted.

    Definition partition_buffer_right : val.
    Admitted.

    Property partition_buffer_right_spec : forall o b,
      {{{ raw_buffer o b ∗ ⌜ length o ∈ [2..6] ⌝ }}}
        partition_buffer_right b
      {{{ b1 b2, RET (b1, b2)%V;
        ∃ o1 o2, raw_buffer o1 b1 ∗ raw_buffer o2 b2 ∗
          ⌜ length o1 ∈ [0; 2; 3] ∧ length o2 ∈ [2; 3] ∧ o1 ++ o2 = o ⌝ }}}.
    Admitted.

    (* NOTE(Juliette): basically [fold_right push] and [fold_left inject] *)
    Definition push_whole_buffer : val. Admitted.
    Definition inject_whole_buffer : val. Admitted.

  End buffers.

End assumptions.

Hint Resolve elem_of_list_here : find_in_list.
Hint Resolve elem_of_list_further : find_in_list.

Ltac find := eauto with find_in_list.

Section configurations.
  (* This section describes buffer configurations and potentials *)

  (* Triple configuration: first and last are [2;3] *)
  Inductive triple_configuration : nat -> nat -> nat -> Prop :=
    | left_leaning : forall x y, x ∈ [2; 3] -> y ∈ [0; 2; 3] -> triple_configuration x 0 y
    | has_child : forall x o y, x ∈ [2; 3] -> o > 0 -> y ∈ [2; 3] -> triple_configuration x o y.

  (* Five-tuple configuration matching OCaml invariants *)
  Inductive five_tuple_configuration : nat -> nat -> nat -> nat -> nat -> Prop :=
    | suffix_only : forall s, s ∈ [1..8] -> five_tuple_configuration 0 0 0 0 s
    | has_middle : forall p ld rd s, p ∈ [3..6] -> s ∈ [3..6] -> five_tuple_configuration p ld 2 rd s.


  Inductive colour : Set :=
    | green | red | very_red.

  Definition buffer_colour : nat -> colour :=
    λ n,
    match n with
    | 8 => very_red
    | 3 | 6 => red
    | _ => green
    end.

End configurations.

(* Potential associated with the first and last argument of the five-tuple configuration *)
Notation "pre ⋄ suf" :=
  (match buffer_colour pre, buffer_colour suf with
  | _, very_red | red, red => 3
  | red, green | green, red => 1
  | _, _ => 0
  end) (at level 60).


Section potential_deques.
  (* This section describes the structure used for the proof of the time-complexity bounds *)

  Context `{!heapGS Σ} `{!na_invG Σ}.
  Variable π : gname.

  Let isDequeType := nat -d> list val -d> val -d> iProp Σ.

  (* Buffer unwinding: abstract content depends on level *)
  Definition bufferPre (size : nat) : isDequeType -d> isDequeType := (
  λ self_triple n content buf,
    match n with
    | 0 => raw_buffer content buf ∗ ⌜ length content = size ⌝
    | S n =>
        ∃ (triples : list val) (triple_contents : list (list val)),
          raw_buffer triples buf ∗
          ⌜ content = concat triple_contents ∧ length triples = size ⌝ ∗
          [∗ list] tri; c ∈ triples; triple_contents, ▷ self_triple n c tri
    end
  )%I.

  Global Instance bufferPreContractive size : Contractive (bufferPre size).
  Proof.
    rewrite /bufferPre.
    intros k f1 f2 Hdist n c b.
    repeat (f_contractive || f_equiv).
    apply (Hdist _ _ _).
  Qed.

  Definition five_tuple_potential : nat -> nat -> iProp Σ :=
    λ pre suf, ⏱ (pre ⋄ suf).

  Let fFiveTuple (triple_pred : isDequeType) (deque_pred : isDequeType) : isDequeType := (
    λ n o d, ∃ (pr ld md rd sf : val)
      (pr_content left_content md_content right_content sf_content : list val)
      (kPr kMd kSf : nat),
      ⌜ d = (pr, ld, md, rd, sf)%V ⌝ ∗
      ⌜ five_tuple_configuration kPr (length left_content) kMd (length right_content) kSf ⌝ ∗
      five_tuple_potential kPr kSf ∗
      bufferPre kPr triple_pred n pr_content pr ∗
      deque_pred (S n) left_content ld ∗
      bufferPre kMd triple_pred n md_content md ∗
      deque_pred (S n) right_content rd ∗
      bufferPre kSf triple_pred n sf_content sf ∗
      ⌜ o = pr_content ++ left_content ++ md_content ++ right_content ++ sf_content ⌝
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
        (fst_content child_content lst_content : list val)
        (kFst kLst : nat),
        ⌜ triple_configuration kFst (length child_content) kLst ⌝ ∗
        ⌜ t = (fst, ch, lst)%V ⌝ ∗
        bufferPre kFst triple_pred n fst_content fst ∗
        deque_pred (S n) child_content ch ∗
        bufferPre kLst triple_pred n lst_content lst ∗
        ⌜ o = fst_content ++ child_content ++ lst_content ⌝
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
    do 30 (f_contractive || f_equiv). apply bufferPreContractive, dist_dist_later, Hdist_cad.
    f_equiv. by apply (Hdist_tri _ _ _).
    f_equiv. by apply bufferPreContractive, dist_dist_later, Hdist_cad.
    f_equiv. apply (Hdist_tri _ _ _).
    f_equiv. apply bufferPreContractive, dist_dist_later, Hdist_cad.
  Qed.

  Local Instance fTriple_contractive :
    ∀ n, Proper (dist_later n ==> dist n ==> dist n) fTriple.
  Proof.
    intros k deque1 deque2 Hdist_cad triple1 triple2 Hdist_tri.
    intros n o t.
    rewrite /fTriple.
    do 19 (f_contractive || f_equiv).
    - by apply bufferPreContractive.
    - f_equiv. by apply (Hdist_tri _ _ _).
      f_equiv. by apply bufferPreContractive.
  Qed.

  Definition triple := fixpoint_A fTriple fDeque.
  Definition isDeque := fixpoint_B fTriple fDeque.
  Definition fiveTuple := fFiveTuple triple isDeque.
  Definition isElement n o e := match n with 0 => ⌜ o = [e] ⌝%I | S n => triple n o e end.
  Definition buffer size := bufferPre size triple.
  Definition IsDeque o d := isDeque 0 o d.

  Definition isPersFiveTuple : isDequeType := (
    λ n o d, ∃ (pr ld md rd sf : val)
      (pr_content left_content md_content right_content sf_content : list val)
      (kPr kMd kSf : nat),
      ⌜ d = (pr, ld, md, rd, sf)%V ⌝ ∗
      ⌜ five_tuple_configuration kPr (length left_content) kMd (length right_content) kSf ⌝ ∗
      bufferPre kPr triple n pr_content pr ∗
      isDeque (S n) left_content ld ∗
      bufferPre kMd triple n md_content md ∗
      isDeque (S n) right_content rd ∗
      bufferPre kSf triple n sf_content sf ∗
      ⌜ o = pr_content ++ left_content ++ md_content ++ right_content ++ sf_content ⌝
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
  Global Instance bufferPersistent s ϕ n b c :
    (∀ n o d, Persistent (ϕ n o d)) → Persistent (bufferPre s ϕ n b c).
  Proof.
    intros HPers.
    rewrite /bufferPre.
    destruct n; apply _.
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
      assert (forall a b, Persistent (fixpoint (fDeque x) (S n) a b)); [| apply _].
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
            & %kPr & %kMd & %kSf & -> & %cfg & pot
            & #Hpr & #Hld & #Hmd & #Hrd & #Hsf & %Heq)".
    iSplitR; iExists pr, ld, md, rd, sf, prC, ldC, mdC, rdC, sfC, kPr, kMd, kSf; iFrame "#"; iFrame;
    (iSplitR; [done | iSplitR; done]).
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
            & %kPr & %kMd & %kSf & -> & %cfg
            & #Hpr & #Hld & #Hmd & #Hrd & #Hsf & %Heq) τ]".
    iExists pr, ld, md, rd, sf, prC, ldC, mdC, rdC, sfC, kPr, kMd, kSf; iFrame "#"; iFrame.
    do 2 (iSplitR; [done |]).
    iSplitL; [iApply (three_time_enough with "τ") | done].
  Qed.

End potential_deques.

Section algorithms.

  Context `{!heapGS Σ}.

  Let empty := NONEV.

  Example singleton : val :=
    λ: "x", SOME (ref (empty_buffer, NONEV, empty_buffer, NONEV, bpush "x" empty_buffer)%E).

  Notation "'let:2' ( x , y ) := u 'in' v"
  := (let: "TMP2" := u in
      let: x := Fst "TMP2" in
      let: y := Snd "TMP2" in
      v)%E
     (at level 190, x,y at next level, u at next level, v at next level, only parsing).

  Notation "'let:5' ( v , w , x , y , z ) := U 'in' V"
    := (let: "TMP5" := U in
        let:2 ("TMP5", z) := "TMP5" in
        let:2 ("TMP5", y) := "TMP5" in
        let:2 ("TMP5", x) := "TMP5" in
        let:2 (v, w) := "TMP5" in
        V)%E
      (at level 190, v,w,x,y,z at next level, U at next level, V at next level, only parsing).

  Definition push : val :=
    rec: "push" "x" "d" :=
    tick #();;
    match: "d" with
      NONE => singleton "x"
    | SOME "r" =>
      let:5 ("prefix", "left_deque", "middle", "right_deque", "suffix") := !"r" in
      if: bsize "middle" = #0%nat then (
        (* suffix-only *)
        if: bsize "suffix" = #8%nat then (
          let:2 ("x1", "suffix") := bpop "suffix" in
          let:2 ("x2", "suffix") := bpop "suffix" in
          let:2 ("x3", "suffix") := bpop "suffix" in
          let: "prefix" := bpush "x1" (bpush "x2" (bpush "x3" empty_buffer)) in
          let:2 ("x4", "suffix") := bpop "suffix" in
          let:2 ("x5", "suffix") := bpop "suffix" in
          let: "middle" := bpush "x4" (bpush "x5" empty_buffer) in
          "r" <- ( "prefix", empty, "middle", empty, "suffix" );;
          SOME (ref (bpush "x" "prefix", empty, "middle", empty, "suffix"))
        ) else (
          "r" <- ("prefix", "left_deque", "middle", "right_deque", "suffix");;
          SOME (ref ("prefix", "left_deque", "middle", "right_deque", bpush "x" "suffix"))
        )
      ) else (
        (* normal mode *)
        if: bsize "prefix" = #6%nat then (
          let:2 ("prefix", "x6") := beject "prefix" in
          let:2 ("prefix", "x5") := beject "prefix" in
          let: "prefix'" := bpush "x5" (bpush "x6" empty_buffer) in
          let: "left_deque" := "push" ("prefix'", empty, empty_buffer) "left_deque" in
          "r" <- ( "prefix", "left_deque", "middle", "right_deque", "suffix" );;
          SOME (ref (bpush "x" "prefix", "left_deque", "middle", "right_deque", "suffix"))
        ) else
          "r" <- ("prefix", "left_deque", "middle", "right_deque", "suffix");;
          SOME (ref (bpush "x" "prefix", "left_deque", "middle", "right_deque", "suffix"))
      )
    end.

  Corollary inject : val. Admitted.

  Definition concat : val :=
    λ: "d1" "d2",
    tick #();;
    match: "d1" with NONE => "d2"
    | SOME "r1" =>
    match: "d2" with NONE => "d1"
    | SOME "r2" =>
    let:5 ("pr1", "ld1", "md1", "rd1", "sf1") := !"r1" in
    if: bsize "md1" = #0%nat then push_whole_buffer push "sf1" "d2" else
    let:5 ("pr2", "ld2", "md2", "rd2", "sf2") := !"r2" in
    if: bsize "md2" = #0%nat then inject_whole_buffer inject "d1" "sf2" else
    let:2 ("y", "pr2'") := bpop "pr2" in
    let:2 ("sf1'", "x") := beject "sf1" in
    let: "middle" := bpush "x" (bpush "y" empty_buffer) in
    let:2 ("s1'", "s1''") := partition_buffer_left "sf1'" in
    let: "ld1'" := inject "ld1" ("md1", "rd1", "s1'") in
    let: "ld1''" := if: bsize "s1''" = #0%nat then "ld1'"
      else inject "ld1'" ("s1''", empty, empty_buffer) in
    let:2 ("p2'", "p2''") := partition_buffer_right "pr2'" in
    let: "rd2'" := push ("p2''", "ld2", "md2") "rd2" in
    let: "rd2''" := if: bsize "p2'" = #0%nat then "rd2'"
      else push ("p2'", empty, empty_buffer) "rd2'" in
    SOME (ref ("pr1", "ld1''", "middle", "rd2''", "sf2"))
    end end.

End algorithms.

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

  Example singleton_spec : forall x : val,
    {{{ emp }}} singleton x {{{ d, RET d; IsDeque π (⋅x) d }}}.
  Proof.
    iIntros (x Φ) "_ Hψ".
    rewrite /singleton. wp_pures.
    wp_bind (bpush _ _)%E.
    wp_apply (bpush_spec) as "%b #Hb".
      { iApply empty_is_buffer. }
    wp_pures.
    wp_bind (ref _)%E.
    wp_apply (ssref_alloc _ (fiveTuple π 0 (⋅ x))) as "%ℓ Hℓ".
      { rewrite /fiveTuple.
        iExists empty_buffer, empty, empty_buffer, empty, b,
                []          , []   , []          , []    , (⋅x),
                0, 0, 1.
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

  Lemma bsize_better_spec k n o b :
    {{{ buffer π k n o b }}}
      bsize b
    {{{ RET #k; True }}}.
  Proof.
    iIntros (ψ) "Hb Hψ".
    destruct n.
    - iDestruct "Hb" as "[Hb <-]".
      by iApply (bsize_spec with "Hb").
    - iDestruct "Hb" as "(%tr & %trC & Hb & (_ & %Heq) & _)".
      iApply (bsize_spec with "Hb").
      by subst.
  Qed.

  Lemma empty_is_buffer_at : forall depth, ⊢ buffer π 0 depth [] empty_buffer.
  Proof.
    destruct depth.
    - iSplitR; [ by iApply empty_is_buffer | done ].
    - iExists [], [].
      iSplitR; [ by iApply empty_is_buffer |].
      iSplitR; done.
  Qed.

  Lemma singleton_better : forall depth x oX b, isElement π depth oX x -∗ raw_buffer (⋅x) b -∗ fiveTuple π depth oX (empty_buffer, NONEV, empty_buffer, NONEV, b)%V.
  Proof.
    iIntros (depth x oX b) "Hx #Hb".
    iExists empty_buffer, empty, empty_buffer, empty, b,
            []          , []   , []          , []   , oX,
            0, 0, 1.
    rewrite /=.
    iSplitR. rewrite //.
    iSplitR. iPureIntro. constructor. auto with find_in_list.
    iSplitR. by iApply time_zero.
    iSplitR. isEmptyBufferAtDepth depth.
    iSplitR. isEmptyDeque.
    iSplitR. isEmptyBufferAtDepth depth.
    iSplitR. isEmptyDeque.
    iSplitL; [| done].
    rewrite /bufferPre.
    destruct depth.
    - iDestruct "Hx" as "->"; iSplitL; rewrite //.
    - rewrite /isElement.
      iExists [x], [oX].
      iSplitR. done.
      iSplitR. iSplitR. iPureIntro. rewrite /=. by aac_reflexivity.
      iPureIntro. split; rewrite //=; by aac_reflexivity.
      rewrite /=; iSplitL; done.
  Qed.

  Lemma empty_buffer_is_empty : forall n b o, buffer π 0 n o b ⊢ ⌜ o = [] ⌝.
  Proof.
    destruct n; iIntros (b o) "H".
    - iDestruct "H" as "[_ %Heq]". iPureIntro; by apply nil_length_inv.
    - iDestruct "H" as "(%t & %c & _ & (%Hc & %Heq) & H)".
      iDestruct (big_sepL2_length with "H") as "%Hl".
      iPureIntro.
      rewrite Hc.
      rewrite Hl in Heq.
      apply nil_length_inv in Heq.
      by rewrite Heq //.
  Qed.

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
      binject x b
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

  Notation time_for_push := 7.

  Lemma push_spec_helper oD oX x d : forall depth,
    {{{ isDeque π depth oD d ∗ isElement π depth oX x ∗ ⏱ time_for_push ∗ Token π depth }}}
      push x d
    {{{ d', RET d'; isDeque π depth (oX ++ oD) d' ∗ Token π depth }}}.
  Proof.
    iLöb as "iH" forall (x d oX oD).
    iIntros (depth ψ) "(Hd & #Hx & τ & O) Hψ".
    rewrite /push.
    iDestruct (split_time 1 with "τ") as "[ι τ]". by auto with arith.
    wp_pures.
    wp_apply (tick_spec with "ι") as "_".
    wp_pures.
    rewrite {1} isDeque_unfold.
    iDestruct "Hd" as "[[-> ->] | (%ℓ & -> & #Hℓ)]".
    - wp_pures.
      rewrite /singleton. wp_pures.
      wp_apply bpush_spec as "%b #Hb".
        { iApply empty_is_buffer. }
      wp_pures.
      wp_bind (ref _)%E.
      wp_apply (ssref_alloc π (fiveTuple _ depth oX) with "[Hx]") as "%ℓ #Hℓ".
      + rewrite app_nil_r. by iApply (singleton_better with "Hx").
      + wp_pures.
        iApply "Hψ".
        iFrame.
        ℓisDeque ℓ. iModIntro. rewrite !app_nil_r //.
    - wp_pures.
      wp_apply (ssref_load_open with "[O]") as "%d (O & πd & DONE)".
        { iFrame. iExact "Hℓ". }
      wp_pures.
      iDestruct (persist_structure with "πd") as
        "[#Hd (%pr & %ld & %md & %rd & %sf & %prC & %ldC & %mdC & %rdC & %sfC
          & %kPr & %kMd & %kSf & -> & %cfg & pot
          & #Hpr & #Hld & #Hmd & #Hrd & #Hsf & %Heq)]".
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
          wp_apply (pop_buffer_element_spec with "Hsf") as "%x1 %b1 (%oX1 & %o1 & Hsf' & -> & Hx1)".
          wp_pures.
          wp_apply (pop_buffer_element_spec with "Hsf'") as "%x2 %b2 (%oX2 & %o2 & Hsf' & -> & Hx2)".
          wp_pures.
          wp_apply (pop_buffer_element_spec with "Hsf'") as "%x3 %b3 (%oX3 & %o3 & Hsf' & -> & Hx3)".
          wp_pures.
          wp_apply (push_buffer_element_spec with "[Hx3]") as "%bp3 Hbp".
            { iFrame. rewrite Heqmd. by iApply empty_is_buffer_at. }
          wp_apply (push_buffer_element_spec with "[Hbp Hx2]") as "%bp2 Hbp". by iFrame.
          wp_apply (push_buffer_element_spec with "[Hbp Hx1]") as "%pr' #Hpr'". by iFrame.
          wp_pures.
          wp_apply (pop_buffer_element_spec with "Hsf'") as "%x4 %b4 (%oX4 & %o4 & Hsf' & -> & Hx4)".
          wp_pures.
          wp_apply (pop_buffer_element_spec with "Hsf'") as "%x5 %sf' (%oX5 & %o5 & #Hsf' & -> & Hx5)".
          wp_pures.
          wp_apply (push_buffer_element_spec with "[Hx5]") as "%bp5 Hbm".
            { iFrame. by iApply empty_is_buffer_at. }
          wp_apply (push_buffer_element_spec with "[Hbm Hx4]") as "%md' #Hmd'". by iFrame.
          wp_pures.
          rewrite !app_nil_r Heqmd.
          wp_bind (#ℓ <- _)%E.
          iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
          iApply (wp_wand with "[DONE ι O]").
          {
            iApply ("DONE" with "[ι]"); [| by iFrame].
            iNext.
            iExists pr', empty, md', empty, sf',
              (oX1 ++ oX2 ++ oX3), [], (oX4 ++ oX5), [], o5,
              3, 2, 3.
            solve_no_middle Heq H H1.
          }
          iIntros (unit) "O".
          wp_pures; clear unit.
          wp_bind (bpush _ _)%E.
          iDestruct "Hx" as "#Hx".
          wp_apply (push_buffer_element_spec with "[Hpr' Hx]") as "%pr'' #Hpr''". by iFrame "#".
          wp_pures.
          wp_bind (ref _)%E.
          iDestruct (split_time 1 with "τ") as "[ι τ]". by lia.
          wp_apply (ssref_alloc π (fiveTuple _ depth (oX ++ oD)) with "[Hx ι]") as "%ℓ' #Hℓ'".
          -- iExists pr'', empty, md', empty, sf',
              (oX ++ oX1 ++ oX2 ++ oX3), [], (oX4 ++ oX5), [], o5,
              4, 2, 3.
            solve_no_middle Heq H H1.
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
            iFrame. iExact "Hd".
          }
          iIntros (unit) "O".
          wp_pures; clear unit.
          wp_apply (push_buffer_element_spec with "[Hsf Hx]") as "%sf' #Hsf'". by iFrame "#".
          wp_pures.
          iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
          wp_apply (ssref_alloc π (fiveTuple _ depth (oX ++ oD)) with "[Hx ι]") as "%ℓ' #Hℓ'".
          -- iExists pr, ld, md, rd, sf',
              [], [], [], [], (oX ++ oD),
              0, 0, (S kSf).
            inversion cfg; [| exfalso; lia ].
            iDestruct (empty_buffer_is_empty with "Hpr") as "->".
            iDestruct (empty_buffer_is_empty with "Hmd") as "->".
            symmetry in H; rewrite (nil_length_inv _ H) in Heq |- *.
            symmetry in H1; rewrite (nil_length_inv _ H1) in Heq |- *.
            iSplitR; [ done |].
            iSplitR; [ iPureIntro; constructor; invert_all_in |].
            iSplitL; [ iApply (three_time_enough with "ι") |].
            do 4 (iSplitR; [by trivial |]).
            aac_normalise in Heq.
            rewrite Heq.
            iSplitR; [ done |].
            iPureIntro; aac_reflexivity.
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
          wp_apply (eject_buffer_element_spec with "Hpr") as "%b6 %x6 (%oX6 & %o6 & Hpr' & -> & Hx6)".
          wp_pures.
          wp_apply (eject_buffer_element_spec with "Hpr'") as "%pr2 %x5 (%oX5 & %o5 & #Hpr2 & -> & Hx5)".
          wp_pures.
          wp_apply (push_buffer_element_spec with "[Hx6]") as "%bs6 Hbp".
            { iFrame. by iApply empty_is_buffer_at. }
          wp_apply (push_buffer_element_spec with "[Hbp Hx5]") as "%pr' #Hpr'". by iFrame.
          do 4 wp_pure.
          iSpecialize ("iH" $! (pr', NONEV, empty_buffer)%V ld (oX5 ++ oX6) ldC (S depth)).
          iDestruct (time_combine with "[τ pot]") as "τ". by (rewrite /=; iFrame).
          iDestruct (split_time time_for_push with "τ") as "[ι τ]".
            { destruct (buffer_colour kSf); rewrite /=; auto. }
          wp_apply ("iH" with "[ι O]") as "%ld' [#Hld' O]"; iClear "iH". {
            iFrame "#".
            rewrite /isElement triple_unfold !app_nil_r.
            iFrame.
            iExists pr', NONEV, empty_buffer,
              (oX5 ++ oX6), [], [],
              2, 0.
            iSplitR. { iPureIntro; eapply left_leaning; auto with find_in_list.  }
            iSplitR. done.
            iSplitR. done.
            iSplitR. isEmptyDeque.
            iSplitR. iApply empty_is_buffer_at.
            iPureIntro; aac_reflexivity.
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
              o5, ((oX5 ++ oX6) ++ ldC), mdC, rdC, sfC,
              4, 2, kSf.
            iFrame "#".
            iSplitR. done.
            iSplitR. { iPureIntro; constructor; auto with find_in_list. }
            iSplitL.
              { rewrite {2}/five_tuple_potential.
                invert_all_in; rewrite //=; auto.
              }
            iPureIntro; aac_rewrite Heq; aac_reflexivity.
          }
          iIntros (unit) "O".
          wp_pures; clear unit.
          wp_apply (push_buffer_element_spec with "[Hx Hpr2]") as "%pr3 #Hpr3". by iFrame "#".
          wp_pures.
          iDestruct (split_time (5 ⋄ kSf) with "τ") as "[ι τ]".
            { invert_all_in; rewrite //=; auto. }
          wp_apply (ssref_alloc π (fiveTuple _ depth (oX ++ oD)) with "[ι]") as "%ℓ' #Hℓ'". {
            iExists pr3, ld', md, rd, sf,
              (oX ++ o5), ((oX5 ++ oX6) ++ ldC), mdC, rdC, sfC,
              5, 2, kSf.
            iFrame "#".
            iSplitR. done.
            iSplitR. { iPureIntro; constructor; auto with find_in_list. }
            iSplitL.
              { rewrite {2}/five_tuple_potential.
                invert_all_in; rewrite //=; auto.
              }
            iPureIntro; aac_rewrite Heq; aac_reflexivity.
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
            iFrame. iExact "Hd".
          }
          iIntros (unit) "O".
          wp_pures; clear unit.
          wp_apply (push_buffer_element_spec with "[Hpr Hx]") as "%pr' #Hpr'". by iFrame "#".
          wp_pures.
          wp_bind (ref _)%E.
          iDestruct (split_time 3 with "τ") as "[ι τ]". by lia.
          wp_apply (ssref_alloc π (fiveTuple _ depth (oX ++ oD)) with "[ι]") as "%ℓ' #Hℓ'".
          -- iExists pr', ld, md, rd, sf,
              (oX ++ prC), ldC, mdC, rdC ,sfC,
              (S kPr), kMd, kSf.
            inversion cfg; [ exfalso; lia |].
            iFrame "#".
            iSplitR. done.
            iSplitR. { iPureIntro; constructor; [invert_all_in | auto with find_in_list]. }
            iSplitL. by iApply (three_time_enough with "ι").
            iPureIntro; aac_rewrite Heq; aac_reflexivity.
          -- wp_pures.
            iApply "Hψ".
            iFrame.
            ℓisDeque ℓ'.
            iExact "Hℓ'".
  Qed.

  Theorem push_spec oD (x : val) (d : val) :
    {{{ IsDeque π oD d ∗ ⏱ time_for_push ∗ Token π 0 }}}
      push x d
    {{{ d', RET d'; IsDeque π (⋅x ++ oD) d' ∗ Token π 0 }}}.
  Proof.
    iIntros (ψ) "(HD & τ & O) Hψ".
    rewrite /IsDeque.
    wp_apply (push_spec_helper with "[HD τ O]") as "%d' HD'".
      { iFrame. rewrite /isElement. rewrite /=. iFrame. done. }
    by iApply "Hψ".
  Qed.

  Corollary inject_spec_helper oD oX x d : forall depth,
    {{{ isDeque π depth oD d ∗ isElement π depth oX x ∗ ⏱ time_for_push ∗ Token π depth }}}
      inject d x
    {{{ d', RET d'; isDeque π depth (oD ++ oX) d' ∗ Token π depth }}}.
 Admitted.

  Corollary inject_spec oD (x : val) (d : val) :
    {{{ IsDeque π oD d ∗ ⏱ time_for_push ∗ Token π 0 }}}
      inject d x
    {{{ d', RET d'; IsDeque π (oD ++ ⋅x) d' ∗ Token π 0 }}}.
  Admitted.

  (* NOTE(Juliette): Marked as 0 time cost, but runs in ⏱ (8 * time_for_push) constant time *)
  Corollary push_whole_spec : forall lvl b oB d oD size,
    {{{ buffer π size lvl oB b ∗ isDeque π lvl oD d ∗ Token π 0 }}}
      push_whole_buffer push b d
    {{{ d', RET d'; isDeque π lvl (oB ++ oD) d' ∗ Token π 0 }}}.
  Admitted.

  (* NOTE(Juliette): Marked as 0 time cost, but runs in ⏱ (8 * time_for_push) constant time *)
  Corollary inject_whole_spec : forall lvl b oB d oD size,
    {{{ buffer π size lvl oB b ∗ isDeque π lvl oD d ∗ Token π 0 }}}
      inject_whole_buffer inject d b
    {{{ d', RET d'; isDeque π lvl (oD ++ oB) d' ∗ Token π 0 }}}.
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

  Property partition_buffer_left_better_spec : forall lvl k o b,
    {{{ buffer π k lvl o b ∗ ⌜ k ∈ [2..6] ⌝ }}}
      partition_buffer_left b
    {{{ b1 b2 o1 o2 k1 k2, RET (b1, b2)%V;
        buffer π k1 lvl o1 b1 ∗ buffer π k2 lvl o2 b2 ∗
        ⌜ k1 ∈ [2; 3] ∧ k2 ∈ [0; 2; 3] ∧ o1 ++ o2 = o ⌝ }}}.
  Proof.
    destruct lvl.
    - iIntros (k o b ψ) "[[#Hb <-] %Hk] Hψ".
      wp_apply partition_buffer_left_spec as (b1 b2) "(%o1 & %o2 & Hb1 & Hb2 & (%Hl1 & %Hl2 & <-))".
        by iFrame "#".
      iApply "Hψ".
      by iFrame.
    - iIntros (k o b ψ) "[(%tr & %con & #Hb & (-> & <-) & Hall) %Hk] Hψ".
      wp_apply partition_buffer_left_spec as (b1 b2) "(%o1 & %o2 & Hb1 & Hb2 & (%Hl1 & %Hl2 & <-))".
        by iFrame "#".
      iApply "Hψ".
  Admitted.

  Property partition_buffer_right_better_spec : forall lvl k o b,
    {{{ buffer π k lvl o b ∗ ⌜ k ∈ [2..6] ⌝ }}}
      partition_buffer_right b
    {{{ b1 b2 o1 o2 k1 k2, RET (b1, b2)%V;
        buffer π k1 lvl o1 b1 ∗ buffer π k2 lvl o2 b2 ∗
        ⌜ k1 ∈ [0; 2; 3] ∧ k2 ∈ [2; 3] ∧ o1 ++ o2 = o ⌝ }}}.
  Admitted.

  Theorem concat_spec (d1 d2 : val) : forall o1 o2,
    {{{ IsDeque π o1 d1 ∗ IsDeque π o2 d2 ∗ ⏱ time_for_concat ∗ Token π 0 }}}
      concat d1 d2
    {{{ d', RET d'; IsDeque π (o1 ++ o2) d' ∗ Token π 0 }}}.
  Proof.
    iIntros (o1 o2 ψ) "(Hd1 & Hd2 & τ & O) Hψ".
    rewrite /concat /IsDeque.
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
      [(%pr1 & %ld1 & %md1 & %rd1 & %sf1 & %oPr1 & %oLd1 & %oMd1 & %oRd1 & %oSf1 &
      %kPr1 & %kMd1 & %kSf1 & -> & %cfg1 & #Hpr1 & #Hld1 & #Hmd1 & #Hrd1 & #Hsf1 & %Ho1)
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
      rewrite (nil_length_inv _ (eq_sym H)) in Ho1 |- *.
      rewrite (nil_length_inv _ (eq_sym H1)) in Ho1 |- *.
      aac_normalise in Ho1.
      rewrite Ho1 //.
      }
    apply bool_decide_eq_false_1 in Heqb as Heqmd1.
    apply bool_decide_code_false in Heqb as ->.
    wp_pures.
    wp_apply (ssref_read π _ (isPersFiveTuple _ _ _) with "[Hℓ2 O]") as "%v'
      [(%pr2 & %ld2 & %md2 & %rd2 & %sf2 & %oPr2 & %oLd2 & %oMd2 & %oRd2 & %oSf2 &
      %kPr2 & %kMd2 & %kSf2 & -> & %cfg2 & #Hpr2 & #Hld2 & #Hmd2 & #Hrd2 & #Hsf2 & %Ho2)
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
      rewrite (nil_length_inv _ (eq_sym H)) in Ho2 |- *.
      rewrite (nil_length_inv _ (eq_sym H1)) in Ho2 |- *.
      aac_normalise in Ho2.
      rewrite Ho2 //.
    }
    apply bool_decide_eq_false_1 in Heqb as Heqmd2.
    apply bool_decide_code_false in Heqb as ->.
    wp_pures.
    inversion cfg1; [exfalso; by apply Heqmd2 |].
    inversion cfg2; [exfalso; by apply Heqmd2 |].
    change (kPr2 ∈ map S [2; 3; 4; 5]) in H6.
    apply decrease_in in H6 as (kPr2' & -> & HkPr2').
    wp_apply (pop_buffer_element_spec with "Hpr2") as "%y %pr1' (%oY & %oBY & Hpr2' & -> & Hy)".
    wp_pures.
    change (kSf1 ∈ map S [2; 3; 4; 5]) in H0.
    apply decrease_in in H0 as (kSf1' & -> & HkSf1').
    wp_apply (eject_buffer_element_spec with "Hsf1") as "%sf1' %x (%oX & %oBX & Hsf1' & -> & Hx)".
    wp_pures.
    wp_apply (push_buffer_element_spec with "[Hy]") as "%bm Hbm".
      { iFrame. by iApply empty_is_buffer_at. }
    wp_apply (push_buffer_element_spec with "[Hbm Hx]") as "%md' #Hmd'". by iFrame.
    wp_pures.
    wp_apply (partition_buffer_left_better_spec with "[Hsf1']") as "%s1' %s1'' %os1' %os1'' %ks1' %ks1'' (#Hs1' & #Hs1'' & (%Hos1' & %Hos1'' & %Hos1eq))".
      { iFrame. iPureIntro. invert_all_in. }
    wp_pures.
    iDestruct (na_own_acc _ _ _ (next_stage 0) with "O") as "[O A]".
    iDestruct (split_time time_for_push with "τ") as "[ι τ]". by lia.
    rewrite !app_nil_r.
    wp_apply (inject_spec_helper with "[Hld1 ι O]") as "%ld1' [#Hld1' O]".
      { iFrame "#". iFrame. rewrite /isElement triple_unfold.
        iExists md1, rd1, s1', oMd1, oRd1, os1', kMd1, ks1'.
        inversion cfg1; [ rewrite -H3 in H14; lia |].
        iSplitR. iPureIntro.
        destruct (length oRd1); [apply left_leaning | apply has_child];
          auto with find_in_list arith.
        iSplitR. done.
        by iFrame "#".
      }
    wp_pures.
    wp_bind (if: _ then _ else _)%E.
    wp_apply (bsize_better_spec with "Hs1''") as "_".
    wp_pures.
    destruct (bool_decide (ks1'' = 0)) eqn:?.
    + apply bool_decide_eq_true_1 in Heqb as Heqs1.
      apply bool_decide_code_true in Heqb as ->.
      wp_pures.
      wp_apply (partition_buffer_right_better_spec with "[Hpr2']") as "%p2' %p2'' %op2' %op2'' %kp2' %kp2'' (#Hp2' & #Hp2'' & (%Hp21' & %Hp2'' & %Hop2eq))".
        { iFrame. iPureIntro. invert_all_in. }
      wp_pures.
      iDestruct ("A" with "O") as "O".
      iDestruct (na_own_acc _ _ _ (next_stage 0) with "O") as "[O A]".
      iDestruct (split_time time_for_push with "τ") as "[ι τ]". by lia.
      wp_apply (push_spec_helper with "[Hrd2 ι O]") as "%rd2' [#Hrd2' O]".
      { iFrame "#". iFrame. rewrite /isElement triple_unfold.
        iExists p2'', ld2, md2, op2'', oLd2, oMd2, kp2'', kMd2.
        inversion cfg2.
        iSplitR. iPureIntro.
        destruct (length oLd2); [apply left_leaning | apply has_child];
          auto with find_in_list arith.
        iSplitR. done.
        by iFrame "#".
      }
      wp_pures.
      wp_bind (if: _ then _ else _)%E.
      wp_apply (bsize_better_spec with "Hp2'") as "_".
      wp_pures.
      destruct (bool_decide (kp2' = 0)) eqn:?.
      * apply bool_decide_eq_true_1 in Heqb as Heqp2.
        apply bool_decide_code_true in Heqb as ->.
        wp_pures.
        wp_apply (ssref_alloc π (fiveTuple π 0 (o1 ++ o2)) with "[τ]") as (ℓ') "Hℓ'".
          { iExists pr1, ld1', md', rd2', sf2,
            oPr1, (oLd1 ++ oMd1 ++ oRd1 ++ os1'), (oX ++ oY), ((op2'' ++ oLd2 ++ oMd2) ++ oRd2), oSf2,
            kPr1, 2, kSf2.
            iSplitR. done.
            iSplitR. iPureIntro. constructor; auto with find_in_list.
            iSplitL "τ". iApply three_time_enough. iDestruct (split_time 3 with "τ") as "[ι _]"; [lia | auto].
            iFrame "#".
            rewrite Heqs1 Heqp2.
            iDestruct (empty_buffer_is_empty with "Hs1''") as "->".
            iDestruct (empty_buffer_is_empty with "Hp2'") as "->".
            iPureIntro.
            rewrite Ho1 Ho2 -Hos1eq -Hop2eq.
            aac_reflexivity.
          }
        wp_pures.
        iApply "Hψ".
        iDestruct ("A" with "O") as "O".
        iFrame.
        ℓisDeque ℓ'. iExact "Hℓ'".
      * apply bool_decide_eq_false_1 in Heqb as Heqp2.
        apply bool_decide_code_false in Heqb as ->.
        wp_pures.
        iDestruct ("A" with "O") as "O".
        iDestruct (na_own_acc _ _ _ (next_stage 0) with "O") as "[O A]".
        iDestruct (split_time time_for_push with "τ") as "[ι τ]". by lia.
        wp_apply (push_spec_helper with "[Hrd2' ι O]") as "%rd2'' [#Hrd2'' O]".
          { iFrame "#". iFrame.
            rewrite /isElement triple_unfold.
            iExists p2', empty, empty_buffer, op2', [], [], kp2', 0.
            iSplitR. iPureIntro. constructor; invert_all_in.
            iSplitR. done.
            iFrame "#".
            iSplitR. isEmptyDeque.
            iSplitR. rewrite /bufferPre. iSplitL. by iApply empty_is_buffer. done.
            done.
          }
        wp_pures.
        wp_apply (ssref_alloc π (fiveTuple π 0 (o1 ++ o2)) with "[τ]") as (ℓ') "Hℓ'".
          { iExists pr1, ld1', md', rd2'', sf2,
            oPr1, (oLd1 ++ oMd1 ++ oRd1 ++ os1'), (oX ++ oY), (op2' ++ (op2'' ++ oLd2 ++ oMd2) ++ oRd2), oSf2,
            kPr1, 2, kSf2.
            iSplitR. done.
            iSplitR. iPureIntro. constructor; auto with find_in_list.
            iSplitL "τ". iApply three_time_enough. iDestruct (split_time 3 with "τ") as "[ι _]"; [lia | auto].
            rewrite Heqs1 !app_nil_r.
            iDestruct (empty_buffer_is_empty with "Hs1''") as "->".
            iFrame "#".
            iPureIntro.
            rewrite Ho1 Ho2 -Hos1eq -Hop2eq.
            aac_reflexivity.
          }
        wp_pures.
        iApply "Hψ".
        iDestruct ("A" with "O") as "O".
        iFrame.
        ℓisDeque ℓ'. iExact "Hℓ'".
    + apply bool_decide_eq_false_1 in Heqb as Heqs1.
      apply bool_decide_code_false in Heqb as ->.
      wp_pures.
      iDestruct ("A" with "O") as "O".
        iDestruct (na_own_acc _ _ _ (next_stage 0) with "O") as "[O A]".
        iDestruct (split_time time_for_push with "τ") as "[ι τ]". by lia.
        wp_apply (inject_spec_helper with "[Hld1' ι O]") as "%ld1'' [#Hld1'' O]".
          { iFrame "#". iFrame.
            rewrite /isElement triple_unfold.
            iExists s1'', empty, empty_buffer, os1'', [], [], ks1'', 0.
            iSplitR. iPureIntro. constructor; invert_all_in.
            iSplitR. done.
            iFrame "#".
            iSplitR. isEmptyDeque.
            iSplitR. rewrite /bufferPre. iSplitL. by iApply empty_is_buffer. done.
            done.
          }
      wp_pures.
      wp_apply (partition_buffer_right_better_spec with "[Hpr2']") as "%p2' %p2'' %op2' %op2'' %kp2' %kp2'' (#Hp2' & #Hp2'' & (%Hp21' & %Hp2'' & %Hop2eq))".
        { iFrame. iPureIntro. invert_all_in. }
      wp_pures.
      iDestruct ("A" with "O") as "O".
      iDestruct (na_own_acc _ _ _ (next_stage 0) with "O") as "[O A]".
      iDestruct (split_time time_for_push with "τ") as "[ι τ]". by lia.
      wp_apply (push_spec_helper with "[Hrd2 ι O]") as "%rd2' [#Hrd2' O]".
      { iFrame "#". iFrame. rewrite /isElement triple_unfold.
        iExists p2'', ld2, md2, op2'', oLd2, oMd2, kp2'', kMd2.
        inversion cfg2.
        iSplitR. iPureIntro.
        destruct (length oLd2); [apply left_leaning | apply has_child];
          auto with find_in_list arith.
        iSplitR. done.
        by iFrame "#".
      }
      wp_pures.
      wp_bind (if: _ then _ else _)%E.
      wp_apply (bsize_better_spec with "Hp2'") as "_".
      wp_pures.
      rewrite !app_nil_r.
      destruct (bool_decide (kp2' = 0)) eqn:?.
      * apply bool_decide_eq_true_1 in Heqb as Heqp2.
        apply bool_decide_code_true in Heqb as ->.
        wp_pures.
        wp_apply (ssref_alloc π (fiveTuple _ 0 (o1 ++ o2)) with "[τ]") as (ℓ') "Hℓ'".
          { iExists pr1, ld1'', md', rd2', sf2,
            oPr1, ((oLd1 ++ oMd1 ++ oRd1 ++ os1') ++ os1''), (oX ++ oY), ((op2'' ++ oLd2 ++ oMd2) ++ oRd2), oSf2,
            kPr1, 2, kSf2.
            iSplitR. done.
            iSplitR. iPureIntro. constructor; auto with find_in_list.
            iSplitL "τ". iApply three_time_enough. iDestruct (split_time 3 with "τ") as "[ι _]"; [lia | auto].
            iFrame "#".
            rewrite Heqp2.
            iDestruct (empty_buffer_is_empty with "Hp2'") as "->".
            iPureIntro.
            rewrite Ho1 Ho2 -Hos1eq -Hop2eq.
            aac_reflexivity.
          }
        wp_pures.
        iApply "Hψ".
        iDestruct ("A" with "O") as "O".
        iFrame.
        ℓisDeque ℓ'. iExact "Hℓ'".
      * apply bool_decide_eq_false_1 in Heqb as Heqp2.
        apply bool_decide_code_false in Heqb as ->.
        wp_pures.
        iDestruct ("A" with "O") as "O".
        iDestruct (na_own_acc _ _ _ (next_stage 0) with "O") as "[O A]".
        iDestruct (split_time time_for_push with "τ") as "[ι τ]". by lia.
        wp_apply (push_spec_helper with "[Hrd2' ι O]") as "%rd2'' [#Hrd2'' O]".
          { iFrame "#". iFrame.
            rewrite /isElement triple_unfold.
            iExists p2', empty, empty_buffer, op2', [], [], kp2', 0.
            iSplitR. iPureIntro. constructor; invert_all_in.
            iSplitR. done.
            iFrame "#".
            iSplitR. isEmptyDeque.
            iSplitR. rewrite /bufferPre. iSplitL. by iApply empty_is_buffer. done.
            done.
          }
        wp_pures.
        wp_apply (ssref_alloc π (fiveTuple _ 0 (o1 ++ o2)) with "[τ]") as (ℓ') "Hℓ'".
          { iExists pr1, ld1'', md', rd2'', sf2,
            oPr1, ((oLd1 ++ oMd1 ++ oRd1 ++ os1')++os1''), (oX ++ oY), (op2' ++ (op2'' ++ oLd2 ++ oMd2) ++ oRd2), oSf2,
            kPr1, 2, kSf2.
            iSplitR. done.
            iSplitR. iPureIntro. constructor; auto with find_in_list.
            iSplitL "τ". iApply three_time_enough. iDestruct (split_time 3 with "τ") as "[ι _]"; [lia | auto].
            rewrite !app_nil_r.
            iFrame "#".
            iPureIntro.
            rewrite Ho1 Ho2 -Hos1eq -Hop2eq.
            aac_reflexivity.
          }
        wp_pures.
        iApply "Hψ".
        iDestruct ("A" with "O") as "O".
        iFrame.
        ℓisDeque ℓ'. iExact "Hℓ'".
  Qed.

End proofs.
