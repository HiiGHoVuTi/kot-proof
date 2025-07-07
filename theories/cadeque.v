From iris.heap_lang Require Import lang proofmode notation.
From iris.bi.lib Require Import fixpoint_banach.
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
Notation "[1..8]" := [1; 2; 3; 4; 5; 6; 7; 8].
(* End notations *)

Section assumptions.
  Context `{!heapGS Σ}.

  (* All functions in this section are assumed to run in O(1) time and space. *)

  Section buffers.
    (* Buffers will have bounded size, guaranteeing O(1) time and space complexity *)

    Definition isBuffer (o : list val) : val -> iProp Σ.   
    Admitted.
  
    Global Instance isBufferPersistent o v : Persistent (isBuffer o v).
    Admitted.
  
    Definition empty_buffer : val.
    Admitted.
  
    Axiom empty_is_buffer : ⊢ isBuffer [] empty_buffer.
  
    Definition bpush : val.
    Admitted.
  
    Property bpush_spec : forall o b x,
      {{{ isBuffer o b }}}
        bpush x b
      {{{ b', RET b'; isBuffer (⋅x ++ o) b' }}}.
    Admitted.
    
    Definition bpop : val.
    Admitted.
    
    Property bpop_spec : forall o b x,
      {{{ isBuffer (⋅x ++ o) b }}}
        bpop b
      {{{ b', RET (x, b')%V; isBuffer o b' }}}.
    Admitted.
  
    Definition binject : val.
    Admitted.

    Property binject_spec : forall o b x,
      {{{ isBuffer o b }}}
        binject x b
      {{{ b', RET b'; isBuffer (o ++ ⋅x) b' }}}.
    Admitted.
  
    Definition beject : val.
    Admitted.

    Property beject_spec : forall o b x,
      {{{ isBuffer (o ++ ⋅x) b }}}
        beject b
      {{{ b', RET (x, b')%V; isBuffer o b' }}}.
    Admitted.
  
    Definition bsize : val.
    Admitted.
  
    Property bsize_spec : forall o b,
      {{{ isBuffer o b }}}
        bsize b
      {{{ RET #(length o); emp }}}.
    Admitted.

    Definition partition_buffer_left : val.
    Admitted.

    Property partition_buffer_left_spec : forall o b,
      {{{ isBuffer o b ∗ ⌜ length o ∈ [2..6] ⌝ }}}
        partition_buffer_left b
      {{{ b1 b2, RET (b1, b2)%V; 
        ∃ o1 o2, isBuffer o1 b1 ∗ isBuffer o2 b2 ∗ 
          ⌜ length o1 ∈ [2; 3] ∧ length o2 ∈ [0; 2; 3] ∧ o1 ++ o2 = o ⌝ }}}.
    Admitted.

    Definition partition_buffer_right : val.
    Admitted.

    Property partition_buffer_right_spec : forall o b,
      {{{ isBuffer o b ∗ ⌜ length o ∈ [2..6] ⌝ }}}
        partition_buffer_right b
      {{{ b1 b2, RET (b1, b2)%V; 
        ∃ o1 o2, isBuffer o1 b1 ∗ isBuffer o2 b2 ∗ 
          ⌜ length o1 ∈ [0; 2; 3] ∧ length o2 ∈ [2; 3] ∧ o1 ++ o2 = o ⌝ }}}.
    Admitted.

    (* NOTE(Juliette): basically [fold_right push] and [fold_left inject] *)
    Definition push_whole_buffer : val. Admitted.
    Definition inject_whole_buffer : val. Admitted.

  End buffers.

End assumptions.

Section shared_cadeques.
  (* This section describes the structure used for the proof of the thread-safety and functional correctness *)
  Context `{!heapGS Σ}.

  Let isCadequeType := nat -d> list val -d> val -d> iProp Σ.

  (* Triple configuration: first and last are [2;3] *)
  Inductive triple_configuration : nat -> nat -> nat -> Prop :=
    | left_leaning : forall x y, x ∈ [2; 3] -> y ∈ [0; 2; 3] -> triple_configuration x 0 y
    | has_child : forall x o y, x ∈ [2; 3] -> o > 0 -> y ∈ [2; 3] -> triple_configuration x o y.

  (* Five-tuple configuration matching OCaml invariants *)
  Inductive five_tuple_configuration : nat -> nat -> nat -> nat -> nat -> Prop :=
    | suffix_only : forall s, s ∈ [1..8] -> five_tuple_configuration 0 0 0 0 s
    | has_middle : forall p ld rd s, p ∈ [3..6] -> s ∈ [3..6] -> five_tuple_configuration p ld 2 rd s.
 
  (* Buffer unwinding: abstract content depends on level *)
  Definition isBufferAtLevelPre (size : nat) : isCadequeType -d> isCadequeType := (
  λ self_triple n content buf,
    match n with
    | 0 => isBuffer content buf ∗ ⌜ length content = size ⌝
    | S n => 
        ∃ (triples : list val) (triple_contents : list (list val)),
          isBuffer triples buf ∗
          ⌜ content = concat triple_contents ∧ length triples = size ⌝ ∗
          [∗ list] tri; c ∈ triples; triple_contents, ▷ self_triple n c tri
    end
  )%I.
  
  Global Instance isBufferAtLevelPreContractive size : Contractive (isBufferAtLevelPre size).
  Proof.
    rewrite /isBufferAtLevelPre.
    intros k f1 f2 Hdist n c b.
    repeat (f_contractive || f_equiv).
    apply (Hdist _ _ _).
  Qed.

  Let fFiveTuple (triple_pred : isCadequeType) (cadeque_pred : isCadequeType) : isCadequeType := (
    λ n o d, ∃ (pr ld md rd sf : val)
      (pr_content left_content md_content right_content sf_content : list val)
      (kPr kMd kSf : nat),
      ⌜ d = (pr, ld, md, rd, sf)%V ⌝ ∗
      ⌜ five_tuple_configuration kPr (length left_content) kMd (length right_content) kSf ⌝ ∗
      isBufferAtLevelPre kPr triple_pred n pr_content pr ∗
      cadeque_pred (S n) left_content ld ∗
      isBufferAtLevelPre kMd triple_pred n md_content md ∗
      cadeque_pred (S n) right_content rd ∗
      isBufferAtLevelPre kSf triple_pred n sf_content sf ∗
      ⌜ o = pr_content ++ left_content ++ md_content ++ right_content ++ sf_content ⌝
  )%I.

  (* Define the mutual fixpoint functions *)
  Let fCadeque (triple_pred : isCadequeType) (cadeque_pred : isCadequeType) : isCadequeType := (
    λ n o d,
      (⌜ d = NONEV ∧ o = [] ⌝) ∨
      (∃ ℓ : loc, ⌜ d = SOMEV #ℓ ⌝ ∗ 
        ℓ ⤇ fFiveTuple triple_pred cadeque_pred n o)
  )%I.

  Let fTriple (triple_pred : isCadequeType) (cadeque_pred : isCadequeType) : isCadequeType := (
    λ n o t,
      ∃ (fst ch lst : val) 
        (fst_content child_content lst_content : list val)
        (kFst kLst : nat),
        ⌜ triple_configuration kFst (length child_content) kLst ⌝ ∗
        ⌜ t = (fst, ch, lst)%V ⌝ ∗
        isBufferAtLevelPre kFst triple_pred n fst_content fst ∗
        cadeque_pred (S n) child_content ch ∗
        isBufferAtLevelPre kLst triple_pred n lst_content lst ∗
        ⌜ o = fst_content ++ child_content ++ lst_content ⌝
  )%I.

  (* Prove contractivity *)
  Local Instance fCadeque_contractive : 
    ∀ n, Proper (dist_later n ==> dist_later n ==> dist n) fCadeque.
  Proof.
    intros k cadeque1 cadeque2 Hdist_cad triple1 triple2 Hdist_tri.
    intros n o d.
    rewrite /fCadeque.
    do 4 (f_contractive || f_equiv).
    rewrite /sref.
    do 4 (f_contractive || f_equiv).
    rewrite /fFiveTuple.
    do 29 (f_contractive || f_equiv). by apply isBufferAtLevelPreContractive, dist_dist_later, Hdist_cad.
    f_equiv. by apply (Hdist_tri _ _ _).
    f_equiv. by apply isBufferAtLevelPreContractive, dist_dist_later, Hdist_cad.
    f_equiv. apply (Hdist_tri _ _ _).
    f_equiv. apply isBufferAtLevelPreContractive, dist_dist_later, Hdist_cad. 
  Qed.

  Local Instance fTriple_contractive : 
    ∀ n, Proper (dist_later n ==> dist n ==> dist n) fTriple.
  Proof.
    intros k cadeque1 cadeque2 Hdist_cad triple1 triple2 Hdist_tri.
    intros n o t.
    rewrite /fTriple.
    do 19 (f_contractive || f_equiv).
    - by apply isBufferAtLevelPreContractive.
    - f_equiv. by apply (Hdist_tri _ _ _).
      f_equiv. by apply isBufferAtLevelPreContractive.
  Qed.

  Definition isTriple := fixpoint_A fTriple fCadeque.
  Definition isCadeque := fixpoint_B fTriple fCadeque.
  Definition isFiveTuple := fFiveTuple isTriple isCadeque.
  Definition isElement n o e := match n with 0 => ⌜ o = [e] ⌝%I | S n => isTriple n o e end.
  Definition isBufferAtLevel size := isBufferAtLevelPre size isTriple.
  Definition IsCadeque o d := isCadeque 0 o d.

  (* Unfolding lemmas come directly from the fixpoint theory *)
  Lemma isCadeque_unfold n o d : 
    isCadeque n o d ⊣⊢ fCadeque isTriple isCadeque n o d.
  Proof.
    symmetry.
    apply (fixpoint_B_unfold fTriple fCadeque _ _ _).
  Qed.

  Lemma isTriple_unfold n o t : 
    isTriple n o t ⊣⊢ fTriple isTriple isCadeque n o t.
  Proof.
    symmetry.
    apply (fixpoint_A_unfold fTriple fCadeque _ _ _).
  Qed.

  (* Persistence instances *)
  Global Instance isBufferAtPersistent s ϕ n b c : 
    (∀ n o d, Persistent (ϕ n o d)) → Persistent (isBufferAtLevelPre s ϕ n b c).
  Proof. 
    intros HPers. 
    rewrite /isBufferAtLevelPre. 
    destruct n; apply _.
  Qed.
  
  Global Instance isCadequePersistent n o d : Persistent (isCadeque n o d).
  Proof. 
    rewrite isCadeque_unfold /fCadeque. 
    apply _.
  Qed.

  Global Instance isTriplePersistent n o t : Persistent (isTriple n o t).
  Proof. 
    rewrite /isTriple /fixpoint_A /ofe.fixpoint_AB.
    revert n o t. apply fixpoint_ind.
    - intros f1 f2 H P n o t. rewrite -(H _ _ _) //.
    - exists (λ _ _ _, emp)%I. apply _.
    - intros.
      rewrite /ofe.fixpoint_AA /fTriple /ofe.fixpoint_AB.
      assert (forall a b, Persistent (fixpoint (fCadeque x) (S n) a b)); [| apply _].
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

  Global Instance isFiveTuplePersistent n o d : Persistent (isFiveTuple n o d).
  Proof. 
    apply _.
  Qed.

  Global Instance isElementPersistent n o e : Persistent (isElement n o e).
  Proof. 
    destruct n; apply _.
  Qed.

End shared_cadeques.

Hint Resolve elem_of_list_here : find_in_list.
Hint Resolve elem_of_list_further : find_in_list.

Ltac find := eauto with find_in_list.

Section algorithms.

  Context `{!heapGS Σ}.

  Let empty := NONEV.

  Example singleton : val :=
    λ: "x", SOME (ref (empty_buffer, NONEV, empty_buffer, NONEV, bpush "x" empty_buffer)%E).

  Notation "'let:2' ( x , y ) := u 'in' v"
  := (let: "TMP" := u in
      let: x := Fst "TMP" in
      let: y := Snd "TMP" in
      v)%E
     (at level 190, x,y at next level, u at next level, v at next level, only parsing).

  (* TODO: passer en linéaire *)
  Notation "'let:5' ( v , w , x , y , z ) := U 'in' V"
    := (let: "TMP" := U in
        let: v := Fst (Fst (Fst (Fst "TMP"))) in
        let: w := Snd (Fst (Fst (Fst "TMP"))) in
        let: x := Snd (Fst (Fst "TMP")) in
        let: y := Snd (Fst "TMP") in
        let: z := Snd "TMP" in
        V)%E
      (at level 190, v,w,x,y,z at next level, U at next level, V at next level, only parsing).

  Definition push : val := 
    rec: "push" "x" "d" :=
    match: "d" with
      NONE => singleton "x"
    | SOME "r" =>
      let:5 ("prefix", "left_deque", "middle", "right_deque", "suffix") :=
        modify "r" (λ: "v",
          let:5 ("prefix", "left_deque", "middle", "right_deque", "suffix") := "v" in
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
              ( "prefix", empty, "middle", empty, "suffix" )
            ) else "v"
          ) else (
            (* normal mode *)
            if: bsize "prefix" = #6%nat then (
              let:2 ("prefix", "x6") := beject "prefix" in
              let:2 ("prefix", "x5") := beject "prefix" in
              let: "prefix'" := bpush "x5" (bpush "x6" empty_buffer) in
              let: "left_deque" := "push" ("prefix'", empty, empty_buffer) "left_deque" in
              ( "prefix", "left_deque", "middle", "right_deque", "suffix" )
            ) else "v"
          )
        )
      in if: bsize "middle" = #0%nat
        then 
          SOME (ref ("prefix", "left_deque", "middle", "right_deque", bpush "x" "suffix")) 
        else   
          SOME (ref (bpush "x" "prefix", "left_deque", "middle", "right_deque", "suffix"))
    end.

  Corollary inject : val. Admitted.

  Definition concat : val :=
    λ: "d1" "d2",
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
      else push ("p2'", empty, empty_buffer) in
    SOME (ref ("pr1", "ld1''", "middle", "rd2''", "sf2"))
    end end.

End algorithms.

Section proofs.

  Context `{!heapGS Σ}.

  Ltac ℓisCadeque ℓ := rewrite !isCadeque_unfold; iRight; iExists ℓ; iSplitR; [done |].

  Ltac isEmptyCadeque := rewrite !isCadeque_unfold; iLeft; iPureIntro; done.

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
    {{{ emp }}} singleton x {{{ d, RET d; IsCadeque (⋅x) d }}}.
  Proof.
    iIntros (x Φ) "_ Hψ".
    rewrite /singleton. wp_pures.
    wp_bind (bpush _ _)%E.
    wp_apply (bpush_spec) as "%b #Hb".
      { iApply empty_is_buffer. }
    wp_pures.
    wp_bind (ref _)%E.
    wp_apply (sref_alloc (isFiveTuple 0 (⋅ x))) as "%ℓ Hℓ".
      { rewrite /isFiveTuple. 
        iExists empty_buffer, empty, empty_buffer, empty, b,
                []          , []   , []          , []    , (⋅x),
                0, 0, 1.
        rewrite //=.
        iSplitL. rewrite //.
        iSplitL. iPureIntro. constructor. by auto with find_in_list.
        iSplitL. iSplitL. iApply empty_is_buffer. done.
        iSplitL. isEmptyCadeque.
        iSplitL. iSplitL. iApply empty_is_buffer. done.
        iSplitL. isEmptyCadeque.
        iFrame "#". done.
      }
    wp_pures.
    iApply "Hψ".
    iModIntro.
    rewrite /IsCadeque. ℓisCadeque ℓ.
    done.
  Qed.

  Ltac isEmptyBufferAtDepth depth := 
  destruct depth; 
  [ iSplitL; [by iApply empty_is_buffer | rewrite //]
  | iExists [], []; iSplitL; try iSplitL; rewrite //; by iApply empty_is_buffer ].

  Lemma bsize_better_spec k n o b : 
    {{{ isBufferAtLevel k n o b }}}
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

  Lemma empty_is_buffer_at : forall depth, ⊢ isBufferAtLevel 0 depth [] empty_buffer.
  Proof.
    destruct depth.
    - iSplitR; [ by iApply empty_is_buffer | done ].
    - iExists [], [].
      iSplitR; [ by iApply empty_is_buffer |].
      iSplitR; done.
  Qed.

  Lemma singleton_better : forall depth x oX b, isElement depth oX x -∗ isBuffer (⋅x) b -∗ isFiveTuple depth oX (empty_buffer, NONEV, empty_buffer, NONEV, b)%V.
  Proof.
    iIntros (depth x oX b) "Hx #Hb".
    iExists empty_buffer, empty, empty_buffer, empty, b,
            []          , []   , []          , []   , oX,
            0, 0, 1.
    rewrite /=.
    iSplitR. rewrite //.
    iSplitR. iPureIntro. constructor. auto with find_in_list. 
    iSplitR. isEmptyBufferAtDepth depth.
    iSplitR. isEmptyCadeque.
    iSplitR. isEmptyBufferAtDepth depth.
    iSplitR. isEmptyCadeque.
    iSplitL; [| done].
    rewrite /isBufferAtLevelPre.
    destruct depth.
    - iDestruct "Hx" as "->"; iSplitL; rewrite //.
    - rewrite /isElement.
      iExists [x], [oX].
      iSplitR. done.
      iSplitR. iSplitR. iPureIntro. rewrite /=. by aac_reflexivity.
      iPureIntro. split; rewrite //=; by aac_reflexivity.
      rewrite /=; iSplitL; done.
  Qed.

  Lemma empty_buffer_is_empty : forall n b o, isBufferAtLevel 0 n o b ⊢ ⌜ o = [] ⌝.
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

  Lemma later_under_big_sepL2 : forall X Y n,
    ([∗list] x;y ∈ X;Y, isTriple n y x) ⊢ [∗list] x;y ∈ X;Y, ▷ isTriple n y x.
  Admitted.

  Lemma push_buffer_element_spec x b : forall n o oX size,
    {{{ isElement n oX x ∗ isBufferAtLevel size n o b }}}
      bpush x b
    {{{ b', RET b'; isBufferAtLevel (S size) n (oX ++ o) b' }}}.
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
      rewrite /isBufferAtLevel /isBufferAtLevelPre.
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
    {{{ isElement n oX x ∗ isBufferAtLevel size n o b }}}
      binject x b
    {{{ b', RET b'; isBufferAtLevel (S size) n (o ++ oX) b' }}}.
  Admitted.

  Lemma pop_buffer_element_spec b : forall n o size,
    {{{ isBufferAtLevel (S size) n o b }}}
      bpop b
    {{{ x b', RET (x, b'); ∃ oX o', isBufferAtLevel size n o' b' ∗ ⌜ o = oX ++ o' ⌝ ∗ isElement n oX x }}}.
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
    {{{ isBufferAtLevel (S size) n o b }}}
      beject b
    {{{ b' x, RET (b', x); ∃ oX o', isBufferAtLevel size n o' b' ∗ ⌜ o = o' ++ oX ⌝ ∗ isElement n oX x }}}.
  Admitted.

  Ltac solve_no_middle Heq H H1 := 
  iSplitR; [done |];
  iSplitR; [iPureIntro; constructor; auto with find_in_list |];
  iSplitR; [trivial |];
  iSplitR; [isEmptyCadeque |];
  iSplitR; [trivial |];
  iSplitR; [isEmptyCadeque |];
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

  Lemma push_spec_helper oD oX x d : forall depth,
    {{{ isCadeque depth oD d ∗ isElement depth oX x }}}
      push x d
    {{{ d', RET d'; isCadeque depth (oX ++ oD) d' }}}.
  Proof.
    iLöb as "iH" forall (x d oX oD).
    iIntros (depth ψ) "[Hd Hx] Hψ".
    rewrite /push.
    wp_pures.
    rewrite {1} isCadeque_unfold.
    iDestruct "Hd" as "[[-> ->] | (%ℓ & -> & #Hℓ)]".
    - wp_pures.
      rewrite /singleton. wp_pures.
      wp_apply bpush_spec as "%b #Hb".
        { iApply empty_is_buffer. }
      wp_pures.
      wp_bind (ref _)%E.
      wp_apply (sref_alloc (isFiveTuple depth oX) with "[Hx]") as "%ℓ #Hℓ".
      + rewrite app_nil_r. by iApply (singleton_better with "Hx").
      + wp_pures.
        iApply "Hψ".
        ℓisCadeque ℓ. iModIntro. rewrite !app_nil_r //.
    - wp_pures.
      rewrite /modify. wp_pures.
      wp_apply (sref_load with "Hℓ") 
        as "%v #Hv".
      iCombine "Hv Hv" as "[_ (%pr & %ld & %md & %rd & %sf & %prC & %ldC & %mdC & %rdC & %sfC 
            & %kPr & %kMd & %kSf & -> & %cfg 
            & #Hpr & Hld & #Hmd & Hrd & #Hsf & %Heq)]".
      wp_pures.
      wp_bind (if: _ then _ else _)%E.
      wp_apply (bsize_better_spec with "Hmd") as "_".
      wp_pures.
      destruct (bool_decide (kMd = 0)) eqn:?.
      + apply bool_decide_eq_true_1 in Heqb as Heqmd.
        apply bool_decide_code_true in Heqb as ->.
        wp_pures.
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
          wp_bind (#ℓ <- _)%E.
          rewrite !app_nil_r !Heqmd.
          wp_apply (sref_store) as "_".
          -- iSplitR. iExact "Hℓ". 
            iExists pr', empty, md', empty, sf',
              (oX1 ++ oX2 ++ oX3), [], (oX4 ++ oX5), [], o5,
              3, 2, 3.
              solve_no_middle Heq H H1.
          -- wp_pures.
            wp_apply (bsize_better_spec with "Hmd'") as "_".
            wp_pures.
            wp_bind (bpush _ _)%E.
            iDestruct "Hx" as "#Hx".
            wp_apply (push_buffer_element_spec with "[Hpr' Hx]") as "%PR #HPR". by iFrame "#".
            wp_pures.
            wp_bind (ref _)%E.
            wp_apply (sref_alloc (isFiveTuple depth (oX ++ oD)) with "[Hx]") as "%ℓ' Hℓ'".
            ++ iExists PR, empty, md', empty, sf',
                (oX ++ oX1 ++ oX2 ++ oX3), [], (oX4 ++ oX5), [], o5,
                4, 2, 3.
                solve_no_middle Heq H H1.
            ++ wp_pures.
              iApply "Hψ".
              iModIntro.
              ℓisCadeque ℓ'.
              rewrite /isFiveTuple //.
          * apply bool_decide_eq_false_1 in Heqb as sfNotFull.
            apply bool_decide_code_false in Heqb as ->.
            wp_pures.
            wp_bind (#ℓ <- _)%E.
            wp_apply (sref_store) as "_".
              { iFrame "#". iExact "Hv". }
            wp_pures.
            iDestruct "Hx" as "#Hx".
            rewrite Heqmd.
            wp_apply (bsize_better_spec with "Hmd") as "_".
            wp_pures.
            wp_bind (bpush _ _)%E.
            wp_apply (push_buffer_element_spec with "[Hsf Hx]") as "%sf' #Hsf'". by iFrame "#".
            wp_pures.
            wp_bind (ref _)%E.
            wp_apply (sref_alloc (isFiveTuple depth (oX ++ oD)) with "[Hx]") as "%ℓ' Hℓ'".
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
              do 4 (iSplitR; [by trivial |]).
              aac_normalise in Heq.
              rewrite Heq.
              iSplitR; [ done |].
              iPureIntro; aac_reflexivity.
            -- wp_pures.
              iApply "Hψ".
              ℓisCadeque ℓ'.
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
          wp_apply "iH" as "%ld' #Hld'"; iClear "iH Hv". {
             iFrame "#".
            rewrite /isElement isTriple_unfold !app_nil_r.
            iExists pr', NONEV, empty_buffer,
              (oX5 ++ oX6), [], [],
              2, 0.
            iSplitR. { iPureIntro; eapply left_leaning; auto with find_in_list.  }
            iSplitR. done.
            iSplitR. done.
            iSplitR. isEmptyCadeque.
            iSplitR. iApply empty_is_buffer_at.
            iPureIntro; aac_reflexivity.
          }
          wp_pures.
          wp_bind (#ℓ <- _)%E.
          wp_apply sref_store as "_".
          -- iFrame "#".
            iExists pr2, ld', md, rd, sf,
              o5, ((oX5 ++ oX6) ++ ldC), mdC, rdC, sfC,
              4, 2, kSf.
            inversion cfg.
            iFrame "#".
            iSplitR. done.
            iSplitR. { iPureIntro; constructor; by auto with find_in_list. }
            iPureIntro; aac_rewrite Heq; aac_reflexivity.
          -- wp_pures. 
            wp_apply (bsize_better_spec with "Hmd") as "_".
            wp_pures. rewrite Heqmd2. wp_pures.
            wp_apply (push_buffer_element_spec with "[Hx Hpr2]") as "%pr3 #Hpr3". by iFrame "#".
            wp_pures.
            wp_bind (ref _)%E.
            wp_apply (sref_alloc (isFiveTuple depth (oX ++ oD))) as "%ℓ' #Hℓ'". {
              iExists pr3, ld', md, rd, sf,
                (oX ++ o5), ((oX5 ++ oX6) ++ ldC), mdC, rdC, sfC,
                5, 2, kSf.
              inversion cfg.
              rewrite !app_nil_r.
              iFrame "#".
              iSplitR. done.
              iSplitR. { iPureIntro; constructor; auto with find_in_list. }
              iPureIntro; aac_rewrite Heq; aac_reflexivity.
            }
            wp_pures.
            iApply "Hψ".
            ℓisCadeque ℓ'.
            iExact "Hℓ'".
        * apply bool_decide_eq_false_1 in Heqb0 as prNotFull.
          apply bool_decide_code_false in Heqb0 as ->.
          wp_pures.
          wp_apply sref_store as "_".
            { iFrame "#"; iExact "Hv". }
          iClear "Hv".
          wp_pures.
          wp_apply (bsize_better_spec with "Hmd") as "_".
          wp_pures. rewrite Heqmd2. wp_pures.
          wp_apply (push_buffer_element_spec with "[Hpr Hx]") as "%pr' #Hpr'". by iFrame "#".
          wp_pures.
          wp_bind (ref _)%E.
          wp_apply (sref_alloc (isFiveTuple depth (oX ++ oD))) as "%ℓ' Hℓ'".
          -- iExists pr', ld, md, rd, sf,
              (oX ++ prC), ldC, mdC, rdC ,sfC,
              (S kPr), kMd, kSf.
            inversion cfg; [ exfalso; lia |].
            iFrame "#".
            iSplitR. done.
            iSplitR. { iPureIntro; constructor; [invert_all_in | auto with find_in_list]. }
            iPureIntro; aac_rewrite Heq; aac_reflexivity.
          -- wp_pures. 
            iApply "Hψ".
            ℓisCadeque ℓ'.
            iExact "Hℓ'".
  Qed.

  Theorem push_spec oD (x : val) (d : val) :
    {{{ IsCadeque oD d }}}
      push x d
    {{{ d', RET d'; IsCadeque (⋅x ++ oD) d' }}}.
  Proof.
    iIntros (ψ) "HD Hψ".
    rewrite /IsCadeque.
    wp_apply (push_spec_helper with "[HD]") as "%d' HD'".
      { iFrame. rewrite /isElement. done. }
    by iApply "Hψ". 
  Qed.

  Corollary inject_spec oD (x : val) (d : val) :
    {{{ IsCadeque oD d }}}
      inject d x
    {{{ d', RET d'; IsCadeque (oD ++ ⋅x) d' }}}.
  Admitted.

  Corollary push_whole_spec : forall lvl b oB d oD size,
    {{{ isBufferAtLevel size lvl oB b ∗ isCadeque lvl oD d }}}
      push_whole_buffer push b d
    {{{ d', RET d'; isCadeque lvl (oB ++ oD) d' }}}.
  Admitted.

  Corollary inject_whole_spec : forall lvl b oB d oD size,
    {{{ isBufferAtLevel size lvl oB b ∗ isCadeque lvl oD d }}}
      inject_whole_buffer inject d b
    {{{ d', RET d'; isCadeque lvl (oD ++ oB) d' }}}.
  Admitted.

  Theorem concat_spec (d1 d2 : val) : forall o1 o2,
    {{{ IsCadeque o1 d1 ∗ IsCadeque o2 d2 }}}
      concat d1 d2
    {{{ d', RET d'; IsCadeque (o1 ++ o2) d' }}}.
  Proof.
    iIntros (o1 o2 ψ) "[Hd1 Hd2] Hψ".
    rewrite /concat /IsCadeque.
    wp_pures.
    (* trivial cases *)
    rewrite {1} isCadeque_unfold.
    iDestruct "Hd1" as "[[-> ->] | (%ℓ1 & -> & #Hℓ1)]".
    { wp_pures. iApply "Hψ". rewrite app_nil_l //. }
    rewrite {1} isCadeque_unfold.
    iDestruct "Hd2" as "[[-> ->] | (%ℓ2 & -> & #Hℓ2)]".
    { wp_pures. iApply "Hψ". ℓisCadeque ℓ1. rewrite app_nil_r. iExact "Hℓ1". }
    wp_pures.
    wp_apply (sref_load with "Hℓ1") as "%v 
      (%pr1 & %ld1 & %md1 & %rd1 & %sf1 & %oPr1 & %oLd1 & %oMd1 & %oRd1 & %oSf1 & 
      %kPr1 & %kMd1 & %kSf1 & -> & %cfg1 & #Hpr1 & #Hld1 & #Hmd1 & #Hrd1 & #Hsf1 & %Ho1)".
    wp_pures.
    wp_apply (bsize_better_spec with "Hmd1") as "_".
    wp_pures.
    destruct (bool_decide (kMd1 = 0)) eqn:?.
    { (* d1 is suffix only *)
      apply bool_decide_eq_true_1 in Heqb as Heqmd.
      apply bool_decide_code_true in Heqb as ->.
      wp_pures.
      wp_apply push_whole_spec as "%d' #Hd'".
        { iSplitL. iExact "Hsf1". ℓisCadeque ℓ2. iExact "Hℓ2". }
      iApply "Hψ".
      inversion cfg1.
      - iDestruct (empty_buffer_is_empty with "Hpr1") as "->".
        iDestruct (empty_buffer_is_empty with "Hmd1") as "->".
        rewrite (nil_length_inv _ (eq_sym H)) in Ho1 |- *.
        rewrite (nil_length_inv _ (eq_sym H1)) in Ho1 |- *.
        aac_normalise in Ho1.
        rewrite Ho1 //.
      - exfalso. lia. }
    apply bool_decide_eq_false_1 in Heqb as Heqmd1.
    apply bool_decide_code_false in Heqb as ->.
    wp_pures.
    wp_apply (sref_load with "Hℓ2") as "%v'
      (%pr2 & %ld2 & %md2 & %rd2 & %sf2 & %oPr2 & %oLd2 & %oMd2 & %oRd2 & %oSf2 & 
      %kPr2 & %kMd2 & %kSf2 & -> & %cfg2 & #Hpr2 & #Hld2 & #Hmd2 & #Hrd2 & #Hsf2 & %Ho2)".
    wp_pures.
    wp_apply (bsize_better_spec with "Hmd2") as "_".
    wp_pures.
    destruct (bool_decide (kMd2 = 0)) eqn:?.
    { (* d2 is suffix only *)
      apply bool_decide_eq_true_1 in Heqb as Heqmd.
      apply bool_decide_code_true in Heqb as ->.
      wp_pures.
      wp_apply inject_whole_spec as "%d' #Hd'".
        { iSplitL. iExact "Hsf2". ℓisCadeque ℓ1. iExact "Hℓ1". }
      iApply "Hψ".
  Abort.
  
End proofs.