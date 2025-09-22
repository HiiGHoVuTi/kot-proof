
From iris.heap_lang Require Import lang proofmode notation.
Require Import List.
From Deque Require Import tick fold.

(* Section notations *)
Notation "⋅ x" := [x] (at level 60).
Definition nonempty {A : Type} (x : list A) := ~(x = []).
(* Notation x ∈ [n..m] := (n <= x /\ x <= m) ? *)
Notation "[4..6]" := [4; 5; 6].
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

    Axiom buffer : nat -> list val -> val -> iProp Σ.
    Axiom buffer_persistent : forall n o v, Persistent (buffer n o v).
    Global Instance Ibuffer_persistent n o v : Persistent (buffer n o v).
    Proof. by apply buffer_persistent. Qed.

    Axiom bempty : val.
    Axiom bempty_spec : ⊢ buffer 0 [] bempty.

    Axiom buffer_length : forall n o b, buffer n o b ⊢ ⌜ length o = n ⌝.
    Axiom buffer_injective : forall k k' o o' b, buffer k o b ∗ (buffer k' o' b : iProp Σ) ⊢ ⌜ o = o' ⌝.

    Axiom blength : val.
    Axiom blength_spec : forall n o b,
      {{{ buffer n o b }}} blength b {{{ RET #n; emp }}}.

    Axiom bis_empty : val.
    Axiom bis_empty_spec : forall n o b,
      {{{ buffer n o b }}} bis_empty b {{{ RET #(bool_decide (n = 0%nat)); emp }}}.

    Axiom bpush : val.
    Axiom bpush_spec : forall x n o b,
      {{{ buffer n o b }}} bpush x b {{{ b', RET b'; buffer (n+1) (⋅x++o) b' }}}.

    Axiom bpop : val.
    Axiom bpop_spec : forall n o b,
      {{{ buffer (n+1) o b }}} bpop b {{{ b' x o', RET (x, b')%V; buffer n o' b' ∗ ⌜ o = ⋅x ++ o' ⌝ }}}.

    Axiom bfirst : val.
    Axiom bfirst_spec : forall x n o b,
      {{{ buffer n (⋅x++o) b }}} bfirst b {{{ RET x; emp }}}.

    Axiom binject : val.
    Axiom binject_spec : forall x n o b,
      {{{ buffer n o b }}} binject b x {{{ b', RET b'; buffer (n+1) (o++⋅x) b' }}}.

    Axiom beject : val.
    Axiom beject_spec : forall n o b,
      {{{ buffer (n+1) o b }}} beject b {{{ b' o' x, RET (b', x)%V; buffer n o' b' ∗ ⌜ o = o' ++ ⋅x ⌝ }}}.

    Axiom blast : val.
    Axiom blast_spec : forall x n o b,
      {{{ buffer (n+1) (o++⋅x) b }}} blast b {{{ RET x; emp }}}.

    (* map??? *)

    (* TODO(Juliette): fold_left & fold_right *)
    Axiom bfold_right : val.
    Axiom bfold_right_spec : forall n, has_fold_right_spec bfold_right (buffer n).
    Axiom bfold_left : val.
    Axiom bfold_left_spec : forall n, has_fold_left_spec bfold_left (buffer n).

    Axiom bdoubleton : val.
    Axiom bdoubleton_spec : forall x y,
      {{{ emp }}} bdoubleton x y {{{ b, RET b; buffer 2 (⋅x ++ ⋅y) b }}}.

    Axiom bhas_length_3 : val.
    Axiom bhas_length_3_spec : forall n b o,
      {{{ buffer n o b }}} bhas_length_3 b {{{ RET #(bool_decide (n = 3%nat)); emp }}}.

    Axiom bhas_length_8 : val.
    Axiom bhas_length_8_spec : forall n b o,
      {{{ buffer n o b }}} bhas_length_8 b {{{ RET #(bool_decide (n = 8%nat)); emp }}}.

    Axiom bhas_length_6 : val.
    Axiom bhas_length_6_spec : forall n b o,
      {{{ buffer n o b }}} bhas_length_6 b {{{ RET #(bool_decide (n = 6%nat)); emp }}}.

    Axiom bmove_left_1_33 : val.
    Axiom bmove_left_1_33_spec : forall b1 b2 o1 o2,
      {{{ buffer 3 o1 b1 ∗ buffer 3 o2 b2 }}}
        bmove_left_1_33 b1 b2
      {{{ b1' b2' o1' o2', RET (b1', b2')%V;
          buffer 4 o1' b1' ∗ buffer 2 o2' b2' ∗ ⌜ o1 ++ o2 = o1' ++ o2' ⌝ }}}.

    Axiom bmove_right_1_33 : val.
    Axiom bmove_right_1_33_spec : forall b1 b2 o1 o2,
      {{{ buffer 3 o1 b1 ∗ buffer 3 o2 b2 }}}
        bmove_right_1_33 b1 b2
      {{{ b1' b2' o1' o2', RET (b1', b2')%V;
          buffer 2 o1' b1' ∗ buffer 4 o2' b2' ∗ ⌜ o1 ++ o2 = o1' ++ o2' ⌝ }}}.

    Axiom bdouble_move_left : val.
    Axiom bdouble_move_left_spec : forall b1 b2 b3 o1 o2 o3 n3,
      {{{ buffer 3 o1 b1 ∗ buffer 2 o2 b2 ∗ buffer (n3+1) o3 b3 }}}
        bdouble_move_left b1 b2 b3
      {{{ b1' b2' b3' o1' o2' o3', RET (b1', b2', b3')%V;
        buffer 4 o1' b1' ∗ buffer 2 o2' b2' ∗ buffer n3 o3' b3' ∗
        ⌜ o1 ++ o2 ++ o3 = o1' ++ o2' ++ o3' ⌝ }}}.

    Axiom bdouble_move_right : val.
    Axiom bdouble_move_right_spec : forall b1 b2 b3 o1 o2 o3 n1,
      {{{ buffer (n1+1) o1 b1 ∗ buffer 2 o2 b2 ∗ buffer 3 o3 b3 }}}
        bdouble_move_right b1 b2 b3
      {{{ b1' b2' b3' o1' o2' o3', RET (b1', b2', b3')%V;
          buffer n1 o1' b1' ∗ buffer 2 o2' b2' ∗ buffer 4 o3' b3' ∗
          ⌜ o1 ++ o2 ++ o3 = o1' ++ o2' ++ o3' ⌝ }}}.

    Axiom bconcat23 : val.
    Axiom bconcat23_spec : forall b1 b2 o1 o2,
      {{{ buffer 2 o1 b1 ∗ buffer 3 o2 b2 }}}
        bconcat23 b1 b2
      {{{ b', RET b'; buffer 5 (o1 ++ o2) b' }}}.

    Axiom bconcat32 : val.
    Axiom bconcat32_spec : forall b1 b2 o1 o2,
      {{{ buffer 3 o1 b1 ∗ buffer 2 o2 b2 }}}
        bconcat32 b1 b2
      {{{ b', RET b'; buffer 5 (o1 ++ o2) b' }}}.

    Axiom bconcat323 : val.
    Axiom bconcat323_spec : forall b1 b2 b3 o1 o2 o3,
      {{{ buffer 3 o1 b1 ∗ buffer 2 o2 b2 ∗ buffer 3 o3 b3 }}}
        bconcat323 b1 b2 b3
      {{{ b', RET b'; buffer 8 (o1 ++ o2 ++ o3) b' }}}.

    Axiom bsplit23l : val.
    Axiom bsplit23l_spec : forall n o b,
      {{{ buffer n o b ∗ ⌜ n ∈ [2..6] ⌝ }}}
        bsplit23l b
      {{{ b1 b2 o1 o2 n1 n2, RET (b1, b2)%V;
          buffer n1 o1 b1 ∗ buffer n2 o2 b2 ∗ ⌜ n1 ∈ [2; 3] /\ n2 ∈ [0; 2; 3] /\ o = o1 ++ o2 ⌝ }}}.

    Axiom bsplit23r : val.
    Axiom bsplit23r_spec : forall n o b,
      {{{ buffer n o b ∗ ⌜ n ∈ [2..6] ⌝ }}}
        bsplit23r b
      {{{ b1 b2 o1 o2 n1 n2, RET (b1, b2)%V;
          buffer n1 o1 b1 ∗ buffer n2 o2 b2 ∗ ⌜ n1 ∈ [0; 2; 3] /\ n2 ∈ [2; 3] /\ o = o1 ++ o2 ⌝ }}}.

    Axiom bsplit8 : val.
    Axiom bsplit8_spec : forall o b,
      {{{ buffer 8 o b }}}
        bsplit8 b
      {{{ b1 b2 b3 o1 o2 o3, RET (b1, b2, b3)%V;
          buffer 3 o1 b1 ∗ buffer 2 o2 b2 ∗ buffer 3 o3 b3 ∗ ⌜ o = o1 ++ o2 ++ o3 ⌝ }}}.

    Axiom bsplit642 : val.
    Axiom bsplit642_spec : forall o b,
      {{{ buffer 6 o b }}}
        bsplit642 b
      {{{ b1 b2 o1 o2, RET (b1, b2)%V; buffer 4 o1 b1 ∗ buffer 2 o2 b2 ∗ ⌜ o = o1 ++ o2 ⌝ }}}.

    Axiom bsplit624 : val.
    Axiom bsplit624_spec : forall o b,
      {{{ buffer 6 o b }}}
        bsplit624 b
      {{{ b1 b2 o1 o2, RET (b1, b2)%V; buffer 2 o1 b1 ∗ buffer 4 o2 b2 ∗ ⌜ o = o1 ++ o2 ⌝ }}}.

    (*
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
    *)

  End buffers.

End assumptions.

Ltac list_elem_of := solve [ repeat first [ assumption | constructor ]].
Lemma elem_of_list_app A (x : A) L M : x ∈ L ∨ x ∈ M -> x ∈ (L ++ M).
Proof.
  induction L; intros H; inversion H; simpl; try list_elem_of.
  - inversion H0.
  - inversion H0; constructor; auto.
  - constructor. auto.
Qed.
Hint Resolve elem_of_list_app : find_in_list.

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

  (* Five-tuple configuration for calling naive_pop *)
  Inductive pop_configuration : nat -> nat -> nat -> nat -> nat -> Prop :=
    | pop_suffix_only : forall s, s ∈ [1..8] -> pop_configuration 0 0 0 0 s
    | pop_has_middle : forall p ld rd s, p ∈ [4..6] -> s ∈ [3..6] -> pop_configuration p ld 2 rd s.

  Inductive colour : Set :=
    | very_green | green | red | very_red.

  Definition buffer_colour : nat -> colour :=
    λ n,
    match n with
    | 8 => very_red
    | 0 => very_green
    | 3 | 6 => red
    | _ => green
    end.

End configurations.

(* Potential associated with the first and last argument of the five-tuple configuration *)
Notation "pre ⋄ suf" :=
  (match buffer_colour pre, buffer_colour suf with
  | _, very_red | red, red => 3
  | very_green, _ => 0
  | red, _ | _, red => 1
  | _, _ => 0
  end) (at level 60).

Section algorithms.

  Context `{!heapGS Σ}.

  Let empty := NONEV.

  Example asingleton : val :=
    λ: "x", SOME (ref (bempty, NONEV, bempty, NONEV, bpush "x" bempty)%E).

  Notation "'let:2' ( x , y ) := u 'in' v"
  := (let: "TMP2" := u in
      let: x := Fst "TMP2" in
      let: y := Snd "TMP2" in
      v)%E
     (at level 190, x,y at next level, u at next level, v at next level, only parsing).

  Notation "'let:3' ( v , w , x ) := U 'in' V"
    := (let: "TMP3" := U in
        let:2 ("TMP3", x) := "TMP3" in
        let:2 (v, w) := "TMP3" in
        V)%E
      (at level 190, v,w,x at next level, U at next level, V at next level, only parsing).

  Notation "'let:5' ( v , w , x , y , z ) := U 'in' V"
    := (let: "TMP5" := U in
        let:2 ("TMP5", z) := "TMP5" in
        let:2 ("TMP5", y) := "TMP5" in
        let:2 ("TMP5", x) := "TMP5" in
        let:2 (v, w) := "TMP5" in
        V)%E
      (at level 190, v,w,x,y,z at next level, U at next level, V at next level, only parsing).

  Definition is_ordinary : val :=
    λ: "b", (#2%nat ≤ blength "b") && (blength "b" ≤ #3%nat).

  Definition assemble_ : val :=
    λ: "p", λ: "l", λ: "m", λ: "r", λ: "s",
      SOME (ref ("p", "l", "m", "r", "s")).

  Definition assemble : val :=
    λ: "p", λ: "l", λ: "m", λ: "r", λ: "s",
    if: bis_empty "m" && bis_empty "s" then
      empty
    else
      assemble_ "p" "l" "m" "r" "s".

  Definition atriple_ : val :=
    λ: "f", λ: "c", λ: "l",
      ("f", "c", "l").

  Definition atriple : val :=
    λ: "f", λ: "c", λ: "l",
    if: bis_empty "f" then
      atriple_ "l" "c" bempty
    else
      atriple_ "f" "c" "l".

  Definition abuffer : val :=
    λ: "b", atriple_ "b" empty bempty.

  Definition push : val :=
    rec: "push" "x" "d" :=
    tick #();;
    match: "d" with
      NONE => asingleton "x"
    | SOME "r" =>
      let:5 ("prefix", "left", "middle", "right", "suffix") := !"r" in
      if: bis_empty "middle" then (
        if: bhas_length_8 "suffix" then (
          let:3 ("prefix", "middle", "suffix") := bsplit8 "suffix" in
          "r" <- ("prefix", "left", "middle", "right", "suffix");;
          assemble_ (bpush "x" "prefix") "left" "middle" "right" "suffix"
        ) else (
          (* NOTE(Juliette): pas dans le OCaml, ne fait rien d'utile *)
          "r" <- ("prefix", "left", "middle", "right", "suffix");;
          assemble_ bempty empty bempty empty (bpush "x" "suffix")
        )
      ) else (
        if: bhas_length_6 "prefix" then (
          let:2 ("prefix", "prefix'") := bsplit642 "prefix" in
          let: "left" := "push" (abuffer "prefix'") "left" in
          "r" <- ( "prefix", "left", "middle", "right", "suffix" );;
          assemble_ (bpush "x" "prefix") "left" "middle" "right" "suffix"
        ) else
          (* NOTE(Juliette): pas dans le OCaml, ne fait rien d'utile *)
          "r" <- ("prefix", "left", "middle", "right", "suffix");;
          assemble_ (bpush "x" "prefix") "left" "middle" "right" "suffix"
      )
    end.

  Definition inject : val :=
    rec: "inject" "d" "x" :=
    tick #();;
    match: "d" with
      NONE => asingleton "x"
    | SOME "r" =>
      let:5 ("prefix", "left", "middle", "right", "suffix") := !"r" in
      if: bis_empty "middle" then (
        if: bhas_length_8 "suffix" then (
          let:3 ("prefix", "middle", "suffix") := bsplit8 "suffix" in
          "r" <- ("prefix", "left", "middle", "right", "suffix");;
          assemble_ "prefix" "left" "middle" "right" (binject "suffix" "x")
        ) else (
          "r" <- ("prefix", "left", "middle", "right", "suffix");;
          assemble_ bempty empty bempty empty (binject "suffix" "x")
        )
      ) else (
        if: bhas_length_6 "suffix" then (
          let:2 ("suffix'", "suffix") := bsplit624 "suffix" in
          let: "right" := "inject" "right" (abuffer "suffix'") in
          "r" <- ("prefix", "left", "middle", "right", "suffix");;
          assemble_ "prefix" "left" "middle" "right" (binject "suffix" "x")
        ) else (
          "r" <- ("prefix", "left", "middle", "right", "suffix");;
          assemble_ "prefix" "left" "middle" "right" (binject "suffix" "x")
        )
      )
    end.

  Definition dconcat : val :=
    λ: "d1" "d2",
    tick #();;
    match: "d1" with NONE => "d2"
    | SOME "r1" =>
    match: "d2" with NONE => "d1"
    | SOME "r2" =>
    let:5 ("pr1", "ld1", "md1", "rd1", "sf1") := !"r1" in
    let:5 ("pr2", "ld2", "md2", "rd2", "sf2") := !"r2" in
    if: bis_empty "md1" then bfold_right push "sf1" "d2" else
    if: bis_empty "md2" then bfold_left inject "d1" "sf2" else
      let:2 ("sf1", "x1") := beject "sf1" in
      let:2 ("x2", "pr2") := bpop "pr2" in
      let: "middle" := bdoubleton "x1" "x2" in
      let:2 ("sf1a", "sf1b") := bsplit23l "sf1" in
      let: "ld1" := inject "ld1" (atriple_ "md1" "rd1" "sf1a") in
      let: "ld1" :=
        if: bis_empty "sf1b" then "ld1"
        else inject "ld1" (abuffer "sf1b")
      in
      let:2 ("pr2a", "pr2b") := bsplit23r "pr2" in
      let: "rd2" := push (atriple_ "pr2b" "ld2" "md2") "rd2" in
      let: "rd2" :=
        if: bis_empty "pr2a" then "rd2"
        else push (abuffer "pr2a") "rd2"
      in
      assemble_ "pr1" "ld1" "middle" "rd2" "sf2"
    end end.

  Definition naive_pop_safe : val :=
    λ: "f",
      let:5 ("p", "_", "m", "_", "_") := "f" in
      (bis_empty "m") || (#3%nat < blength "p").

  Definition naive_pop : val :=
    λ: "f",
    let:5 ("pr", "ld", "md", "rd", "sf") := "f" in
    if: bis_empty "md" then (
      let:2 ("x", "sf'") := bpop "sf" in
      ("x", assemble "pr" "ld" "md" "rd" "sf'")
    ) else (
      let:2 ("x", "pr'") := bpop "pr" in
      ("x", assemble_ "pr'" "ld" "md" "rd" "sf")
    ).

  Definition inspect_first : val :=
    λ: "f",
    let:5 ("pr", "_", "md", "_", "sf") := "f" in
    if: bis_empty "md" then bfirst "sf" else bfirst "pr".

  Definition prepare_pop_case_1 : val :=
    λ: "f", λ: "t", λ: "left",
    let:5 ("prefix", "_", "middle", "right", "suffix") := "f" in
    let:3 ("first", "child", "last") := "t" in

    if: bhas_length_3 "first" then (
      let:2 ("prefix", "first") := bmove_left_1_33 "prefix" "first" in
      let: "t" := atriple_ "first" "child" "last" in
      let: "left" := push "t" "left" in
      ("prefix", "left", "middle", "right", "suffix")
    ) else (
      let: "prefix" := bconcat32 "prefix" "first" in
      if: ("child" = NONEV) && bis_empty "last" then (
        ("prefix", "left", "middle", "right", "suffix")
      ) else (
        let: "t" := abuffer "last" in
        let: "left" := push "t" "left" in
        let: "left" := dconcat "child" "left" in
        ("prefix", "left", "middle", "right", "suffix")
      )
    ).

  Definition prepare_pop_case_2 : val :=
    λ: "f", λ: "t", λ: "right",
    let:5 ("prefix", "left", "middle", "_", "suffix") := "f" in
    let:3 ("first", "child", "last") := "t" in
    if: bhas_length_3 "first" then (
      let:3 ("prefix", "middle", "first") := bdouble_move_left "prefix" "middle" "first" in
      let: "t" := atriple_ "first" "child" "last" in
      let: "right" := push "t" "right" in
      ("prefix", "left", "middle", "right", "suffix")
    ) else (
      let: "prefix" := bconcat32 "prefix" "middle" in
      let: "middle" := "first" in
      if: ("child" = NONEV) && bis_empty "last" then (
        ("prefix", "left", "middle", "right", "suffix")
      ) else (
        let: "t" := abuffer "last" in
        let: "right" := push "t" "right" in
        let: "right" := dconcat "child" "right" in
        ("prefix", "left", "middle", "right", "suffix")
      )
    ).

  (* Tarjan's
  Definition pop_triple target := (
    let: "f" := !target in
    let: "t" := inspect_first "f" in
    let:3 ("first", "child", "last") := "t" in
    if: (~ "child" = NONEV) || bhas_length_3 "first"
      then naive_pop "f"
      else "pop_nonempty" target
  )%E.
  *)

  Definition pop_triple target := (
    let: "f" := !target in
    let: "t" := inspect_first "f" in
    let:3 ("first", "child", "last") := "t" in
    (* if: (~ "child" = NONEV) || bhas_length_3 "first" *)
    if: bhas_length_3 "first" || ~bis_empty "last"
      then naive_pop "f"
      else "pop_nonempty" target
  )%E.


  Definition prepare_pop target := (
   let:5 ("prefix", "left", "middle", "right", "suffix") := target in
      match: "left" with
        SOME "left" =>
          let:2 ("t", "left") := pop_triple "left" in
          prepare_pop_case_1 target "t" "left"
        | NONE =>
      match: "right" with
        SOME "right" =>
          let:2 ("t", "right") := pop_triple "right" in
          prepare_pop_case_2 target "t" "right"
        | NONE =>
          if: bhas_length_3 "suffix" then (
            let: "suffix" := bconcat323 "prefix" "middle" "suffix" in
            let: "middle" := bempty in
            let: "prefix" := bempty in
            ("prefix", "left", "middle", "right", "suffix")
          ) else (
            let:3 ("prefix", "middle", "suffix") := bdouble_move_left "prefix" "middle" "suffix" in
            ("prefix", "left", "middle", "right", "suffix")
          )
      end end
  )%E.

  Definition pop_nonempty : val :=
    rec: "pop_nonempty" "r" :=
    tick #();;
    let: "f" := !"r" in
    let: "f" := if: naive_pop_safe "f" then "f" else prepare_pop "f" in
    "r" <- "f";;
    naive_pop "f".

  (*
  Definition pop_nonempty : val :=
    rec: "pop_nonempty" "r" :=
    tick #();;
    let: "f" := !"r" in
    if: naive_pop_safe "f" then naive_pop "f" else
    let: "f" := prepare_pop "f" in
    "r" <- "f";;
    naive_pop "f".
  *)

  Definition pop : val :=
    λ: "d",
      match: "d" with
        NONE => "explosion"
      | SOME "r" => pop_nonempty "r" end.

  Definition antinormalize : val :=
    λ: "t",
      let:3 ("first", "child", "last") := "t" in
      if: bis_empty "last" then (
        let: "first" := bempty in
        let: "last" := "first" in
        ("first", "child", "last")
      ) else "t".

  Definition naive_eject_safe : val :=
    λ: "f",
      let:5 ("_", "_", "m", "_", "s") := "f" in
      (bis_empty "m") || (#3%nat < blength "s").

  Definition naive_eject : val :=
    λ: "f",
      let:5 ("p", "l", "m", "r", "s") := "f" in
      let:2 ("s", "x") := beject "s" in
      (assemble "p" "l" "m" "r" "s", "x").

  Definition inspect_last : val :=
    λ: "f",
      let:5 ("_", "_", "_", "_", "s") := "f" in
      blast "s".

  Definition eject_nonempty : val :=
    rec: "eject_nonempty" "r" :=
    let: "f" := !"r" in
    if: naive_eject_safe "f" then naive_eject "f" else
    let: "f" := (* prepare_eject "f" *)
      let:5 ("prefix", "left", "middle", "right", "suffix") := "f" in
      match: "right" with
        SOME "right" =>
          let:2 ("right", "t") := (* eject_triple "right" *)
            let: "f" := !"right" in
            let: "t" := inspect_last "f" in
            let:2 ("d", "t") :=
              let:3 ("first", "child", "last") := "t" in
              if: ~("child" = NONEV) || bhas_length_3 "last"
              || (bis_empty "last" && bhas_length_3 "first")
                then naive_eject "f"
                else "eject_nonempty" "r"
              in ("d", antinormalize "t")
          in
          let:3 ("first", "child", "last") := "t" in
          if: bhas_length_3 "last" then (
            let:2 ("last", "suffix") := bmove_right_1_33 "last" "suffix" in
            let: "t" := atriple "first" "child" "right" in
            let: "right" := inject "right" "t" in
            ("prefix", "left", "middle", "right", "suffix")
          ) else (
            let: "suffix" := bconcat23 "last" "suffix" in
            if: ("child" = NONEV) && bis_empty "first" then (
              ("prefix", "left", "middle", "right", "suffix")
            ) else (
              let: "t" := abuffer "first" in
              let: "right" := inject "right" "t" in
              let: "right" := dconcat "right" "child" in
              ("prefix", "left", "middle", "right", "suffix")
            )
          )
      | NONE =>
      match: "left" with
        SOME "left" =>
          let:2 ("left", "t") := (* eject_triple "left" *)
            let: "f" := !"right" in
            let: "t" := inspect_last "f" in
            let:2 ("d", "t") :=
              let:3 ("first", "child", "last") := "t" in
              if: ~("child" = NONEV) || bhas_length_3 "last"
              || (bis_empty "last" && bhas_length_3 "first")
                then naive_eject "f"
                else "eject_nonempty" "r"
              in ("d", antinormalize "t")
          in
          let:3 ("first", "child", "last") := "t" in
          if: bhas_length_3 "last" then (
            let:3 ("last", "middle", "suffix") := bdouble_move_right "last" "middle" "suffix" in
            let: "t" := atriple "first" "child" "last" in
            let: "left" := inject "left" "t" in
            ("prefix", "left", "middle", "right", "suffix")
          ) else (
            let: "suffix" := bconcat23 "middle" "suffix" in
            let: "middle" := "last" in
            if: ("child" = NONEV) && bis_empty "first" then (
              ("prefix", "left", "middle", "right", "suffix")
            ) else (
              let: "t" := abuffer "first" in
              let: "left" := inject "left" "t" in
              let: "left" := dconcat "left" "child" in
              ("prefix", "left", "middle", "right", "suffix")
            )
          )
      | NONE =>
        if: bhas_length_3 "prefix" then (
          let: "suffix" := bconcat323 "prefix" "middle" "suffix" in
          let: "middle" := bempty in
          let: "prefix" := bempty in
          ("prefix", "left", "middle", "right", "suffix")
        ) else (
          let:3 ("prefix", "middle", "suffix") := bdouble_move_right "prefix" "middle" "suffix" in
          ("prefix", "left", "middle", "right", "suffix")
        )
      end end
    in
    "r" <- "f"
    naive_eject "f"
    .

  Definition eject : val :=
    λ: "d",
      match: "d" with
        NONE => "dragon à trois têtes"
      | SOME "r" => eject_nonempty "r"
      end.

End algorithms.


Section lemmas.

  Context `{heapGS Σ}.

  Definition list_factor {α} : list α -> list α -> Prop :=
    λ ℓ ℓ', ∃ p s, ℓ' = p ++ ℓ ++ s.

  Notation "ℓ ⊑ ℓ'" := (list_factor ℓ ℓ').

  (* NOTE(Juliette): variant for sep_L2 *)
  Lemma list_factor_sep : forall α (ℓ : list α) ℓ' (ϕ : α -> iProp Σ),
    ℓ ⊑ ℓ' ->
    ([∗list] x ∈ ℓ', ϕ x) ⊢ [∗list] x ∈ ℓ, ϕ x.
  Proof.
  Abort.

End lemmas.