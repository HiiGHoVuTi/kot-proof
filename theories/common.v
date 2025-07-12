
From iris.heap_lang Require Import lang proofmode notation.
From Deque Require Import tick.

(* Section notations *)
Notation "⋅ x" := [x] (at level 60).
Definition nonempty {A : Type} (x : list A) := ~(x = []).
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

  (* Five-tuple configuration for calling naive_pop *)
  Inductive pop_configuration : nat -> nat -> nat -> nat -> nat -> Prop :=
    | pop_suffix_only : forall s, s ∈ [1..8] -> pop_configuration 0 0 0 0 s
    | pop_has_middle : forall p ld rd s, p ∈ [4..6] -> s ∈ [3..6] -> pop_configuration p ld 2 rd s.

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

Section algorithms.

  Context `{!heapGS Σ}.

  Let empty := NONEV.

  Example singleton_deque : val :=
    λ: "x", SOME (ref (empty_buffer, NONEV, empty_buffer, NONEV, bpush "x" empty_buffer)%E).

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

  Definition push : val :=
    rec: "push" "x" "d" :=
    tick #();;
    match: "d" with
      NONE => singleton_deque "x"
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

  Definition dconcat : val :=
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

  Definition naive_pop : val :=
    λ: "d",
    let:5 ("pr", "ld", "md", "rd", "sf") := "d" in
    if: bsize "md" = #0%nat then (
      let:2 ("x", "sf'") := bpop "sf" in
      ("x", SOME (ref ("pr", "ld", "md", "rd", "sf'")))
    ) else (
      let:2 ("x", "pr'") := bpop "pr" in
      ("x", SOME (ref ("pr'", "ld", "md", "rd", "sf")))
    ).

  Definition inspect_first : val :=
    λ: "d", Fst (naive_pop "d").

  (* TODO: lookup actual not *)
  Let not : val := λ: "b", if: "b" then (#0 = #1) else (#0 = #0).

  Definition first_nonempty : val :=
    λ: "tr",
      let:3 ("first", "middle", "last") := "tr" in
      if: not (bsize "first" = #0%nat)%E
        then SOME "first"
      else if: not (bsize "last" = #0%nat)
        then SOME "last"
      else NONE.

  Definition pop : val :=
    rec: "pop" "d" :=
    tick #();;
    match: "d" with NONE => "unreachable"
    | SOME "ptr" =>
    let: "d" := !"ptr" in
    let:5 ("prefix", "left", "middle", "right", "suffix") := "d" in
    let: "d'" :=
    if: (bsize "middle" = #0%nat) || not (bsize "prefix" = #3%nat) then "d" else (
      (* assert: bsize "prefix" = #3%nat *)
      match: "left" with
        SOME "left" =>
        let: "left" := !"left" in
        let: "t" := inspect_first "left" in
        let:2 ("t", "l") :=
          let:3 ("first", "child", "last") := "t" in
          let: "fn_result" := first_nonempty "t" in
          match: "fn_result" with
            SOME "b" =>
            if: bsize "b" = #3%nat || ("child" = NONE) then
              naive_pop "left"
            else
              "pop" (SOME (ref "left"))
          | NONE => "UNREACHABLE"
          end in
        let:3 ("x", "d'", "y") := "t" in
        let: "x_len" := bsize "x" in
        let: "y_len" := bsize "y" in
        if: "x_len" = #3%nat then (
          let:2 ("a", "x'") := bpop "x" in
          let: "p'" := binject "prefix" "a" in
          let: "triple" := ("x'", "d'", "y") in
          let: "ld'" := push "triple" "l" in
          ("p'", "ld'", "middle", "right", "suffix")
        ) else if: "x_len" = #2%nat then (
          let: "p'" := inject_whole_buffer inject "prefix" "x" in
          if: ("d'" = NONE) && (bsize "y" = #0%nat) then
            ("p'", "l", "middle", "right", "suffix")
          else
            let: "triple" := ("y", empty, empty_buffer) in
            let: "l'" := dconcat "d'" (push "triple" "l") in
            ("p'", "l'", "middle", "right", "suffix")
        ) else if: ("x_len" = #0%nat) && ("y_len" = #3%nat) then (
          (* x is empty therefore d' is empty *)
          let:2 ("a", "y'") := bpop "y" in
          let: "p'" := binject "prefix" "a" in
          let: "triple" := ("x", "d'", "y'") in
          let: "ld'" := push "triple" "l" in
          ("p'", "ld'", "middle", "right", "suffix")
        ) else if: ("x_len" = #0%nat) && ("y_len" = #2%nat) then (
          let: "p'" := inject_whole_buffer inject "prefix" "y" in
          ("p'", "l", "middle", "right", "suffix")
        ) else
          "UNREACHABLE"
      | NONE =>
        match: "right" with
          SOME "right" =>
          let: "right" := !"right" in
          let: "t" := inspect_first "right" in
          let:2 ("t", "r") :=
            let: "fn_result" := first_nonempty "t" in
            match: "fn_result" with
              SOME "b" =>
              if: (bsize "b" = #3%nat) || not ("child" = NONE) then
                naive_pop "right"
              else
                "pop" (SOME (ref "right"))
            | NONE => "UNREACHABLE"
            end in
          let:3 ("x", "d'", "y") := "t" in
          let: "x_len" := bsize "x" in
          let: "y_len" := bsize "y" in
          if: "x_len" = #3%nat then (
            let:2 ("a", "m") := bpop "middle" in
            let: "p" := binject "prefix" "a" in
            let:2 ("b", "x'") := bpop "x" in
            let: "m'" := binject "m" "b" in
            let: "triple" := ("x'", "d'", "y") in
            let: "r'" := push "triple" "r" in
            ("p", "left", "m'", "r'", "suffix")
          ) else if: "x_len" = #2%nat then (
            let: "p" := inject_whole_buffer binject "prefix" "middle" in
            let: "r'" :=
              if: ("d'" = NONE) && (bsize "y" = #0%nat) then
                "r"
              else
                let: "triple" := ("y", empty, empty_buffer) in
                dconcat "d'" (push "triple" "r")
            in
            ("p", "left", "x", "r'", "suffix")
          ) else if: ("x_len" = #0%nat) && ("y_len" = #3%nat) then (
            (* x is empty therefore d' is empty too *)
            let:2 ("a", "m") := bpop "middle" in
            let: "p" := binject "prefix" "a" in
            let:2 ("b", "y'") := bpop "y" in
            let: "m'" := binject "m" "b" in
            let: "triple" := ("x", "d'", "y'") in
            let: "r'" := push "triple" "r" in
            ("p", "left", "m'", "r'", "suffix")
          ) else if: ("x_len") = #0%nat && ("y_len" = #2%nat) then (
            let: "p" := inject_whole_buffer binject "prefix" "middle" in
            ("p", "left", "y", "right", "suffix")
          ) else
            "UNREACHABLE"
        | NONE =>
          (* is_empty left, is_empty right *)
          if: bsize "suffix" = #3%nat then
            let: "suffix'" := inject_whole_buffer binject "prefix" (inject_whole_buffer binject "middle" "suffix") in
            (empty_buffer, "left", empty_buffer, "right", "suffix'")
          else
            let:2 ("a", "m") := bpop "middle" in
            let: "prefix'" := binject "prefix" "a" in
            let:2 ("a", "suffix'") := bpop "suffix" in
            let: "middle'" := binject "m" "a" in
            ("prefix'", "left", "middle'", "right", "suffix'")
        end
      end
    )
    in
    (* TODO: fix OCaml code *)
    "ptr" <- "d'";;
    naive_pop "d'"
    end.

  Definition eject : val. Admitted.

End algorithms.
