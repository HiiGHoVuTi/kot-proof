
From iris.heap_lang Require Import lang proofmode notation.
Require Import List.

Notation fflip := (λ f, (λ: "x", λ: "y", f "y" "x")%V).

Section fold.
  Context `{heapGS Σ}.

  (* This predicate means that it is safe to fold_left the function f, with initial state s, over the sequence of elements xs, and that the final state will satisfy the postcondition π. *)
  Fixpoint safe_fold (call : val -> val) (f : val) (s0 : val) (xs : list val) π : iProp Σ :=
    match xs with
    | [] => π s0
    | x::xs => WP call f s0 x {{ s1, safe_fold call f s1 xs π }}
    end.

  Definition has_fold_left_spec (fold : val) (coll : list val -> val -> iProp Σ) :=
    forall f s0 xs π c,
    {{{ safe_fold id f s0 xs π ∗ coll xs c }}}
        fold f s0 c
    {{{ s', RET s'; π s' }}}.


  Definition has_fold_right_spec (fold : val) (coll : list val -> val -> iProp Σ) :=
    forall f xs s0 π c,
    {{{ safe_fold fflip f s0 (rev xs) π ∗ coll xs c }}}
        fold f c s0
    {{{ s', RET s'; π s' }}}.

End fold.
