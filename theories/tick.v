From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation.
Require Import Unicode.Utf8.

Section axioms.
  Context `{!heapGS Σ}.

  (* This parameter is set to 1 for the time complexity proof and 0 for the functional correction proof *)
  Parameter TICK_COST : nat.
  Axiom tick : val.
  Axiom time_credits : nat -> iProp Σ.
  Axiom time_combine : forall n m, time_credits (n + m) ⊣⊢ time_credits n ∗ time_credits m.
  Axiom time_zero : time_credits 0 ⊣⊢ emp.

  Axiom tick_spec : {{{ time_credits TICK_COST }}} tick #() {{{ RET #(); True }}}.

  Notation "⏱ n" := (time_credits n) (at level 60).
  Lemma split_time : forall k n, k <= n -> ⏱ n ⊢ ⏱ k ∗ ⏱ (n - k).
  Proof.
    iIntros (k n H) "τ".
    rewrite -time_combine.
    rewrite Nat.add_comm Nat.sub_add //.
  Qed.

End axioms.

Notation "⏱ n" := (time_credits n) (at level 60).
Hint Resolve time_combine : time.
Hint Resolve time_zero : time.