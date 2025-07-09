
From iris.heap_lang Require Import lang proofmode notation.

Section counter.
  Context `{!heapGS Σ}.

  (* Program Counter *)
  Local Parameter ℓ : loc.

  Definition CounterExact (n : Z) : iProp Σ := ℓ ↦ #n.
  Definition Counter (n : Z) : iProp Σ := ∃ k, ⌜ (k <= n)%Z ⌝ ∗ CounterExact k.

  Definition tick_up : val :=
    λ: "", (#ℓ <- !#ℓ + #1)%E.

  Theorem tick_up_spec : forall n : nat,
    {{{ Counter n }}} tick_up #() {{{ RET #(); Counter (n + 1) }}}.
  Proof.
    iIntros (n ψ) "(%k & %Hlt & Hℓ) Hψ".
    rewrite /tick_up. wp_pures.
    wp_load.
    wp_pures.
    wp_store.
    iApply "Hψ".
    iExists (k+1)%Z.
    iFrame.
    iPureIntro.
    lia.
  Qed.

  Theorem Counter_single : forall n m, Counter n ∗ Counter m ⊢ False.
  Proof.
    iIntros (n m) "[(%k1 & _ & H1) (%k2 & _ & H2)]".
    rewrite /CounterExact.
    iCombine "H1 H2" gives "[%H _]".
    contradiction.
  Qed.
End counter.

Opaque CounterExact.
Opaque tick_up.