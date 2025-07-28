
From iris.base_logic.lib Require Export own na_invariants invariants iprop.
From iris.heap_lang Require Import lang proofmode notation.
From iris.algebra Require Import agree.

Section concurrent_stable_ref.

Context `{!heapGS Σ}.

Let N := nroot .@ "sref".

Definition csref (ℓ : loc) (ϕ : val -> iProp Σ) : iProp Σ :=
  inv N (∃ v, ϕ v ∗ ℓ ↦ v).

Notation "l ⤇ ϕ" := (csref l ϕ) (at level 60).

Theorem pers_sref : forall ℓ ϕ, Persistent (csref ℓ ϕ).
Proof. apply _. Qed.

Variable ϕ : val -> iProp Σ.

Theorem csref_alloc (v : val) :
  {{{ ϕ v }}} ref v {{{ ℓ, RET #ℓ; ℓ ⤇ ϕ }}}.
Proof.
  iIntros (ψ) "Hv Hψ".
  wp_alloc ℓ as "Hℓ".
  iApply "Hψ".
  iFrame "#".
  iApply inv_alloc. iNext.
  iExists v. by iFrame.
Qed.

Theorem csref_load `{forall x, Persistent (ϕ x)} (ℓ : loc) :
  {{{ ℓ ⤇ ϕ }}} ! #ℓ {{{ v', RET v'; ϕ v' }}}.
Proof.
  iIntros (ψ) "#ι Hψ".
  iInv "ι" as "(%v' & #Hv' & Hℓ)".
  wp_load.
  iSplitL "Hℓ".
  - by iFrame "#".
  - by iApply "Hψ".
Qed.

Theorem csref_store (ℓ : loc) (x : val) :
  {{{ ℓ ⤇ ϕ ∗ ϕ x }}} #ℓ <- x {{{ RET #(); True }}}.
Proof.
  iIntros (ψ) "(#ι & Hx) Hψ".
  iInv "ι" as "(%v' & Hv' & Hℓ)".
  wp_store.
  iSplitR "Hψ"; [| by iApply "Hψ"].
  iModIntro. iNext.
  iExists x. by iFrame.
Qed.

End concurrent_stable_ref.

Section namespacing.
  (* This section describes the namespaces used by the na_invariants *)
  Context `{!na_invG Σ}.

  (* The main namespace used by cadeques *)
  Definition NKot := nroot .@ "stable ref".

  (* Ξ n is the namespace of cadeques at depth n or deeper *)
  Fixpoint Ξ (n : nat) : namespace :=
    match n with
    | 0 => NKot
    | S n => Ξ n .@ (S n)
    end.

  Lemma next_stage : forall n, ↑Ξ (S n) ⊆@{coPset} ↑Ξ n.
  Proof.
    move=> n.
    by apply nclose_subseteq.
  Qed.

  (* W n is the right to write in a cadeque of depth exactly n *)
  Definition W n := Ξ n .@ 0.

  Lemma incl_trans : forall A B C : coPset, A ⊆ B -> B ⊆ C -> A ⊆ C.
  Proof.
    move=> A B C H K i L.
    by apply H, K in L.
  Qed.

  (* Accessing stage n cadeques allows for writing in them *)
  Lemma access_stage : forall n, ↑W n ⊆@{coPset} ↑Ξ n.
  Proof.
    move=> n.
    apply nclose_subseteq.
  Qed.

  Lemma next_stage_split : forall n, ↑Ξ (S n) ⊆@{coPset} difference (↑Ξ n) (↑W n).
  Proof.
    move=> n.
    apply namespaces.coPset_subseteq_difference_r.
    - rewrite /W /=. by apply ndot_ne_disjoint.
    - apply next_stage.
  Qed.

  (* Access to depth n is writing at level n & access to depth (n+1) & a rest σ *)
  Property own_next_stage : forall ρ n, ∃ σ, na_own ρ (difference (↑Ξ n) (↑W n)) ∗-∗ (na_own ρ (↑Ξ (S n)) ∗ na_own ρ σ).
  Proof.
    move=> ρ n.
    set (H := next_stage_split n).
    apply subseteq_disjoint_union_L in H as [σ [Heq Hdisj]].
    exists σ. iSplitL.
    - iIntros "H".
      rewrite Heq.
      by iApply na_own_union.
    - iIntros "[H K]".
      rewrite Heq.
      iApply na_own_union. done. iFrame.
  Qed.

End namespacing.

Section property_ref.

Context `{!heapGS Σ} `{!na_invG Σ}.

Definition ssref (ℓ : loc) (π : gname) (n : nat) (ϕ : val -> iProp Σ) : iProp Σ :=
  na_inv π (W n) (∃ v, ϕ v ∗ ℓ ↦ v).

Notation "l ⤇{ π , N } ϕ" := (ssref l π N ϕ) (at level 60).

Definition Token π n := na_own π (↑ Ξ n).

Global Instance pers_ssref ℓ π N ϕ : Persistent (ℓ ⤇{π , N} ϕ).
Proof. apply _. Qed.

Theorem new_pool : ⊢ |==> ∃ π, Token π 0.
Proof.
  iStartProof.
  iMod (na_alloc) as "[%π H]".
  iModIntro.
  iExists π.
  by iDestruct (na_own_acc (↑ Ξ 0) ⊤ with "H") as "[H _]".
Qed.

Variable π : gname.
Variable ϕ : val -> iProp Σ.

Theorem ssref_alloc (v : val) : forall N,
  {{{ ϕ v }}} ref v {{{ ℓ, RET #ℓ; ℓ ⤇{π , N} ϕ }}}.
Proof.
  iIntros (N ψ) "Hv Hψ".
  wp_alloc ℓ as "Hℓ".
  iApply "Hψ".
  iFrame "#".
  iApply (na_inv_alloc π _ (W N) (∃ v, ϕ v ∗ ℓ ↦ v) with "[Hv Hℓ]").
    { iNext. iExists v. iFrame. }
Qed.

(* Unused. *)
Theorem ssref_load `{forall x, Persistent (ϕ x)} (ℓ : loc) : forall n,
  {{{ ℓ ⤇{π , n} ϕ ∗ Token π n }}} ! #ℓ {{{ v', RET v'; ϕ v' ∗ Token π n }}}.
Proof.
  iIntros (n ψ) "[ι O] Hψ".
  iDestruct (na_own_acc (↑ W n) with "O") as "[O A]". by apply access_stage.
  iInv "ι" as "[(%v' & #Hv' & Hℓ) O]".
  wp_load.
  iModIntro.
  iSplitL "Hℓ O".
  - iSplitL "Hℓ"; by iFrame "#".
  - iIntros "H". iApply "Hψ".
    iDestruct ("A" with "H") as "H". by iFrame "#".
Qed.

(* Unused. *)
Theorem ssref_store (ℓ : loc) (x : val) : forall n,
  {{{ ℓ ⤇{π , n} ϕ ∗ ϕ x ∗ Token π n }}} #ℓ <- x {{{ RET #(); Token π n }}}.
Proof.
  iIntros (n ψ) "(#ι & Hx & O) Hψ".
  iDestruct (na_own_acc (↑ W n) with "O") as "[O A]". by apply access_stage.
  iInv "ι" as "[(%v' & Hv' & Hℓ) O]".
  wp_store.
  iSplitR "Hψ A"; iModIntro.
  - iSplitR "O"; [| done].
    iExists x. iNext. iFrame.
  - iIntros "H".
    iDestruct ("A" with "H") as "O".
    by iApply "Hψ".
Qed.

Theorem ssref_load_open (ℓ : loc) : forall n,
  {{{ ℓ ⤇{π , n} ϕ ∗ Token π n }}}
    !#ℓ
  {{{ v, RET v; Token π (S n) ∗ ϕ v ∗
    ∀ v', ▷ ϕ v' -∗ Token π (S n) -∗ WP (#ℓ <- v') {{ _, Token π n }}
  }}}.
Proof.
  iIntros (n ψ) "[#ι O] Hψ".
  destruct (own_next_stage π n) as [σ Next].
  rewrite /Token.
  rewrite (union_difference_L (↑ W n) (↑ Ξ n)); [| by apply access_stage].
  iDestruct (na_own_union with "O") as "[OW OX]".
    { symmetry. by apply namespaces.coPset_disjoint_difference_l1. }
  iInv "ι" as "[(%v & Hv & Hℓ) O']" "Hclose".
  wp_load.
  iModIntro.
  iApply "Hψ".
  iFrame.
  iDestruct (Next with "OX") as "[On Oσ]".
  iFrame.
  iIntros (v') "ϕv' O".
  wp_store.
  iDestruct (Next with "[O Oσ]") as "O". by iFrame.
  iApply na_own_union.
    { symmetry.  by apply namespaces.coPset_disjoint_difference_l1. }
  iFrame.
  iApply "Hclose".
  iFrame.
Qed.

Theorem ssref_read P `{forall v, Persistent (P v)} (ℓ : loc) : forall n,
  {{{ ℓ ⤇{π , n} ϕ ∗ Token π n ∗ (∀ v, ϕ v -∗ (P v ∗ ϕ v)) }}} !#ℓ {{{ v', RET v'; P v' ∗ Token π n }}}.
Proof.
  iIntros (n ψ) "(Hℓ & O & HP) Hψ".
  iDestruct (na_own_acc (↑ W n) with "O") as "[O A]". by apply access_stage.
  iInv "Hℓ" as "[(%v & ϕv & ℓv) O]".
  wp_load.
  iModIntro.
  iDestruct ("HP" with "ϕv") as "[Pv ϕv]".
  iFrame.
  iIntros "O".
  iApply "Hψ".
  iFrame.
  by iApply "A".
Qed.

End property_ref.

Notation "l ⤇ ϕ" := (csref l ϕ) (at level 60).
Notation "l ⤇{ π , N } ϕ" := (ssref l π N ϕ) (at level 60).

Section instances.
  Context `{!heapGS Σ} `{!na_invG Σ}.
  Global Instance na_inv_contractive π N : Contractive (na_inv π N).
  Proof. solve_contractive. Qed.
End instances.
