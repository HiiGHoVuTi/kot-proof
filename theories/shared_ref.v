
From iris.base_logic.lib Require Export own na_invariants invariants iprop.
From iris.heap_lang Require Import lang proofmode notation.
From iris.algebra Require Import agree.

Section shared_ref.

Context `{!heapGS Σ}.

Let N := nroot .@ "sref".

Definition sref (ℓ : loc) (π : val -> iProp Σ) : iProp Σ :=
  inv N (∃ v, π v ∗ ℓ ↦ v).

Notation "l ⤇ π" := (sref l π) (at level 60).

Theorem pers_sref : forall ℓ π, Persistent (sref ℓ π).
Proof. apply _. Qed.

Variable π : val -> iProp Σ.

Theorem sref_alloc (v : val) :
  {{{ π v }}} ref v {{{ ℓ, RET #ℓ; ℓ ⤇ π }}}.
Proof.
  iIntros (ψ) "Hv Hψ".
  wp_alloc ℓ as "Hℓ".
  iApply "Hψ".
  iFrame "#".
  iApply inv_alloc. iNext.
  iExists v. by iFrame.
Qed.

Theorem sref_load `{forall x, Persistent (π x)} (ℓ : loc) :
  {{{ ℓ ⤇ π }}} ! #ℓ {{{ v', RET v'; π v' }}}.
Proof.
  iIntros (ψ) "#ι Hψ".
  iInv "ι" as "(%v' & #Hv' & Hℓ)".
  wp_load.
  iSplitL "Hℓ".
  - by iFrame "#".
  - by iApply "Hψ".
Qed.

Theorem sref_store (ℓ : loc) (x : val) :
  {{{ ℓ ⤇ π ∗ π x }}} #ℓ <- x {{{ RET #(); True }}}.
Proof.
  iIntros (ψ) "(#ι & Hx) Hψ".
  iInv "ι" as "(%v' & Hv' & Hℓ)".
  wp_store.
  iSplitR "Hψ"; [| by iApply "Hψ"].
  iModIntro. iNext.
  iExists x. by iFrame.
Qed.

End shared_ref.

Section alloc.
  Context `{!heapGS Σ} `{!na_invG Σ}.
  Theorem na_pool_alloc :
    ⊢ |==> ∃ p : gname, na_own p ⊤.
  Proof. by apply na_alloc. Qed.
End alloc.

Section property_ref.

Context `{!heapGS Σ} `{!na_invG Σ}.

Parameter ρ : gname.

Definition πref (ℓ : loc) (N : namespace) (π : val -> iProp Σ) : iProp Σ :=
  na_inv ρ N (∃ v, π v ∗ ℓ ↦ v).

Notation "l ⤇{ N } π" := (πref l N π) (at level 60).

Global Instance pers_πref ℓ N π : Persistent (πref ℓ N π).
Proof. apply _. Qed.

Variable π : val -> iProp Σ.

Theorem πref_alloc (v : val) : forall N,
  {{{ π v }}} ref v {{{ ℓ, RET #ℓ; ℓ ⤇{N} π }}}.
Proof.
  iIntros (N ψ) "Hv Hψ".
  wp_alloc ℓ as "Hℓ".
  iApply "Hψ".
  iFrame "#".
  iApply (na_inv_alloc ρ _ N (∃ v, π v ∗ ℓ ↦ v) with "[Hv Hℓ]").
    { iNext. iExists v. iFrame. }
Qed.

Theorem πref_load `{forall x, Persistent (π x)} (ℓ : loc) : forall N,
  {{{ ℓ ⤇{N} π ∗ na_own ρ (↑N) }}} ! #ℓ {{{ v', RET v'; π v' ∗ na_own ρ (↑N) }}}.
Proof.
  iIntros (N ψ) "[ι O] Hψ".
  iInv "ι" as "[(%v' & #Hv' & Hℓ) O]".
  wp_load.
  iModIntro.
  iSplitL "Hℓ O".
  - iSplitL "Hℓ"; by iFrame "#".
  - iIntros "H". iApply "Hψ". by iFrame "#".
Qed.

Theorem πref_store (ℓ : loc) (x : val) : forall N,
  {{{ ℓ ⤇{N} π ∗ π x ∗ na_own ρ (↑N) }}} #ℓ <- x {{{ RET #(); na_own ρ (↑N) }}}.
Proof.
  iIntros (N ψ) "(#ι & Hx & O) Hψ".
  iInv "ι" as "[(%v' & Hv' & Hℓ) O]".
  wp_store.
  iSplitR "Hψ"; iModIntro.
  - iSplitR "O"; [| done].
    iExists x. iNext. iFrame.
  - iIntros "H". by iApply "Hψ".
Qed.

Definition use : val :=
  λ: "r" "f",
    let: "v" := !"r" in
    let: "v'" := "f" "v" in
    "r" <- "v'".

Definition uses : val :=
  λ: "r" "f",
    let: "v" := !"r" in
    let: "v'r" := "f" "v" in
    "r" <- Fst "v'r";;
    Snd "v'r".

Definition modify : val :=
  λ: "r" "f",
    let: "v" := !"r" in
    let: "v'" := "f" "v" in
    "r" <- "v'";;
    "v'".

Theorem πref_read P `{forall v, Persistent (P v)} (ℓ : loc) : forall N,
  {{{ ℓ ⤇{N} π ∗ na_own ρ (↑N) ∗ (∀ v, π v -∗ (P v ∗ π v)) }}} !#ℓ {{{ v', RET v'; P v' ∗ na_own ρ (↑N) }}}.
Proof.
  iIntros (N ψ) "(Hℓ & O & HP) Hψ".
  iInv "Hℓ" as "[(%v & πv & ℓv) O]".
  wp_load.
  iModIntro.
  iDestruct ("HP" with "πv") as "[Pv πv]".
  iFrame.
  iIntros "O".
  iApply "Hψ".
  iFrame.
Qed.

Theorem πref_use (ℓ : loc) :
  ∀ (f : val) (R : iProp Σ) (N N' : namespace),
    ↑N ⊆@{coPset} ↑N' →
    na_own ρ (↑N') -∗
    ℓ ⤇{N} π -∗
    (∀ v, π v -∗ na_own ρ (↑N' ∖ ↑N) -∗
         WP f v {{ v', π v' ∗ R ∗ na_own ρ (↑N' ∖ ↑N) }})
    -∗ WP use #ℓ f
    {{ _, ℓ ⤇{N} π ∗ R ∗ na_own ρ (↑N') }}.
Proof.
  iIntros (f R N N' Hincl) "Hown #ι Hf".
  rewrite /use.
  wp_pures.
  iInv "ι" as "[(%v & Hv & Hℓ) O]".
  wp_load. wp_pures.
  wp_bind (f v).
  iApply (wp_wand with "[Hf Hv O]").
    { iApply ("Hf" with "Hv"). done. }
  iIntros (v') "(Hv' & R & O)".
  wp_pures. wp_store.
  iModIntro. iFrame.
  iIntros "H".
  by iFrame "#".
Qed.

Theorem πref_uses (ℓ : loc) :
  ∀ (f : val) (R : val → iProp Σ) (N N' : namespace),
    ↑N ⊆@{coPset} ↑N' →
    na_own ρ (↑N') -∗
    ℓ ⤇{N} π -∗
    (∀ v, π v -∗ na_own ρ (↑N' ∖ ↑N) -∗
         WP f v {{ v'r, ∃ v' r, ⌜ v'r = (v', r)%V ⌝ ∗ π v' ∗ R r ∗ na_own ρ (↑N' ∖ ↑N) }})
    -∗ WP uses #ℓ f
    {{ r, ℓ ⤇{N} π ∗ R r ∗ na_own ρ (↑N') }}.
Proof.
  iIntros (f R N N' Hincl) "Hown #ι Hf".
  rewrite /uses.
  wp_pures.
  iInv "ι" as "[(%v & Hv & Hℓ) O]".
  wp_load. wp_pures.
  wp_bind (f v).
  iApply (wp_wand with "[Hf Hv O]").
    { iApply ("Hf" with "Hv"). done. }
  iIntros (v'r) "(%v' & %r & -> & πv' & Rr & O)".
  wp_pures. wp_store. wp_pures.
  iModIntro. iFrame.
  iIntros "O".
  by iFrame "#".
Qed.

Theorem πref_load_open (ℓ : loc) :
  ∀ (N N' : namespace), ↑N ⊆@{coPset} ↑N' →
  {{{ ℓ ⤇{N} π ∗ na_own ρ (↑N') }}} 
    !#ℓ 
  {{{ v, RET v; na_own ρ (↑N' ∖ ↑N) ∗ π v ∗
    ∀ v', ▷ π v' -∗ na_own ρ (↑N' ∖ ↑N) -∗ WP (#ℓ <- v') {{ _, na_own ρ (↑N') }}
  }}}.
Proof.
  iIntros (N N' Hincl ψ) "[#ι O] Hψ".
  iInv "ι" as "[(%v & Hv & Hℓ) O]" "Hclose".
  wp_load.
  iModIntro.
  iApply "Hψ".
  iFrame.
  iIntros (v') "πv' O".
  wp_store.
  iApply "Hclose".
  iFrame.
Qed.

End property_ref.

Notation "l ⤇ π" := (sref l π) (at level 60).
Notation "l ⤇{ N } π" := (πref l N π) (at level 60).

Section instances.
  Context `{!heapGS Σ} `{!na_invG Σ}.
  (* TODO  
  Global Instance isSrefContractive (ℓ : loc) : Contractive (λ π, ℓ ⤇ π).
  *)
  Global Instance na_inv_contractive ρ N : Contractive (na_inv ρ N).
  Proof. solve_contractive. Qed.
End instances.
