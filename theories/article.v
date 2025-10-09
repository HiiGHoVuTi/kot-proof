From iris.heap_lang Require Import lang proofmode notation.
From iris.bi Require Import derived_laws.

From Coq Require Import List.
Import ListNotations.

From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Deque Require Import common tick shared_ref.

Section functional_correctness.
    From Deque Require Import deque_corr push_corr inject_corr concat_corr pop_corr eject_corr.

    Context `{!heapGS Σ}.

    Theorem PushSpec : forall xs x d,
        {{{ IsDeque xs d }}}
            push x d
        {{{ d', RET d'; IsDeque ([x] ++ xs) d' }}}.
    by exact push_corr.push_spec. Qed.

    Theorem InjectSpec : forall xs x d,
        {{{ IsDeque xs d }}}
            inject d x
        {{{ d', RET d'; IsDeque (xs++[x]) d' }}}.
    by exact inject_corr.inject_spec. Qed.

    Theorem ConcatSpec : forall d1 d2 xs1 xs2,
        {{{ IsDeque xs1 d1 ∗ IsDeque xs2 d2 }}}
            dconcat d1 d2
        {{{ d', RET d'; IsDeque (xs1 ++ xs2) d' }}}.
    by exact concat_corr.dconcat_spec. Qed.

    Theorem PopSpec : forall x xs d,
        {{{ IsDeque ([x] ++ xs) d }}}
            pop d
        {{{ d', RET (x, d')%V; IsDeque xs d' }}}.
    by exact pop_corr.pop_spec. Qed.

    Theorem EjectSpec : forall x xs d,
        {{{ IsDeque (xs ++ [x]) d }}}
            eject d
        {{{ d', RET (d', x)%V; IsDeque xs d' }}}.
    by exact eject_corr.eject_spec. Qed.

End functional_correctness.

Section time_complexity.
    From Deque Require Import deque_cost push_cost inject_cost concat_cost pop_cost eject_cost.

    Context `{!heapGS Σ} `{!na_invG Σ}.
    Context {π : gname}.
    Notation T := (Token π 0).

    Theorem PushSpec' : forall xs x d,
        {{{ IsDeque π xs d ∗ ⏱ 7 ∗ T }}}
            push x d
        {{{ d', RET d'; IsDeque π ([x] ++ xs) d' ∗ T }}}.
    by exact push_cost.push_spec. Qed.

    Theorem InjectSpec' : forall xs x d,
        {{{ IsDeque π xs d ∗ ⏱ 7 ∗ T }}}
            inject d x
        {{{ d', RET d'; IsDeque π (xs++[x]) d' ∗ T }}}.
    by exact inject_cost.inject_spec. Qed.

    Theorem ConcatSpec' : forall d1 d2 xs1 xs2,
        {{{ IsDeque π xs1 d1 ∗ IsDeque π xs2 d2 ∗ ⏱ 57 ∗ T }}}
            dconcat d1 d2
        {{{ d', RET d'; IsDeque π (xs1 ++ xs2) d' ∗ T }}}.
    by exact concat_cost.dconcat_spec. Qed.

    Theorem PopSpec' : forall x xs d,
        {{{ IsDeque π ([x] ++ xs) d ∗ T ∗ ⏱ 171 }}}
            pop d
        {{{ d', RET (x, d')%V; IsDeque π xs d' ∗ T }}}.
    by exact pop_cost.pop_spec. Qed.

    Theorem EjectSpec' : forall x xs d,
        {{{ IsDeque π (xs ++ [x]) d ∗ T ∗ ⏱ 171 }}}
            eject d
        {{{ d', RET (d', x)%V; IsDeque π xs d' ∗ T }}}.
    by exact eject_cost.eject_spec. Qed.

End time_complexity.
