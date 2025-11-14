From iris.base_logic.lib Require Import invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr.hazptr Require Import spec_hazptr.
From iris.prelude Require Import options.

Definition BigAtomicT Σ : Type :=
  ∀ (γ : gname) (vs : list val), iProp Σ.

Definition IsBigAtomicT Σ (N : namespace) : Type :=
  ∀ (γ : gname) (l : val) (n : nat), iProp Σ.

Section spec.
Context `{!heapGS Σ}.
Context (big_atomicN : namespace) (hazptrN : namespace) (DISJN : big_atomicN ## hazptrN).
Variables
  (big_atomic_new : val)
  (big_atomic_read : val)
  (big_atomic_cas : val).
Variables
  (hazptr : hazard_pointer_spec Σ hazptrN)
  (BigAtomic : BigAtomicT Σ)
  (IsBigAtomic : IsBigAtomicT Σ big_atomicN).

Definition big_atomic_new_spec' : Prop :=
  ∀ γd d n l dq vs,
    n > 0 → length vs = n →
      {{{ hazptr.(IsHazardDomain) γd d ∗ l ↦∗{dq} vs }}}
        big_atomic_new #d #l #n
      {{{ γ ba, RET ba; IsBigAtomic γ ba n ∗ BigAtomic γ vs ∗ l ↦∗{dq} vs }}}.

Definition big_atomic_read_spec' : Prop :=
  ⊢ ∀ γ ba n,
    IsBigAtomic γ ba n -∗
      <<{ ∀∀ vs, BigAtomic γ vs }>>
        big_atomic_read ba #n @ ⊤,(↑big_atomicN ∪ ↑(ptrsN hazptrN)),↑(mgmtN hazptrN)
      <<{ ∃∃ l, BigAtomic γ vs | RET #l; l ↦∗ vs }>>.

Definition big_atomic_cas_spec' : Prop :=
  ∀ γ ba n (l_expected l_desired : loc) (dq dq' : dfrac) (expected desired : list val),
    length expected = n → length desired = n →
      Forall val_is_unboxed expected → Forall val_is_unboxed desired →
        IsBigAtomic γ ba n -∗ l_expected ↦∗{dq} expected -∗ l_desired ↦∗{dq'} desired -∗
          <<{ ∀∀ actual, BigAtomic γ actual }>>
            big_atomic_cas ba #n @ ⊤,(↑big_atomicN ∪ ↑(ptrsN hazptrN)),↑(mgmtN hazptrN)
          <<{ if bool_decide (actual = expected) then 
                BigAtomic γ desired 
              else 
                BigAtomic γ actual 
            | RET #(bool_decide (actual = expected)); l_expected ↦∗{dq} expected ∗ l_desired ↦∗{dq'} desired  }>>.

End spec.

Record big_atomic_code : Type := BigAtomicCode {
  big_atomic_new : val;
  big_atomic_read : val;
  big_atomic_cas : val;
}.

Record big_atomic_spec {Σ} `{!heapGS Σ} {big_atomicN hazptrN : namespace}
    {DISJN : big_atomicN ## hazptrN}
    {hazptr : hazard_pointer_spec Σ hazptrN}
  : Type := BigAtomicSpec {
  big_atomic_spec_code :> big_atomic_code;

  BigAtomic: BigAtomicT Σ;
  IsBigAtomic : IsBigAtomicT Σ big_atomicN;

  BigAtomic_Timeless : ∀ γ vs, Timeless (BigAtomic γ vs);
  IsBigAtomic_Persistent : ∀ γ l n, Persistent (IsBigAtomic γ l n);

  big_atomic_new_spec : big_atomic_new_spec' big_atomicN hazptrN big_atomic_spec_code.(big_atomic_new) hazptr BigAtomic IsBigAtomic;
  big_atomic_read_spec : big_atomic_read_spec' big_atomicN hazptrN big_atomic_spec_code.(big_atomic_read) BigAtomic IsBigAtomic;
  big_atomic_cas_spec : big_atomic_cas_spec' big_atomicN hazptrN big_atomic_spec_code.(big_atomic_cas) BigAtomic IsBigAtomic;
}.

Global Arguments big_atomic_spec : clear implicits.
Global Arguments big_atomic_spec _ {_} _ _ _ _ : assert.
Global Existing Instances BigAtomic_Timeless IsBigAtomic_Persistent.
