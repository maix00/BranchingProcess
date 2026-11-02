/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.Selection.NSelection.Mechanism.Infinite.Basic
public import Combinatorics.BranchingWalk.Step.Basic

/-!
# Finite selections from a branching step

A finite step selection chooses finitely many surviving child slots from an
otherwise arbitrary branching step. It carries no order or capacity rule;
those belong to particular selection operations.

## Public declarations

A finite step selector chooses only surviving child slots; its capacity and
first-\(N\) specialization satisfy
\[
R(\xi)\subseteq\operatorname{support}(\xi),\qquad
|R(\xi)|\le N,\qquad
\operatorname{IsFirstNBy}\bigl(N,\operatorname{value}_\xi,
  \operatorname{support}(\xi),R(\xi)\bigr).
\]

- `Combinatorics.Branching.Step.FiniteSelection α X` assigns a finite set
  `R ξ` with `↑(R ξ) ⊆ support ξ`; its `select` field returns that set.
- `Combinatorics.Branching.Step.FiniteSelection.mem_support` states
  `i ∈ R ξ → survive ξ i`.
- `Combinatorics.Branching.Step.FiniteSelection.IsBoundedBy R N` means
  `(R ξ).card ≤ N` for every step `ξ`.
- `Combinatorics.Branching.Step.FiniteSelection.filter R keep` retains the
  selected slots with `keep ξ i`; `.mem_filter` gives its membership formula,
  and `.filter_isBoundedBy` preserves every capacity bound.
- `Combinatorics.Branching.Step.FiniteSelection.firstNBy N value hadmits`
  constructs a first-`N` selection from existence witnesses;
  `.firstNBy_spec` gives `IsFirstNBy N (value ξ) (support ξ) (R ξ)`,
  `.firstNBy_isBoundedBy` gives `(R ξ).card ≤ N`, and
  `.firstNBy_subset_of_le` gives monotonicity in `N`.
-/

@[expose] public section

namespace Combinatorics.Branching

/-- A finite selection of surviving slots from every branching step. -/
structure Step.FiniteSelection (α X : Type*) where
  select : Step α X → Finset α
  subset_support : ∀ ξ i, i ∈ select ξ → survive ξ i

namespace Step.FiniteSelection

variable {α X : Type*}

open Selection.NSelection

attribute [local instance] Classical.propDecidable Classical.decEq

instance : CoeFun (Step.FiniteSelection α X)
    (fun _ => Step α X → Finset α) :=
  ⟨Step.FiniteSelection.select⟩

@[simp] theorem mem_support (R : Step.FiniteSelection α X)
    (ξ : Step α X) {i : α} (hi : i ∈ R ξ) : survive ξ i :=
  R.subset_support ξ i hi

/-- A uniform capacity bound on the number of selected child slots. -/
def IsBoundedBy (R : Step.FiniteSelection α X) (N : ℕ) : Prop :=
  ∀ ξ, (R ξ).card ≤ N

/-- Keep from a finite step selection only slots satisfying a further
step-dependent predicate. -/
noncomputable def filter (R : Step.FiniteSelection α X)
    (keep : Step α X → α → Prop) : Step.FiniteSelection α X where
  select ξ := (R ξ).filter (keep ξ)
  subset_support ξ i hi :=
    R.subset_support ξ i (Finset.mem_filter.mp hi).1

@[simp] theorem mem_filter (R : Step.FiniteSelection α X)
    (keep : Step α X → α → Prop) (ξ : Step α X) (i : α) :
    i ∈ R.filter keep ξ ↔ i ∈ R ξ ∧ keep ξ i := by
  classical
  simp [filter]

theorem filter_isBoundedBy (R : Step.FiniteSelection α X)
    (keep : Step α X → α → Prop) {N : ℕ}
    (hR : R.IsBoundedBy N) : (R.filter keep).IsBoundedBy N := by
  intro ξ
  exact (Finset.card_filter_le _ _).trans (hR ξ)

/-- Select the intrinsic first `N` surviving slots by a step-dependent
ordered observation.  Existence is supplied explicitly, so the constructor
does not hide any local-finiteness assumption. -/
noncomputable def firstNBy
    {Value : Type*} [LinearOrder α] [LinearOrder Value]
    (N : ℕ) (value : Step α X → α → Value)
    (hadmits : ∀ ξ, AdmitsFirstNBy N (value ξ) (support ξ)) :
    Step.FiniteSelection α X where
  select ξ := selectFirstNFromSet N (value ξ) (support ξ) (hadmits ξ)
  subset_support ξ _ hi :=
    (selectFirstNFromSet_spec N (value ξ) (support ξ) (hadmits ξ)).subset hi

theorem firstNBy_spec
    {Value : Type*} [LinearOrder α] [LinearOrder Value]
    (N : ℕ) (value : Step α X → α → Value)
    (hadmits : ∀ ξ, AdmitsFirstNBy N (value ξ) (support ξ)) (ξ : Step α X) :
    IsFirstNBy N (value ξ) (support ξ)
      (firstNBy N value hadmits ξ) :=
  selectFirstNFromSet_spec N (value ξ) (support ξ) (hadmits ξ)

theorem firstNBy_isBoundedBy
    {Value : Type*} [LinearOrder α] [LinearOrder Value]
    (N : ℕ) (value : Step α X → α → Value)
    (hadmits : ∀ ξ, AdmitsFirstNBy N (value ξ) (support ξ)) :
    (firstNBy N value hadmits).IsBoundedBy N :=
  fun ξ => (firstNBy_spec N value hadmits ξ).card_le

theorem firstNBy_subset_of_le
    {Value : Type*} [LinearOrder α] [LinearOrder Value]
    {N M : ℕ} (hNM : N ≤ M) (value : Step α X → α → Value)
    (hadmitsN : ∀ ξ, AdmitsFirstNBy N (value ξ) (support ξ))
    (hadmitsM : ∀ ξ, AdmitsFirstNBy M (value ξ) (support ξ))
    (ξ : Step α X) :
    firstNBy N value hadmitsN ξ ⊆ firstNBy M value hadmitsM ξ :=
  (firstNBy_spec N value hadmitsN ξ).subset_of_le
    (firstNBy_spec M value hadmitsM ξ) hNM


end Step.FiniteSelection

end Combinatorics.Branching

end
