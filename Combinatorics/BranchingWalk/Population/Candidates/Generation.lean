/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.Sibling.ParentSibling
public import Combinatorics.Selection.NSelection.Mechanism.Infinite.Basic
public import Combinatorics.BranchingWalk.Population.Offspring
public import Combinatorics.UlamHarris.Relation

/-!
# Root-indexed generation candidates

For a finite parent set $P$ at depth $n$ and a root-indexed step field $\omega$,
`childrenAtGeneration n P ω` is the set of all surviving child addresses at
depth $n+1$. The set may be infinite when the child-slot type is infinite.

## Public declarations

- `Combinatorics.Branching.Population.childrenAtGeneration` defines the
  surviving child-address set at generation $n+1$ for a finite generation-$n$
  parent population. `Combinatorics.Branching.Population.childAddress_mem_childrenAtGeneration`,
  `Combinatorics.Branching.Population.mem_childrenAtGeneration_iff`, and
  `Combinatorics.Branching.Population.childrenAtGeneration_depth` give its
  constructor, membership characterization, and depth.
- `Combinatorics.Branching.Population.childrenAtGeneration_filter_finite_of_upperBound`
  proves that filtering by a bounded value set is finite under finite
  single-parent sublevel sets.
- `Combinatorics.Branching.Population.childrenAtGeneration_eq_offspringAddressSet`
  identifies a generation slice with the generic offspring-address set.
- `Combinatorics.Branching.Population.childrenAtGeneration_isLowerFiniteBy`
  lifts finite single-parent lower sections to the whole finite-parent
  offspring population; `Combinatorics.Branching.Population.childrenAtGeneration_admitsFirstNBy`
  applies the generic first-$N$ existence interface.

The construction uses the generic root-preserving address extension from
`Combinatorics.UlamHarris.RootIndexed`; it has no sample-space or
measurability assumptions.
-/

@[expose] public section

namespace Combinatorics.Branching

namespace Population

open Combinatorics.UlamHarris

def childrenAtGeneration
    {Root α X : Type*} [DecidableEq (RootIndexed.TreeNode Root α)]
    (n : ℕ)
    (parents : Finset (RootIndexed.TreeNode Root α))
    (ω : Root → Combinatorics.Branching.StepField α X) :
    Set (RootIndexed.TreeNode Root α) :=
  {q | q.2.length = n + 1 ∧
    match q.2.getLast? with
    | none => False
    | some i =>
      RootIndexed.parent q ∈ parents ∧
        survive (ω (RootIndexed.parent q).1 (RootIndexed.parent q).2) i}

theorem childAddress_mem_childrenAtGeneration
    {Root α X : Type*} [DecidableEq (RootIndexed.TreeNode Root α)]
    (n : ℕ) (parents : Finset (RootIndexed.TreeNode Root α))
    (ω : Root → Combinatorics.Branching.StepField α X)
    (p : RootIndexed.TreeNode Root α) (hp : p ∈ parents)
    (hpdepth : p.2.length = n) (i : α) (hi : survive (ω p.1 p.2) i) :
    RootIndexed.childAddress p i ∈ childrenAtGeneration n parents ω := by
  simp [childrenAtGeneration, RootIndexed.parent,
    hpdepth, hp, hi]

theorem mem_childrenAtGeneration_iff
    {Root α X : Type*} [DecidableEq (RootIndexed.TreeNode Root α)]
    (n : ℕ) (parents : Finset (RootIndexed.TreeNode Root α))
    (ω : Root → Combinatorics.Branching.StepField α X)
    (q : RootIndexed.TreeNode Root α) :
    q ∈ childrenAtGeneration n parents ω ↔
      ∃ p ∈ parents, p.2.length = n ∧ ∃ i,
        survive (ω p.1 p.2) i ∧ q = RootIndexed.childAddress p i := by
  constructor
  · intro hq
    have hnonempty : q.2 ≠ [] := by
      intro h
      simp [childrenAtGeneration, h] at hq
    let i := q.2.getLast hnonempty
    have hi : q.2.getLast? = some i :=
      List.getLast?_eq_some_getLast hnonempty
    have hdata : RootIndexed.parent q ∈ parents ∧
        survive (ω (RootIndexed.parent q).1 (RootIndexed.parent q).2) i := by
      simpa [childrenAtGeneration, hi] using hq.2
    refine ⟨RootIndexed.parent q, hdata.1, ?_, i, hdata.2, ?_⟩
    · simp only [RootIndexed.parent]
      rw [List.length_dropLast, hq.1]
      omega
    · apply Prod.ext
      · rfl
      · exact (List.dropLast_append_getLast hnonempty).symm
  · rintro ⟨p, hp, hpdepth, i, hi, rfl⟩
    exact childAddress_mem_childrenAtGeneration n parents ω p hp hpdepth i hi

theorem childrenAtGeneration_depth
    {Root α X : Type*} [DecidableEq (RootIndexed.TreeNode Root α)]
    (n : ℕ) (parents : Finset (RootIndexed.TreeNode Root α))
    (ω : Root → Combinatorics.Branching.StepField α X)
    (q : RootIndexed.TreeNode Root α)
    (hq : q ∈ childrenAtGeneration n parents ω) :
    q.2.length = n + 1 :=
  hq.1

/-- Filtering the children of finitely many parents by a value set with a
common upper bound is finite when every parent's offspring have finite lower
levels.  Neither the slot type nor the unfiltered offspring set is assumed
countable. -/
theorem childrenAtGeneration_filter_finite_of_upperBound
    {Root α X Value : Type*} [LinearOrder Value]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    (n : ℕ) (parents : Finset (RootIndexed.TreeNode Root α))
    (field : Root → Combinatorics.Branching.StepField α X)
    (value : RootIndexed.TreeNode Root α → Value)
    (window : Set Value) (upper : Value)
    (hwindow : window ⊆ Set.Iic upper)
    (hlevel : ∀ p ∈ parents, p.2.length = n → ∀ a,
      {i | survive (field p.1 p.2) i ∧
        value (RootIndexed.childAddress p i) ≤ a}.Finite) :
    {q | q ∈ childrenAtGeneration n parents field ∧
      value q ∈ window}.Finite := by
  let U : Set (RootIndexed.TreeNode Root α) :=
    ⋃ p ∈ (↑parents : Set (RootIndexed.TreeNode Root α)),
      (fun i => RootIndexed.childAddress p i) ''
        {i | p.2.length = n ∧ survive (field p.1 p.2) i ∧
          value (RootIndexed.childAddress p i) ≤ upper}
  have hUfinite : U.Finite := by
    apply parents.finite_toSet.biUnion
    intro p hp
    by_cases hdepth : p.2.length = n
    · apply ((hlevel p hp hdepth upper).subset ?_).image
      intro i hi
      exact hi.2
    · have hempty :
          {i | p.2.length = n ∧ survive (field p.1 p.2) i ∧
            value (RootIndexed.childAddress p i) ≤ upper} = ∅ := by
        ext i
        simp [hdepth]
      rw [hempty]
      exact Set.finite_empty.image _
  apply hUfinite.subset
  intro q hq
  obtain ⟨p, hp, _, i, hi, rfl⟩ :=
    (mem_childrenAtGeneration_iff n parents field q).mp hq.1
  apply Set.mem_iUnion_of_mem p
  apply Set.mem_iUnion_of_mem hp
  exact ⟨i, ⟨by assumption, hi, hwindow hq.2⟩, rfl⟩

/-- The generation candidate set is the abstract offspring address set when
all retained parents belong to generation `n`. This is the interface used by
the pathwise multi-root coupling theorems. -/
theorem childrenAtGeneration_eq_offspringAddressSet
    {Root α X : Type*} [DecidableEq (RootIndexed.TreeNode Root α)]
    (n : ℕ) (parents : Finset (RootIndexed.TreeNode Root α))
    (ω : Root → Combinatorics.Branching.StepField α X)
    (hdepth : ∀ p ∈ parents, p.2.length = n) :
    childrenAtGeneration n parents ω =
      Combinatorics.Branching.Population.offspringAddressSet
        (↑parents) (fun p => {i | survive (ω p.1 p.2) i}) := by
  ext q
  rw [mem_childrenAtGeneration_iff]
  rw [Combinatorics.Branching.Population.mem_offspringAddressSet]
  constructor
  · rintro ⟨p, hp, _, i, hi, rfl⟩
    exact ⟨p, hp, i, hi, rfl⟩
  · rintro ⟨p, hp, i, hi, rfl⟩
    exact ⟨p, hp, hdepth p hp, i, hi, rfl⟩

/-- A finite parent population has a lower-finite full offspring population
when each parent has finitely many children below every observed threshold. -/
theorem childrenAtGeneration_isLowerFiniteBy
    {Root α X Value : Type*}
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ) (parents : Finset (RootIndexed.TreeNode Root α))
    (ω : Root → Combinatorics.Branching.StepField α X)
    (value : RootIndexed.TreeNode Root α → Value)
    (hlevel : ∀ p ∈ parents, ∀ a,
      {i | survive (ω p.1 p.2) i ∧
        value (RootIndexed.childAddress p i) ≤ a}.Finite) :
    Combinatorics.Selection.NSelection.IsLowerFiniteBy value
      (childrenAtGeneration n parents ω) := by
  intro q hq
  let U : Set (RootIndexed.TreeNode Root α) :=
    ⋃ p ∈ (↑parents : Set (RootIndexed.TreeNode Root α)),
      (fun i => RootIndexed.childAddress p i) ''
        {i | survive (ω p.1 p.2) i ∧
          value (RootIndexed.childAddress p i) ≤ value q}
  have hUfinite : U.Finite := by
    apply parents.finite_toSet.biUnion
    intro p hp
    exact (hlevel p hp (value q)).image _
  apply hUfinite.subset
  intro r hr
  obtain ⟨p, hp, _, i, hi, rfl⟩ :=
    (mem_childrenAtGeneration_iff n parents ω r).mp hr.1
  apply Set.mem_iUnion_of_mem p
  apply Set.mem_iUnion_of_mem hp
  refine ⟨i, ⟨hi, ?_⟩, rfl⟩
  exact (Prod.Lex.le_iff.mp hr.2).elim le_of_lt (fun h => h.1.le)

theorem childrenAtGeneration_admitsFirstNBy
    {Root α X Value : Type*}
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (N n : ℕ) (parents : Finset (RootIndexed.TreeNode Root α))
    (ω : Root → Combinatorics.Branching.StepField α X)
    (value : RootIndexed.TreeNode Root α → Value)
    (hlevel : ∀ p ∈ parents, ∀ a,
      {i | survive (ω p.1 p.2) i ∧
        value (RootIndexed.childAddress p i) ≤ a}.Finite) :
    Combinatorics.Selection.NSelection.AdmitsFirstNBy N value
      (childrenAtGeneration n parents ω) :=
  Combinatorics.Selection.NSelection.admitsFirstNBy_of_lowerFinite
    N value (childrenAtGeneration_isLowerFiniteBy n parents ω value hlevel)
end Population

end Combinatorics.Branching

end
