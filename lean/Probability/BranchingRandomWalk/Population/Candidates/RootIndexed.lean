module

public import Combinatorics.BranchingWalk.Basic.Descendant
public import Combinatorics.BranchingWalk.Selection.NSelection.Infinite
public import Combinatorics.BranchingWalk.Selection.Coupling.Offspring.Address
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Measurability

/-!
# Root-indexed generation candidates

The candidate population consists of every surviving child of the retained
parents. It is set-valued and allows infinitely many children. The definition
uses the unique final slot of an address, so measurability of a fixed child
does not require the whole slot type to be countable.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.RootIndexed

open Combinatorics.UlamHarris Combinatorics.Branching

/-- All surviving children at generation `n + 1` of a finite retained parent
population at generation `n`. -/
def childrenAtGeneration
    {Root α X : Type*} [DecidableEq (RootIndexed.TreeNode Root α)]
    (n : ℕ)
    (parents : Finset (RootIndexed.TreeNode Root α))
    (ω : RootIndexed.StepField Root α X) :
    Set (RootIndexed.TreeNode Root α) :=
  {q | q.2.length = n + 1 ∧
    match q.2.getLast? with
    | none => False
    | some i => parent q ∈ parents ∧ survive (ω (parent q).1 (parent q).2) i}

theorem childAddress_mem_childrenAtGeneration
    {Root α X : Type*} [DecidableEq (RootIndexed.TreeNode Root α)]
    (n : ℕ) (parents : Finset (RootIndexed.TreeNode Root α))
    (ω : RootIndexed.StepField Root α X)
    (p : RootIndexed.TreeNode Root α) (hp : p ∈ parents)
    (hpdepth : p.2.length = n) (i : α) (hi : survive (ω p.1 p.2) i) :
    (p.1, p.2 ++ [i]) ∈ childrenAtGeneration n parents ω := by
  simp [childrenAtGeneration, parent, hpdepth, hp, hi]

theorem mem_childrenAtGeneration_iff
    {Root α X : Type*} [DecidableEq (RootIndexed.TreeNode Root α)]
    (n : ℕ) (parents : Finset (RootIndexed.TreeNode Root α))
    (ω : RootIndexed.StepField Root α X)
    (q : RootIndexed.TreeNode Root α) :
    q ∈ childrenAtGeneration n parents ω ↔
      ∃ p ∈ parents, p.2.length = n ∧ ∃ i,
        survive (ω p.1 p.2) i ∧ q = (p.1, p.2 ++ [i]) := by
  constructor
  · intro hq
    have hnonempty : q.2 ≠ [] := by
      intro h
      simp [childrenAtGeneration, h] at hq
    let i := q.2.getLast hnonempty
    have hi : q.2.getLast? = some i :=
      List.getLast?_eq_some_getLast hnonempty
    have hdata : parent q ∈ parents ∧
        survive (ω (parent q).1 (parent q).2) i := by
      simpa [childrenAtGeneration, hi] using hq.2
    refine ⟨parent q, hdata.1, ?_, i, hdata.2, ?_⟩
    · simp only [parent]
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
    (ω : RootIndexed.StepField Root α X)
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
    (field : RootIndexed.StepField Root α X)
    (value : RootIndexed.TreeNode Root α → Value)
    (window : Set Value) (upper : Value)
    (hwindow : window ⊆ Set.Iic upper)
    (hlevel : ∀ p ∈ parents, p.2.length = n → ∀ a,
      {i | survive (field p.1 p.2) i ∧
        value (p.1, p.2 ++ [i]) ≤ a}.Finite) :
    {q | q ∈ childrenAtGeneration n parents field ∧
      value q ∈ window}.Finite := by
  let U : Set (RootIndexed.TreeNode Root α) :=
    ⋃ p ∈ (↑parents : Set (RootIndexed.TreeNode Root α)),
      (fun i => (p.1, p.2 ++ [i])) ''
        {i | p.2.length = n ∧ survive (field p.1 p.2) i ∧
          value (p.1, p.2 ++ [i]) ≤ upper}
  have hUfinite : U.Finite := by
    apply parents.finite_toSet.biUnion
    intro p hp
    by_cases hdepth : p.2.length = n
    · apply ((hlevel p hp hdepth upper).subset ?_).image
      intro i hi
      exact hi.2
    · have hempty :
          {i | p.2.length = n ∧ survive (field p.1 p.2) i ∧
            value (p.1, p.2 ++ [i]) ≤ upper} = ∅ := by
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
    (ω : RootIndexed.StepField Root α X)
    (hdepth : ∀ p ∈ parents, p.2.length = n) :
    childrenAtGeneration n parents ω =
      Combinatorics.Branching.Selection.Coupling.offspringAddressSet
        (↑parents) (fun p => {i | survive (ω p.1 p.2) i}) := by
  ext q
  rw [mem_childrenAtGeneration_iff]
  rw [Combinatorics.Branching.Selection.Coupling.mem_offspringAddressSet]
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
    (ω : RootIndexed.StepField Root α X)
    (value : RootIndexed.TreeNode Root α → Value)
    (hlevel : ∀ p ∈ parents, ∀ a,
      {i | survive (ω p.1 p.2) i ∧
        value (p.1, p.2 ++ [i]) ≤ a}.Finite) :
    Combinatorics.Branching.Selection.NSelection.IsLowerFiniteBy value
      (childrenAtGeneration n parents ω) := by
  intro q hq
  let U : Set (RootIndexed.TreeNode Root α) :=
    ⋃ p ∈ (↑parents : Set (RootIndexed.TreeNode Root α)),
      (fun i => (p.1, p.2 ++ [i])) ''
        {i | survive (ω p.1 p.2) i ∧
          value (p.1, p.2 ++ [i]) ≤ value q}
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
    (ω : RootIndexed.StepField Root α X)
    (value : RootIndexed.TreeNode Root α → Value)
    (hlevel : ∀ p ∈ parents, ∀ a,
      {i | survive (ω p.1 p.2) i ∧
        value (p.1, p.2 ++ [i]) ≤ a}.Finite) :
    Combinatorics.Branching.Selection.NSelection.AdmitsFirstNBy N value
      (childrenAtGeneration n parents ω) :=
  Combinatorics.Branching.Selection.NSelection.admitsFirstNBy_of_lowerFinite
    N value (childrenAtGeneration_isLowerFiniteBy n parents ω value hlevel)

/-- The full child-candidate set is observable one generation after its
parents. No finiteness or countability condition is imposed on offspring
slots. -/
theorem childrenAtGeneration_measurable
    {Root α X : Type*} [MeasurableSpace X]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    (n : ℕ)
    (parents : RootIndexed.StepField Root α X →
      Finset (RootIndexed.TreeNode Root α))
    (hparents : Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] parents) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) (n + 1)]
      (fun ω => childrenAtGeneration n (parents ω) ω) := by
  let _ : MeasurableSpace (RootIndexed.StepField Root α X) :=
    RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) (n + 1)
  rw [measurable_set_iff]
  intro q
  by_cases hdepth : q.2.length = n + 1
  · have hnonempty : q.2 ≠ [] := by
      intro h
      simp [h] at hdepth
    let i := q.2.getLast hnonempty
    have hi : q.2.getLast? = some i :=
      List.getLast?_eq_some_getLast hnonempty
    have hparentDepth : (parent q).2.length = n := by
      simp only [parent]
      rw [List.length_dropLast, hdepth]
      omega
    have hparents' : Measurable[RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) (n + 1)] parents :=
      hparents.mono
        (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) |>.mono
          (Nat.le_succ n)) le_rfl
    have hparentMem : Measurable[RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) (n + 1)]
        (fun ω => parent q ∈ parents ω) :=
      (measurable_finset_mem (parent q)).comp hparents'
    have hsurvive : Measurable[RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) (n + 1)]
        (fun ω => survive (ω (parent q).1 (parent q).2) i) := by
      apply measurableSet_setOfPred.mp
      exact (RootIndexed.step_measurable (X := X)
        (parent q).1 (parent q).2 (by omega))
          (survive_measurableSet (X := X) i)
    simpa [childrenAtGeneration, hdepth, hi] using hparentMem.and hsurvive
  · simp [childrenAtGeneration, hdepth]

end ProbabilityTheory.BranchingRandomWalk.RootIndexed
