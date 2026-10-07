/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Restart.Trial
public import Probability.BranchingRandomWalk.Restart.FirstSplit

/-!
# Split trials started from a fixed genealogical root

The local split-completion theorem is already available at the root of a
tree.  This file transfers it to a fixed descendant subtree in the global
generation filtration, with the absolute generation offset made explicit.
This is the fixed-root step needed before treating a reserve root selected at
a previous observable split.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory

/-- The first selected-population split in a fixed descendant subtree, timed
in the ambient generation filtration.  The root is at global depth `start`,
and its local split completion is shifted by that deterministic offset. -/
theorem RootIndexed.fixedSubtree_splitCompletion_isStoppingTime
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    (root : Root × TreeNode α) (start : ℕ)
    (hdepth : root.2.length = start)
    (R : Step.FiniteSelection α X) (hR : Measurable R.select) :
    IsStoppingTime (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X))
      (fun ω => (start : WithTop ℕ) +
        selectedPopulationSplitCompletion R
          (fun v => ω root.1 (root.2 ++ v))) := by
  let subtree : RootIndexed.StepField Root α X → Mark α (Step α X) :=
    fun ω v => ω root.1 (root.2 ++ v)
  have hlocal : IsStoppingTime
      (generationFiltration (M := Step α X))
      (selectedPopulationSplitCompletion R) :=
    selectedPopulationSplitCompletion_isStoppingTime R hR
  intro n
  change MeasurableSet[RootIndexed.stepFiltration
    (Root := Root) (α := α) (X := X) n]
    {ω | (start : WithTop ℕ) +
      selectedPopulationSplitCompletion R (subtree ω) ≤ n}
  by_cases hle : start ≤ n
  · let age := n - start
    have hsum : start + age = n := Nat.add_sub_of_le hle
    have hsub : @Measurable (RootIndexed.StepField Root α X)
        (Mark α (Step α X))
        (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
          (start + age))
        (generationFiltration (M := Step α X) age) subtree := by
      exact RootIndexed.fixedSubtree_measurable_at root start age hdepth
    have hevent :
        {ω | (start : WithTop ℕ) +
            selectedPopulationSplitCompletion R (subtree ω) ≤ n} =
          subtree ⁻¹' {ξ | selectedPopulationSplitCompletion R ξ ≤ age} := by
      ext ω
      cases hσ : selectedPopulationSplitCompletion R (subtree ω) with
      | top => simp [hσ]
      | coe k =>
          simp only [Set.mem_ofPred_eq, Set.mem_preimage, hσ]
          constructor
          · intro h
            have hn : start + k ≤ n := by
              have h' : (↑(start + k) : WithTop ℕ) ≤ ↑n := by
                convert h using 1
                exact WithTop.coe_add start k
              exact WithTop.coe_le_coe.mp h'
            have hk : k ≤ n - start := by omega
            have hk' : k ≤ age := by simpa [age] using hk
            exact WithTop.coe_le_coe.mpr hk'
          · intro h
            have hk : k ≤ age := WithTop.coe_le_coe.mp h
            have hk' : k ≤ n - start := by simpa [age] using hk
            have hn : start + k ≤ n := by omega
            have h' : (↑(start + k) : WithTop ℕ) ≤ ↑n :=
              WithTop.coe_le_coe.mpr hn
            convert h' using 1
            exact WithTop.coe_add start k
    rw [hevent]
    rw [← hsum]
    exact (hlocal age).preimage hsub
  · have hnot :
        {ω | (start : WithTop ℕ) +
            selectedPopulationSplitCompletion R (subtree ω) ≤ n} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro htime
      cases hσ : selectedPopulationSplitCompletion R (subtree ω) with
      | top => simp [hσ] at htime
      | coe k =>
          have hk0 : k ≠ 0 := by
            intro hk
            apply selectedPopulationSplitCompletion_ne_zero R (subtree ω)
            simp [hσ, hk]
          have hk : 0 < k := Nat.pos_of_ne_zero hk0
          have htime' : (start : WithTop ℕ) + k ≤ n := by
            simpa [hσ] using htime
          have hnat : start + k ≤ n := by
            have h' : (↑(start + k) : WithTop ℕ) ≤ ↑n := by
              convert htime' using 1
              exact WithTop.coe_add start k
            exact WithTop.coe_le_coe.mp h'
          omega
    rw [hnot]
    exact (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n).measurableSet_empty

end ProbabilityTheory.BranchingRandomWalk

end
