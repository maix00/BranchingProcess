/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Population.Processes.Selected.RootIndexed
public import Probability.BranchingRandomWalk.Step.Field.Update
public import MeasureTheory.Selection.NSelection.Totalized

/-!
# Selected populations under generation-local field updates

## Public declarations

- `selectedPopulation_updateGeneration_of_le` and
  `selectedPopulationTotalized_updateGeneration_of_le`: if $n\le m$, changing
  the step field at generation $m$ leaves the selected population at time $n$
  unchanged.
- `selectedPopulation_updateGeneration`: the preceding equality at $n=m$.

Installing steps at generation `m` leaves every selected population through
that generation unchanged.  The proof uses only the intrinsic `IsFirstNBy`
specification, so it does not depend on how the finite initial segment is
constructed or on countability of the ambient particle type.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.RootIndexed

open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection

noncomputable section

variable {Root α Mark Position Value : Type*}

private theorem childrenAtGeneration_updateGeneration_of_lt
    [DecidableEq (RootIndexed.TreeNode Root α)]
    (n m : ℕ) (hnm : n < m)
    (parents : Finset (RootIndexed.TreeNode Root α))
    (replacement fallback : RootIndexed.StepField Root α Mark) :
    Combinatorics.Branching.Population.childrenAtGeneration n parents
        (Combinatorics.Branching.RootIndexed.StepField.updateGeneration
          m replacement fallback) =
      Combinatorics.Branching.Population.childrenAtGeneration n parents fallback := by
  ext q
  rw [Combinatorics.Branching.Population.mem_childrenAtGeneration_iff, Combinatorics.Branching.Population.mem_childrenAtGeneration_iff]
  constructor
  · rintro ⟨p, hp, hpdepth, i, hi, rfl⟩
    refine ⟨p, hp, hpdepth, i, ?_, rfl⟩
    have hstep :
        Combinatorics.Branching.RootIndexed.StepField.updateGeneration
            m replacement fallback p.1 p.2 = fallback p.1 p.2 := by
      apply Combinatorics.Branching.StepField.updateGeneration_of_lt
      simpa [hpdepth] using hnm
    rw [hstep] at hi
    exact hi
  · rintro ⟨p, hp, hpdepth, i, hi, rfl⟩
    refine ⟨p, hp, hpdepth, i, ?_, rfl⟩
    have hstep :
        Combinatorics.Branching.RootIndexed.StepField.updateGeneration
            m replacement fallback p.1 p.2 = fallback p.1 p.2 := by
      apply Combinatorics.Branching.StepField.updateGeneration_of_lt
      simpa [hpdepth] using hnm
    rw [hstep]
    exact hi

/-- Updating the steps owned by generation `m` cannot change selected
populations at generations `n ≤ m`. -/
theorem selectedPopulation_updateGeneration_of_le
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hadmits : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (observedPositionAtGeneration initial d φ (n + 1) ω)
        (Combinatorics.Branching.Population.childrenAtGeneration n parents ω))
    (n m : ℕ) (hnm : n ≤ m)
    (replacement fallback : RootIndexed.StepField Root α Mark) :
    selectedPopulation N roots initial d φ hadmits n
        (Combinatorics.Branching.RootIndexed.StepField.updateGeneration
          m replacement fallback) =
      selectedPopulation N roots initial d φ hadmits n fallback := by
  let updated :=
    Combinatorics.Branching.RootIndexed.StepField.updateGeneration
      m replacement fallback
  induction n with
  | zero => rfl
  | succ k ih =>
      have hklt : k < m := lt_of_lt_of_le (Nat.lt_succ_self k) hnm
      have hparents :
          selectedPopulation N roots initial d φ hadmits k updated =
            selectedPopulation N roots initial d φ hadmits k fallback :=
        ih (Nat.le_of_succ_le hnm)
      let parents := selectedPopulation N roots initial d φ hadmits k fallback
      have hcandidates :
          Combinatorics.Branching.Population.childrenAtGeneration k parents updated =
            Combinatorics.Branching.Population.childrenAtGeneration k parents fallback := by
        exact childrenAtGeneration_updateGeneration_of_lt
          k m hklt parents replacement fallback
      have hvalue : Set.EqOn
          (observedPositionAtGeneration initial d φ (k + 1) fallback)
          (observedPositionAtGeneration initial d φ (k + 1) updated)
          (Combinatorics.Branching.Population.childrenAtGeneration k parents fallback) := by
        intro q hq
        have hdepth : q.2.length = k + 1 :=
          Combinatorics.Branching.Population.childrenAtGeneration_depth k parents fallback q hq
        rw [observedPositionAtGeneration_eq initial d φ (k + 1)
          fallback q hdepth]
        rw [observedPositionAtGeneration_eq initial d φ (k + 1)
          updated q hdepth]
        apply congrArg φ
        symm
        exact Combinatorics.Branching.RootIndexed.BranchingWalk.position_updateGeneration_of_le
          d m initial replacement fallback q.1 q.2 (by omega)
      have hupdated := selectedPopulation_succ_spec
        N roots initial d φ hadmits k updated
      have hfallback := selectedPopulation_succ_spec
        N roots initial d φ hadmits k fallback
      rw [hparents] at hupdated
      have hfallback' := hfallback.congr_value hvalue
      rw [← hcandidates] at hfallback'
      exact hupdated.unique hfallback'

/-- In particular, installing a new step family at the currently selected
parent generation preserves that parent population exactly. -/
theorem selectedPopulation_updateGeneration
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hadmits : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (observedPositionAtGeneration initial d φ (n + 1) ω)
        (Combinatorics.Branching.Population.childrenAtGeneration n parents ω))
    (n : ℕ) (replacement fallback : RootIndexed.StepField Root α Mark) :
    selectedPopulation N roots initial d φ hadmits n
        (Combinatorics.Branching.RootIndexed.StepField.updateGeneration
          n replacement fallback) =
      selectedPopulation N roots initial d φ hadmits n fallback :=
  selectedPopulation_updateGeneration_of_le N roots initial d φ hadmits
    n n le_rfl replacement fallback

/-- Totalized first-`N` selection through generation `n` is unaffected by a
field update at any generation `m ≥ n`. This does not require pointwise
existence of a first-`N` segment on unrelated raw fields. -/
theorem selectedPopulationTotalized_updateGeneration_of_le
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (n m : ℕ) (hnm : n ≤ m)
    (replacement fallback : RootIndexed.StepField Root α Mark) :
    selectedPopulationTotalized N roots initial d φ n
        (Combinatorics.Branching.RootIndexed.StepField.updateGeneration
          m replacement fallback) =
      selectedPopulationTotalized N roots initial d φ n fallback := by
  let updated := Combinatorics.Branching.RootIndexed.StepField.updateGeneration
    m replacement fallback
  induction n with
  | zero => rfl
  | succ k ih =>
      have hklt : k < m := lt_of_lt_of_le (Nat.lt_succ_self k) hnm
      have hparents :
          selectedPopulationTotalized N roots initial d φ k updated =
            selectedPopulationTotalized N roots initial d φ k fallback :=
        ih (Nat.le_of_succ_le hnm)
      have hcandidates :
          Combinatorics.Branching.Population.childrenAtGeneration k
              (selectedPopulationTotalized N roots initial d φ k updated) updated =
            Combinatorics.Branching.Population.childrenAtGeneration k
              (selectedPopulationTotalized N roots initial d φ k fallback) fallback := by
        calc
          Combinatorics.Branching.Population.childrenAtGeneration k
              (selectedPopulationTotalized N roots initial d φ k updated) updated =
            Combinatorics.Branching.Population.childrenAtGeneration k
              (selectedPopulationTotalized N roots initial d φ k fallback) updated := by
                rw [hparents]
          _ = Combinatorics.Branching.Population.childrenAtGeneration k
              (selectedPopulationTotalized N roots initial d φ k fallback) fallback :=
            childrenAtGeneration_updateGeneration_of_lt k m hklt _ replacement fallback
      change Combinatorics.Selection.NSelection.selectFirstNFromSetTotalized N
            (observedPositionAtGeneration initial d φ (k + 1))
            (fun field => Combinatorics.Branching.Population.childrenAtGeneration k
              (selectedPopulationTotalized N roots initial d φ k field) field) updated =
        Combinatorics.Selection.NSelection.selectFirstNFromSetTotalized N
            (observedPositionAtGeneration initial d φ (k + 1))
            (fun field => Combinatorics.Branching.Population.childrenAtGeneration k
              (selectedPopulationTotalized N roots initial d φ k field) field) fallback
      apply Combinatorics.Selection.NSelection.selectFirstNFromSetTotalized_congr
          N (observedPositionAtGeneration initial d φ (k + 1))
          (observedPositionAtGeneration initial d φ (k + 1))
          (fun field => Combinatorics.Branching.Population.childrenAtGeneration k
            (selectedPopulationTotalized N roots initial d φ k field) field)
          (fun field => Combinatorics.Branching.Population.childrenAtGeneration k
            (selectedPopulationTotalized N roots initial d φ k field) field)
          updated fallback hcandidates
      intro p hp
      have hp' : p ∈ Combinatorics.Branching.Population.childrenAtGeneration k
          (selectedPopulationTotalized N roots initial d φ k fallback) fallback := by
        rw [← hcandidates]
        exact hp
      have hdepth := Combinatorics.Branching.Population.childrenAtGeneration_depth k
        (selectedPopulationTotalized N roots initial d φ k fallback) fallback p hp'
      rw [observedPositionAtGeneration_eq initial d φ (k + 1) updated p hdepth,
        observedPositionAtGeneration_eq initial d φ (k + 1) fallback p hdepth]
      congr 1
      exact Combinatorics.Branching.RootIndexed.BranchingWalk.position_updateGeneration_of_le
        d m initial replacement fallback p.1 p.2 (by omega)

end

end ProbabilityTheory.BranchingRandomWalk.RootIndexed
