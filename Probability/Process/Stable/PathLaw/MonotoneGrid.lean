/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLaw.WalkGrid
public import Probability.Process.Stable.PathLaw.Basic
public import Probability.ConvergenceInDistribution.CadlagPath.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.Pi

import all Probability.Process.Stable.PathLaw.Lemmas.MonotoneGrid

/-!
# Stable position laws on monotone time grids

`ProbabilityTheory.stableGridPositionLaws_of_strictGridPositionLaws` extends
the finite-dimensional stable position law from strictly increasing grids to
all monotone grids. More precisely, if the process law has the stable increment
product law on every strictly increasing grid that starts at zero, then the
process starts at zero almost surely and, for every monotone grid `t`, its
position vector has law
`(stableTimeLawProductProbability α t).map Fin.partialSum`.

The zero increment at a repeated grid point is handled by the internal
coordinate and product-measure calculations in
`Probability.Process.Stable.PathLaw.Lemmas.MonotoneGrid`.

## Public declarations

- `ProbabilityTheory.stableGridPositionLaws_of_strictGridPositionLaws`:
  strict-grid stable increment laws imply both the almost-sure zero-start
  property and the position-vector law on every monotone grid. For each
  monotone `t` with `t 0 = ⊥`,
  `P.map (denseEvaluation t) =
    (stableTimeLawProductProbability α t).map Fin.partialSum`.
-/

@[expose] public section

open MeasureTheory
open MeasureTheory.CadlagPath
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

namespace ProbabilityTheory

open ProbabilityTheory.StablePathLaw.MonotoneGrid.Lemmas

/-- Strict-grid laws determine position laws on all monotone grids. A flat
edge contributes a Dirac-zero increment; deleting that edge gives the smaller
strict-grid law, and the finite product formula reinserts the zero coordinate.
The first component derives the required zero-start property from the
zero-dimensional increment grid. -/
theorem stableGridPositionLaws_of_strictGridPositionLaws
    {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (hStable : IsStrictlyAlphaStable α μ)
    (hStrict : ∀ (n : ℕ) (grid : Fin (n + 1) → unitInterval),
      StrictMono grid → grid 0 = ⊥ →
      P.map (denseEvaluation grid) =
        ((stableTimeLawProductProbability (μ := μ) α grid :
          ProbabilityMeasure (Fin n → ℝ)) : Measure (Fin n → ℝ)).map
            (Fin.partialSum : (Fin n → ℝ) → (Fin (n + 1) → ℝ))) :
    (∀ᵐ f ∂P, f ⊥ = 0) ∧
      ∀ (n : ℕ) (grid : Fin (n + 1) → unitInterval),
        Monotone grid → grid 0 = ⊥ →
        P.map (denseEvaluation grid) =
          ((stableTimeLawProductProbability (μ := μ) α grid :
            ProbabilityMeasure (Fin n → ℝ)) : Measure (Fin n → ℝ)).map
              (Fin.partialSum : (Fin n → ℝ) → (Fin (n + 1) → ℝ)) := by
  have hstart := ae_start_eq_zero_of_strictGridPositionLaws hStrict
  have hmonotone : ∀ n : ℕ, ∀ grid : Fin (n + 1) → unitInterval,
      Monotone grid → grid 0 = ⊥ →
      P.map (denseEvaluation grid) =
        ((stableTimeLawProductProbability (μ := μ) α grid :
          ProbabilityMeasure (Fin n → ℝ)) : Measure (Fin n → ℝ)).map
            (Fin.partialSum : (Fin n → ℝ) → (Fin (n + 1) → ℝ)) := by
    intro n
    induction n with
    | zero =>
        intro grid hgrid hstartGrid
        have hstrictGrid : StrictMono grid := by
          intro i j hij
          have : i = j := Fin.ext (by omega)
          subst j
          exact False.elim (lt_irrefl i hij)
        exact hStrict 0 grid hstrictGrid hstartGrid
    | succ n ih =>
        intro grid hgrid hstartGrid
        by_cases hstrictGrid : StrictMono grid
        · exact hStrict (n + 1) grid hstrictGrid hstartGrid
        · have hrepeat : ∃ i : Fin (n + 1), grid i.castSucc = grid i.succ := by
            rw [Fin.strictMono_iff_lt_succ] at hstrictGrid
            push Not at hstrictGrid
            obtain ⟨i, hi⟩ := hstrictGrid
            refine ⟨i, le_antisymm ((Fin.monotone_iff_le_succ.mp hgrid) i)
              hi⟩
          obtain ⟨i, hrep⟩ := hrepeat
          let grid' := deleteRepeatedPointGrid i grid
          have hgrid' : Monotone grid' := by
            exact deleteRepeatedPointGrid_monotone i grid hgrid
          have hstart' : grid' 0 = ⊥ :=
            deleteRepeatedPointGrid_start i grid hstartGrid
          have hposition' := ih grid' hgrid' hstart'
          let L : ProbabilityMeasure (Fin (n + 1) → ℝ) :=
            stableTimeLawProductProbability (μ := μ) α grid
          let L' : ProbabilityMeasure (Fin n → ℝ) :=
            stableTimeLawProductProbability (μ := μ) α grid'
          let ν : Fin (n + 1) → Measure ℝ := fun j =>
            stableTimeLaw α μ ((grid j.succ : unitInterval) - (grid j.castSucc : unitInterval))
          let ν' : Fin n → Measure ℝ := fun j =>
            stableTimeLaw α μ
              ((grid' j.succ : unitInterval) - (grid' j.castSucc : unitInterval))
          have hνsigma (j : Fin (n + 1)) : SigmaFinite (ν j) := by
            dsimp [ν, stableTimeLaw]
            infer_instance
          have hν'sigma (j : Fin n) : SigmaFinite (ν' j) := by
            dsimp [ν', stableTimeLaw]
            infer_instance
          have hνzero : ν i = Measure.dirac 0 := by
            dsimp [ν]
            have htime : (grid i.succ : ℝ) - grid i.castSucc = 0 := by
              have hcoe := congrArg (fun t : unitInterval => (t : ℝ)) hrep
              linarith
            rw [htime]
            exact hStable.stableTimeLaw_zero
          have hνrest : ∀ j : Fin n, ν (i.succAbove j) = ν' j := by
            intro j
            dsimp [ν, ν']
            rw [deleteRepeatedPointGrid_increment_interval i grid hrep j]
          have hproduct : (L : Measure (Fin (n + 1) → ℝ)) =
              ((L' : Measure (Fin n → ℝ)).map (insertZeroCoordinate i)) := by
            change Measure.pi ν = (Measure.pi ν').map (insertZeroCoordinate i)
            exact @measure_pi_insertZeroCoordinate n i ν' ν hν'sigma hνsigma
              hνzero hνrest
          have hevaluation := denseEvaluation_insertRepeatedPoint i grid hrep
          calc
            P.map (denseEvaluation grid) =
                (P.map (denseEvaluation grid')).map (insertRepeatedPosition i) := by
              rw [Measure.map_map (measurable_insertRepeatedPosition i)
                (measurable_denseEvaluation grid')]
              congr 1
              funext f
              exact hevaluation f
            _ = (((L' : Measure (Fin n → ℝ)).map
                  (Fin.partialSum : (Fin n → ℝ) → (Fin (n + 1) → ℝ))).map
                    (insertRepeatedPosition i)) := by
              rw [hposition']
            _ = (L' : Measure (Fin n → ℝ)).map
                  (fun x => insertRepeatedPosition i (Fin.partialSum x)) := by
              exact Measure.map_map (measurable_insertRepeatedPosition i)
                (Fin.continuous_partialSum n).measurable
            _ = (L' : Measure (Fin n → ℝ)).map
                  (fun x => Fin.partialSum (insertZeroCoordinate i x)) := by
              congr 1
              funext x
              exact (partialSum_insertZeroCoordinate i x).symm
            _ = (((L' : Measure (Fin n → ℝ)).map (insertZeroCoordinate i)).map
                  (Fin.partialSum : (Fin (n + 1) → ℝ) → (Fin (n + 2) → ℝ))) := by
              symm
              exact Measure.map_map (Fin.continuous_partialSum (n + 1)).measurable
                (measurable_insertZeroCoordinate i)
            _ = (L : Measure (Fin (n + 1) → ℝ)).map
                  (Fin.partialSum : (Fin (n + 1) → ℝ) → (Fin (n + 2) → ℝ)) := by
              rw [← hproduct]
  exact ⟨hstart, hmonotone⟩

end ProbabilityTheory

end
