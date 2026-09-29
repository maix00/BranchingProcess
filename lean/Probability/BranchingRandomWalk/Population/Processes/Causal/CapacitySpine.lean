import Probability.BranchingRandomWalk.Population.Processes.Causal.FirstMoment

/-!
# Capacity bounds from spine first moments

This file is the capacity-event bridge: generic causal-population Markov bounds
are instantiated with the one-dimensional restarted-window first moments.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching.Walk
namespace RootIndexed.CausalPopulation

open Combinatorics.UlamHarris Combinatorics.Branching
open ProbabilityTheory.BranchingRandomWalk.Spine

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Finite-horizon overload of the finite-root killed population is bounded
entirely by one-dimensional spine first moments. -/
theorem measure_capacityEvent_compl_le_sum_spine_restartedWindow
    {Root α Mark : Type*} [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    (roots : Finset Root) (initialPosition : Root → ℝ) (d : Mark → ℝ)
    (hd : Measurable d)
    (μ : Measure (Combinatorics.Branching.Step α Mark))
    [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization (⟨d, hd⟩ : Potential Mark) μ)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ n, MeasurableSet (window n))
    (hzero : 0 ∈ window 0)
    (upper : ℕ → ℝ) (hupper : ∀ n, window n ⊆ Set.Iic (upper n))
    (N T : ℕ) :
    let P := ofRestartedRealPositionSets initialPosition d hd
      (RootIndexed.initialPopulation (α := α) roots)
      (by simp [RootIndexed.mem_initialPopulation_iff])
      cutoff window hwindow upper hupper
    (RootIndexed.stepFieldLaw (Root := Root) μ) (P.capacityEvent N T)ᶜ ≤
      ∑ k : Fin (T + 1),
        (∑ r ∈ roots, ∫⁻ increment,
          ENNReal.ofReal (Real.exp (partialSum k increment)) *
            restartedWindowTest cutoff window
              (history k (initialPosition r) increment)
          ∂tiltedIncrementFieldLaw (⟨d, hd⟩ : Potential Mark) μ) /
          (N + 1 : ℕ) := by
  dsimp only
  let P := ofRestartedRealPositionSets initialPosition d hd
    (RootIndexed.initialPopulation (α := α) roots)
    (by simp [RootIndexed.mem_initialPopulation_iff])
    cutoff window hwindow upper hupper
  calc
    (RootIndexed.stepFieldLaw (Root := Root) μ) (P.capacityEvent N T)ᶜ ≤
        ∑ k : Fin (T + 1),
          (∫⁻ field, P.size k field
            ∂RootIndexed.stepFieldLaw (Root := Root) μ) / (N + 1 : ℕ) :=
      P.measure_capacityEvent_compl_le_lintegral
        (RootIndexed.stepFieldLaw (Root := Root) μ) N T
        (fun k => (RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := Mark)).le k)
    _ ≤ ∑ k : Fin (T + 1),
        (∑ r ∈ roots, ∫⁻ increment,
          ENNReal.ofReal (Real.exp (partialSum k increment)) *
            restartedWindowTest cutoff window
              (history k (initialPosition r) increment)
          ∂tiltedIncrementFieldLaw (⟨d, hd⟩ : Potential Mark) μ) /
          (N + 1 : ℕ) := by
      apply Finset.sum_le_sum
      intro k _
      gcongr
      exact lintegral_size_le_sum_spine_restartedWindow roots initialPosition
        d hd μ hboundary cutoff window hwindow hzero upper hupper k

/-- A uniform one-dimensional tube estimate implies the finite-root capacity
bound. This is the separation point between the branching argument and the
random-walk small-deviation argument: the latter only has to establish
`HasRestartedWindowFirstMomentBound` for the tilted increment law. -/
theorem measure_capacityEvent_compl_le_card_mul_sum_of_windowFirstMomentBound
    {Root α Mark : Type*} [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    (roots : Finset Root) (initialPosition : Root → ℝ) (d : Mark → ℝ)
    (hd : Measurable d)
    (μ : Measure (Combinatorics.Branching.Step α Mark))
    [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization (⟨d, hd⟩ : Potential Mark) μ)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ n, MeasurableSet (window n))
    (hzero : 0 ∈ window 0)
    (upper : ℕ → ℝ) (hupper : ∀ n, window n ⊆ Set.Iic (upper n))
    (initialSet : Set ℝ) (bound : ℕ → ENNReal)
    (hinitial : ∀ r ∈ roots, initialPosition r ∈ initialSet)
    (hbound : HasRestartedWindowFirstMomentBound
      (tiltedIncrementFieldLaw (⟨d, hd⟩ : Potential Mark) μ)
      cutoff window initialSet bound)
    (N T : ℕ) :
    let P := ofRestartedRealPositionSets initialPosition d hd
      (RootIndexed.initialPopulation (α := α) roots)
      (by simp [RootIndexed.mem_initialPopulation_iff])
      cutoff window hwindow upper hupper
    (RootIndexed.stepFieldLaw (Root := Root) μ) (P.capacityEvent N T)ᶜ ≤
      (roots.card : ENNReal) *
        (∑ k : Fin (T + 1), bound k) / (N + 1 : ℕ) := by
  dsimp only
  calc
    (RootIndexed.stepFieldLaw (Root := Root) μ)
        ((ofRestartedRealPositionSets initialPosition d hd
          (RootIndexed.initialPopulation (α := α) roots)
          (by simp [RootIndexed.mem_initialPopulation_iff])
          cutoff window hwindow upper hupper).capacityEvent N T)ᶜ ≤
        ∑ k : Fin (T + 1),
          (∑ r ∈ roots, restartedWindowFirstMoment
            (tiltedIncrementFieldLaw (⟨d, hd⟩ : Potential Mark) μ)
            cutoff window k (initialPosition r)) / (N + 1 : ℕ) := by
      simpa only [restartedWindowFirstMoment] using
        measure_capacityEvent_compl_le_sum_spine_restartedWindow
          roots initialPosition d hd μ hboundary cutoff window hwindow hzero
          upper hupper N T
    _ ≤ ∑ k : Fin (T + 1),
        ((roots.card : ENNReal) * bound k) / (N + 1 : ℕ) := by
      apply Finset.sum_le_sum
      intro k _
      gcongr
      calc
        (∑ r ∈ roots, restartedWindowFirstMoment
            (tiltedIncrementFieldLaw (⟨d, hd⟩ : Potential Mark) μ)
            cutoff window k (initialPosition r)) ≤
            ∑ _r ∈ roots, bound k := by
          apply Finset.sum_le_sum
          intro r hr
          exact hbound k (initialPosition r) (hinitial r hr)
        _ = (roots.card : ENNReal) * bound k := by simp
    _ = (roots.card : ENNReal) *
        (∑ k : Fin (T + 1), bound k) / (N + 1 : ℕ) := by
      rw [ENNReal.mul_div_right_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [ENNReal.mul_div_right_comm]

/-- A horizontal-tube estimate for the tilted one-step law gives the complete
finite-root capacity bound for the restarted killed population.  All
branching information has disappeared from the right-hand side except for
the number of initial roots. -/
theorem measure_capacityEvent_compl_le_horizontalTubeBound
    {Root α Mark : Type*} [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    (roots : Finset Root) (initialPosition : Root → ℝ) (d : Mark → ℝ)
    (hd : Measurable d)
    (μ : Measure (Combinatorics.Branching.Step α Mark))
    [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization (⟨d, hd⟩ : Potential Mark) μ)
    {a width : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hwidth : 0 ≤ width)
    (cutoff N T : ℕ) :
    let window : ℕ → Set ℝ :=
      fun _ => Set.Icc (-a * width) ((1 - a) * width)
    let P := ofRestartedRealPositionSets initialPosition d hd
      (RootIndexed.initialPopulation (α := α) roots)
      (by simp [RootIndexed.mem_initialPopulation_iff])
      cutoff window (fun _ => measurableSet_Icc)
      (fun _ => (1 - a) * width) (fun _ => Set.Icc_subset_Iic_self)
    (RootIndexed.stepFieldLaw (Root := Root) μ) (P.capacityEvent N T)ᶜ ≤
      (roots.card : ENNReal) *
        (∑ k : Fin (T + 1),
          ENNReal.ofReal (Real.exp
            (if (k : ℕ) ≤ cutoff then (1 - a) * width
              else (1 - a) * width + (1 - a) * width)) *
          if (k : ℕ) ≤ cutoff then
            RandomWalk.horizontalTubeProbability
              (tiltedIncrementFieldLaw
                (⟨d, hd⟩ : Potential Mark) μ) a width k
          else
            RandomWalk.horizontalTubeProbability
                (tiltedIncrementFieldLaw
                  (⟨d, hd⟩ : Potential Mark) μ) a width cutoff *
              RandomWalk.horizontalTubeProbability
                (tiltedIncrementFieldLaw
                  (⟨d, hd⟩ : Potential Mark) μ) a width (k - cutoff)) /
          (N + 1 : ℕ) := by
  dsimp only
  let ν := tiltedPotentialLaw (⟨d, hd⟩ : Potential Mark) (-1) μ
  let _ : IsProbabilityMeasure ν :=
    tiltedPotentialLaw_isProbability (⟨d, hd⟩ : Potential Mark) μ hboundary
  have hfield : RandomWalk.independentIncrementLaw ν =
      tiltedIncrementFieldLaw (⟨d, hd⟩ : Potential Mark) μ := by
    rfl
  have hbound := hasRestartedWindowFirstMomentBound_horizontal
    ν ha0 ha1 hwidth cutoff (Set.univ : Set ℝ)
  rw [hfield] at hbound
  apply measure_capacityEvent_compl_le_card_mul_sum_of_windowFirstMomentBound
    roots initialPosition d hd μ hboundary cutoff
    (fun _ => Set.Icc (-a * width) ((1 - a) * width))
    (fun _ => measurableSet_Icc)
    (by constructor <;> nlinarith)
    (fun _ => (1 - a) * width) (fun _ => Set.Icc_subset_Iic_self)
    Set.univ _ (fun _ _ => Set.mem_univ _) hbound N T

end RootIndexed.CausalPopulation
end ProbabilityTheory.BranchingRandomWalk
