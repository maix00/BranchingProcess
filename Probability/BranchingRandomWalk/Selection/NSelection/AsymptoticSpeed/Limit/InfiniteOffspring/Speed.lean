/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.Repair
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.SubadditiveArray
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.KingmanLimit
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Environment.Basic
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Selection.Infinite
import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.Kingman.Lemmas.ArrayBounds
import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.Kingman.Lemmas.Convergence

/-!
# Leftmost speed for countable-offspring selection

- `infiniteOffspringRun_leftmost_ae_hasAsymptoticSpeed`: if the repaired
  subadditive array is integrable and its normalized expectations are bounded
  below, then the rank-zero path has an almost-sure deterministic speed.
- `infiniteOffspringRun_leftmost_ae_hasAsymptoticSpeed_of_stepLaw`: under the
  boundary normalization, nonempty support, and leftmost first-moment
  assumptions on a `StepLaw`, the ordered potential-projected process has an
  almost-sure leftmost speed.
- `infiniteOffspringRun_leftmost_ae_hasAsymptoticSpeed_and_L1_of_stepLaw`:
  under the same `StepLaw` assumptions, the rank-zero path has that speed and
  its normalized error converges to zero in `L¹`.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

theorem infiniteOffspringRun_leftmost_ae_hasAsymptoticSpeed {N : ℕ}
    (hN : 0 < N) (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (hint : ∀ n, Integrable
      (fun ω : GenerationEnvironment N =>
        repairedInfiniteSelectionSubadditiveArray hN ω 0 n)
      (generationEnvironmentLaw μ N))
    (hbdd : BddBelow (Set.range fun n : ℕ =>
      (∫ ω, repairedInfiniteSelectionSubadditiveArray hN ω 0 (n + 1)
        ∂generationEnvironmentLaw μ N) / (n + 1))) :
    ∃ c : ℝ, ∀ᵐ ω ∂generationEnvironmentLaw μ N,
      ∃ hgood : ∀ t, IsGoodInfiniteOffspringBatch (ω t),
        Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
          (𝕜 := ℝ)
          (fun n => infiniteOffspringRun ω hgood (fun _ => 0) n ⟨0, hN⟩)
          (-c) := by
  obtain ⟨c, hconv⟩ := infiniteSelection_tendsto_constant
    hN μ hboundary hnonempty hint hbdd
  refine ⟨c, ?_⟩
  filter_upwards [hconv] with ω hω
  rcases hω with ⟨hgood, hlim⟩
  refine ⟨hgood, ?_⟩
  change Tendsto
    (fun n : ℕ => (n : ℝ)⁻¹ *
      infiniteOffspringRun ω hgood (fun _ => 0) n ⟨0, hN⟩)
    atTop (𝓝 (-c))
  refine hlim.neg.congr' ?_
  filter_upwards [] with n
  simp [infiniteSelectionSubadditiveArray, infiniteSelectionBlockMinimum]

/-- The ordered, potential-projected realization has an almost-sure
leftmost speed under the separate boundary, nonempty-offspring, and
leftmost first-moment assumptions. The integrability and normalized lower
bound required by Kingman are derived internally from those assumptions. -/
theorem infiniteOffspringRun_leftmost_ae_hasAsymptoticSpeed_of_stepLaw
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    {N : ℕ} (hN : 0 < N) (L : StepLaw ι ℕ X)
    [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1)
    (hfirst : HasLeftmostFirstMoment L) :
    ∃ c : ℝ,
      ∀ᵐ ω ∂generationEnvironmentLaw L.sortedPotentialImage N,
        ∃ hgood : ∀ t, IsGoodInfiniteOffspringBatch (ω t),
          Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
            (𝕜 := ℝ)
            (fun n => infiniteOffspringRun ω hgood (fun _ => 0) n ⟨0, hN⟩)
            (-c) := by
  let μ := L.sortedPotentialImage
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hboundaryμ : HasBoundaryNormalization realPotential μ :=
    L.sortedPotentialImage_hasBoundaryNormalization hboundary
  have hnonemptyμ : μ nonemptySupport = 1 := by
    rw [show μ = L.sortedPotentialImage from rfl,
      L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport]
    exact hnonempty
  have horderedμ : μ (orderedBySteps realPotential) = 1 := by
    rw [show μ = L.sortedPotentialImage from rfl,
      L.sortedPotentialImage_orderedBy]
    simp
  have hslot : Integrable (fun ξ : Step ℕ ℝ => |value' ξ 0|) μ :=
    L.integrable_sortedPotentialImage_firstSlot_abs hboundary hfirst
  have hint : ∀ n, Integrable
      (fun ω : GenerationEnvironment N =>
        repairedInfiniteSelectionSubadditiveArray hN ω 0 n)
      (generationEnvironmentLaw μ N) := by
    intro n
    exact repairedInfiniteSelectionSubadditiveArray_integrable_of_leftmostMoment
      hN μ hboundaryμ hnonemptyμ horderedμ hslot n
  have hbdd := repairedInfiniteSelection_normalizedIntegral_bddBelow_of_leftmostMoment
    hN μ hboundaryμ hnonemptyμ horderedμ hslot
  exact infiniteOffspringRun_leftmost_ae_hasAsymptoticSpeed
    hN μ hboundaryμ hnonemptyμ hint hbdd

/-! The speed and `L¹` conclusions for exactly `N` particles, in the
`StepLaw` assumptions, are packaged together here. The rightmost result is
obtained by applying this theorem to the OrderDual/reflected law, with its own
right-side moment assumptions; no reflection invariance is required. -/
theorem infiniteOffspringRun_leftmost_ae_hasAsymptoticSpeed_and_L1_of_stepLaw
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    {N : ℕ} (hN : 0 < N) (L : StepLaw ι ℕ X)
    [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1)
    (hfirst : HasLeftmostFirstMoment L) :
    ∃ c : ℝ,
      (∀ᵐ ω ∂generationEnvironmentLaw L.sortedPotentialImage N,
        ∃ hgood : ∀ t, IsGoodInfiniteOffspringBatch (ω t),
          Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
            (𝕜 := ℝ)
            (fun n => infiniteOffspringRun ω hgood (fun _ => 0) n ⟨0, hN⟩)
            (-c)) ∧
      Tendsto
        (fun n : ℕ => eLpNorm
          (fun ω : GenerationEnvironment N =>
            (n : ℝ)⁻¹ * measurableRepairedInfiniteOffspringRun n
              ((fun _ : Fin N => (0 : ℝ)), ω) ⟨0, hN⟩ - (-c))
          (1 : ℝ≥0∞) (generationEnvironmentLaw L.sortedPotentialImage N))
        atTop (𝓝 0) := by
  let μ := L.sortedPotentialImage
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hboundaryμ : HasBoundaryNormalization realPotential μ :=
    L.sortedPotentialImage_hasBoundaryNormalization hboundary
  have hnonemptyμ : μ nonemptySupport = 1 := by
    rw [show μ = L.sortedPotentialImage from rfl,
      L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport]
    exact hnonempty
  have horderedμ : μ (orderedBySteps realPotential) = 1 := by
    rw [show μ = L.sortedPotentialImage from rfl,
      L.sortedPotentialImage_orderedBy]
    simp
  have hslot : Integrable (fun ξ : Step ℕ ℝ => |value' ξ 0|) μ :=
    L.integrable_sortedPotentialImage_firstSlot_abs hboundary hfirst
  let ν := generationEnvironmentLaw μ N
  haveI : IsProbabilityMeasure ν := generationEnvironmentLaw_isProbability μ N
  obtain ⟨c, hconv, hL1⟩ :=
    repairedInfiniteSelection_tendsto_constant_L1_of_leftmostMoment
      hN μ hboundaryμ hnonemptyμ horderedμ hslot
  have hgood : ∀ᵐ ω ∂ν, ∀ t, IsGoodInfiniteOffspringBatch (ω t) :=
    generationEnvironmentLaw_ae_allGood μ hboundaryμ hnonemptyμ N
  have hconvOriginal : ∀ᵐ ω ∂ν,
      ∃ hgood : ∀ t, IsGoodInfiniteOffspringBatch (ω t),
        Tendsto
          (fun n : ℕ => (n : ℝ)⁻¹ *
            infiniteSelectionSubadditiveArray hN ω hgood 0 n)
          atTop (𝓝 c) := by
    filter_upwards [hgood, hconv] with ω hgoodω hω
    refine ⟨hgoodω, ?_⟩
    apply hω.congr'
    filter_upwards [] with n
    rw [← repairedInfiniteSelectionSubadditiveArray_eq_of_allGood
      hN ω hgoodω 0 n]
  have hspeed : ∀ᵐ ω ∂ν,
      ∃ hgood : ∀ t, IsGoodInfiniteOffspringBatch (ω t),
        Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
          (𝕜 := ℝ)
          (fun n => infiniteOffspringRun ω hgood (fun _ => 0) n ⟨0, hN⟩)
          (-c) := by
    filter_upwards [hconvOriginal] with ω hω
    rcases hω with ⟨hgoodω, hlim⟩
    refine ⟨hgoodω, ?_⟩
    change Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ *
        infiniteOffspringRun ω hgoodω (fun _ => 0) n ⟨0, hN⟩)
      atTop (𝓝 (-c))
    have hneg := hlim.neg
    apply hneg.congr'
    filter_upwards [] with n
    simp [infiniteSelectionSubadditiveArray, infiniteSelectionBlockMinimum]
  let P : ℕ → GenerationEnvironment N → ℝ := fun n ω =>
    measurableRepairedInfiniteOffspringRun n
      ((fun _ : Fin N => (0 : ℝ)), ω) ⟨0, hN⟩
  have hL1position : Tendsto
      (fun n : ℕ => eLpNorm
        (fun ω : GenerationEnvironment N => (n : ℝ)⁻¹ * P n ω - (-c))
        (1 : ℝ≥0∞) ν) atTop (𝓝 0) := by
    have hnorm (n : ℕ) : eLpNorm
        (fun ω : GenerationEnvironment N => (n : ℝ)⁻¹ * P n ω - (-c))
        (1 : ℝ≥0∞) ν =
      eLpNorm
        (fun ω : GenerationEnvironment N =>
          (n : ℝ)⁻¹ * repairedInfiniteSelectionSubadditiveArray hN ω 0 n - c)
        (1 : ℝ≥0∞) ν := by
      have hfun : (fun ω : GenerationEnvironment N =>
          (n : ℝ)⁻¹ * P n ω - (-c)) =
        fun ω => -((n : ℝ)⁻¹ *
          repairedInfiniteSelectionSubadditiveArray hN ω 0 n - c) := by
        funext ω
        have harray : repairedInfiniteSelectionSubadditiveArray hN ω 0 n = -P n ω := by
          simp [P, repairedInfiniteSelectionSubadditiveArray]
        rw [harray]
        ring
      rw [hfun]
      exact eLpNorm_neg _ _ _
    have hseq : (fun n : ℕ => eLpNorm
        (fun ω : GenerationEnvironment N => (n : ℝ)⁻¹ * P n ω - (-c))
        (1 : ℝ≥0∞) ν) =
      fun (n : ℕ) => eLpNorm
        (fun ω : GenerationEnvironment N =>
          (n : ℝ)⁻¹ * repairedInfiniteSelectionSubadditiveArray hN ω 0 n - c)
        (1 : ℝ≥0∞) ν := by
      funext n
      exact hnorm n
    rw [hseq]
    simpa [ν, μ] using hL1
  exact ⟨c, by simpa [ν, μ] using hspeed, by simpa [ν, μ] using hL1position⟩

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
