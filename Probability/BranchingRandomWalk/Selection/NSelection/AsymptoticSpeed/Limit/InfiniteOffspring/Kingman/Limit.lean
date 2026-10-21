/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.Repair
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.SubadditiveArray
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Environment.Basic
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Selection.Infinite
import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.Kingman.Lemmas.ArrayBounds
import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.Kingman.Lemmas.Subadditivity
import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.Kingman.Lemmas.Convergence
public import Probability.Ergodic.Kingman.Core
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Kingman limits for the infinite-offspring selection array

- `repairedInfiniteSelection_tendsto_constant`: under integrability and a
  lower bound on normalized expectations, the repaired block array has an
  almost-sure deterministic normalized limit.
- `repairedInfiniteSelection_tendsto_constant_L1_of_leftmostMoment`: under
  the boundary, nonempty-support, ordered-support, and leftmost first-moment
  assumptions, the normalized array converges almost surely and in `L¹`.
- `infiniteSelection_tendsto_constant`: transfers the repaired limit to the
  original subadditive array on almost every valid environment.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

theorem repairedInfiniteSelection_tendsto_constant {N : ℕ}
    (hN : 0 < N) (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hint : ∀ n, Integrable
      (fun ω : GenerationEnvironment N =>
        repairedInfiniteSelectionSubadditiveArray hN ω 0 n)
      (generationEnvironmentLaw μ N))
    (hbdd : BddBelow (Set.range fun n : ℕ =>
      (∫ ω, repairedInfiniteSelectionSubadditiveArray hN ω 0 (n + 1)
        ∂generationEnvironmentLaw μ N) / (n + 1))) :
    ∃ c : ℝ, ∀ᵐ ω ∂generationEnvironmentLaw μ N,
      Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ *
          repairedInfiniteSelectionSubadditiveArray hN ω 0 n)
        atTop (𝓝 c) := by
  let ν := generationEnvironmentLaw μ N
  have hν : IsProbabilityMeasure ν := generationEnvironmentLaw_isProbability μ N
  letI := hν
  obtain ⟨G, hGinv, hGint, hGconv⟩ :=
    repairedInfiniteSelection_tendsto_invariant_integrable hN μ hint hbdd
  have hErg := generationEnvironmentShift_ergodic μ N
  obtain ⟨c, hc⟩ := hErg.ae_eq_const_of_ae_eq_comp_ae
    hGint.aestronglyMeasurable hGinv
  refine ⟨c, ?_⟩
  filter_upwards [hGconv, hc] with ω hω hωc
  simpa [hωc] using hω

/-- The first-row Kingman limit also holds in `L¹` under the same one-step
leftmost-child moment condition used to prove integrability and the lower
bound. The proof dominates the normalized endpoint array by averages of the
i.i.d. generation envelope, obtains uniform integrability from Mathlib's
uniform-integrability API, and applies Vitali convergence to the almost-sure
Kingman limit.

This is still the speed result for exactly `N` particles. It does not include
the extension from an initial population of size `N₀ ≤ N` to size
`N`; that extension needs a finite-time saturation/restart argument for the
root-indexed selected-population process. -/
theorem repairedInfiniteSelection_tendsto_constant_L1_of_leftmostMoment
    {N : ℕ} (hN : 0 < N) (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (hordered : μ (orderedBySteps realPotential) = 1)
    (hslot : Integrable (fun ξ : Step ℕ ℝ => |value' ξ 0|) μ) :
    ∃ c : ℝ,
      (∀ᵐ ω ∂generationEnvironmentLaw μ N,
        Tendsto
          (fun n : ℕ => (n : ℝ)⁻¹ *
            repairedInfiniteSelectionSubadditiveArray hN ω 0 n)
          atTop (𝓝 c)) ∧
      Tendsto
        (fun n : ℕ => eLpNorm
          (fun ω : GenerationEnvironment N =>
            (n : ℝ)⁻¹ * repairedInfiniteSelectionSubadditiveArray hN ω 0 n - c)
          (1 : ℝ≥0∞) (generationEnvironmentLaw μ N))
        atTop (𝓝 0) := by
  let ν := generationEnvironmentLaw μ N
  let D : ℕ → GenerationEnvironment N → ℝ := fun t ω =>
    infiniteOffspringBatchSlotZeroNorm hN (repairGenerationBatch (ω t))
  let f : ℕ → GenerationEnvironment N → ℝ := fun n ω =>
    (n : ℝ)⁻¹ * repairedInfiniteSelectionSubadditiveArray hN ω 0 n
  let g : ℕ → GenerationEnvironment N → ℝ := fun n ω =>
    (∑ t ∈ Finset.range n, D t ω) / (n : ℝ)
  have hν : IsProbabilityMeasure ν := generationEnvironmentLaw_isProbability μ N
  letI := hν
  have hDint (t : ℕ) : Integrable (D t) ν := by
    exact integrable_repairedInfiniteOffspringBatchSlotZeroNorm_at
      hN μ hboundary hnonempty hslot t
  have hD0 : MemLp (D 0) (1 : ℝ≥0∞) ν :=
    MeasureTheory.memLp_one_iff_integrable.mpr (hDint 0)
  have hbatchMeas : Measurable
      (fun batch : GenerationBatch N =>
        infiniteOffspringBatchSlotZeroNorm hN (repairGenerationBatch batch)) :=
    (measurable_infiniteOffspringBatchSlotZeroNorm hN).comp
      measurable_repairGenerationBatch
  have hcoord (t : ℕ) : IdentDistrib (fun ω : GenerationEnvironment N => ω t)
      (fun ω : GenerationEnvironment N => ω 0) ν ν := by
    refine ⟨(measurable_pi_apply t).aemeasurable,
      (measurable_pi_apply 0).aemeasurable, ?_⟩
    rw [generationEnvironmentLaw_generation_marginal μ N t,
      generationEnvironmentLaw_generation_marginal μ N 0]
  have hDident (t : ℕ) : IdentDistrib (D t) (D 0) ν ν := by
    simpa [D, Function.comp_def] using (hcoord t).comp hbatchMeas
  have hDui : UniformIntegrable D (1 : ℝ≥0∞) ν :=
    MemLp.uniformIntegrable_of_identDistrib (by norm_num) (by norm_num)
      hD0 hDident
  have havg : UniformIntegrable g (1 : ℝ≥0∞) ν := by
    have h := uniformIntegrable_average_real (p := (1 : ℝ≥0∞))
      (by norm_num) hDui
    convert h using 1
    ext n ω
    simp [g, D, div_eq_mul_inv, mul_comm]
  have hDnonneg (t : ℕ) (ω : GenerationEnvironment N) : 0 ≤ D t ω := by
    dsimp [D]
    unfold infiniteOffspringBatchSlotZeroNorm
    exact le_trans (abs_nonneg _) <| Finset.le_sup'
      (fun i : Fin N => |value' (repairGenerationBatch (ω t) i) 0|)
      (Finset.mem_univ ⟨0, hN⟩)
  have hg_nonneg (n : ℕ) (ω : GenerationEnvironment N) : 0 ≤ g n ω := by
    dsimp [g]
    exact div_nonneg (Finset.sum_nonneg fun t ht => hDnonneg t ω)
      (Nat.cast_nonneg n)
  have hdom (n : ℕ) : ∀ᵐ ω ∂ν, |f n ω| ≤ g n ω := by
    by_cases hn : n = 0
    · subst n
      filter_upwards [] with ω
      simp [f, g, repairedInfiniteSelectionSubadditiveArray]
    · filter_upwards [repairedInfiniteSelectionSubadditiveArray_ae_abs_le_envelope
        hN μ hordered hnonempty n] with ω hω
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hinv : 0 ≤ (n : ℝ)⁻¹ := (inv_nonneg.mpr hnpos.le)
      calc
        |f n ω| = (n : ℝ)⁻¹ *
            |repairedInfiniteSelectionSubadditiveArray hN ω 0 n| := by
              simp [f, abs_mul, abs_of_nonneg hinv]
        _ ≤ (n : ℝ)⁻¹ * (∑ t ∈ Finset.range n, D t ω) := by
              exact mul_le_mul_of_nonneg_left (by simpa [D] using hω) hinv
        _ = g n ω := by
              simp [g, div_eq_mul_inv, mul_comm]
  have hfmeas (n : ℕ) : AEStronglyMeasurable (f n) ν := by
    dsimp [f]
    exact (measurable_const.mul
      (measurable_repairedInfiniteSelectionSubadditiveArray hN 0 n)).aestronglyMeasurable
  have hui : UnifIntegrable f (1 : ℝ≥0∞) ν := by
    apply havg.unifIntegrable.ae_mono hfmeas
    intro n
    filter_upwards [hdom n] with ω hω
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (hg_nonneg n ω)]
    exact ENNReal.ofReal_le_ofReal hω
  have hint : ∀ n, Integrable
      (fun ω : GenerationEnvironment N =>
        repairedInfiniteSelectionSubadditiveArray hN ω 0 n) ν := by
    intro n
    exact repairedInfiniteSelectionSubadditiveArray_integrable_of_leftmostMoment
      hN μ hboundary hnonempty hordered hslot n
  have hbdd := repairedInfiniteSelection_normalizedIntegral_bddBelow_of_leftmostMoment
    hN μ hboundary hnonempty hordered hslot
  obtain ⟨c, hconv⟩ := repairedInfiniteSelection_tendsto_constant hN μ hint hbdd
  have hL1 : Tendsto
      (fun n : ℕ => eLpNorm (fun ω : GenerationEnvironment N => f n ω - c)
        (1 : ℝ≥0∞) ν) atTop (𝓝 0) := by
    apply MeasureTheory.tendsto_Lp_finite_of_tendsto_ae
      (μ := ν) (p := (1 : ℝ≥0∞)) (by norm_num) (by norm_num)
      (fun n => hfmeas n) (memLp_const c) hui
    simpa only [f] using hconv
  refine ⟨c, ?_, ?_⟩
  · simpa only [f] using hconv
  · simpa only [f] using hL1

/-- On an environment whose every generation is a valid transition, repairing
the environment leaves the deterministic selection array unchanged. -/
theorem infiniteSelection_tendsto_constant {N : ℕ}
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
        Tendsto
          (fun n : ℕ => (n : ℝ)⁻¹ *
            infiniteSelectionSubadditiveArray hN ω hgood 0 n)
          atTop (𝓝 c) := by
  obtain ⟨c, hconv⟩ := repairedInfiniteSelection_tendsto_constant
    hN μ hint hbdd
  refine ⟨c, ?_⟩
  filter_upwards [generationEnvironmentLaw_ae_allGood μ hboundary hnonempty N,
    hconv] with ω hgood hω
  refine ⟨hgood, ?_⟩
  apply hω.congr'
  filter_upwards [] with n
  rw [← repairedInfiniteSelectionSubadditiveArray_eq_of_allGood
    hN ω hgood 0 n]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
