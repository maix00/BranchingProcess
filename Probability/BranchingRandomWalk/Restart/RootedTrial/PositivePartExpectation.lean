/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.RootedTrial.PositivePart
import Probability.BranchingRandomWalk.Restart.RootedTrial.SampledMark
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Measurability

/-!
# First-moment estimate for a reserve spine

The pathwise positive-part estimate for the causal reserve spine can be
integrated using the fixed-generation marginal law of its predictably sampled
steps.  The result only assumes a first moment for the one-step observable;
it does not identify that observable with a paper-specific offspring mark, or
identify the causal reserve source with the retrospective restart process.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris

/-- The positive potential of the first slot selected by `R`.  This is an
observable of the selected slot, not a distinguished raw offspring mark. -/
noncomputable def firstRSelectedSlotPositivePotential
    {α X : Type*} [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (φ : Potential X) : Step α X → ℝ :=
  fun ξ => max 0 (ξ.potentialValue' φ (firstSelectedSlot R ξ))

/-- Integrating the pathwise reserve-spine bound gives a linear first-moment
bound.  The hypotheses make all model inputs explicit: `R.select` is
measurable, the first-R-selected-slot positive potential is integrable under
the one-step law, and the ordered/nonempty assumptions hold almost surely at
each of the first `n` spine generations.  The endpoint's strong measurability
is included explicitly so the dominating integrable sum yields its
integrability.  No iid claim about the adaptive marks is used: only their
fixed-generation marginal expectation identity is needed. -/
theorem integral_selectedReserveSpinePath_positivePart_le
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hRcap : R.IsBoundedBy 2) (φ : Potential X) (M : ℝ) (hM : 0 ≤ M)
    (r : Root) (n : ℕ)
    (honeStep : Integrable (firstRSelectedSlotPositivePotential R φ) μ)
    (hordered : ∀ᵐ ω ∂RootIndexed.stepFieldLaw (Root := Root) μ,
      ∀ k < n,
        (ω r (selectedReserveSpinePath
          (reserveSelectionBelowPotential R φ M) r k ω)).IsOrderedBy φ)
    (hnonempty : ∀ᵐ ω ∂RootIndexed.stepFieldLaw (Root := Root) μ,
      ∀ k < n,
        (R (ω r (selectedReserveSpinePath
          (reserveSelectionBelowPotential R φ M) r k ω))).Nonempty)
    :
    (∫ ω, max 0 (Spine.pathPotential φ (ω r)
      (selectedReserveSpinePath
        (reserveSelectionBelowPotential R φ M) r n ω))
      ∂RootIndexed.stepFieldLaw (Root := Root) μ) ≤
      M * (n : ℝ) + (n : ℝ) *
        (∫ ξ, firstRSelectedSlotPositivePotential R φ ξ ∂μ) := by
  let P := RootIndexed.stepFieldLaw (Root := Root) μ
  let S := reserveSelectionBelowPotential R φ M
  let g := firstRSelectedSlotPositivePotential R φ
  let endpoint : RootIndexed.StepField Root α X → ℝ := fun ω =>
    max 0 (Spine.pathPotential φ (ω r) (selectedReserveSpinePath S r n ω))
  let reserveBound : RootIndexed.StepField Root α X → ℝ := fun ω =>
    M * (n : ℝ) + ∑ k ∈ Finset.range n,
      g (selectedReserveSpineStep S r k ω)

  have hS : Measurable S.select := by
    simpa [S] using reserveSelectionBelowPotential_measurable R hR φ M

  have hsampleIntegrable (k : ℕ) :
      Integrable (fun ω => g (selectedReserveSpineStep S r k ω)) P := by
    have hlaw := selectedReserveSpineStep_law μ S hS r k
    have hmap : Integrable g (P.map (selectedReserveSpineStep S r k)) := by
      rw [hlaw]
      exact honeStep
    exact hmap.comp_measurable
      (selectedReserveSpineStep_measurable S hS r k)

  have hsumIntegrable : Integrable
      (fun ω => ∑ k ∈ Finset.range n,
        g (selectedReserveSpineStep S r k ω)) P := by
    exact integrable_finsetSum (Finset.range n) (fun k hk => hsampleIntegrable k)

  have hreserveBoundIntegrable : Integrable reserveBound P := by
    dsimp [reserveBound]
    exact (integrable_const (M * (n : ℝ))).add hsumIntegrable

  have hreserveBoundNonneg : ∀ ω, 0 ≤ reserveBound ω := by
    intro ω
    dsimp [reserveBound]
    apply add_nonneg
    · exact mul_nonneg hM (Nat.cast_nonneg _)
    · apply Finset.sum_nonneg
      intro k hk
      exact le_max_left 0 _

  have hpathwise : ∀ᵐ ω ∂P, endpoint ω ≤ reserveBound ω := by
    filter_upwards [hordered, hnonempty] with ω hωordered hωnonempty
    have h := selectedReserveSpinePath_positivePart_le_cutoff_add_firstChildSum
      R hRcap φ M hM r n ω hωordered hωnonempty
    simpa [endpoint, reserveBound, S, g,
      firstRSelectedSlotPositivePotential, selectedReserveSpineStep] using h

  have hpath : Measurable[
      RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) n]
      (selectedReserveSpinePath S r n) :=
    selectedReserveSpinePath_adapted S hS r n
  have hposition : Measurable[
      RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) n]
      (fun ω => RootIndexed.position (fun _ : Root => (0 : ℝ)) φ ω r
        (selectedReserveSpinePath S r n ω)) :=
    RootIndexed.selectedPositionAtGeneration_measurable_of_countableAddress
      (fun _ : Root => (0 : ℝ)) (fun x => φ x) φ.measurable_toFun n r
      (selectedReserveSpinePath S r n) hpath
      (fun ω => selectedReserveSpinePath_depth S r ω n)
  have hpositionFull : Measurable (fun ω =>
      RootIndexed.position (fun _ : Root => (0 : ℝ)) φ ω r
        (selectedReserveSpinePath S r n ω)) :=
    hposition.mono (RootIndexed.stepFiltration.le n) le_rfl
  have hendpointMeas : Measurable endpoint := by
    have heq : endpoint = fun ω => max 0
        (RootIndexed.position (fun _ : Root => (0 : ℝ)) φ ω r
          (selectedReserveSpinePath S r n ω)) := by
      funext ω
      simp [endpoint, RootIndexed.position, RootIndexed.displace,
        Spine.pathPotential, S]
    rw [heq]
    exact measurable_const.max hpositionFull

  have hendpointIntegrable : Integrable endpoint P := by
    apply hreserveBoundIntegrable.mono' hendpointMeas.aestronglyMeasurable
    filter_upwards [hpathwise] with ω hω
    simpa only [endpoint, Real.norm_eq_abs,
      abs_of_nonneg (le_max_left (0 : ℝ) _)] using hω

  have hintegralBound := integral_mono_ae hendpointIntegrable
    hreserveBoundIntegrable hpathwise
  have hsumIntegral :
      (∫ ω, ∑ k ∈ Finset.range n,
        g (selectedReserveSpineStep S r k ω) ∂P) =
        ∑ k ∈ Finset.range n,
          ∫ ω, g (selectedReserveSpineStep S r k ω) ∂P := by
    exact integral_finsetSum (Finset.range n)
      (fun k hk => hsampleIntegrable k)
  have htermIntegral (k : ℕ) :
      (∫ ω, g (selectedReserveSpineStep S r k ω) ∂P) =
        ∫ ξ, g ξ ∂μ := by
    exact integral_selectedReserveSpineStep_observable μ S hS r k g honeStep
  calc
    (∫ ω, endpoint ω ∂P) ≤ ∫ ω, reserveBound ω ∂P := hintegralBound
    _ = M * (n : ℝ) + (n : ℝ) * (∫ ξ, g ξ ∂μ) := by
      rw [show reserveBound = fun ω => M * (n : ℝ) +
        ∑ k ∈ Finset.range n, g (selectedReserveSpineStep S r k ω) by
          funext ω; rfl]
      rw [integral_add (integrable_const _) hsumIntegrable]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      rw [hsumIntegral]
      simp_rw [htermIntegral]
      simp [g, firstRSelectedSlotPositivePotential]

end ProbabilityTheory.BranchingRandomWalk
