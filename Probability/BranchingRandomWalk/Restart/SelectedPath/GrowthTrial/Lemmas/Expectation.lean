/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Lemmas.PositivePart
import Probability.BranchingRandomWalk.Restart.SelectedPath.Path
import Probability.BranchingRandomWalk.Restart.SelectedPath.Coupling.SampledMark
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Measurability
import Combinatorics.BranchingWalk.Step.Selection.Potential

/-!
# First-moment estimate for a selected path

The pathwise positive-part estimate for the selected-path BRW can
be integrated using the fixed-generation marginal law of its predictably
sampled steps. The only moment assumption is a first moment for the one-step
selected-edge observable. The estimate concerns the causal selected-path BRW;
the retrospective restart is treated as a separate process.

## Internal proof declarations

For a cutoff \(M\), the expected positive part of the selected-path
potential after \(n\) generations is bounded by the cutoff contribution and
the one-step first moment:

\[\mathbb E\!\left[\max\{0,\,S_n\}\right]
  \le Mn+n\,\mathbb E_\mu[Y^+],\]

where \(S_n\) is the selected-path potential and \(Y\) is the positive part of the
first-selected-slot potential.

- `integral_positivePart_le`: integrates the
  pathwise selected-path estimate to obtain a linear first-moment bound from
  the one-step selected-slot observable.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Lemmas

open Combinatorics.Branching Combinatorics.UlamHarris
open Combinatorics.Branching.Step.FiniteSelection

/-- Integrating the pathwise selected-path bound gives a linear first-moment
bound.  The hypotheses make all model inputs explicit: `R.select` is
measurable, the first-R-selected-slot positive potential is integrable under
the one-step law, and the ordered/nonempty assumptions hold almost surely at
each of the first `n` selected-path generations.  The endpoint's strong measurability
is included explicitly so the dominating integrable sum yields its
integrability.  No iid claim about the adaptive marks is used: only their
fixed-generation marginal expectation identity is needed. -/
lemma integral_positivePart_le
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hRcap : R.IsBoundedBy 2) (φ : Potential X) (M : ℝ) (hM : 0 ≤ M)
    (r : Root) (n : ℕ)
    (honeStep : Integrable (firstSelectedSlotPositivePotential R φ) μ)
    (hordered : ∀ᵐ ω ∂RootIndexed.stepFieldLaw (Root := Root) μ,
      ∀ k < n,
        (ω r (Restart.selectedPath
          (reserveSelectionBelowPotential R φ M) r k ω)).IsOrderedBy φ)
    (hnonempty : ∀ᵐ ω ∂RootIndexed.stepFieldLaw (Root := Root) μ,
      ∀ k < n,
        (R (ω r (Restart.selectedPath
          (reserveSelectionBelowPotential R φ M) r k ω))).Nonempty)
    :
    (∫ ω, max 0 (Spine.pathPotential φ (ω r)
      (Restart.selectedPath
        (reserveSelectionBelowPotential R φ M) r n ω))
      ∂RootIndexed.stepFieldLaw (Root := Root) μ) ≤
      M * (n : ℝ) + (n : ℝ) *
        (∫ ξ, firstSelectedSlotPositivePotential R φ ξ ∂μ) := by
  let P := RootIndexed.stepFieldLaw (Root := Root) μ
  let S := reserveSelectionBelowPotential R φ M
  let g := firstSelectedSlotPositivePotential R φ
  let endpoint : RootIndexed.StepField Root α X → ℝ := fun ω =>
    max 0 (Spine.pathPotential φ (ω r) (Restart.selectedPath S r n ω))
  let selectedPathBound : RootIndexed.StepField Root α X → ℝ := fun ω =>
    M * (n : ℝ) + ∑ k ∈ Finset.range n,
      g (Restart.SelectedPath.Coupling.step S r k ω)

  have hS : Measurable S.select := by
    simpa [S] using reserveSelectionBelowPotential_measurable R hR φ M

  have hsampleIntegrable (k : ℕ) :
      Integrable (fun ω => g (Restart.SelectedPath.Coupling.step S r k ω)) P := by
    have hlaw := Restart.SelectedPath.Coupling.step_law μ S hS r k
    have hmap : Integrable g (P.map (Restart.SelectedPath.Coupling.step S r k)) := by
      rw [hlaw]
      exact honeStep
    exact hmap.comp_measurable
      (Restart.SelectedPath.Coupling.step_measurable S hS r k)

  have hsumIntegrable : Integrable
      (fun ω => ∑ k ∈ Finset.range n,
        g (Restart.SelectedPath.Coupling.step S r k ω)) P := by
    exact integrable_finsetSum (Finset.range n) (fun k hk => hsampleIntegrable k)

  have hselectedPathBoundIntegrable : Integrable selectedPathBound P := by
    dsimp [selectedPathBound]
    exact (integrable_const (M * (n : ℝ))).add hsumIntegrable

  have hselectedPathBoundNonneg : ∀ ω, 0 ≤ selectedPathBound ω := by
    intro ω
    dsimp [selectedPathBound]
    apply add_nonneg
    · exact mul_nonneg hM (Nat.cast_nonneg _)
    · apply Finset.sum_nonneg
      intro k hk
      exact le_max_left 0 _

  have hpathwise : ∀ᵐ ω ∂P, endpoint ω ≤ selectedPathBound ω := by
    filter_upwards [hordered, hnonempty] with ω hωordered hωnonempty
    have h := Restart.SelectedPath.GrowthTrial.Lemmas.positivePart_le_cutoff_add_firstSelectedChildSum
      R hRcap φ M hM r n ω hωordered hωnonempty
    simpa [endpoint, selectedPathBound, S, g,
      firstSelectedSlotPositivePotential, Restart.SelectedPath.Coupling.step] using h

  have hpath : Measurable[
      RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) n]
      (Restart.selectedPath S r n) :=
    Restart.SelectedPath.adapted S hS r n
  have hposition : Measurable[
      RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) n]
      (fun ω => RootIndexed.position (fun _ : Root => (0 : ℝ)) φ ω r
        (Restart.selectedPath S r n ω)) :=
    RootIndexed.selectedPositionAtGeneration_measurable_of_countableAddress
      (fun _ : Root => (0 : ℝ)) (fun x => φ x) φ.measurable_toFun n r
      (Restart.selectedPath S r n) hpath
      (fun ω => Restart.SelectedPath.depth S r ω n)
  have hpositionFull : Measurable (fun ω =>
      RootIndexed.position (fun _ : Root => (0 : ℝ)) φ ω r
        (Restart.selectedPath S r n ω)) :=
    hposition.mono (RootIndexed.stepFiltration.le n) le_rfl
  have hendpointMeas : Measurable endpoint := by
    have heq : endpoint = fun ω => max 0
        (RootIndexed.position (fun _ : Root => (0 : ℝ)) φ ω r
          (Restart.selectedPath S r n ω)) := by
      funext ω
      simp [endpoint, RootIndexed.position, RootIndexed.displace,
        Spine.pathPotential, S]
    rw [heq]
    exact measurable_const.max hpositionFull

  have hendpointIntegrable : Integrable endpoint P := by
    apply hselectedPathBoundIntegrable.mono' hendpointMeas.aestronglyMeasurable
    filter_upwards [hpathwise] with ω hω
    simpa only [endpoint, Real.norm_eq_abs,
      abs_of_nonneg (le_max_left (0 : ℝ) _)] using hω

  have hintegralBound := integral_mono_ae hendpointIntegrable
    hselectedPathBoundIntegrable hpathwise
  have hsumIntegral :
      (∫ ω, ∑ k ∈ Finset.range n,
        g (Restart.SelectedPath.Coupling.step S r k ω) ∂P) =
        ∑ k ∈ Finset.range n,
          ∫ ω, g (Restart.SelectedPath.Coupling.step S r k ω) ∂P := by
    exact integral_finsetSum (Finset.range n)
      (fun k hk => hsampleIntegrable k)
  have htermIntegral (k : ℕ) :
      (∫ ω, g (Restart.SelectedPath.Coupling.step S r k ω) ∂P) =
        ∫ ξ, g ξ ∂μ := by
    exact Restart.SelectedPath.Coupling.integral_step_observable μ S hS r k g honeStep
  calc
    (∫ ω, endpoint ω ∂P) ≤ ∫ ω, selectedPathBound ω ∂P := hintegralBound
    _ = M * (n : ℝ) + (n : ℝ) * (∫ ξ, g ξ ∂μ) := by
      rw [show selectedPathBound = fun ω => M * (n : ℝ) +
        ∑ k ∈ Finset.range n, g (Restart.SelectedPath.Coupling.step S r k ω) by
          funext ω; rfl]
      rw [integral_add (integrable_const _) hsumIntegrable]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      rw [hsumIntegral]
      simp_rw [htermIntegral]
      simp [g, firstSelectedSlotPositivePotential]

end ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Lemmas
