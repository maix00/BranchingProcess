/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Lemmas.PositivePart
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Path
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.SampledMark
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Measurability
import Combinatorics.BranchingWalk.Step.Selection.Potential
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# First-moment estimate for a selected path

The pathwise positive-part estimate for the selected-path BRW can
be integrated using the fixed-generation marginal law of its predictably
sampled steps. The only moment assumption is a first moment for the one-step
selected-edge observable. The estimate concerns the causal selected-path BRW;
the retrospective restart is treated as a separate process.

## Internal proof declarations

* `eLpNorm_cutoff_add_selectedMarkSum_le` bounds the $L^2$ norm of the cutoff
  envelope by $H(M+\|(\Xi_1)_+\|_2)$.

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
open scoped BigOperators ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Lemmas

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
        (ω r (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.selectedPath
          (firstOrBelowPotential R φ M) r k ω)).IsOrderedBy φ)
    (hnonempty : ∀ᵐ ω ∂RootIndexed.stepFieldLaw (Root := Root) μ,
      ∀ k < n,
        (R (ω r (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.selectedPath
          (firstOrBelowPotential R φ M) r k ω))).Nonempty)
    :
    (∫ ω, max 0 (Spine.pathPotential φ (ω r)
      (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.selectedPath
        (firstOrBelowPotential R φ M) r n ω))
      ∂RootIndexed.stepFieldLaw (Root := Root) μ) ≤
      M * (n : ℝ) + (n : ℝ) *
        (∫ ξ, firstSelectedSlotPositivePotential R φ ξ ∂μ) := by
  let P := RootIndexed.stepFieldLaw (Root := Root) μ
  let S := firstOrBelowPotential R φ M
  let g := firstSelectedSlotPositivePotential R φ
  let endpoint : RootIndexed.StepField Root α X → ℝ := fun ω =>
    max 0 (Spine.pathPotential φ (ω r) (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.selectedPath S r n ω))
  let selectedPathBound : RootIndexed.StepField Root α X → ℝ := fun ω =>
    M * (n : ℝ) + ∑ k ∈ Finset.range n,
      g (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.step S r k ω)

  have hS : Measurable S.select := by
    simpa [S] using firstOrBelowPotential_measurable R hR φ M

  have hsampleIntegrable (k : ℕ) :
      Integrable (fun ω => g (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.step S r k ω)) P := by
    have hlaw := ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.step_law μ S hS r k
    have hmap : Integrable g (P.map (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.step S r k)) := by
      rw [hlaw]
      exact honeStep
    exact hmap.comp_measurable
      (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.step_measurable S hS r k)

  have hsumIntegrable : Integrable
      (fun ω => ∑ k ∈ Finset.range n,
        g (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.step S r k ω)) P := by
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
    have h := ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Lemmas.positivePart_le_cutoff_add_firstSelectedChildSum
      R hRcap φ M hM r n ω hωordered hωnonempty
    simpa [endpoint, selectedPathBound, S, g,
      firstSelectedSlotPositivePotential, ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.step] using h

  have hpath : Measurable[
      RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) n]
      (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.selectedPath S r n) :=
    ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.adapted S hS r n
  have hposition : Measurable[
      RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) n]
      (fun ω => RootIndexed.position (fun _ : Root => (0 : ℝ)) φ ω r
        (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.selectedPath S r n ω)) :=
    RootIndexed.selectedPositionAtGeneration_measurable_of_countableAddress
      (fun _ : Root => (0 : ℝ)) (fun x => φ x) φ.measurable_toFun n r
      (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.selectedPath S r n) hpath
      (fun ω => ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.depth S r ω n)
  have hpositionFull : Measurable (fun ω =>
      RootIndexed.position (fun _ : Root => (0 : ℝ)) φ ω r
        (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.selectedPath S r n ω)) :=
    hposition.mono (RootIndexed.stepFiltration.le n) le_rfl
  have hendpointMeas : Measurable endpoint := by
    have heq : endpoint = fun ω => max 0
        (RootIndexed.position (fun _ : Root => (0 : ℝ)) φ ω r
          (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.selectedPath S r n ω)) := by
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
        g (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.step S r k ω) ∂P) =
        ∑ k ∈ Finset.range n,
          ∫ ω, g (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.step S r k ω) ∂P := by
    exact integral_finsetSum (Finset.range n)
      (fun k hk => hsampleIntegrable k)
  have htermIntegral (k : ℕ) :
      (∫ ω, g (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.step S r k ω) ∂P) =
        ∫ ξ, g ξ ∂μ := by
    exact ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.integral_step_observable μ S hS r k g honeStep
  calc
    (∫ ω, endpoint ω ∂P) ≤ ∫ ω, selectedPathBound ω ∂P := hintegralBound
    _ = M * (n : ℝ) + (n : ℝ) * (∫ ξ, g ξ ∂μ) := by
      rw [show selectedPathBound = fun ω => M * (n : ℝ) +
        ∑ k ∈ Finset.range n, g (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.step S r k ω) by
          funext ω; rfl]
      rw [integral_add (integrable_const _) hsumIntegrable]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      rw [hsumIntegral]
      simp_rw [htermIntegral]
      simp [g, firstSelectedSlotPositivePotential]

set_option maxHeartbeats 600000 in
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath (Coupling.step Coupling.step_law Coupling.step_measurable) in
/-- Minkowski's inequality for the cutoff and the predictable first-child
marks sampled before a finite horizon. Each sampled mark has the original
one-step law. -/
lemma eLpNorm_cutoff_add_selectedMarkSum_le
    {Root α X : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (B : Step.FiniteSelection α X) (hB : Measurable B.select)
    (φ : Potential X) (M : ℝ) (hM : 0 ≤ M) (r : Root) (H : ℕ)
    (hmark : MemLp (firstSelectedSlotPositivePotential B φ) 2 μ) :
    let R := firstOrBelowPotential B φ M
    let P := RootIndexed.stepFieldLaw (Root := Root) μ
    eLpNorm (fun ω => M * (H : ℝ) + ∑ j ∈ Finset.range H,
      firstSelectedSlotPositivePotential B φ (Coupling.step R r j ω)) 2 P ≤
        (H : ℝ≥0∞) *
          (ENNReal.ofReal M + eLpNorm (firstSelectedSlotPositivePotential B φ) 2 μ) := by
  intro R P
  let g := firstSelectedSlotPositivePotential B φ
  let marks (j : ℕ) := g ∘ Coupling.step R r j
  have hR : Measurable R.select := firstOrBelowPotential_measurable B hB φ M
  have hlaw (j : ℕ) : eLpNorm (marks j) 2 P = eLpNorm g 2 μ := by
    have hm := Coupling.step_law μ R hR r j
    have hg : AEStronglyMeasurable g (P.map (Coupling.step R r j)) := by
      rw [hm]
      exact hmark.aestronglyMeasurable
    exact (eLpNorm_map_measure hg (Coupling.step_measurable R hR r j).aemeasurable).symm.trans
      (by rw [hm])
  have hconst : eLpNorm (fun _ : RootIndexed.StepField Root α X => M * (H : ℝ)) 2 P =
      ENNReal.ofReal M * (H : ℝ≥0∞) := by
    rw [eLpNorm_const' _ (by norm_num) (by simp)]
    simp [Real.eNorm_eq_ofReal (mul_nonneg hM (Nat.cast_nonneg _)),
      ENNReal.ofReal_mul hM]
  have hfun : (fun ω => M * (H : ℝ) + ∑ j ∈ Finset.range H, g (Coupling.step R r j ω)) =
      (fun _ => M * (H : ℝ)) + ∑ j ∈ Finset.range H, marks j := by
    funext ω
    simp [Finset.sum_apply, marks]
  change eLpNorm (fun ω => M * (H : ℝ) + ∑ j ∈ Finset.range H, g (Coupling.step R r j ω))
    2 P ≤ _
  rw [hfun]
  calc
    _ ≤ eLpNorm (fun _ => M * (H : ℝ)) 2 P +
        ∑ j ∈ Finset.range H, eLpNorm (marks j) 2 P :=
      (eLpNorm_add_le (p := 2) (by norm_num)).trans
        (add_le_add_right (eLpNorm_sum_le (p := 2) (by norm_num)) _)
    _ = _ := by
      simp [hconst, hlaw, g, mul_add, mul_comm]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Lemmas
