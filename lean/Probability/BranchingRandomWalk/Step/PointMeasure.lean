module

public import Combinatorics.BranchingWalk.Step.PointMeasure
public import Combinatorics.BranchingWalk.Step.ExponentialWeight
public import Combinatorics.BranchingWalk.Step.Measurability
public import Probability.PointProcess.Tilted
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# The branching point measure in slot coordinates

The point measure of a branching step is the Dirac sum of its realized children,
`stepPointMeasure ξ = Measure.sum (stepAtomMeasure ξ)`, and both of those live in
`Combinatorics/BranchingWalk/Step/PointMeasure.lean` together with their measurability in the step. This file
records what the child-slot reading of it says: the mass counts slots, so equal positions keep their
multiplicity, and the mass is zero exactly for a step with no child. The statements are generic in the slot
type and in the mark type; the exponential integral at the end is the thesis's boundary weight and needs real
marks.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching MeasureTheory

/-- Evaluation counts raw slots, so equal positions retain multiplicity. -/
theorem stepPointMeasure_apply_children {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) (s : Set X) (hs : MeasurableSet s) :
    stepPointMeasure ξ s =
      ∑' i : ι, (ξ i).elim 0 (fun x => s.indicator (1 : X → ENNReal) x) := by
  classical
  rw [stepPointMeasure, Measure.sum_apply _ hs]
  refine tsum_congr (fun i => ?_)
  cases h : ξ i with
  | none => simp [stepAtomMeasure, h]
  | some x => simp [stepAtomMeasure, h, Measure.dirac_apply' _ hs]

/-- The Dirac-sum point measure is zero exactly for a step with no child. -/
theorem stepPointMeasure_eq_zero_iff {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) :
    stepPointMeasure ξ = 0 ↔ ξ ∉ nonemptySupport := by
  constructor
  · intro hzero hnonempty
    obtain ⟨i, hi⟩ := hnonempty
    have hmass := stepPointMeasure_apply_children ξ Set.univ MeasurableSet.univ
    rw [hzero] at hmass
    have hterm : (ξ i).elim 0 (fun _ => (1 : ENNReal)) = 1 := by
      rcases hi with ⟨x, hx⟩
      simp [hx]
    have hall : ∀ j : ι, (ξ j).elim 0 (fun _ => (1 : ENNReal)) = 0 :=
      ENNReal.tsum_eq_zero.mp (by simpa using hmass.symm)
    have halli := hall i
    rw [hterm] at halli
    exact one_ne_zero halli
  · intro hempty
    apply Measure.ext
    intro s hs
    rw [stepPointMeasure_apply_children ξ s hs]
    have habsent : ∀ i : ι, ¬ survive ξ i := by
      intro i hi
      exact hempty ⟨i, hi⟩
    have hterm : ∀ i : ι,
        (ξ i).elim 0 (fun x => s.indicator (1 : X → ENNReal) x) = 0 := by
      intro i
      cases h : ξ i with
      | none => rfl
      | some x => exact (habsent i ⟨x, h⟩).elim
    simp [hterm]

/-- Integration of the exponential test against the point measure is exactly the slotwise total exponential
weight used in the thesis — the paper's `ψ` at real marks. -/
theorem lintegral_stepPointMeasure_exp {ι : Type*} (ξ : Step ι ℝ) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-x))
      ∂stepPointMeasure ξ) = totalChildWeight ξ := by
  rw [stepPointMeasure, lintegral_sum_measure]
  unfold totalChildWeight
  congr 1
  funext i
  by_cases hi : survive ξ i
  · obtain ⟨x, hx⟩ := hi
    have hval : value' ξ i = x := value'_some ξ i x hx
    have hsurv : survive ξ i := ⟨x, hx⟩
    simp [stepAtomMeasure, hx, realizedChildWeight, hsurv, hval,
      lintegral_dirac]
  · have hnone : ξ i = none := by
      cases h : ξ i with
      | none => rfl
      | some y => exact absurd ⟨y, h⟩ hi
    simp [stepAtomMeasure, hnone, realizedChildWeight, hi]

/-- Integrating a potential test against the point measure is the slotwise
sum over present children.  This identity itself does not require the slot
type or the ambient mark space to be countable. -/
theorem lintegral_stepPointMeasure_potential
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (ξ : Step ι X)
    {f : ℝ → ENNReal} (hf : Measurable f) :
    (∫⁻ x, ProbabilityTheory.PointProcess.exponentialWeight φ θ x * f (φ x)
        ∂stepPointMeasure ξ) =
      ∑' i : ι, realizedPotentialWeight φ θ ξ i *
        f (ξ.potentialValue' φ i) := by
  rw [stepPointMeasure, lintegral_sum_measure]
  apply tsum_congr
  intro i
  cases hi : ξ i with
  | none =>
      simp [stepAtomMeasure, hi, realizedPotentialWeight, survive]
  | some x =>
      have hsurvive : survive ξ i := ⟨x, hi⟩
      have hvalue : ξ.potentialValue' φ i = φ x := by
        simp [Step.potentialValue', Step.potentialAt?, hi]
      rw [stepAtomMeasure]
      simp only [hi, Option.elim_some]
      rw [lintegral_dirac' x]
      · simp [realizedPotentialWeight, hsurvive, hvalue,
          ProbabilityTheory.PointProcess.exponentialWeight]
      · exact ((ProbabilityTheory.PointProcess.exponentialWeight_measurable
          φ.measurable_toFun θ).mul (hf.comp φ.measurable_toFun))

end ProbabilityTheory.BranchingRandomWalk
