module

public import Mathlib.Probability.BrownianMotion.Basic
public import Probability.Process.Levy.Basic

/-!
# Brownian motion as a Lévy process

Brownian motion is an instance of the general Lévy-process interface.  The
stable specialization is developed separately in `Probability.Process.Stable`.
-/

open MeasureTheory
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A Brownian motion is a Lévy process: its increments are stationary and
independent, it starts at zero, and its paths are càdlàg almost surely. -/
theorem IsBrownianReal.isLevyProcess
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) : IsLevyProcess B P := by
  let hpre := hB.toIsPreBrownianReal
  refine ⟨hpre.eval_zero_ae_eq_zero, hpre.hasIndepIncrements, ?_, ?_⟩
  · intro s t
    have hfirst : HasLaw (fun ω => B (s + t) ω - B s ω)
        (gaussianReal 0 t) P := by
      have h := hpre.hasLaw_sub (s + t) s
      change HasLaw (B (s + t) - B s)
        (gaussianReal 0 (nndist ((s + t : ℝ≥0) : ℝ) (s : ℝ))) P at h
      have hle : s ≤ s + t := by simp
      have hdist : nndist ((s + t : ℝ≥0) : ℝ) (s : ℝ) = t := by
        apply NNReal.eq
        rw [Real.nndist_eq, Real.coe_nnabs, abs_of_nonneg
          (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hle))]
        push_cast
        ring
      rw [hdist] at h
      exact h
    have hsecond : HasLaw (fun ω => B t ω - B 0 ω)
        (gaussianReal 0 t) P := by
      have h := hpre.hasLaw_sub t 0
      change HasLaw (fun ω => B t ω - B 0 ω)
        (gaussianReal 0 (nndist (t : ℝ) (0 : ℝ))) P at h
      simpa using h
    exact hfirst.identDistrib hsecond
  · filter_upwards [hB.cont] with ω hω
    exact hω.isCadlag

end ProbabilityTheory
