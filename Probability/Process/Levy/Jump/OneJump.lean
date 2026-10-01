module

public import Probability.Process.Levy.Jump.SmallVariation
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Independence.Basic

/-!
# One marked Poisson jump and small residual variation

A finite-rate Poisson count with an independent jump mark has positive
probability of exactly one jump in any positive-mass mark window. If the
residual total variation is independent of this pair and has sufficiently
small expectation, all three requirements hold simultaneously.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

theorem measure_oneMarkedJump_and_smallVariation_pos
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (N : Ω → ℕ) (W : Ω → ℝ) (V : Ω → ENNReal)
    (rate : ℝ≥0) (ν : Measure ℝ) (J : Set ℝ) (ρ : ENNReal)
    (hrate : 0 < rate) (hν : 0 < ν J) (hJ : MeasurableSet J)
    (hN : HasLaw N (poissonMeasure rate) P)
    (hW : HasLaw W ν P)
    (hNW : IndepFun N W P)
    (hVNW : IndepFun V (fun ω => (N ω, W ω)) P)
    (hV : Measurable V)
    (hE : (∫⁻ ω, V ω ∂P) < ρ) :
    0 < P {ω | V ω < ρ ∧ N ω = 1 ∧ W ω ∈ J} := by
  have hsmall : 0 < P {ω | V ω < ρ} :=
    measure_smallVariation_pos P V hV ρ hE
  have hcount : 0 < P {ω | N ω = 1} := by
    have h := hN.measure_eq (p := fun n => n = 1) (measurableSet_singleton 1)
    rw [h]
    change 0 < poissonMeasure rate {1}
    rw [poissonMeasure_singleton]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hmark : 0 < P {ω | W ω ∈ J} := by
    have h := hW.measure_eq (p := fun x => x ∈ J) hJ
    change P {ω | W ω ∈ J} = ν J at h
    rw [h]
    exact hν
  have hbig : 0 < P {ω | N ω = 1 ∧ W ω ∈ J} := by
    have hprod := hNW.measure_inter_preimage_eq_mul
      ({1} : Set ℕ) J (measurableSet_singleton _) hJ
    change P {ω | N ω = 1 ∧ W ω ∈ J} =
      P {ω | N ω = 1} * P {ω | W ω ∈ J} at hprod
    rw [hprod]
    exact ENNReal.mul_pos hcount.ne' hmark.ne'
  have hprod := hVNW.measure_inter_preimage_eq_mul
    (Set.Iio ρ) (({1} : Set ℕ) ×ˢ J)
    measurableSet_Iio ((measurableSet_singleton _).prod hJ)
  change P {ω | V ω < ρ ∧ N ω = 1 ∧ W ω ∈ J} =
    P {ω | V ω < ρ} * P {ω | N ω = 1 ∧ W ω ∈ J} at hprod
  rw [hprod]
  exact ENNReal.mul_pos hsmall.ne' hbig.ne'

/-- The zero-target alternative: no large jump, while the small-jump total
variation stays below its threshold. -/
theorem measure_noJump_and_smallVariation_pos
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (N : Ω → ℕ) (V : Ω → ENNReal)
    (rate : ℝ≥0) (ρ : ENNReal)
    (hN : HasLaw N (poissonMeasure rate) P)
    (hVN : IndepFun V N P)
    (hV : Measurable V)
    (hE : (∫⁻ ω, V ω ∂P) < ρ) :
    0 < P {ω | V ω < ρ ∧ N ω = 0} := by
  have hsmall : 0 < P {ω | V ω < ρ} :=
    measure_smallVariation_pos P V hV ρ hE
  have hcount : 0 < P {ω | N ω = 0} := by
    have h := hN.measure_eq (p := fun n => n = 0) (measurableSet_singleton 0)
    rw [h]
    change 0 < poissonMeasure rate {0}
    rw [poissonMeasure_singleton]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hprod := hVN.measure_inter_preimage_eq_mul
    (Set.Iio ρ) ({0} : Set ℕ) measurableSet_Iio (measurableSet_singleton _)
  change P {ω | V ω < ρ ∧ N ω = 0} =
    P {ω | V ω < ρ} * P {ω | N ω = 0} at hprod
  rw [hprod]
  exact ENNReal.mul_pos hsmall.ne' hcount.ne'

end ProbabilityTheory

end
