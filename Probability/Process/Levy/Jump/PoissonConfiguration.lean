/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.RandomMeasure.Poisson.Basic
import Probability.Process.Levy.Jump.SmallVariation

/-!
# A positive finite-jump configuration

For disjoint finite-intensity mark regions, the Poisson random measure has
positive probability of one point in the target region and none in the other.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

theorem measure_poissonRandomMeasure_one_and_zero_pos
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {J B : Set E} (hJ : MeasurableSet J) (hB : MeasurableSet B)
    (hfinJ : m J < ⊤) (hfinB : m B < ⊤)
    (hJpos : 0 < m J) (hdisj : Disjoint J B) :
    0 < P {ω : Ω | (poissonRandomMeasure K X ω : Measure E) J = 1 ∧
      (poissonRandomMeasure K X ω : Measure E) B = 0} := by
  have hindep := indepFun_poissonRandomMeasure_apply hd hJ hB hfinJ hfinB hdisj
  have hproduct := hindep.measure_inter_preimage_eq_mul
    ({1} : Set ENNReal) ({0} : Set ENNReal)
    (measurableSet_singleton _) (measurableSet_singleton _)
  change P {ω : Ω | poissonRandomMeasure K X ω J = 1 ∧
      poissonRandomMeasure K X ω B = 0} =
      P {ω | poissonRandomMeasure K X ω J = 1} *
      P {ω | poissonRandomMeasure K X ω B = 0} at hproduct
  rw [hproduct]
  have hcountJ := map_poissonRandomMeasure_apply hd hJ hfinJ
  have hcountB := map_poissonRandomMeasure_apply hd hB hfinB
  have hcast1 : (fun k : ℕ => (k : ENNReal)) ⁻¹' ({1} : Set ENNReal) = {1} := by
    ext k
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    simpa only [Nat.cast_one] using (Nat.cast_inj (R := ENNReal) (m := k) (n := 1))
  have hcast0 : (fun k : ℕ => (k : ENNReal)) ⁻¹' ({0} : Set ENNReal) = {0} := by
    ext k
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    simpa only [Nat.cast_zero] using (Nat.cast_inj (R := ENNReal) (m := k) (n := 0))
  have hone : P {ω | poissonRandomMeasure K X ω J = 1} =
      poissonMeasure (m J).toNNReal {1} := by
    have h := congrArg (fun ν : Measure ENNReal => ν {1}) hcountJ
    rw [Measure.map_apply
      (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hJ)
      (measurableSet_singleton (1 : ENNReal)),
      Measure.map_apply (by fun_prop : Measurable fun k : ℕ => (k : ENNReal))
        (measurableSet_singleton (1 : ENNReal))] at h
    rw [hcast1] at h
    exact h
  have hzero : P {ω | poissonRandomMeasure K X ω B = 0} =
      poissonMeasure (m B).toNNReal {0} := by
    have h := congrArg (fun ν : Measure ENNReal => ν {0}) hcountB
    rw [Measure.map_apply
      (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hB)
      (measurableSet_singleton (0 : ENNReal)),
      Measure.map_apply (by fun_prop : Measurable fun k : ℕ => (k : ENNReal))
        (measurableSet_singleton (0 : ENNReal))] at h
    rw [hcast0] at h
    exact h
  rw [hone, hzero, poissonMeasure_singleton, poissonMeasure_singleton]
  apply ENNReal.mul_pos
  · have hrate : 0 < (m J).toNNReal :=
      ENNReal.toNNReal_pos hJpos.ne' hfinJ.ne
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
    exact (ENNReal.ofReal_pos.mpr
      (mul_pos (Real.exp_pos _) (by exact_mod_cast hrate))).ne'
  · positivity

/-- A small residual variation can be combined with the one-jump Poisson
configuration when it is independent of the two large-region counts. -/
theorem measure_poissonRandomMeasure_one_zero_smallVariation_pos
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {J B : Set E} (hJ : MeasurableSet J) (hB : MeasurableSet B)
    (hfinJ : m J < ⊤) (hfinB : m B < ⊤)
    (hJpos : 0 < m J) (hdisj : Disjoint J B)
    (V : Ω → ENNReal) (ρ : ENNReal)
    (hV : Measurable V) (hE : (∫⁻ ω, V ω ∂P) < ρ)
    (hIndep : IndepFun V (fun ω =>
      (poissonRandomMeasure K X ω J, poissonRandomMeasure K X ω B)) P) :
    0 < P {ω : Ω | V ω < ρ ∧ poissonRandomMeasure K X ω J = 1 ∧
      poissonRandomMeasure K X ω B = 0} := by
  have hsmall := measure_smallVariation_pos P V hV ρ hE
  have hbig := measure_poissonRandomMeasure_one_and_zero_pos
    hd hJ hB hfinJ hfinB hJpos hdisj
  have hproduct := hIndep.measure_inter_preimage_eq_mul
    (Set.Iio ρ) (({1} : Set ENNReal) ×ˢ ({0} : Set ENNReal))
    measurableSet_Iio ((measurableSet_singleton _).prod (measurableSet_singleton _))
  change P {ω : Ω | V ω < ρ ∧ poissonRandomMeasure K X ω J = 1 ∧
      poissonRandomMeasure K X ω B = 0} =
      P {ω | V ω < ρ} *
      P {ω | poissonRandomMeasure K X ω J = 1 ∧
        poissonRandomMeasure K X ω B = 0} at hproduct
  rw [hproduct]
  exact ENNReal.mul_pos hsmall.ne' hbig.ne'

end ProbabilityTheory
