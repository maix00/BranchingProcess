/-
Copyright (c) 2026 WANG Yiyang.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Analysis.SpecialFunctions.LogarithmicCeiling
import Probability.MeasureTheory.Moments.PaleyZygmund

/-!
# Probability bounds from geometric second-moment growth

## Public declarations

- `normalizedSecondMomentConstant ρ v` is
  $K(\rho,v)=1+v/(\rho(\rho-1))$. If
  $M_{n+1}=\rho^2M_n+v\rho^n$ and $M_0=1$, then
  `normalizedSecondMoment_le_of_recursion` proves
  $M_n/\rho^{2n}\le K(\rho,v)$.
- `measure_ge_half_mean_of_moment_recursion` applies this estimate and the
  Paley--Zygmund inequality to a nonnegative square-integrable random-variable
  sequence with mean $\rho^n$ and the stated second-moment recursion. It gives
  a uniform positive lower bound for reaching half the mean.
- `measure_ge_floor_rpow_of_moment_recursion` chooses the horizon
  $h=\lceil(a\log N+\log 2)/\log\rho\rceil_+$ and gives the same uniform
  lower bound for reaching $\lfloor N^a\rfloor_+$.

The probability-space statements apply to any sequence satisfying the listed
moment identities. Finite-slot Galton--Watson applications are in
`Probability.BranchingProcess.GaltonWatson.BoundedGrowth`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory
/-- The normalized second-moment bound associated with a geometric recursion. -/
noncomputable def normalizedSecondMomentConstant (ρ variance : ℝ) : ℝ :=
  1 + variance / (ρ * (ρ - 1))

/-- For a sequence $M_n$ with $M_0=1$ and
$M_{n+1}=\rho^2M_n+v\rho^n$, this bounds the normalized second moment
$M_n/\rho^{2n}$. -/
theorem normalizedSecondMoment_le_of_recursion
    (ρ variance : ℝ) (hρ : 1 < ρ) (hvariance : 0 ≤ variance)
    (m₂ : ℕ → ℝ) (hm₂_zero : m₂ 0 = 1)
    (hm₂_succ : ∀ n, m₂ (n + 1) = ρ ^ 2 * m₂ n + variance * ρ ^ n) :
    ∀ n, m₂ n / ρ ^ (2 * n) ≤ normalizedSecondMomentConstant ρ variance := by
  have hρpos : 0 < ρ := by linarith
  have hρne : ρ ≠ 0 := hρpos.ne'
  have hρsubpos : 0 < ρ - 1 := by linarith
  let c : ℝ := variance / (ρ * (ρ - 1))
  let stage : ℕ → ℝ := fun n => 1 + c * (1 - (ρ ^ n)⁻¹)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hstage_zero : stage 0 = 1 := by simp [stage]
  have hstage_succ (n : ℕ) :
      stage (n + 1) = stage n + variance / ρ ^ (n + 2) := by
    dsimp [stage, c]
    rw [pow_succ]
    field_simp [hρne, pow_ne_zero n hρne]
    ring
  have hm₂_formula (n : ℕ) : m₂ n = ρ ^ (2 * n) * stage n := by
    induction n with
    | zero => simp [hm₂_zero, stage]
    | succ n ih =>
        rw [hm₂_succ n, ih, hstage_succ]
        have hpow : ρ ^ (2 * (n + 1)) = ρ ^ 2 * ρ ^ (2 * n) := by
          rw [Nat.mul_succ, pow_add]
          ring
        rw [hpow]
        have hpow' : ρ ^ (2 * n) = (ρ ^ n) ^ 2 := by
          rw [show 2 * n = n * 2 by omega, pow_mul]
        rw [hpow']
        dsimp [stage, c] at *
        field_simp [hρne, hρsubpos.ne', pow_ne_zero n hρne]
        ring
  intro n
  rw [hm₂_formula n]
  have hpowpos : 0 < ρ ^ n := pow_pos hρpos _
  have hinv_nonneg : 0 ≤ (ρ ^ n)⁻¹ := inv_nonneg.mpr hpowpos.le
  have hpow_ge_one : 1 ≤ ρ ^ n := one_le_pow₀ hρ.le
  have hinv_le_one : (ρ ^ n)⁻¹ ≤ 1 := (inv_le_one₀ hpowpos).2 hpow_ge_one
  have hstage_le : stage n ≤ 1 + c := by
    dsimp [stage]
    nlinarith [mul_nonneg hc_nonneg hinv_nonneg]
  have hden : ρ ^ (2 * n) ≠ 0 := pow_ne_zero _ hρne
  rw [mul_div_cancel_left₀ _ hden]
  calc
    stage n ≤ 1 + c := hstage_le
    _ = normalizedSecondMomentConstant ρ variance := by
      simp [normalizedSecondMomentConstant, c]

/-- The normalized second-moment recursion also gives the elementary lower
bound `E[Zₙ²] ≥ (E[Zₙ])²`. -/
private theorem rho_pow_sq_le_secondMoment_of_recursion
    (ρ variance : ℝ) (hρ : 1 < ρ) (hvariance : 0 ≤ variance)
    (m₂ : ℕ → ℝ) (hm₂_zero : m₂ 0 = 1)
    (hm₂_succ : ∀ n, m₂ (n + 1) = ρ ^ 2 * m₂ n + variance * ρ ^ n) :
    ∀ n, ρ ^ (2 * n) ≤ m₂ n := by
  have hρ_nonneg : 0 ≤ ρ := by linarith
  intro n
  induction n with
  | zero => simpa using hm₂_zero.ge
  | succ n ih =>
      have hpow : ρ ^ (2 * (n + 1)) = ρ ^ 2 * ρ ^ (2 * n) := by
        rw [Nat.mul_succ, pow_add]
        ring
      rw [hpow, hm₂_succ n]
      calc
        ρ ^ 2 * ρ ^ (2 * n) ≤ ρ ^ 2 * m₂ n :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg ρ)
        _ ≤ ρ ^ 2 * m₂ n + variance * ρ ^ n :=
          le_add_of_nonneg_right (mul_nonneg hvariance (pow_nonneg hρ_nonneg _))

/-- For any nonnegative, square-integrable real-valued random-variable sequence
with mean $\rho^n$ and second-moment recursion
$M_{n+1}=\rho^2M_n+v\rho^n$, Paley--Zygmund gives a uniform lower bound
on the probability of reaching half the mean. -/
theorem measure_ge_half_mean_of_moment_recursion
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ρ variance : ℝ) (hρ : 1 < ρ) (hvariance : 0 ≤ variance)
    (Z : ℕ → Ω → ℝ) (m₂ : ℕ → ℝ)
    (hZmeas : ∀ n, Measurable (Z n))
    (hZ_nonneg : ∀ n, 0 ≤ᵐ[μ] Z n)
    (hZ_integrable : ∀ n, Integrable (Z n) μ)
    (hZ_memLp : ∀ n, MemLp (Z n) 2 μ)
    (hmean : ∀ n, ∫ ω, Z n ω ∂μ = ρ ^ n)
    (hm₂_zero : m₂ 0 = 1)
    (hsecond : ∀ n, ∫ ω, Z n ω ^ 2 ∂μ = m₂ n)
    (hm₂_succ : ∀ n, m₂ (n + 1) = ρ ^ 2 * m₂ n + variance * ρ ^ n)
    (n : ℕ) (threshold : ℝ) (hthreshold : 0 ≤ threshold)
    (hthreshold_le : 2 * threshold ≤ ρ ^ n) :
    (μ.real {ω | threshold ≤ Z n ω}) ≥
      1 / (4 * normalizedSecondMomentConstant ρ variance) := by
  have hρpos : 0 < ρ := by linarith
  have hsecond_lower := rho_pow_sq_le_secondMoment_of_recursion ρ variance hρ
    hvariance m₂ hm₂_zero hm₂_succ n
  have hsecond_pos : 0 < m₂ n := lt_of_lt_of_le (pow_pos hρpos _) hsecond_lower
  have hsecond_ratio := normalizedSecondMoment_le_of_recursion ρ variance hρ
    hvariance m₂ hm₂_zero hm₂_succ n
  have hdenom_pos : 0 < ρ ^ (2 * n) := pow_pos hρpos _
  have hsecond_upper : m₂ n ≤ normalizedSecondMomentConstant ρ variance * ρ ^ (2 * n) :=
    (div_le_iff₀ hdenom_pos).1 hsecond_ratio
  have hpow : ρ ^ (2 * n) = (ρ ^ n) ^ 2 := by
    rw [show 2 * n = n * 2 by omega, pow_mul]
  have hsecond_upper' : m₂ n ≤ normalizedSecondMomentConstant ρ variance * (ρ ^ n) ^ 2 :=
    hpow ▸ hsecond_upper
  have hCpos : 0 < normalizedSecondMomentConstant ρ variance := by
    dsimp [normalizedSecondMomentConstant]
    positivity
  exact measure_ge_threshold_of_secondMoment_le μ (Z n) (hZmeas n)
    (hZ_nonneg n) (hZ_integrable n) (hZ_memLp n) (ρ ^ n) (m₂ n) threshold
    (normalizedSecondMomentConstant ρ variance) (hmean n) (hsecond n)
    hthreshold (pow_pos hρpos n) hthreshold_le hsecond_pos hCpos hsecond_upper'

/-- The explicit threshold version of the geometric second-moment growth
bound. If a random-variable sequence satisfies the stated moment recursion,
then at
`h_N = ceil ((a log N + log 2) / log ρ)` the population reaches
`floor (N^a)` with a probability bounded away from zero. -/
theorem measure_ge_floor_rpow_of_moment_recursion
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ρ variance : ℝ) (hρ : 1 < ρ) (hvariance : 0 ≤ variance)
    (Z : ℕ → Ω → ℝ) (m₂ : ℕ → ℝ)
    (hZmeas : ∀ n, Measurable (Z n))
    (hZ_nonneg : ∀ n, 0 ≤ᵐ[μ] Z n)
    (hZ_integrable : ∀ n, Integrable (Z n) μ)
    (hZ_memLp : ∀ n, MemLp (Z n) 2 μ)
    (hmean : ∀ n, ∫ ω, Z n ω ∂μ = ρ ^ n)
    (hm₂_zero : m₂ 0 = 1)
    (hsecond : ∀ n, ∫ ω, Z n ω ^ 2 ∂μ = m₂ n)
    (hm₂_succ : ∀ n, m₂ (n + 1) = ρ ^ 2 * m₂ n + variance * ρ ^ n)
    (N : ℕ) (a : ℝ) (hN : 1 ≤ N) :
    (μ.real {ω | (⌊(N : ℝ) ^ a⌋₊ : ℝ) ≤
      Z ⌈(a * Real.log N + Real.log 2) / Real.log ρ⌉₊ ω}) ≥
      1 / (4 * normalizedSecondMomentConstant ρ variance) := by
  have hNpow_nonneg : 0 ≤ (N : ℝ) ^ a :=
    Real.rpow_nonneg (by positivity : 0 ≤ (N : ℝ)) a
  have hfloor_le : (⌊(N : ℝ) ^ a⌋₊ : ℝ) ≤ (N : ℝ) ^ a := Nat.floor_le hNpow_nonneg
  have hscale : 2 * (⌊(N : ℝ) ^ a⌋₊ : ℝ) ≤
      ρ ^ ⌈(a * Real.log N + Real.log 2) / Real.log ρ⌉₊ := by
    have hNpos : 0 < (N : ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
    have htarget_pos : 0 < 2 * (N : ℝ) ^ a := by positivity
    have hlog : Real.log (2 * (N : ℝ) ^ a) =
        Real.log 2 + a * Real.log N := by
      rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hNpos a).ne',
        Real.log_rpow hNpos]
    have hlogb : Real.logb ρ (2 * (N : ℝ) ^ a) =
        (a * Real.log N + Real.log 2) / Real.log ρ := by
      rw [Real.logb, hlog]
      ring
    have hlarge := Real.le_pow_natCeil_logb hρ htarget_pos
    rw [hlogb] at hlarge
    exact (mul_le_mul_of_nonneg_left hfloor_le (by norm_num)).trans
      hlarge
  exact measure_ge_half_mean_of_moment_recursion μ ρ variance hρ
    hvariance Z m₂ hZmeas hZ_nonneg hZ_integrable hZ_memLp hmean hm₂_zero
    hsecond hm₂_succ _ _ (Nat.cast_nonneg _) hscale

end ProbabilityTheory

end
