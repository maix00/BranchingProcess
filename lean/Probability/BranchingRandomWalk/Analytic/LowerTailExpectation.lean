/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.EReal.Basic
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Tactic

/-!
# One-sided endpoint expectations from lower-tail bounds

A polynomial lower-tail estimate and an exponential moment for the negative
part give a one-sided first-moment estimate.  This is the analytic step needed
for the `a = 1` endpoint in the speed lower bound; it does not require a
second moment or the full `L²` trajectory limit.
-/

open Filter MeasureTheory Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

/-- The elementary one-sided exponential bound, used after shifting by the
logarithmic scale. -/
theorem neg_exp_neg_le_self (x : ℝ) : -Real.exp (-x) ≤ x := by
  have h := Real.add_one_le_exp (-x)
  linarith

/-- If a random variable is at least `z` off a bad event, its expectation is
bounded below by the good-event contribution and the exponentially controlled
negative tail on the bad event.  The `max z 0` term makes the estimate valid
for negative as well as nonnegative thresholds.

For `L = log N`, `M = N`, and a polynomially small bad-event probability this
implies a normalized `liminf` lower bound. -/
theorem integral_ge_of_lower_bound_off_event_exp_neg
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (A : Set Ω) (z L p M : ℝ)
    (hA : MeasurableSet A)
    (hX : Integrable X μ)
    (hExp : Integrable (fun ω => Real.exp (-X ω)) μ)
    (hgoodOn : ∀ ω ∉ A, z ≤ X ω)
    (hL : 0 ≤ L)
    (hprob : μ.real A ≤ p)
    (hExpBound : (∫ ω, Real.exp (-X ω) ∂μ) ≤ M) :
    z - max z 0 * p - L * p - Real.exp (-L) * M ≤
      ∫ ω, X ω ∂μ := by
  let bad : Ω → ℝ := A.indicator (fun _ => (1 : ℝ))
  let good : Ω → ℝ := Aᶜ.indicator (fun _ => (1 : ℝ))
  have hbadInt : Integrable bad μ :=
    (integrable_const (1 : ℝ)).indicator hA
  have hgoodInt : Integrable good μ :=
    (integrable_const (1 : ℝ)).indicator hA.compl
  have hscaledExp : Integrable (fun ω => Real.exp (-X ω - L)) μ := by
    have heq : (fun ω => Real.exp (-X ω - L)) =
        fun ω => Real.exp (-L) * Real.exp (-X ω) := by
      funext ω
      rw [show -X ω - L = -L + -X ω by ring, Real.exp_add]
    rw [heq]
    exact hExp.const_mul (Real.exp (-L))
  have hgoodMulInt : Integrable (fun ω => z * good ω) μ :=
    hgoodInt.const_mul z
  have hbadMulInt : Integrable (fun ω => L * bad ω) μ :=
    hbadInt.const_mul L
  have hdiffInt : Integrable (fun ω => z * good ω - L * bad ω) μ :=
    hgoodMulInt.sub hbadMulInt
  have hmajorInt : Integrable
      (fun ω => z * good ω - L * bad ω - Real.exp (-X ω - L)) μ :=
    hdiffInt.sub hscaledExp
  have hshift : ∀ x : ℝ, -L - Real.exp (-x - L) ≤ x := by
    intro x
    have h := neg_exp_neg_le_self (x + L)
    have heq : Real.exp (-(x + L)) = Real.exp (-x - L) := by
      congr 1
      ring
    rw [heq] at h
    linarith
  have hpointwise : ∀ ω,
      z * good ω - L * bad ω - Real.exp (-X ω - L) ≤ X ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp [bad, good, hω]
      linarith [hshift (X ω)]
    · simp [bad, good, hω]
      have hnonneg : 0 ≤ Real.exp (-X ω - L) := Real.exp_nonneg _
      linarith [hgoodOn ω hω]
  have hintLower := integral_mono_ae hmajorInt hX
    (ae_of_all μ hpointwise)
  have hbadIntegral : (∫ ω, bad ω ∂μ) = μ.real A := by
    simpa [bad] using integral_indicator_const (1 : ℝ) hA
  have hgoodIntegral : (∫ ω, good ω ∂μ) = μ.real Aᶜ := by
    simpa [good] using integral_indicator_const (1 : ℝ) hA.compl
  have hscaledIntegral :
      (∫ ω, Real.exp (-X ω - L) ∂μ) =
        Real.exp (-L) * ∫ ω, Real.exp (-X ω) ∂μ := by
    have heq : (fun ω => Real.exp (-X ω - L)) =
        fun ω => Real.exp (-L) * Real.exp (-X ω) := by
      funext ω
      rw [show -X ω - L = -L + -X ω by ring, Real.exp_add]
    rw [heq, integral_const_mul]
  have hmajorIntegral :
      (∫ ω, z * good ω - L * bad ω - Real.exp (-X ω - L) ∂μ) =
        z * (1 - μ.real A) - L * μ.real A -
          Real.exp (-L) * ∫ ω, Real.exp (-X ω) ∂μ := by
    calc
      (∫ ω, z * good ω - L * bad ω - Real.exp (-X ω - L) ∂μ) =
          (∫ ω, z * good ω ∂μ) - (∫ ω, L * bad ω ∂μ) -
            (∫ ω, Real.exp (-X ω - L) ∂μ) := by
              rw [integral_sub hdiffInt hscaledExp,
                integral_sub hgoodMulInt hbadMulInt]
      _ = z * (1 - μ.real A) - L * μ.real A -
            Real.exp (-L) * ∫ ω, Real.exp (-X ω) ∂μ := by
              rw [integral_const_mul, hgoodIntegral,
                integral_const_mul, hbadIntegral, hscaledIntegral,
                MeasureTheory.probReal_compl_eq_one_sub hA]
  rw [hmajorIntegral] at hintLower
  have hgoodWeight :
      z - max z 0 * p ≤ z * (1 - μ.real A) := by
    by_cases hz : 0 ≤ z
    · have hmul := mul_le_mul_of_nonneg_left hprob hz
      simp [max_eq_left hz]
      nlinarith
    · have hz' : z ≤ 0 := le_of_not_ge hz
      have hq : 0 ≤ μ.real A := measureReal_nonneg
      simp [max_eq_right hz']
      have hprod : z * μ.real A ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hz' hq
      nlinarith
  have hbadWeight : L * μ.real A ≤ L * p :=
    mul_le_mul_of_nonneg_left hprob hL
  have hexpWeight :
      Real.exp (-L) * ∫ ω, Real.exp (-X ω) ∂μ ≤ Real.exp (-L) * M :=
    mul_le_mul_of_nonneg_left hExpBound (Real.exp_nonneg _)
  linarith

/-- A polynomial lower-tail bound, together with the exponential moment bound
`E[exp(-Xₙ)] ≤ n`, gives a one-sided logarithmic-scale expectation limit.

The family of measures may vary with `n`. For each threshold below `target`,
the bad-event probability is assumed to be eventually bounded by `n⁻ᵋ` for
some positive `ε`; this is the abstract analytic input supplied by a
polynomial estimate such as (4.16). The theorem proves the sequence liminf,
in the extended reals so no separate upper-bound assumption is needed. It does
not itself prove any branching-random-walk tail estimate. -/
theorem target_le_liminf_integral_div_log_of_polynomial_lower_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (X : ℕ → Ω → ℝ) (target : ℝ)
    (hMeas : ∀ n, Measurable (X n))
    (hX : ∀ n, Integrable (X n) (μ n))
    (hExp : ∀ n, Integrable (fun ω => Real.exp (-X n ω)) (μ n))
    (hExpBound : ∀ᶠ n : ℕ in atTop,
      (∫ ω, Real.exp (-X n ω) ∂μ n) ≤ (n : ℝ))
    (hTail : ∀ z < target, ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop,
      (μ n).real {ω | X n ω ≤ z * Real.log (n : ℝ)} ≤
        1 / ((n : ℝ) ^ ε)) :
    (target : EReal) ≤ atTop.liminf (fun n : ℕ =>
      (((∫ ω, X n ω ∂μ n) / Real.log (n : ℝ) : ℝ) : EReal)) := by
  let endpointMean : ℕ → ℝ := fun n =>
    (∫ ω, X n ω ∂μ n) / Real.log (n : ℝ)
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinvLog : Tendsto (fun n : ℕ => 1 / Real.log (n : ℝ))
      atTop (𝓝 0) := by
    convert hlog.inv_tendsto_atTop using 1
    ext n
    simp [one_div]
  have hbelow (z : ℝ) (hz : z < target) : ∀ᶠ n : ℕ in atTop,
      z < endpointMean n := by
    obtain ⟨z', hzz', hz'target⟩ := exists_between hz
    obtain ⟨ε, hε, htail⟩ := hTail z' hz'target
    let p : ℕ → ℝ := fun n => 1 / ((n : ℝ) ^ ε)
    have hpZero : Tendsto p atTop (𝓝 0) := by
      have hpower : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
        (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
      convert hpower.inv_tendsto_atTop using 1
      ext n
      simp [p, one_div]
    let error : ℕ → ℝ := fun n =>
      (max z' 0 + 1) * p n + 1 / Real.log (n : ℝ)
    have herrorZero : Tendsto error atTop (𝓝 0) := by
      simpa [error] using (tendsto_const_nhds.mul hpZero).add hinvLog
    have herrorSmall : ∀ᶠ n : ℕ in atTop, error n < z' - z :=
      herrorZero.eventually (Iio_mem_nhds (sub_pos.mpr hzz'))
    have hlogPos : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n : ℝ) := by
      exact hlog.eventually_gt_atTop 0
    filter_upwards [htail, hExpBound, hlogPos, herrorSmall,
      eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n htailN hExpN hlogN herr hn
    letI : IsProbabilityMeasure (μ n) := hμ n
    let A : Set Ω := {ω | X n ω ≤ z' * Real.log (n : ℝ)}
    have hA : MeasurableSet A := by
      exact measurableSet_Iic.preimage (hMeas n)
    have hprob : (μ n).real A ≤ p n := by
      simpa [A, p] using htailN
    have hnNat : 1 < n := by omega
    have hnReal : 1 < (n : ℝ) := by exact_mod_cast hnNat
    have hL : 0 ≤ Real.log (n : ℝ) := (Real.log_pos hnReal).le
    have hExpMoment : (∫ ω, Real.exp (-X n ω) ∂μ n) ≤ (n : ℝ) := hExpN
    have hfinite := integral_ge_of_lower_bound_off_event_exp_neg
      (μ n) (X n) A (z' * Real.log (n : ℝ)) (Real.log (n : ℝ))
      (p n) (n : ℝ) hA (hX n) (hExp n)
      (by
        intro ω hω
        exact le_of_lt (lt_of_not_ge hω))
      hL hprob hExpMoment
    have hmax : max (z' * Real.log (n : ℝ)) 0 =
        max z' 0 * Real.log (n : ℝ) := by
      by_cases hz' : 0 ≤ z'
      · simp [max_eq_left hz', max_eq_left (mul_nonneg hz' hL)]
      · have hz'le : z' ≤ 0 := le_of_not_ge hz'
        have hprod : z' * Real.log (n : ℝ) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hz'le hL
        simp [max_eq_right hz'le, max_eq_right hprod]
    have hexp : Real.exp (-Real.log (n : ℝ)) * (n : ℝ) = 1 := by
      have hnPos : 0 < (n : ℝ) := by positivity
      rw [Real.exp_neg, Real.exp_log hnPos]
      field_simp
    have hnormalized : z' - max z' 0 * p n - p n -
          1 / Real.log (n : ℝ) ≤ endpointMean n := by
      have hdiv := div_le_div_of_nonneg_right hfinite hL
      have hleft :
          (z' * Real.log (n : ℝ) -
            max (z' * Real.log (n : ℝ)) 0 * p n -
            Real.log (n : ℝ) * p n -
            Real.exp (-Real.log (n : ℝ)) * (n : ℝ)) /
              Real.log (n : ℝ) =
            z' - max z' 0 * p n - p n -
              1 / Real.log (n : ℝ) := by
        rw [hmax, hexp]
        field_simp [ne_of_gt hlogN]
      unfold endpointMean
      rw [← hleft]
      exact hdiv
    dsimp [error] at herr
    change z < endpointMean n
    linarith [hnormalized]
  let endpointMeanE : ℕ → EReal := fun n => endpointMean n
  have hliminf (z : ℝ) (hz : z < target) :
      (z : EReal) ≤ atTop.liminf endpointMeanE := by
    have hEventually : ∀ᶠ n : ℕ in atTop, (z : EReal) ≤ endpointMeanE n :=
      (hbelow z hz).mono fun _ hn => EReal.coe_le_coe_iff.mpr hn.le
    have hconst := Filter.liminf_le_liminf hEventually
    simpa [endpointMeanE] using hconst
  change (target : EReal) ≤ atTop.liminf endpointMeanE
  by_contra hnot
  have hlt : atTop.liminf endpointMeanE < (target : EReal) := lt_of_not_ge hnot
  obtain ⟨z, hz, hztarget⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  exact (not_lt_of_ge (hliminf z (EReal.coe_lt_coe_iff.mp hztarget))) hz

end ProbabilityTheory.BranchingRandomWalk

end
