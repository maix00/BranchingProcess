/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Order.Group.Lattice
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

namespace ProbabilityTheory

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

/-- For a family of probability spaces that may vary with the index, convergence
of every fixed-threshold tail probability to zero together with a uniform
fourth-moment bound implies convergence of the second moments to zero. This
is the analytic last step from the two polynomial tail estimates and the
fourth-moment estimate in the trajectory-limit proof. -/
theorem tendsto_integral_abs_sq_of_tendsto_tail_and_fourth_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (X : ℕ → Ω → ℝ) (c : ℝ)
    (hX : ∀ n, Measurable (X n))
    (hfourth : ∃ C : ℝ, ∀ n,
      Integrable (fun ω => |X n ω - c| ^ 4) (μ n) ∧
        (∫ ω, |X n ω - c| ^ 4 ∂μ n) ≤ C)
    (htail : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (μ n).real {ω | ε ≤ |X n ω - c|})
        atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |X n ω - c| ^ 2 ∂μ n)
      atTop (𝓝 0) := by
  obtain ⟨C, hfourth⟩ := hfourth
  have hC : 0 ≤ C := by
    letI : IsProbabilityMeasure (μ 0) := hμ 0
    have hnonneg : 0 ≤ ∫ ω, |X 0 ω - c| ^ 4 ∂μ 0 := by
      apply integral_nonneg
      intro ω
      positivity
    have hbound := (hfourth 0).2
    linarith
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hnonneg (n : ℕ) : 0 ≤ ∫ ω, |X n ω - c| ^ 2 ∂μ n :=
      by
        letI : IsProbabilityMeasure (μ n) := hμ n
        apply integral_nonneg
        intro ω
        positivity
    filter_upwards [] with n
    exact lt_of_lt_of_le hb (hnonneg n)
  · intro ε hε
    let δ : ℝ := Real.sqrt (ε / 3)
    let K : ℝ := Real.sqrt (3 * (C + 1) / ε)
    have hδ : 0 < δ := by
      dsimp [δ]
      exact Real.sqrt_pos.2 (by positivity)
    have hK : 0 < K := by
      dsimp [K]
      exact Real.sqrt_pos.2 (by positivity)
    have htailδ := htail δ hδ
    have hthreshold : 0 < ε / 3 / K ^ 2 := by positivity
    have hsmallTail : ∀ᶠ n : ℕ in atTop,
        (μ n).real {ω | δ ≤ |X n ω - c|} < ε / 3 / K ^ 2 :=
      htailδ.eventually (Iio_mem_nhds hthreshold)
    have hδsq : δ ^ 2 = ε / 3 := by
      dsimp [δ]
      exact Real.sq_sqrt (by positivity)
    have hKsq : K ^ 2 = 3 * (C + 1) / ε := by
      dsimp [K]
      exact Real.sq_sqrt (by positivity)
    have hmomentSmall : C / K ^ 2 ≤ ε / 3 := by
      rw [hKsq]
      have heq : C / (3 * (C + 1) / ε) = ε * C / (3 * (C + 1)) := by
        field_simp [ne_of_gt hε]
      rw [heq]
      have hden : 0 < 3 * (C + 1) := by positivity
      rw [div_le_iff₀ hden]
      nlinarith [hC]
    filter_upwards [hsmallTail] with n hn
    letI : IsProbabilityMeasure (μ n) := hμ n
    let A : Set Ω := {ω | δ ≤ |X n ω - c|}
    let bad : Ω → ℝ := A.indicator (fun _ => (1 : ℝ))
    let y : Ω → ℝ := fun ω => |X n ω - c|
    have hA : MeasurableSet A := by
      exact measurableSet_Ici.preimage
        (Measurable.abs ((hX n).sub measurable_const))
    have hbad : Integrable bad (μ n) :=
      (integrable_const (1 : ℝ)).indicator hA
    have hfourInt : Integrable (fun ω => y ω ^ 4) (μ n) := by
      simpa [y] using (hfourth n).1
    have htailInt : Integrable (fun ω => (K ^ 2)⁻¹ * y ω ^ 4) (μ n) :=
      hfourInt.const_mul ((K ^ 2)⁻¹)
    have hboundInt : Integrable
        (fun ω => δ ^ 2 + K ^ 2 * bad ω + (K ^ 2)⁻¹ * y ω ^ 4)
        (μ n) := by
      exact ((integrable_const _).add (hbad.const_mul (K ^ 2))).add htailInt
    have hsecondInt : Integrable (fun ω => y ω ^ 2) (μ n) := by
      have hmajor : Integrable (fun ω => y ω ^ 4 + 1) (μ n) :=
        hfourInt.add (integrable_const 1)
      have hymeas : Measurable (fun ω => y ω ^ 2) := by
        exact (Measurable.abs ((hX n).sub measurable_const)).pow_const 2
      apply hmajor.mono' hymeas.aestronglyMeasurable
      filter_upwards [] with ω
      change ‖y ω ^ 2‖ ≤ y ω ^ 4 + 1
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (y ω))]
      have hy : 0 ≤ y ω ^ 2 := sq_nonneg _
      nlinarith [sq_nonneg (y ω ^ 2 - 1)]
    have hpoint : ∀ ω,
        y ω ^ 2 ≤ δ ^ 2 + K ^ 2 * bad ω + (K ^ 2)⁻¹ * y ω ^ 4 := by
      intro ω
      have htailNonneg : 0 ≤ (K ^ 2)⁻¹ * y ω ^ 4 :=
        mul_nonneg (inv_nonneg.mpr (sq_nonneg K)) (by positivity)
      by_cases hAω : ω ∈ A
      · simp [A, bad, hAω]
        by_cases hKω : K ≤ y ω
        · have hKsq_le : K ^ 2 ≤ y ω ^ 2 := by
            have hleft : 0 ≤ y ω - K := sub_nonneg.mpr hKω
            have hright : 0 ≤ y ω + K := by positivity
            nlinarith [mul_nonneg hleft hright]
          have hfour : K ^ 2 * y ω ^ 2 ≤ y ω ^ 4 := by
            have hleft : 0 ≤ y ω ^ 2 - K ^ 2 := sub_nonneg.mpr hKsq_le
            have hright : 0 ≤ y ω ^ 2 := sq_nonneg _
            nlinarith [mul_nonneg hleft hright]
          have hquot : y ω ^ 2 ≤ (K ^ 2)⁻¹ * y ω ^ 4 := by
            calc
              y ω ^ 2 = (K ^ 2)⁻¹ * (K ^ 2 * y ω ^ 2) := by
                field_simp [ne_of_gt (sq_pos_of_pos hK)]
              _ ≤ (K ^ 2)⁻¹ * y ω ^ 4 :=
                mul_le_mul_of_nonneg_left hfour
                  (inv_nonneg.mpr (sq_nonneg K))
          calc
            y ω ^ 2 ≤ (K ^ 2)⁻¹ * y ω ^ 4 := hquot
            _ ≤ δ ^ 2 + K ^ 2 + (K ^ 2)⁻¹ * y ω ^ 4 := by
              nlinarith [sq_nonneg δ, sq_nonneg K]
        · have hyK : y ω ≤ K := le_of_not_ge hKω
          have hysq : y ω ^ 2 ≤ K ^ 2 := by
            have hleft : 0 ≤ K - y ω := sub_nonneg.mpr hyK
            have hright : 0 ≤ K + y ω := by positivity
            nlinarith [mul_nonneg hleft hright]
          calc
            y ω ^ 2 ≤ K ^ 2 := hysq
            _ ≤ δ ^ 2 + K ^ 2 + (K ^ 2)⁻¹ * y ω ^ 4 := by
              nlinarith [sq_nonneg δ, htailNonneg]
      · have hyδ : y ω < δ := lt_of_not_ge (by simpa [A, y] using hAω)
        simp [bad, hAω]
        have hysq : y ω ^ 2 ≤ δ ^ 2 := by
          have hleft : 0 ≤ δ - y ω := sub_nonneg.mpr hyδ.le
          have hright : 0 ≤ δ + y ω := by positivity
          nlinarith [mul_nonneg hleft hright]
        calc
          y ω ^ 2 ≤ δ ^ 2 := hysq
          _ ≤ δ ^ 2 + (K ^ 2)⁻¹ * y ω ^ 4 := by
            linarith
    have hmono := integral_mono_ae hsecondInt hboundInt
      (ae_of_all (μ n) hpoint)
    have hbadIntegral : (∫ ω, bad ω ∂μ n) = (μ n).real A := by
      simpa [bad] using integral_indicator_const (1 : ℝ) hA
    have hboundIntegral :
        (∫ ω, δ ^ 2 + K ^ 2 * bad ω + (K ^ 2)⁻¹ * y ω ^ 4 ∂μ n) =
          δ ^ 2 + K ^ 2 * (μ n).real A +
            (K ^ 2)⁻¹ * ∫ ω, y ω ^ 4 ∂μ n := by
      calc
        (∫ ω, δ ^ 2 + K ^ 2 * bad ω + (K ^ 2)⁻¹ * y ω ^ 4 ∂μ n) =
            ∫ ω, (δ ^ 2 + K ^ 2 * bad ω) + (K ^ 2)⁻¹ * y ω ^ 4 ∂μ n := by
              congr 1
        _ = (∫ ω, δ ^ 2 + K ^ 2 * bad ω ∂μ n) +
            (∫ ω, (K ^ 2)⁻¹ * y ω ^ 4 ∂μ n) :=
              integral_add ((integrable_const _).add (hbad.const_mul (K ^ 2))) htailInt
        _ = ((∫ ω, δ ^ 2 ∂μ n) + (∫ ω, K ^ 2 * bad ω ∂μ n)) +
            (∫ ω, (K ^ 2)⁻¹ * y ω ^ 4 ∂μ n) := by
              rw [integral_add (integrable_const _) (hbad.const_mul (K ^ 2))]
        _ = δ ^ 2 + K ^ 2 * (μ n).real A +
            (K ^ 2)⁻¹ * ∫ ω, y ω ^ 4 ∂μ n := by
              rw [integral_const_mul, integral_const_mul, hbadIntegral]
              simp [add_assoc]
    have hfourBound : (∫ ω, y ω ^ 4 ∂μ n) ≤ C := by
      simpa [y] using (hfourth n).2
    have hupper : (∫ ω, y ω ^ 2 ∂μ n) ≤
        δ ^ 2 + K ^ 2 * (μ n).real A + (K ^ 2)⁻¹ * C := by
      rw [hboundIntegral] at hmono
      have htailBound := mul_le_mul_of_nonneg_left hfourBound
        (inv_nonneg.mpr (sq_nonneg K))
      exact hmono.trans (by
        simpa [add_assoc] using add_le_add_left htailBound
          (δ ^ 2 + K ^ 2 * (μ n).real A))
    rw [hδsq] at hupper
    have htailTerm : K ^ 2 * (μ n).real A < ε / 3 := by
      have hmul := mul_lt_mul_of_pos_left hn (sq_pos_of_pos hK)
      calc
        K ^ 2 * (μ n).real A =
            K ^ 2 * (μ n).real {ω | δ ≤ |X n ω - c|} := by rfl
        _ < K ^ 2 * (ε / 3 / K ^ 2) := hmul
        _ = ε / 3 := by field_simp [ne_of_gt (sq_pos_of_pos hK)]
    have hmomentTerm : (K ^ 2)⁻¹ * C ≤ ε / 3 := by
      calc
        (K ^ 2)⁻¹ * C = C / K ^ 2 := by rw [div_eq_mul_inv]; ring
        _ ≤ ε / 3 := hmomentSmall
    have : (∫ ω, y ω ^ 2 ∂μ n) < ε := by
      calc
        (∫ ω, y ω ^ 2 ∂μ n) ≤ ε / 3 + K ^ 2 * (μ n).real A +
            (K ^ 2)⁻¹ * C := hupper
        _ < ε / 3 + ε / 3 + ε / 3 := by linarith
        _ = ε := by ring
    simpa [y] using this

/-- The two one-sided polynomial tail bounds used in the trajectory-limit
argument imply the fixed-threshold tail convergence required by
`tendsto_integral_abs_sq_of_tendsto_tail_and_fourth_moment`. The exponents may
depend on the threshold. -/
theorem tendsto_integral_abs_sq_of_polynomial_tails_and_fourth_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (X : ℕ → Ω → ℝ) (c : ℝ)
    (hX : ∀ n, Measurable (X n))
    (hfourth : ∃ C : ℝ, ∀ n,
      Integrable (fun ω => |X n ω - c| ^ 4) (μ n) ∧
        (∫ ω, |X n ω - c| ^ 4 ∂μ n) ≤ C)
    (hleft : ∀ z : ℝ, z < c → ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      (μ n).real {ω | X n ω ≤ z} ≤ 1 / ((n : ℝ) ^ α))
    (hright : ∀ z : ℝ, c < z → ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      (μ n).real {ω | z ≤ X n ω} ≤ 1 / ((n : ℝ) ^ α)) :
    Tendsto (fun n => ∫ ω, |X n ω - c| ^ 2 ∂μ n)
      atTop (𝓝 0) := by
  have hpolyZero (tail : ℕ → ℝ)
      (hbound : ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
        tail n ≤ 1 / ((n : ℝ) ^ α))
      (hnonneg : ∀ n, 0 ≤ tail n) : Tendsto tail atTop (𝓝 0) := by
    obtain ⟨α, hα, hbound⟩ := hbound
    let p : ℕ → ℝ := fun n => 1 / ((n : ℝ) ^ α)
    have hp : Tendsto p atTop (𝓝 0) := by
      have hpower : Tendsto (fun n : ℕ => (n : ℝ) ^ α) atTop atTop :=
        (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
      convert hpower.inv_tendsto_atTop using 1
      ext n
      simp [p, one_div]
    apply tendsto_order.mpr
    constructor
    · intro b hb
      filter_upwards [] with n
      exact lt_of_lt_of_le hb (hnonneg n)
    · intro ε hε
      filter_upwards [hbound, hp.eventually (Iio_mem_nhds hε)] with n h₁ h₂
      exact lt_of_le_of_lt h₁ h₂
  have htail : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (μ n).real {ω | ε ≤ |X n ω - c|})
        atTop (𝓝 0) := by
    intro ε hε
    let left : ℕ → ℝ := fun n =>
      (μ n).real {ω | X n ω ≤ c - ε}
    let right : ℕ → ℝ := fun n =>
      (μ n).real {ω | c + ε ≤ X n ω}
    have hleftZero : Tendsto left atTop (𝓝 0) := by
      apply hpolyZero left ?_ (fun n => by dsimp [left]; exact measureReal_nonneg)
      obtain ⟨α, hα, hbound⟩ := hleft (c - ε) (by linarith)
      exact ⟨α, hα, hbound⟩
    have hrightZero : Tendsto right atTop (𝓝 0) := by
      apply hpolyZero right ?_ (fun n => by dsimp [right]; exact measureReal_nonneg)
      obtain ⟨α, hα, hbound⟩ := hright (c + ε) (by linarith)
      exact ⟨α, hα, hbound⟩
    have hsumZero : Tendsto (fun n => left n + right n) atTop (𝓝 0) := by
      simpa using hleftZero.add hrightZero
    let tail : ℕ → ℝ := fun n =>
      (μ n).real {ω | ε ≤ |X n ω - c|}
    have hbound : ∀ᶠ n : ℕ in atTop, tail n ≤ left n + right n := by
      filter_upwards [] with n
      letI : IsProbabilityMeasure (μ n) := hμ n
      have hsubset : {ω | ε ≤ |X n ω - c|} ⊆
          {ω | X n ω ≤ c - ε} ∪ {ω | c + ε ≤ X n ω} := by
        intro ω hω
        change ε ≤ |X n ω - c| at hω
        by_cases hx : 0 ≤ X n ω - c
        · right
          rw [abs_of_nonneg hx] at hω
          change c + ε ≤ X n ω
          linarith
        · left
          have hx' : X n ω - c ≤ 0 := le_of_not_ge hx
          rw [abs_of_nonpos hx'] at hω
          change X n ω ≤ c - ε
          linarith
      calc
        tail n ≤ (μ n).real
            ({ω | X n ω ≤ c - ε} ∪ {ω | c + ε ≤ X n ω}) :=
          measureReal_mono hsubset
        _ ≤ (μ n).real {ω | X n ω ≤ c - ε} +
            (μ n).real {ω | c + ε ≤ X n ω} := measureReal_union_le _ _
        _ = left n + right n := by rfl
    apply tendsto_order.mpr
    constructor
    · intro b hb
      filter_upwards [] with n
      exact lt_of_lt_of_le hb
        (measureReal_nonneg : 0 ≤ (μ n).real {ω | ε ≤ |X n ω - c|})
    · intro η hη
      filter_upwards [hbound, hsumZero.eventually (Iio_mem_nhds hη)]
        with n hn hs
      exact lt_of_le_of_lt hn hs
  exact tendsto_integral_abs_sq_of_tendsto_tail_and_fourth_moment
    μ hμ X c hX hfourth htail

end ProbabilityTheory

end
