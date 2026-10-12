/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Tail.RightTailKilledCapacityRawRangeRate

/-!
# Finite-variance polynomial bounds for killed capacity

The raw finite-variance drawdown estimate cancels the deterministic drift in
the restarted tube. This gives a polynomial bound for the killed-capacity
failure term in the paper's two-stage decomposition, without a Brownian
realization.
-/

open Filter MeasureTheory
open scoped ENNReal BigOperators Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- The raw finite-variance rate cancels the restarted tube drift when the
drift coefficient is chosen to equal the rate coefficient. -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfRawRangeRateDrawdown_canceled_of_bound
    (m ell ellN N : ℕ) (logN b v c κ p : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN) (hκ : 0 ≤ κ) (hvb : v ≤ b)
    (hc : 0 < c) (hvc : v ≤ c)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    {sigma : ℝ}
    (hκrate : κ = (Real.pi ^ 2 / 4608) * sigma ^ 2)
    (delta0 : ℝ)
    (hdrawdown : ∀ d : ℕ, d ≤ ellN - ell →
      delta0 ≤ c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) →
      (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ (2 + p) ≤ (d : ℝ) →
      iidSequenceLaw ν
        (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
          d (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
          (rightTailPositiveADrift ell ellN κ c d +
            c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) ≤
        ENNReal.ofReal (Real.exp
          (-(Real.pi ^ 2 / 4608) * sigma ^ 2 * (d : ℝ) /
            (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ 2))) :
    delta0 ≤ c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) →
    let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
    let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
    let P := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
      (fun _ : Fin m => (0 : ℝ)) id measurable_id
      (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
      (by
        intro q hq
        rcases RootIndexed.mem_initialPopulation_iff.mp hq with ⟨r, _hr, rfl⟩
        simp) ell window
      (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
      upper (rightTailPositiveARestartedWindow_subset_Iic_upper
        ell ellN logN b v c κ)
    (RootIndexed.stepFieldLaw (Root := Fin m) μ) (P.capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) *
        (((ell + 1 : ℕ) : ℝ≥0∞) +
          ((ellN - ell : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal (Real.exp
              ((-b + v) * logN +
                c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) +
                κ * c ^ p * (((ellN - ell : ℕ) : ℝ) ^ (p / 3))))) /
          (N + 1 : ℕ) := by
  have htilted : IsProbabilityMeasure (tiltedIncrementFieldLaw realPotential μ) :=
    tiltedIncrementFieldLaw_isProbability realPotential μ hboundary
  have hfirstPath : ∀ k : Fin (ellN + 1), (k : ℕ) ≤ ell →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ 1 := by
    intro k _hk
    calc
      _ ≤ (tiltedIncrementFieldLaw realPotential μ) Set.univ := by
        unfold RandomWalk.restartedWindowProbability
        exact measure_mono (Set.subset_univ _)
      _ = 1 := htilted.measure_univ
  intro hscale
  let width : ℝ := c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  let alpha : ℝ := Real.pi ^ 2 / 4608
  let pSecond : ℕ → ℝ≥0∞ := fun k =>
    if width ^ (2 + p) ≤ ((k - ell : ℕ) : ℝ) then
      ENNReal.ofReal (Real.exp
        (-alpha * sigma ^ 2 * ((k - ell : ℕ) : ℝ) / width ^ 2))
    else 1
  have hdrawdown' : ∀ k : Fin (ellN + 1), ell < (k : ℕ) →
      iidSequenceLaw ν
        (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
          ((k : ℕ) - ell) width
          (rightTailPositiveADrift ell ellN κ c ((k : ℕ) - ell) + width)) ≤
        pSecond (k : ℕ) := by
    intro k hk
    have hd : (k : ℕ) - ell ≤ ellN - ell := by omega
    by_cases hlong : width ^ (2 + p) ≤ (((k : ℕ) - ell : ℕ) : ℝ)
    · have hbound := hdrawdown ((k : ℕ) - ell) hd (by simpa [width] using hscale) hlong
      simpa [pSecond, width, alpha, hlong] using hbound
    · have hprob : iidSequenceLaw ν
          (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
            ((k : ℕ) - ell) width
            (rightTailPositiveADrift ell ellN κ c ((k : ℕ) - ell) + width)) ≤ 1 := by
        calc
          _ ≤ iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      simpa [pSecond, width, alpha, hlong] using hprob
  have hcapacity' :=
    measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfDrawdownBounds
      m ell ellN N logN b v c κ hell hellN hb hlog hκ hvb hc hvc μ hboundary
      ν hν (fun _ : ℕ => 1) pSecond hfirstPath hdrawdown'
  have hsum :
      (∑ k : Fin (ellN + 1),
        if (k : ℕ) ≤ ell then 1 else
          ENNReal.ofReal (Real.exp
            (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
              rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) *
            pSecond (k : ℕ)) ≤
      ((ell + 1 : ℕ) : ℝ≥0∞) +
        ((ellN - ell : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp
            ((-b + v) * logN + width +
              κ * c ^ p * (((ellN - ell : ℕ) : ℝ) ^ (p / 3)))) := by
    have hsumPointwise :
        (∑ k : Fin (ellN + 1),
          if (k : ℕ) ≤ ell then 1 else
            ENNReal.ofReal (Real.exp
              (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
                rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) *
              pSecond (k : ℕ)) ≤
        ∑ k : Fin (ellN + 1),
          if (k : ℕ) ≤ ell then 1 else
            if width ^ (2 + p) ≤ (((k : ℕ) - ell : ℕ) : ℝ) then
              ENNReal.ofReal (Real.exp ((-b + v) * logN + width))
            else ENNReal.ofReal (Real.exp
              (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
                rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) := by
      apply Finset.sum_le_sum
      intro k _hk
      by_cases hkle : (k : ℕ) ≤ ell
      · simp [hkle]
      · have hk : ell < (k : ℕ) := Nat.lt_of_not_ge hkle
        have hkN : (k : ℕ) ≤ ellN := Nat.le_of_lt_succ k.isLt
        by_cases hlong : width ^ (2 + p) ≤ (((k : ℕ) - ell : ℕ) : ℝ)
        · have hcancel := rightTailPositiveAWindowWeightedAH_le
            ell ellN (k : ℕ) logN b v c κ alpha sigma hellN hvc hc hk
            hkN (by dsimp [alpha]; exact hκrate)
          simpa [hkle, hlong, pSecond, width, alpha] using hcancel
        · have hd : (((k : ℕ) - ell : ℕ) : ℝ) ≤ width ^ (2 + p) :=
            le_of_not_ge hlong
          have hdrift := rightTailPositiveADrift_le_shortPrefix_power
            ell ellN ((k : ℕ) - ell) κ c p hellN hκ hc (by
              simpa [width] using hd)
          have hupper := rightTailPositiveAWindowUpper_le_generationDrift_add_width
            ell ellN (k : ℕ) logN b v c κ hellN hvc hk hkN
          have hcutoff := rightTailPositiveAWindowUpper_at_cutoff
            ell ellN logN b v c κ
          have hexponent :
              rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
                rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ) ≤
              (-b + v) * logN + width +
                κ * c ^ p * (((ellN - ell : ℕ) : ℝ) ^ (p / 3)) := by
            rw [hcutoff]
            dsimp [width]
            linarith
          simpa [hkle, hlong, pSecond] using
            (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent))
    calc
      _ ≤ _ := hsumPointwise
      _ ≤ _ := by
        simpa [width] using
          rightTailPositiveA_canceledAH_sum_le ell ellN logN b v c κ p
            hellN hκ hc hvc
  calc
    _ ≤ (m : ℝ≥0∞) *
        (∑ k : Fin (ellN + 1),
          if (k : ℕ) ≤ ell then 1 else
            ENNReal.ofReal (Real.exp
              (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
                rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) *
              pSecond (k : ℕ)) / (N + 1 : ℕ) := by
      simpa [pSecond, width, alpha] using hcapacity'
    _ ≤ (m : ℝ≥0∞) *
        (((ell + 1 : ℕ) : ℝ≥0∞) +
          ((ellN - ell : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal (Real.exp
              ((-b + v) * logN + width +
                κ * c ^ p * (((ellN - ell : ℕ) : ℝ) ^ (p / 3))))) /
          (N + 1 : ℕ) := by
      apply ENNReal.div_le_div_right
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by simp [width]

/-- The uniform raw finite-variance estimate supplies the drawdown bound
needed by the canceled two-stage capacity estimate. -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfRawRangeRateDrawdown_canceled
    (m ell ellN N : ℕ) (logN b v c κ p : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN) (hκ : 0 ≤ κ) (hvb : v ≤ b)
    (hc : 0 < c) (hvc : v ≤ c) (hp : 0 < p)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    {sigma : ℝ}
    (hspine : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    (hκrate : κ = (Real.pi ^ 2 / 4608) * sigma ^ 2) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      (delta0 ≤ c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) →
        let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
        let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
        let P := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
          (fun _ : Fin m => (0 : ℝ)) id measurable_id
          (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
          (by
            intro q hq
            rcases RootIndexed.mem_initialPopulation_iff.mp hq with ⟨r, _hr, rfl⟩
            simp) ell window
          (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          upper (rightTailPositiveARestartedWindow_subset_Iic_upper
            ell ellN logN b v c κ)
        (RootIndexed.stepFieldLaw (Root := Fin m) μ) (P.capacityEvent N ellN)ᶜ ≤
          (m : ℝ≥0∞) *
            (((ell + 1 : ℕ) : ℝ≥0∞) +
              ((ellN - ell : ℕ) : ℝ≥0∞) *
                ENNReal.ofReal (Real.exp
                  ((-b + v) * logN +
                    c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) +
                    κ * c ^ p * (((ellN - ell : ℕ) : ℝ) ^ (p / 3))))) /
              (N + 1 : ℕ)) := by
  obtain ⟨delta0, hdelta0, hraw⟩ :=
    iidSequenceLaw_rightTailPositiveASecondStageDrawdown_le_of_rawRangeRate
      ν hspine hsigma κ c p hκ hc hp
  refine ⟨delta0, hdelta0, ?_⟩
  intro hscale
  apply measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfRawRangeRateDrawdown_canceled_of_bound
    m ell ellN N logN b v c κ p hell hellN hb hlog hκ hvb hc hvc
    μ hboundary ν hν hκrate delta0 ?_ hscale
  intro d hd hwidth hlength
  exact hraw ell ellN d hellN hd hwidth hlength

/-- The killed-capacity failure term has polynomial decay under the paper's
logarithmic scales and finite-variance spine assumption. This is the first
term of the two-stage decomposition; no Brownian realization is required. -/
private theorem tendsto_log_add_one_div_log_of_cubic_scale_finiteVariance
    {u L : ℕ → ℝ} {t : ℝ}
    (hL : Tendsto L atTop atTop)
    (hu : ∀ n, 0 ≤ u n)
    (hscale : Tendsto (fun n => u n / L n ^ 3) atTop (𝓝 t))
    (ht : 0 < t) :
    Tendsto (fun n => Real.log (u n + 1) / L n) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0) :=
    hL.inv_tendsto_atTop
  have hinvCube : Tendsto (fun n => (L n)⁻¹ ^ 3) atTop (𝓝 0) := by
    simpa using hinv.pow 3
  have hLpos : ∀ᶠ n : ℕ in atTop, 0 < L n := hL.eventually_gt_atTop 0
  have hscaled : Tendsto (fun n => (u n + 1) / L n ^ 3)
      atTop (𝓝 t) := by
    have hsum := hscale.add hinvCube
    have heq : (fun n => (u n + 1) / L n ^ 3) =ᶠ[atTop]
        fun n => u n / L n ^ 3 + (L n)⁻¹ ^ 3 := by
      filter_upwards [hLpos] with n hn
      field_simp
    simpa using hsum.congr' heq.symm
  have hlogScaled : Tendsto
      (fun n => Real.log ((u n + 1) / L n ^ 3)) atTop (𝓝 (Real.log t)) :=
    (Real.continuousAt_log (ne_of_gt ht)).tendsto.comp hscaled
  have hlogScaledDiv : Tendsto
      (fun n => Real.log ((u n + 1) / L n ^ 3) / L n)
      atTop (𝓝 0) := hlogScaled.div_atTop hL
  have hlogLDiv : Tendsto (fun n => Real.log (L n) / L n)
      atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1
      (by norm_num : (1 : ℝ) ≠ 0)).comp hL
    convert h using 1
    ext n
    simp [pow_one]
  have hsum := hlogScaledDiv.add (hlogLDiv.const_mul 3)
  have heq : (fun n => Real.log (u n + 1) / L n) =ᶠ[atTop]
      fun n => Real.log ((u n + 1) / L n ^ 3) / L n +
        3 * (Real.log (L n) / L n) := by
    filter_upwards [hLpos] with n hn
    have hu1 : 0 < u n + 1 := by linarith [hu n]
    rw [Real.log_div (ne_of_gt hu1) (pow_ne_zero 3 (ne_of_gt hn)),
      Real.log_pow]
    field_simp
    ring
  simpa using hsum.congr' heq.symm

theorem eventually_rightTailPositiveAKilledCapacityFailure_le_polynomial_of_logarithmicScales_of_rawRangeRate
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    {sigma : ℝ}
    (hspine : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {a t b v c κ p : ℝ}
    (ha1 : a < 1) (ht : 0 < t)
    (hb : 0 ≤ b) (hvb : v ≤ b) (hc : 0 < c) (hvc : v ≤ c)
    (hκ : 0 ≤ κ)
    (hκrate : κ = (Real.pi ^ 2 / 4608) * sigma ^ 2)
    (hp : 0 < p) (hp1 : p < 1)
    (hmargin : a + (-b + v + c * (t ^ (3⁻¹ : ℝ))) < 1) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ᶠ n : ℕ in atTop,
      rightTailPositiveAKilledCapacityFailureProbability
        (Nat.floor ((N n : ℝ) ^ a))
        (rightTailPositiveAFirstCutoff N n)
        (logarithmicHorizon N t n) (N n)
        (logarithmOfSampleSize N n) b v c κ μ ≤
        ENNReal.ofReal (Real.exp (-epsilon * Real.log (N n : ℝ))) := by
  let m : ℕ → ℕ := fun n => Nat.floor ((N n : ℝ) ^ a)
  let ell : ℕ → ℕ := rightTailPositiveAFirstCutoff N
  let ellN : ℕ → ℕ := logarithmicHorizon N t
  let D : ℕ → ℕ := fun n => ellN n - ell n
  let L : ℕ → ℝ := logarithmOfSampleSize N
  let E : ℕ → ℝ := fun n =>
    (-b + v) * L n + c * ((D n : ℝ) ^ (3⁻¹ : ℝ)) +
      κ * c ^ p * ((D n : ℝ) ^ (p / 3))
  let P : ℕ → ℝ≥0∞ := fun n =>
    rightTailPositiveAKilledCapacityFailureProbability
      (m n) (ell n) (ellN n) (N n) (L n) b v c κ μ
  have hL : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hN)
  have hLpos : ∀ᶠ n : ℕ in atTop, 0 < L n := hL.eventually_gt_atTop 0
  have hellPos : ∀ᶠ n : ℕ in atTop, 0 < ell n := by
    simpa [ell] using
      (tendsto_rightTailPositiveAFirstCutoff_atTop hN).eventually_gt_atTop 0
  have hellN : ∀ᶠ n : ℕ in atTop, ell n < ellN n := by
    simpa [ell, ellN] using eventually_rightTailPositiveAFirstCutoff_lt_horizon hN ht
  have horder : ∀ᶠ n : ℕ in atTop, ell n ≤ ellN n :=
    hellN.mono (fun _ h => Nat.le_of_lt h)
  have hcutoffScale : Tendsto (fun n => (ell n : ℝ) / L n ^ 3)
      atTop (𝓝 0) := by
    simpa [ell, L] using tendsto_rightTailPositiveAFirstCutoff_div_logCube hN
  have hhorizonScale : Tendsto (fun n => (ellN n : ℝ) / L n ^ 3)
      atTop (𝓝 t) := by
    simpa [ellN, L] using logarithmicHorizon_div_logCube_tendsto hN ht
  have hDScale : Tendsto (fun n => (D n : ℝ) / L n ^ 3)
      atTop (𝓝 t) := by
    apply tendsto_rightTailPositiveASpan_cubicRatio_of_stageRatios hL
      hcutoffScale hhorizonScale
    exact horder
  have hfirstCountLog : Tendsto
      (fun n => Real.log ((ellN n : ℝ) + 1) / L n) atTop (𝓝 0) := by
    simpa using tendsto_log_add_one_div_log_of_cubic_scale_finiteVariance
      hL (fun _ => Nat.cast_nonneg _) hhorizonScale ht
  have hspanCountLog : Tendsto
      (fun n => Real.log ((D n : ℝ) + 1) / L n) atTop (𝓝 0) := by
    simpa using tendsto_log_add_one_div_log_of_cubic_scale_finiteVariance
      hL (fun _ => Nat.cast_nonneg _) hDScale ht
  have hERate : Tendsto (fun n => E n / L n) atTop
      (𝓝 (-b + v + c * (t ^ (3⁻¹ : ℝ)))) := by
    simpa [E, D, L, ell, ellN] using
      tendsto_rightTailPositiveAAHExponent_div_log_of_logarithmicScales
        hN ht hp1
  have hspan : Tendsto (fun n => (D n : ℝ)) atTop atTop := by
    simpa [D, ell, ellN] using
      tendsto_rightTailPositiveASpan_atTop_of_logarithmicScales hN ht
  obtain ⟨delta0, hdelta0, hrawRate⟩ :=
    iidSequenceLaw_rightTailPositiveASecondStageDrawdown_le_of_rawRangeRate
      ν hspine hsigma κ c p hκ hc hp
  have hscale := eventually_rightTailPositiveASecondStageAHScale
    D c p delta0 hc hp1 hspan
  have htiltedLog : ∀ᶠ n : ℕ in atTop, 0 ≤ L n :=
    hLpos.mono (fun _ h => h.le)
  have hm : ∀ᶠ n : ℕ in atTop, (m n : ℝ) ≤ (N n : ℝ) ^ a := by
    filter_upwards [hN.eventually_gt_atTop 0] with n hn
    dsimp [m]
    exact Nat.floor_le (by positivity : 0 ≤ (N n : ℝ) ^ a)
  have hraw : ∀ᶠ n : ℕ in atTop,
      P n ≤ (m n : ℝ≥0∞) *
        (((ell n + 1 : ℕ) : ℝ≥0∞) +
          ((D n : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (E n))) /
          (N n + 1 : ℕ) := by
    filter_upwards [hscale, hellPos, hellN, htiltedLog]
      with n hscale hnell hnorder hnlog
    have hdrawdown : ∀ d : ℕ, d ≤ ellN n - ell n →
        delta0 ≤ c * (((ellN n - ell n : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) →
        (c * (((ellN n - ell n : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ (2 + p) ≤ (d : ℝ) →
        iidSequenceLaw ν
          (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
            d (c * (((ellN n - ell n : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
            (rightTailPositiveADrift (ell n) (ellN n) κ c d +
              c * (((ellN n - ell n : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) ≤
          ENNReal.ofReal (Real.exp
            (-(Real.pi ^ 2 / 4608) * sigma ^ 2 * (d : ℝ) /
              (c * (((ellN n - ell n : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ 2)) := by
      intro d hd hwidth hlength
      exact hrawRate (ell n) (ellN n) d hnorder hd hwidth hlength
    have hcap :=
      measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfRawRangeRateDrawdown_canceled_of_bound
        (m n) (ell n) (ellN n) (N n) (L n) b v c κ p
        hnell hnorder hb hnlog hκ hvb hc hvc μ hboundary ν hν
        hκrate delta0 hdrawdown
    have hbound := hcap hscale.1
    simpa [P, rightTailPositiveAKilledCapacityFailureProbability, m, ell,
      ellN, D, E, L] using hbound
  exact eventually_probability_le_polynomial_of_canceledAH_capacity_bound
    (P := P) (m := m) (ell := ell) (ellN := ellN) (N := N) (E := E)
    hN horder (by simpa [L, logarithmOfSampleSize] using hfirstCountLog)
    (by simpa [L, D, logarithmOfSampleSize] using hspanCountLog)
    (by simpa [L, logarithmOfSampleSize] using hERate) ha1 hmargin hm hraw

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
