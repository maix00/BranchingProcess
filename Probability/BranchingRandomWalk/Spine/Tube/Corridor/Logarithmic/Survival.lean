/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.Event
public import Probability.Process.RandomWalk.Path.Corridor.Affine
public import Probability.BranchingRandomWalk.Assumptions.CrossWeight
public import Probability.Distributions.Moments.Real
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.Logarithmic.TerminalExpectation
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.SecondMoment.FiniteVariance
import Analysis.Asymptotics.Sequence.LogarithmicScale

/-!
# Survival in a logarithmic corridor

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.LogarithmicCorridor.tendsto_log_survival_div_log`:
  for a boundary-normalized branching random walk with finite cross-child
  weight and centered spine of variance $\sigma^2>0$, let $b>v>0$ and
  $H_n=\lfloor(\log n)^{5/2}\rfloor$. If $p_n$ is the probability of a path
  in $[-b\log n,0]$ through generation $H_n$ with terminal position at most
  $(v-b)\log n$, then $\log(p_n)/\log n\to v-b$.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine.LogarithmicCorridor

open Combinatorics.Branching
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.RandomWalk

/-- Equation (3.10) of Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (master's thesis, Fudan University,
2026), Chapter 3, Lemma 3.8. Use the first and second moments in the corridor
with lower edge raised by $u\log n$, then take $u$ up to $v$. -/
theorem tendsto_log_survival_div_log
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ) (hcross : HasFiniteCrossWeight φ μ)
    {sigma b v : ℝ}
    (hcentered : ProbabilityTheory.IsCenteredSecondMoment (tiltedPotentialLaw φ (-1) μ)
      (sigma ^ 2)) (hsigma : 0 < sigma) (hv : 0 < v) (hvb : v < b) :
    Tendsto (fun n : ℕ =>
      let t := Real.log (n : ℝ)
      let H := ⌊t ^ (5 / 2 : ℝ)⌋₊
      Real.log ((offspringFieldLaw μ).real (hasPathHistoryIn φ H 0
        (affineCorridorThrough H (-b * t) 0 (b * t) ((v - b) * t)))) / t)
      atTop (𝓝 (v - b)) := by
  let t (n : ℕ) := Real.log (n : ℝ)
  let H (n : ℕ) := ⌊t n ^ (5 / 2 : ℝ)⌋₊
  let A (n : ℕ) := affineCorridorThrough (H n) (-b * t n) 0 (b * t n) ((v - b) * t n)
  let p (n : ℕ) := (offspringFieldLaw μ).real (hasPathHistoryIn φ (H n) 0 (A n))
  change Tendsto (fun n => Real.log (p n) / t n) atTop (𝓝 (v - b))
  have ht : Tendsto t atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hH (n : ℕ) (hn : 0 ≤ t n) : (H n : ℝ) ≤ t n ^ (5 / 2 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hn _)
  have hHpos : ∀ᶠ n in atTop, 1 ≤ H n := by
    filter_upwards [ht.eventually_ge_atTop 1] with n hn
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_rpow hn (by norm_num : (0 : ℝ) ≤ 5 / 2)
  have hHlog : Tendsto (fun n => Real.log ((H n : ℝ) + 1) / t n) atTop (𝓝 0) :=
    Asymptotics.tendsto_log_add_one_div_scale_of_power_bound ht
      (Eventually.of_forall fun n => Nat.cast_nonneg (H n)) (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) < 5 / 2)
      ((ht.eventually_gt_atTop 0).mono fun n hn => by simpa only [one_mul] using hH n hn.le)
  let K := (Real.pi ^ 2 / 2) * sigma ^ 2
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨threshold, _, hsecond⟩ :=
    exists_lintegral_pathGeneration_affineCorridor_sq_le_exp_sum_of_finiteVariance
      φ μ hboundary hcross hcentered (by positivity) (by norm_num : (0 : ℝ) < 1 / 2)
      (show (0 : ℝ) ≤ 0 from le_rfl) (show 0 < K / 2 by positivity) (show K / 2 < K by linarith)
  have hlower (a : ℝ) (ha : a < v - b) : ∀ᶠ n in atTop,
      0 < p n ∧ a < Real.log (p n) / t n := by
    let u := max 0 ((a + b + v) / 2)
    have hu : 0 ≤ u := le_max_left _ _
    have huv : u < v := max_lt hv (by linarith)
    have hau : a < u - b := by linarith [le_max_right (0 : ℝ) ((a + b + v) / 2)]
    have hbu : 0 < b - u := by linarith
    let W (n : ℕ) := (b - u) * t n
    let U (n : ℕ) := (v - b) * t n
    let C (n : ℕ) := affineCorridorThrough (H n) (-(b - u) * t n) 0 (W n) (U n)
    let M (n : ℕ) := ∫⁻ ω, pathGeneration φ (H n)
      ((C n).indicator (fun _ => (1 : ℝ≥0∞))) 0 ω ∂offspringFieldLaw μ
    have hC (n : ℕ) : MeasurableSet (C n) := measurableSet_affineCorridorThrough ..
    have hMrate : Tendsto (fun n => Real.log (M n).toReal / t n) atTop (𝓝 (v - b)) := by
      have hm := tendsto_log_expectedTerminalPopulation_div_log φ μ hboundary hcentered hsigma
        (show 0 < v - u by linarith) (show v - u < b - u by linarith)
      convert hm using 1
      · ext n
        have heq : v - u - (b - u) = v - b := by ring
        simp [M, C, W, U, H, t, heq]
      · congr 1
        ring
    have hW : Tendsto W atTop atTop := ht.const_mul_atTop hbu
    have hSqrt : Tendsto (fun n => W n ^ (1 / 2 : ℝ) / t n) atTop (𝓝 0) := by
      have hhalf : Tendsto (fun n => t n ^ (1 / 2 : ℝ)) atTop atTop :=
        (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp ht
      apply ((tendsto_const_nhds (x := (b - u) ^ (1 / 2 : ℝ))).div_atTop hhalf).congr'
      filter_upwards [ht.eventually_gt_atTop 0] with n hn
      have hhalfPos := Real.rpow_pos_of_pos hn (1 / 2 : ℝ)
      rw [show W n = (b - u) * t n from rfl, Real.mul_rpow hbu.le hn.le]
      apply (eq_div_iff hn.ne').2
      have heq : t n ^ (1 / 2 : ℝ) * t n ^ (1 / 2 : ℝ) = t n := by
        rw [← Real.rpow_add hn]; norm_num
      calc
        _ = (b - u) ^ (1 / 2 : ℝ) / t n ^ (1 / 2 : ℝ) *
            (t n ^ (1 / 2 : ℝ) * t n ^ (1 / 2 : ℝ)) := by rw [heq]
        _ = _ := by field_simp
    let gap := (u - b - a) / 4
    have hgap : 0 < gap := by dsimp [gap]; linarith
    have herrors := (hSqrt.const_mul (4 : ℝ)).add hHlog
    simp only [mul_zero, add_zero] at herrors
    filter_upwards [ht.eventually_gt_atTop 0, hW.eventually_ge_atTop threshold, hHpos,
      hMrate.eventually (Ioo_mem_nhds (sub_lt_self _ hgap) (sub_neg.mpr hvb)),
      herrors.eventually (Iio_mem_nhds hgap)] with n htn hWn hHn hMn herr
    have hmpos : 0 < (M n).toReal := by
      refine lt_of_le_of_ne ENNReal.toReal_nonneg ?_
      intro heq
      have hh : Real.log (M n).toReal / t n < 0 := hMn.2
      rw [← heq, Real.log_zero, zero_div] at hh
      exact (lt_irrefl _ hh)
    let E := (2 * v - b - u) * t n + 4 * W n ^ (1 / 2 : ℝ)
    let S : ℝ≥0∞ := (H n + 1 : ℝ≥0∞) * ENNReal.ofReal (Real.exp E)
    have hS : (∫⁻ ω, (pathGeneration φ (H n)
        ((C n).indicator (fun _ => (1 : ℝ≥0∞))) 0 ω) ^ 2 ∂offspringFieldLaw μ) ≤ S := by
      have hb := hsecond (W n) hWn (-(b - u) * t n) (by dsimp [W]; rw [neg_mul])
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) htn.le) (H n) hHn (U n)
      simp only [zero_div] at hb
      refine hb.trans ?_
      have hrate : 0 ≤ (K / 2) / W n ^ 2 := by positivity
      have hh : 0 ≤ (H n : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hHn)
      have hterm (m : Fin (H n)) :
          4 * W n ^ (1 / 2 : ℝ) + 2 * U n - 2 * (K / 2) * ((H n : ℝ) - 1) / W n ^ 2 +
            (K / 2 * (m.val : ℝ) / W n ^ 2 - (-(b - u) * t n + 0 * (m.val : ℝ))) ≤ E := by
        have hm : (m.val : ℝ) ≤ (H n : ℝ) - 1 := by
          have hhNat : m.val + 1 ≤ H n := m.isLt
          have hhR : (m.val : ℝ) + 1 ≤ (H n : ℝ) := by exact_mod_cast hhNat
          linarith
        have hmul := mul_le_mul_of_nonneg_left hm hrate
        have hminus := mul_nonneg hrate hh
        have hlin : (K / 2 / W n ^ 2) * (m.val : ℝ) -
            2 * (K / 2 / W n ^ 2) * ((H n : ℝ) - 1) ≤ 0 := by
          linarith only [hmul, hminus]
        apply sub_nonpos.mp
        convert hlin using 1
        dsimp [E, U]
        ring
      have hdiag : U n + W n ^ (1 / 2 : ℝ) - K / 2 * (H n : ℝ) / W n ^ 2 ≤ E := by
        have h1 : 0 ≤ (v - u) * t n := mul_nonneg (sub_nonneg.mpr huv.le) htn.le
        have h2 : 0 ≤ W n ^ (1 / 2 : ℝ) := Real.rpow_nonneg (mul_nonneg hbu.le htn.le) _
        have h3 : 0 ≤ K / 2 * (H n : ℝ) / W n ^ 2 := by positivity
        dsimp [U, E]
        linarith only [h1, h2, h3]
      rw [Finset.mul_sum]
      unfold S
      rw [add_mul, one_mul]
      apply add_le_add _ (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hdiag))
      calc
        _ ≤ ∑ _m : Fin (H n), ENNReal.ofReal (Real.exp E) := by
          apply Finset.sum_le_sum
          intro m _
          simp only [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hterm m))
        _ = _ := by simp [nsmul_eq_mul]
    have hSfinite : S ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, ENNReal.one_ne_top⟩)
        ENNReal.ofReal_ne_top
    have hSpos : 0 < S := lt_of_le_of_ne bot_le
      (mul_ne_zero (by simp) (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))).symm
    have hmono : hasPathHistoryIn (ι := ℕ) φ (H n) 0 (C n) ⊆ hasPathHistoryIn φ (H n) 0 (A n) := by
      rintro ω ⟨address, hdepth, hsurvive, hpath⟩
      refine ⟨address, hdepth, hsurvive, ⟨fun j => ?_, hpath.2⟩⟩
      have hj := hpath.1 j
      constructor
      · calc
          _ ≤ -(b - u) * t n + 0 * (j.val : ℝ) := by nlinarith only [mul_nonneg hu htn.le]
          _ ≤ _ := hj.1
      · refine hj.2.trans_eq ?_
        dsimp [W]
        ring
    have hpz := (measure_hasPathHistoryIn_ge_of_pathGeneration_moments φ μ
      (H n) 0 (C n) (hC n) (M n) S rfl hS hSpos hSfinite).trans (measure_mono hmono)
    have hpzReal : (M n).toReal ^ 2 / (((H n : ℝ) + 1) * Real.exp E) ≤ p n := by
      have hpReal := ENNReal.toReal_mono (measure_ne_top (offspringFieldLaw μ) _) hpz
      simpa only [S, p, Measure.real, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_mul,
        ENNReal.toReal_add (ENNReal.natCast_ne_top _) ENNReal.one_ne_top, ENNReal.toReal_natCast,
        ENNReal.toReal_one, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hpReal
    have hpos : 0 < (M n).toReal ^ 2 / (((H n : ℝ) + 1) * Real.exp E) := by positivity
    refine ⟨hpos.trans_le hpzReal, ?_⟩
    have hlog := Real.log_le_log hpos hpzReal
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow,
      Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at hlog
    refine lt_of_lt_of_le ?_ (div_le_div_of_nonneg_right hlog htn.le)
    have heq : (2 * Real.log (M n).toReal - (Real.log ((H n : ℝ) + 1) + E)) / t n =
        2 * (Real.log (M n).toReal / t n) - (2 * v - b - u) -
          (4 * (W n ^ (1 / 2 : ℝ) / t n) + Real.log ((H n : ℝ) + 1) / t n) := by
      dsimp [E]
      field_simp [htn.ne']
      ring
    norm_num only [Nat.cast_ofNat] at hlog ⊢
    rw [heq]
    have h1 : v - b - gap < Real.log (M n).toReal / t n := hMn.1
    have h2 : 4 * (W n ^ (1 / 2 : ℝ) / t n) + Real.log ((H n : ℝ) + 1) / t n < gap := herr
    dsimp [gap] at h1 h2 ⊢
    linarith only [h1, h2, hau]
  refine tendsto_order.2 ⟨fun a ha => (hlower a ha).mono fun _ h => h.2, ?_⟩
  intro a ha
  have hpos := hlower (v - b - 1) (by linarith)
  filter_upwards [hpos, ht.eventually_gt_atTop 0] with n hn htn
  let : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
    tiltedIncrementFieldLaw_isProbability φ μ hboundary
  have hbound := measure_hasPathHistoryIn_le_exp_mul_spineProbability φ μ hboundary
    (H n) 0 ((v - b) * t n) (A n) (measurableSet_affineCorridorThrough ..)
    (fun _ h => h.2)
  have hupper : p n ≤ Real.exp ((v - b) * t n) := by
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (hbound.trans (mul_le_of_le_one_right' prob_le_one))
    simpa only [p, Measure.real, sub_zero, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hreal
  have hlog := Real.log_le_log hn.1 hupper
  rw [Real.log_exp] at hlog
  exact lt_of_le_of_lt ((div_le_iff₀ htn).2 hlog) ha

end ProbabilityTheory.BranchingRandomWalk.Spine.LogarithmicCorridor

end
