/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.PathCount
public import Probability.Process.RandomWalk.Path.Corridor.Affine
public import Probability.Distributions.Moments.Real
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.IndependentRoot
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.EndpointBounds

/-!
# Expected terminal population in a logarithmic corridor

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.LogarithmicCorridor.tendsto_log_expectedTerminalPopulation_div_log`:
  for a boundary-normalized branching random walk with centered finite
  variance spine and $0<v<b$, let $H_n=\lfloor(\log n)^{5/2}\rfloor$.
  If $X_n$ counts the paths through generation $H_n$ within $[-b\log n,0]$
  with terminal position at most $(v-b)\log n$, then
  $\log\mathbb E[X_n]/\log n\to v-b$.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine.LogarithmicCorridor

open Combinatorics.Branching
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

private lemma narrowerEndpointWindow_subset (H : ℕ) {t b v u : ℝ}
    (ht : 0 ≤ t) (hu : 0 ≤ u) (huv : u < v) (hvb : v < b) :
    driftedTubeEndpointWindowEvent H ((b - u) * t) 0 ((u - b) * t)
        ((v - u) / (b - u)) ⊆
      {z | history H 0 z ∈ affineCorridorThrough H (-b * t) 0 (b * t) ((v - b) * t) ∩
        {h | (u - b) * t ≤ h ⟨H, Nat.lt_succ_self H⟩}} := by
  intro z hz
  have hTerminal := hz.2
  simp only [zero_mul, zero_div, add_zero] at hTerminal
  have htermUpper : AdditivePath.displacement H z ≤ (v - b) * t := by
    refine hTerminal.2.trans_eq ?_
    have hbu : b - u ≠ 0 := ne_of_gt (by linarith)
    field_simp
    ring
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    have hbt : 0 ≤ b * t := mul_nonneg (by linarith) ht
    by_cases hi : i.val = 0
    · have : i = 0 := Fin.ext hi
      subst i
      simp only [history_zero, zero_mul, add_zero]
      constructor <;> linarith
    · have hpath := hz.1 i.val (by omega) (by omega)
      simp only [zero_mul, zero_div, add_zero] at hpath
      simp only [history_apply, zero_add, zero_mul, add_zero]
      exact ⟨(by nlinarith [mul_nonneg hu ht] : -b * t ≤ (u - b) * t).trans hpath.1,
        hpath.2.trans_eq (by ring)⟩
  · simpa only [history_apply, zero_add] using htermUpper
  · simpa only [Set.mem_ofPred_eq, history_apply, zero_add] using hTerminal.1

/-- Equation (3.12) of Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (master's thesis, Fudan University,
2026), Chapter 3, Lemma 3.8. In the lower bound, raise the corridor floor
to $(u-b)\log n$ for $0<u<v$, then send $u$ up to $v$. -/
theorem tendsto_log_expectedTerminalPopulation_div_log
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ) {sigma b v : ℝ}
    (hcentered : ProbabilityTheory.IsCenteredSecondMoment (tiltedPotentialLaw φ (-1) μ)
      (sigma ^ 2)) (hsigma : 0 < sigma) (hv : 0 < v) (hvb : v < b) :
    Tendsto (fun n : ℕ =>
      let t := Real.log (n : ℝ)
      let H := ⌊t ^ (5 / 2 : ℝ)⌋₊
      Real.log ((∫⁻ ω, pathGeneration φ H
        ((affineCorridorThrough H (-b * t) 0 (b * t) ((v - b) * t)).indicator
          (fun _ => (1 : ℝ≥0∞))) 0 ω ∂offspringFieldLaw μ).toReal) / t) atTop (𝓝 (v - b)) := by
  let t (n : ℕ) := Real.log (n : ℝ)
  let H (n : ℕ) := ⌊t n ^ (5 / 2 : ℝ)⌋₊
  let A (n : ℕ) := affineCorridorThrough (H n) (-b * t n) 0 (b * t n) ((v - b) * t n)
  let M (n : ℕ) := ∫⁻ ω, pathGeneration φ (H n)
    ((A n).indicator (fun _ => (1 : ℝ≥0∞))) 0 ω ∂offspringFieldLaw μ
  change Tendsto (fun n => Real.log (M n).toReal / t n) atTop (𝓝 (v - b))
  let ν := tiltedPotentialLaw φ (-1) μ
  let : IsProbabilityMeasure ν := tiltedPotentialLaw_isProbability φ μ hboundary
  let : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
    tiltedIncrementFieldLaw_isProbability φ μ hboundary
  have ht : Tendsto t atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hA (n : ℕ) : MeasurableSet (A n) := measurableSet_affineCorridorThrough ..
  have hupper (n : ℕ) : M n ≤ ENNReal.ofReal (Real.exp ((v - b) * t n)) := by
    refine (lintegral_pathGeneration_le_exp_mul_spineProbability φ μ hboundary (H n) 0 _
      (A n) (hA n) (fun _ hx => hx.2)).trans ?_
    simp only [sub_zero]
    exact mul_le_of_le_one_right' prob_le_one
  have hfinite (n : ℕ) : M n ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hupper n)
  have hlower {u : ℝ} (hu : 0 < u) (huv : u < v) :
      ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.exp ((u - b) * t n -
        ((Real.pi ^ 2 / 2) * sigma ^ 2 + 1) * (H n : ℝ) / ((b - u) * t n) ^ 2)) ≤ M n := by
    let d := (Real.pi ^ 2 / 2) * sigma ^ 2 + 1
    have hbu : 0 < b - u := by linarith
    have hWidth : Tendsto (fun n => (b - u) * t n) atTop atTop := ht.const_mul_atTop hbu
    have hQuarter : Tendsto (fun n => t n ^ (1 / 4 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp ht
    obtain ⟨threshold, _, hbound⟩ :=
      exists_uniform_driftedTube_endpoint_bounds hcentered hsigma
        (div_pos (sub_pos.mpr huv) hbu) (show _ < d by dsimp [d]; linarith)
        (le_refl (0 : ℝ)) (show (0 : ℝ) < 1 / 4 by norm_num)
    filter_upwards [ht.eventually_gt_atTop 0, hWidth.eventually_ge_atTop threshold,
      hQuarter.eventually_ge_atTop ((b - u) ^ (2 + 1 / 4 : ℝ))]
      with n htN hthreshold hlarge
    let W := (b - u) * t n
    let L := (u - b) * t n
    let C := A n ∩ {h | L ≤ h ⟨H n, Nat.lt_succ_self (H n)⟩}
    have hC : MeasurableSet C :=
      (hA n).inter (measurableSet_le measurable_const (measurable_pi_apply _))
    have hfloor : ⌊W ^ (2 + 1 / 4 : ℝ)⌋₊ ≤ H n := by
      apply Nat.floor_mono
      dsimp [H, W]
      rw [Real.mul_rpow hbu.le htN.le]
      calc
        _ ≤ t n ^ (2 + 1 / 4 : ℝ) * t n ^ (1 / 4 : ℝ) := by
          simpa only [mul_comm ((b - u) ^ (2 + 1 / 4 : ℝ))] using
            mul_le_mul_of_nonneg_left hlarge (Real.rpow_nonneg htN.le (2 + 1 / 4 : ℝ))
        _ = _ := by rw [← Real.rpow_add htN]; norm_num
    have hspine : ENNReal.ofReal (Real.exp (-d * (H n : ℝ) / W ^ 2)) ≤
        tiltedIncrementFieldLaw φ μ {z | history (H n) 0 z ∈ C} := by
      apply le_trans ?_ (measure_mono (narrowerEndpointWindow_subset (H n) htN.le hu.le huv hvb))
      change _ ≤ iidSequenceLaw ν _
      rw [← ofReal_measureReal (measure_ne_top _ _)]
      have hstart : 0 ≤ L + W := by
        have heq : L + W = 0 := by dsimp [L, W]; ring
        rw [heq]
      exact ENNReal.ofReal_le_ofReal (hbound W hthreshold (H n) L hfloor
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) htN.le) hstart).1
    have hmean := lintegral_pathGeneration_ge_exp_mul_spineProbability φ μ hboundary (H n) 0 L
      C hC (fun _ hx => hx.2)
    refine le_trans ?_ ((mul_le_mul_right hspine _).trans (hmean.trans ?_))
    · apply le_of_eq
      simp only [sub_zero, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      dsimp [L, W, d]
      ring
    · apply lintegral_mono
      intro ω
      unfold pathGeneration
      apply tsum_le_tsum
      intro address
      by_cases hs : address.length = H n ∧ surviveAlong ω [] address
      · simp only [pathGenerationTerm, Set.indicator, Set.mem_ofPred_eq, hs, true_and, ite_true]
        generalize pathHistory φ (H n) 0 ω address = history
        by_cases hmem : history ∈ C
        · simp only [ite_eq_left hmem, ite_eq_left hmem.1, le_refl]
        · simp only [ite_eq_right hmem, zero_le]
      · simp only [pathGenerationTerm, Set.indicator, Set.mem_ofPred_eq, hs, ite_false, le_refl]
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < (M n).toReal := by
    filter_upwards [hlower (show 0 < v / 2 by positivity) (show v / 2 < v by linarith)]
      with n h
    exact (Real.exp_pos _).trans_le (by
      simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using ENNReal.toReal_mono (hfinite n) h)
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    let u := (max 0 (a + b) + v) / 2
    have hu : 0 < u := by dsimp [u]; linarith [le_max_left (0 : ℝ) (a + b)]
    have huv : u < v := by dsimp [u]; have := max_lt hv (by linarith : a + b < v); linarith
    have hau : a < u - b := by dsimp [u]; linarith [le_max_right (0 : ℝ) (a + b)]
    let d := (Real.pi ^ 2 / 2) * sigma ^ 2 + 1
    have hd : 0 < d := by dsimp [d]; positivity
    have hbu : 0 < b - u := by linarith
    have hsmall : Tendsto (fun n => (d / (b - u) ^ 2) / t n ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp ht)
    filter_upwards [hlower hu huv, ht.eventually_gt_atTop 0,
      hsmall.eventually (Iio_mem_nhds (sub_pos.mpr hau))] with n hlo htn hcost
    have hreal := ENNReal.toReal_mono (hfinite n) hlo
    rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hreal
    have hlog := Real.log_le_log (Real.exp_pos _) hreal
    rw [Real.log_exp] at hlog
    have hcost' : (d * (H n : ℝ) / ((b - u) * t n) ^ 2) / t n ≤
        (d / (b - u) ^ 2) / t n ^ (1 / 2 : ℝ) := by
      have hH : (H n : ℝ) ≤ t n ^ (5 / 2 : ℝ) := Nat.floor_le (Real.rpow_nonneg htn.le _)
      calc
        _ ≤ (d * t n ^ (5 / 2 : ℝ) / ((b - u) * t n) ^ 2) / t n := by gcongr
        _ = _ := by
          have hhalf := Real.rpow_pos_of_pos htn (1 / 2 : ℝ)
          field_simp [htn.ne', hbu.ne', hhalf.ne']
          rw [← Real.rpow_add htn, show (5 / 2 : ℝ) + 1 / 2 = (3 : ℕ) by norm_num,
            Real.rpow_natCast]
    refine lt_of_lt_of_le ?_ (div_le_div_of_nonneg_right hlog htn.le)
    change a < ((u - b) * t n - d * (H n : ℝ) / ((b - u) * t n) ^ 2) / t n
    rw [sub_div, mul_div_cancel_right₀ _ htn.ne']
    exact lt_sub_iff_add_lt.mpr (by
      change (d / (b - u) ^ 2) / t n ^ (1 / 2 : ℝ) < u - b - a at hcost
      linarith)
  · intro a ha
    filter_upwards [hpositive, ht.eventually_gt_atTop 0] with n hpos htn
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hupper n)
    rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hreal
    have hlog := Real.log_le_log hpos hreal
    rw [Real.log_exp] at hlog
    exact lt_of_le_of_lt ((div_le_iff₀ htn).2 hlog) ha

end ProbabilityTheory.BranchingRandomWalk.Spine.LogarithmicCorridor

end
