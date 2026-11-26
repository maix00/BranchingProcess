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
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceUpper.Basic
import all Probability.BranchingRandomWalk.Spine.Tube.Corridor.Critical.Lemmas.Scale

/-!
# Expected cumulative population in a critical affine corridor

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.CriticalCorridor.tendsto_log_expectedCumulativePopulation_div_cubeRoot`:
  for a boundary-normalized branching random walk with centered spine of
  variance $\sigma^2>0$, take $\Delta=cN^{1/3}$, $c>0$, and
  $r_j=(\pi^2\sigma^2/2)j/\Delta^2$.
  If $X_j$ counts the generation-$j$ paths within $[r_i,r_i+\Delta]$,
  then $N^{-1/3}\log\mathbb E[\sum_{j=1}^N X_j]\to c$.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine.CriticalCorridor

open Combinatorics.Branching
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

private lemma criticalPrefix_iff_driftedTube (j : ℕ) (width K : ℝ)
    (hw : 0 ≤ width) (z : ℕ → ℝ) :
    history j 0 z ∈ affineCorridorPrefix j 0 (K / width ^ 2) width ↔
      z ∈ driftedTubeEvent j width K 0 := by
  constructor
  · intro hz i _ hij
    have h := hz ⟨i, by omega⟩
    simpa [history_apply, div_mul_eq_mul_div] using h
  · intro hz i
    have hi : i.val ≤ j := by omega
    by_cases hzero : i.val = 0
    · have : i = 0 := Fin.ext hzero
      subst i
      simpa using hw
    · have h := hz i.val (by omega) hi
      simpa [history_apply, div_mul_eq_mul_div] using h

/-- Equation (3.11) of Wang Yiyang, *Asymptotic Speed of the N-Branching Random
Walk with Infinite Offspring* (master's thesis, Fudan University, 2026),
Chapter 3, Lemma 3.7. The upper bound sums the generation bounds from Lemma
3.4; the lower bound uses only the last generation and the upper endpoint
window from Lemma 3.5. -/
theorem tendsto_log_expectedCumulativePopulation_div_cubeRoot
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    {sigma c : ℝ}
    (hcentered : ProbabilityTheory.IsCenteredSecondMoment (tiltedPotentialLaw φ (-1) μ)
      (sigma ^ 2)) (hsigma : 0 < sigma) (hc : 0 < c) :
    let K := (Real.pi ^ 2 / 2) * sigma ^ 2
    Tendsto (fun N : ℕ =>
      let t := (N : ℝ) ^ (1 / 3 : ℝ)
      let width := c * t
      Real.log ((∫⁻ ω, ∑ j ∈ Finset.Icc 1 N, pathGeneration φ j
        ((affineCorridorPrefix j 0 (K / width ^ 2) width).indicator
          (fun _ => (1 : ℝ≥0∞))) 0 ω ∂offspringFieldLaw μ).toReal) / t) atTop (𝓝 c) := by
  intro K
  have hK : 0 < K := by dsimp [K]; positivity
  let ν := tiltedPotentialLaw φ (-1) μ
  let : IsProbabilityMeasure ν := tiltedPotentialLaw_isProbability φ μ hboundary
  let t (N : ℕ) := (N : ℝ) ^ (1 / 3 : ℝ)
  let width (N : ℕ) := c * t N
  let A (N j : ℕ) := affineCorridorPrefix j 0 (K / width N ^ 2) (width N)
  let M (N j : ℕ) := ∫⁻ ω, pathGeneration φ j
    ((A N j).indicator (fun _ => (1 : ℝ≥0∞))) 0 ω ∂offspringFieldLaw μ
  let total (N : ℕ) := ∑ j ∈ Finset.Icc 1 N, M N j
  have hidentity (N : ℕ) :
      (∫⁻ ω, ∑ j ∈ Finset.Icc 1 N, pathGeneration φ j
        ((A N j).indicator (fun _ => (1 : ℝ≥0∞))) 0 ω ∂offspringFieldLaw μ) = total N :=
    lintegral_finsetSum _ fun j _ =>
      pathGeneration_measurable φ j (measurable_const.indicator (measurableSet_affineCorridorPrefix ..)) 0
  change Tendsto (fun N : ℕ => Real.log ((∫⁻ ω, ∑ j ∈ Finset.Icc 1 N,
    pathGeneration φ j ((A N j).indicator (fun _ => (1 : ℝ≥0∞))) 0 ω
      ∂offspringFieldLaw μ).toReal) / t N) atTop (𝓝 c)
  simp_rw [hidentity]
  obtain ⟨_ht, hw, htpos, hratioRaw, hscale, hsqrt, hcount⟩ := cubeRootWidthFacts hc
  have hratio (N : ℕ) (hN : 1 ≤ N) : (N : ℝ) / width N ^ 2 = t N / c ^ 2 :=
    hratioRaw N hN
  have hupper {δ : ℝ} (hδ : 0 < δ) (hδK : δ < K) :
      ∀ᶠ N : ℕ in atTop, total N ≤ (N + 1 : ℝ≥0∞) * ENNReal.ofReal (Real.exp
        (width N + width N ^ (1 / 2 : ℝ) + δ * (N : ℝ) / width N ^ 2)) := by
    obtain ⟨threshold, hone, hbound⟩ :=
      exists_driftedTubeProbability_le_exp_of_finiteVariance ν hcentered (by positivity)
        (by norm_num : (0 : ℝ) < 1 / 2) hK.le
        (show 0 < K - δ by linarith) (show K - δ < K by linarith)
    filter_upwards [hw.eventually_ge_atTop threshold] with N hN
    have hwN : 0 ≤ width N := by linarith [hone.trans hN]
    let U := width N + width N ^ (1 / 2 : ℝ) + δ * (N : ℝ) / width N ^ 2
    have hterm (j : ℕ) (hj : j ∈ Finset.Icc 1 N) : M N j ≤ ENNReal.ofReal (Real.exp U) := by
      have hle := (Finset.mem_Icc.mp hj).2
      have hterminal : ∀ history ∈ A N j, history ⟨j, Nat.lt_succ_self j⟩ ≤
          K / width N ^ 2 * (j : ℝ) + width N := by
        intro history hhistory
        simpa only [zero_add] using (hhistory ⟨j, Nat.lt_succ_self j⟩).2
      refine (lintegral_pathGeneration_le_exp_mul_spineProbability φ μ hboundary j 0 _
        (A N j) (measurableSet_affineCorridorPrefix ..) hterminal).trans ?_
      have hevent : {z | history j 0 z ∈ A N j} =
          driftedTubeEvent j (width N) K 0 := Set.ext (criticalPrefix_iff_driftedTube j _ K hwN)
      have htube : tiltedIncrementFieldLaw φ μ {z | history j 0 z ∈ A N j} ≤
          ENNReal.ofReal (Real.exp (width N ^ (1 / 2 : ℝ) -
            (K - δ) * ((j : ℝ) / width N ^ 2))) := by
        rw [hevent]
        change iidSequenceLaw ν _ ≤ _
        rw [← ofReal_measureReal (measure_ne_top _ _)]
        exact ENNReal.ofReal_le_ofReal (hbound _ hN 0 (by linarith) le_rfl j)
      refine (mul_le_mul_right htube _).trans ?_
      simp only [sub_zero, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hmono : δ * (j : ℝ) / width N ^ 2 ≤ δ * (N : ℝ) / width N ^ 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hle) hδ.le) (sq_nonneg _)
      convert add_le_add_right hmono (width N + width N ^ (1 / 2 : ℝ)) using 1; ring
    calc
      total N ≤ ∑ _j ∈ Finset.Icc 1 N, ENNReal.ofReal (Real.exp U) :=
        Finset.sum_le_sum hterm
      _ ≤ _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        apply mul_le_mul_left
        exact_mod_cast (show (Finset.Icc 1 N).card ≤ N + 1 by simp)
  have hlower {δ u : ℝ} (hδ : 0 < δ) (hu : 0 < u) :
      ∀ᶠ N : ℕ in atTop, ENNReal.ofReal (Real.exp
        (width N - u * width N - δ * (N : ℝ) / width N ^ 2)) ≤ total N := by
    obtain ⟨threshold, _, hbound⟩ :=
      exists_uniform_driftedTube_endpoint_bounds hcentered hsigma hu
        (show K < K + δ by linarith) hK.le (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [hw.eventually_ge_atTop threshold, hscale,
      eventually_ge_atTop (1 : ℕ)] with N hN hfloor hpos
    have hwN : 0 ≤ width N := mul_nonneg hc.le (htpos N hpos).le
    let L := K * (N : ℝ) / width N ^ 2 + width N - u * width N
    let C := A N N ∩ {h | L ≤ h ⟨N, Nat.lt_succ_self N⟩}
    have hC : MeasurableSet C :=
      (measurableSet_affineCorridorPrefix ..).inter (measurableSet_le measurable_const (measurable_pi_apply _))
    have hsub : driftedTubeUpperEndpointWindowEvent N (width N) K 0 u ⊆
        {z | history N 0 z ∈ C} := by
      intro z hz
      exact ⟨(criticalPrefix_iff_driftedTube N _ K hwN z).2 hz.1,
        by simpa [L, history_apply] using hz.2.1⟩
    have htube : ENNReal.ofReal (Real.exp (-(K + δ) * (N : ℝ) / width N ^ 2)) ≤
        tiltedIncrementFieldLaw φ μ {z | history N 0 z ∈ C} := by
      apply le_trans ?_ (measure_mono hsub)
      change _ ≤ iidSequenceLaw ν _
      rw [← ofReal_measureReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal (hbound _ hN N 0 hfloor le_rfl (by simpa only [zero_add] using hwN)).2
    have hmean := lintegral_pathGeneration_ge_exp_mul_spineProbability φ μ hboundary N 0 L
      C hC (fun _ hx => hx.2)
    refine le_trans ?_ ((mul_le_mul_right htube _).trans (hmean.trans ?_))
    · apply le_of_eq
      simp only [sub_zero, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      dsimp [L]
      ring
    · refine le_trans ?_ (Finset.single_le_sum (f := fun j => M N j)
        (fun _ _ => zero_le) (Finset.mem_Icc.mpr ⟨hpos, le_rfl⟩))
      apply lintegral_mono
      intro ω
      unfold pathGeneration
      apply tsum_le_tsum
      intro address
      by_cases hsurv : address.length = N ∧ surviveAlong ω [] address
      · simp only [pathGenerationTerm, Set.indicator, Set.mem_ofPred_eq, hsurv, true_and, ite_true]
        generalize pathHistory φ N 0 ω address = history
        by_cases hmem : history ∈ C
        · simp only [ite_eq_left hmem, ite_eq_left hmem.1, le_refl]
        · simp only [ite_eq_right hmem, zero_le]
      · simp only [pathGenerationTerm, Set.indicator, Set.mem_ofPred_eq, hsurv, ite_false, le_refl]
  have hfinite : ∀ᶠ N : ℕ in atTop, total N ≠ ⊤ := by
    filter_upwards [hupper (show 0 < K / 2 by positivity) (show K / 2 < K by linarith)] with N h
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, ENNReal.one_ne_top⟩)
        ENNReal.ofReal_ne_top) h
  have hpositive : ∀ᶠ N : ℕ in atTop, 0 < (total N).toReal := by
    filter_upwards [hfinite, hlower (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1)] with N hfin h
    exact lt_of_lt_of_le (Real.exp_pos _)
      (by simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using ENNReal.toReal_mono hfin h)
  change Tendsto (fun N => Real.log (total N).toReal / t N) atTop (𝓝 c)
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    let δ := (c - a) * c ^ 2 / 4
    let u := (c - a) / (4 * c)
    have hgap : 0 < c - a := sub_pos.mpr ha
    filter_upwards [hlower (show 0 < δ by dsimp [δ]; positivity)
      (show 0 < u by dsimp [u]; positivity), hfinite,
      eventually_ge_atTop (1 : ℕ)] with N hlow hfin hN
    have htN : 0 < t N := htpos N hN
    have hlowReal := ENNReal.toReal_mono hfin hlow
    rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hlowReal
    have hlog := Real.log_le_log (Real.exp_pos _) hlowReal
    rw [Real.log_exp] at hlog
    apply (lt_div_iff₀ htN).2
    have heq : width N - u * width N - δ * (N : ℝ) / width N ^ 2 =
        ((c + a) / 2) * t N := by
      rw [mul_div_assoc, hratio N hN]
      dsimp [δ, u, width]
      field_simp
      ring
    rw [heq] at hlog
    exact (mul_lt_mul_of_pos_right (by linarith : a < (c + a) / 2) htN).trans_le hlog
  · intro a ha
    let δ := min (K / 2) ((a - c) * c ^ 2 / 4)
    have hgap : 0 < a - c := sub_pos.mpr ha
    have hδ : 0 < δ := lt_min (by positivity) (by positivity)
    have hδK : δ < K := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδbound : δ / c ^ 2 ≤ (a - c) / 4 := by
      apply (div_le_iff₀ (sq_pos_of_pos hc)).2
      convert (min_le_right (K / 2) ((a - c) * c ^ 2 / 4)) using 1; ring
    filter_upwards [hupper hδ hδK, hpositive, eventually_ge_atTop (1 : ℕ),
      (hsqrt.add hcount).eventually (Iio_mem_nhds (by linarith :
        0 + 0 < (a - c) / 2))] with N hup hpos hN herr
    have htN : 0 < t N := htpos N hN
    have hfin : (N + 1 : ℝ≥0∞) * ENNReal.ofReal (Real.exp
        (width N + width N ^ (1 / 2 : ℝ) + δ * (N : ℝ) / width N ^ 2)) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, ENNReal.one_ne_top⟩)
        ENNReal.ofReal_ne_top
    have hreal := ENNReal.toReal_mono hfin hup
    simp only [ENNReal.toReal_mul,
      ENNReal.toReal_add (ENNReal.natCast_ne_top _) ENNReal.one_ne_top,
      ENNReal.toReal_natCast, ENNReal.toReal_one,
      ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hreal
    have hlog := Real.log_le_log hpos hreal
    rw [Real.log_mul (by positivity : (N : ℝ) + 1 ≠ 0) (Real.exp_ne_zero _),
      Real.log_exp] at hlog
    apply lt_of_le_of_lt (div_le_div_of_nonneg_right hlog htN.le)
    have heq : (Real.log ((N : ℝ) + 1) + (width N + width N ^ (1 / 2 : ℝ) +
        δ * (N : ℝ) / width N ^ 2)) / t N =
        c + δ / c ^ 2 + (width N ^ (1 / 2 : ℝ) / t N + Real.log ((N : ℝ) + 1) / t N) := by
      rw [mul_div_assoc, hratio N hN, show width N = c * t N from rfl]
      field_simp
      ring
    rw [heq]
    change width N ^ (1 / 2 : ℝ) / t N + Real.log ((N : ℝ) + 1) / t N < (a - c) / 2 at herr
    linarith

end ProbabilityTheory.BranchingRandomWalk.Spine.CriticalCorridor

end
