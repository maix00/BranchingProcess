/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Concrete.Uniform

/-!
# Finite-variance tilted-tube endpoint bounds

The public theorem in this file is:

- `exists_uniform_driftedTube_endpoint_bounds`: if the increment law has
  mean zero and variance $\sigma^2>0$, $v>0$, $c\ge0$,
  $\varepsilon>0$, and $d'>\pi^2\sigma^2/2$, one width threshold
  controls the two tilted-tube endpoint probabilities for every admissible
  initial boundary and horizon $L\ge\lfloor\Delta^{2+\varepsilon}\rfloor$.

This is Wang Yiyang, *Asymptotic speed of the $N$-branching random walk
with infinite offspring*, Chapter 3, Lemma 3.5. Its parameter selection
follows the proof there: first choose an intermediate exponential rate,
then a finite bin count, strict window margins, and an intermediate power
block length.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

private theorem exists_staircase_bin_count
    {sigma d v : ℝ}
    (hrate : (Real.pi ^ 2 / 2) * sigma ^ 2 < d)
    (hv : 0 < v) :
    ∃ m : ℕ, 2 ≤ m ∧
      (Real.pi ^ 2 / 2) * sigma ^ 2 < d * staircaseBinWidth m ^ 2 ∧
      1 / (3 * (m : ℝ)) < v := by
  have hdenom : Tendsto (fun m : ℕ => 3 * (m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 3)
  have hinv : Tendsto (fun m : ℕ => 1 / (3 * (m : ℝ))) atTop (𝓝 0) := by
    convert tendsto_inv_atTop_zero.comp hdenom using 1
    funext m
    simp [one_div, mul_inv_rev, mul_comm]
  have hbeta : Tendsto staircaseBinWidth atTop (𝓝 (1 : ℝ)) := by
    convert (tendsto_const_nhds.sub hinv : Tendsto
      (fun m : ℕ => 1 - 1 / (3 * (m : ℝ))) atTop (𝓝 (1 - 0))) using 1
    · funext m
      unfold staircaseBinWidth
      simp [one_div, mul_inv_rev, mul_comm]
    · norm_num
  have hrateLimit : Tendsto (fun m : ℕ => d * staircaseBinWidth m ^ 2)
      atTop (𝓝 d) := by
    convert tendsto_const_nhds.mul (hbeta.pow 2) using 1
    norm_num
  have hmRate : ∀ᶠ m : ℕ in atTop,
      (Real.pi ^ 2 / 2) * sigma ^ 2 < d * staircaseBinWidth m ^ 2 :=
    hrateLimit.eventually (eventually_gt_nhds hrate)
  have hmV : ∀ᶠ m : ℕ in atTop, 1 / (3 * (m : ℝ)) < v :=
    hinv.eventually (eventually_lt_nhds hv)
  obtain ⟨m, hm⟩ := (Filter.eventually_ge_atTop 2 |>.and hmRate |>.and hmV).exists
  exact ⟨m, hm.1.1, hm.1.2, hm.2⟩


private theorem exists_staircase_windows
    {a b A U : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hA : 0 ≤ A) (hA1 : A < 1) (hU : 0 < U) :
    ∃ margin uInterior vInterior uLower vLower uUpper vUpper : ℝ,
      0 < margin ∧
      0 < uInterior ∧ uInterior < vInterior ∧ vInterior < 1 ∧
      0 < uLower ∧ uLower < vLower ∧ vLower < 1 ∧
      0 < uUpper ∧ uUpper < vUpper ∧ vUpper < 1 ∧
      a + margin < uInterior ∧ vInterior + margin ≤ b ∧
      margin ≤ uLower ∧ vLower + margin ≤ U ∧
      A + margin < uUpper ∧ vUpper + margin ≤ 1 := by
  let B : ℝ := min U 1
  have hB : 0 < B := lt_min hU (by norm_num)
  have hBU : B ≤ U := min_le_left _ _
  have hB1 : B ≤ 1 := min_le_right _ _
  let uInterior : ℝ := (2 * a + b) / 3
  let vInterior : ℝ := (a + 2 * b) / 3
  let uLower : ℝ := B / 4
  let vLower : ℝ := B / 2
  let uUpper : ℝ := (A + 1) / 2
  let vUpper : ℝ := (A + 3) / 4
  let margin : ℝ := min ((b - a) / 12) (min (B / 8) ((1 - A) / 16))
  have hmargin : 0 < margin := by
    dsimp [margin]
    apply lt_min
    · positivity
    · apply lt_min <;> positivity
  have hmarginI : margin ≤ (b - a) / 12 := by
    dsimp [margin]
    exact min_le_left _ _
  have hmarginB : margin ≤ B / 8 := by
    dsimp [margin]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hmarginA : margin ≤ (1 - A) / 16 := by
    dsimp [margin]
    exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨margin, uInterior, vInterior, uLower, vLower,
    uUpper, vUpper, hmargin, ?_⟩
  repeat' constructor
  all_goals dsimp [uInterior, vInterior, uLower, vLower, uUpper, vUpper]
  all_goals linarith


private theorem exists_staircase_geometric_margins
    {m : ℕ} (hm : 2 ≤ m) {v : ℝ}
    (hv : 1 / (3 * (m : ℝ)) < v) :
    ∃ margin uInterior vInterior uLower vLower uUpper vUpper : ℝ,
      0 < margin ∧
      0 < uInterior ∧ uInterior < vInterior ∧ vInterior < 1 ∧
      0 < uLower ∧ uLower < vLower ∧ vLower < 1 ∧
      0 < uUpper ∧ uUpper < vUpper ∧ vUpper < 1 ∧
      (1 / 3 : ℝ) / staircaseBinWidth m + margin < uInterior ∧
      vInterior + margin ≤
        ((2 / 3 : ℝ) - 1 / (3 * (m : ℝ))) / staircaseBinWidth m ∧
      margin ≤ uLower ∧
      vLower + margin ≤
        (v - 1 / (3 * (m : ℝ))) / staircaseBinWidth m ∧
      max (1 - v) 0 / staircaseBinWidth m + margin < uUpper ∧
      vUpper + margin ≤ 1 := by
  let t : ℝ := 1 / (3 * (m : ℝ))
  let beta : ℝ := staircaseBinWidth m
  let a : ℝ := (1 / 3 : ℝ) / beta
  let b : ℝ := ((2 / 3 : ℝ) - t) / beta
  let A : ℝ := max (1 - v) 0 / beta
  let U : ℝ := (v - t) / beta
  have hbeta : 0 < beta := staircaseBinWidth_pos hm
  have hbetaEq : beta = 1 - t := by
    dsimp [beta, t, staircaseBinWidth]
  have hmreal : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hdenom : 0 < 3 * (m : ℝ) := by positivity
  have htSmall : t < 1 / 3 := by
    dsimp [t]
    apply (div_lt_iff₀ hdenom).2
    nlinarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a < b := by
    dsimp [a, b]
    apply (div_lt_div_iff₀ hbeta hbeta).2
    nlinarith [sq_pos_of_pos hbeta]
  have hb : b < 1 := by
    dsimp [b]
    apply (div_lt_iff₀ hbeta).2
    linarith
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hA1 : A < 1 := by
    dsimp [A]
    apply (div_lt_iff₀ hbeta).2
    apply max_lt
    · dsimp [t] at hbetaEq
      linarith
    · simpa using hbeta
  have hU : 0 < U := by
    dsimp [U]
    exact div_pos (sub_pos.mpr hv) hbeta
  exact exists_staircase_windows ha hab hb hA hA1 hU


/-- The two endpoint forms of Wang Yiyang's Lemma 3.5, with one real-width
threshold uniform in the horizon and the initial tube position. -/
theorem exists_uniform_driftedTube_endpoint_bounds
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma v d drift epsilon : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    (hv : 0 < v)
    (hrate : (Real.pi ^ 2 / 2) * sigma ^ 2 < d)
    (hdrift : 0 ≤ drift)
    (hepsilon : 0 < epsilon) :
    ∃ threshold : ℝ, 0 < threshold ∧
      ∀ width ≥ threshold, ∀ horizon : ℕ, ∀ base : ℝ,
      Nat.floor (width ^ (2 + epsilon)) ≤ horizon →
      base ≤ 0 → 0 ≤ base + width →
      Real.exp (-d * (horizon : ℝ) / width ^ 2) ≤
        (iidSequenceLaw ν).real
          (driftedTubeEndpointWindowEvent horizon width drift base v) ∧
      Real.exp (-d * (horizon : ℝ) / width ^ 2) ≤
        (iidSequenceLaw ν).real
          (driftedTubeUpperEndpointWindowEvent horizon width drift base v) := by
  let criticalRate : ℝ := (Real.pi ^ 2 / 2) * sigma ^ 2
  let blockRate : ℝ := (criticalRate + d) / 2
  have hcriticalNonneg : 0 ≤ criticalRate := by
    dsimp [criticalRate]
    positivity
  have hblockCritical : criticalRate < blockRate := by
    dsimp [blockRate, criticalRate]
    linarith
  have hblockNonneg : 0 ≤ blockRate :=
    hcriticalNonneg.trans hblockCritical.le
  have hdelta : 0 < d - blockRate := by
    dsimp [blockRate, criticalRate]
    linarith
  obtain ⟨m, hm, hmRate, hmV⟩ :=
    exists_staircase_bin_count hblockCritical hv
  change criticalRate < blockRate * staircaseBinWidth m ^ 2 at hmRate
  let narrowedRate : ℝ :=
    (criticalRate + blockRate * staircaseBinWidth m ^ 2) / 2
  have hnarrowedK : criticalRate < narrowedRate := by
    dsimp [narrowedRate]
    linarith
  have hnarrowedBlock :
      narrowedRate < blockRate * staircaseBinWidth m ^ 2 := by
    dsimp [narrowedRate]
    linarith
  obtain ⟨margin, uInterior, vInterior, uLower, vLower,
    uUpper, vUpper, hmargin, huInterior, huvInterior, hvInterior,
    huLower, huvLower, hvLower, huUpper, huvUpper, hvUpper,
    hinteriorLower, hinteriorUpper, hlowerLower, hlowerUpper,
    hupperLower, hupperUpper⟩ :=
    exists_staircase_geometric_margins hm hmV
  let eta : ℝ := min epsilon 1 / 2
  have heta : 0 < eta := by
    dsimp [eta]
    exact div_pos (lt_min hepsilon (by norm_num)) (by norm_num)
  have hetaOne : eta < 1 := by
    dsimp [eta]
    have h := min_le_right epsilon 1
    linarith
  have hetaEpsilon : eta < epsilon := by
    dsimp [eta]
    have h := min_le_left epsilon 1
    have hpos := lt_min hepsilon (by norm_num : (0 : ℝ) < 1)
    linarith
  have hupperFinal : vUpper + margin ≤
      (1 - 1 / (3 * (m : ℝ))) / staircaseBinWidth m := by
    have hratio : (1 - 1 / (3 * (m : ℝ))) /
        staircaseBinWidth m = 1 := by
      change staircaseBinWidth m / staircaseBinWidth m = 1
      exact div_self (ne_of_gt (staircaseBinWidth_pos hm))
    rw [hratio]
    exact hupperUpper
  obtain ⟨threshold, hthreshold⟩ :=
    exists_uniform_concreteStaircase_bounds_of_powerBlock
    hν hsigma m hm huInterior huvInterior hvInterior huLower huvLower hvLower
    huUpper huvUpper hvUpper hnarrowedK heta hetaOne hetaEpsilon
    hmargin hdrift (by exact le_of_lt hv) hblockNonneg
    hepsilon hdelta hnarrowedBlock
    hinteriorLower hinteriorUpper hlowerLower hlowerUpper
    hupperLower hupperFinal
  refine ⟨max 1 threshold,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left 1 threshold), ?_⟩
  intro width hwidth horizon base hhorizon hbase hbaseWidth
  have hstart : -base ∈ Set.Icc 0 width := by
    constructor <;> linarith
  exact hthreshold width ((le_max_right 1 threshold).trans hwidth)
    horizon base hhorizon hstart

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
