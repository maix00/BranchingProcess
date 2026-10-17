/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Staircase.Binning.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Basic
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Binning.Geometry

/-!
# Admissible parameters for narrowed staircase tubes

The module-visible lemmas in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseBinWidth_pos`:
  $1-1/(3m)>0$ for $m\ge2$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseBinTubeParameter_pos`:
  the narrowed tube parameter $a_l=-b_{l+1}/(1-1/(3m))$ is positive.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseBinTubeParameter_lt_one`:
  the same parameter is less than one.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.exists_staircase_bin_count`:
  if $(\pi^2/2)\sigma^2<d$ and $v>0$, some $m\ge2$ satisfies
  $(\pi^2/2)\sigma^2<d\beta_m^2$ and $1/(3m)<v$, where
  $\beta_m=1-1/(3m)$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.exists_staircase_windows`:
  if $0<a<b<1$, $0\le A<1$, and $U>0$, there are $\delta>0$ and
  $0<u_i<v_i<1$ ($i\in\{\mathrm{int},\mathrm{low},\mathrm{up}\}$) such that
  $a+\delta<u_{\mathrm{int}}<v_{\mathrm{int}}+\delta\le b$,
  $\delta\le u_{\mathrm{low}}<v_{\mathrm{low}}+\delta\le U$, and
  $A+\delta<u_{\mathrm{up}}<v_{\mathrm{up}}+\delta\le1$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.exists_staircase_geometric_margins`:
  if $m\ge2$ and $1/(3m)<v$, the preceding window bounds hold with
  $\beta_m=1-1/(3m)$, $a=1/(3\beta_m)$,
  $b=(2/3-1/(3m))/\beta_m$, $A=\max(1-v,0)/\beta_m$, and
  $U=(v-1/(3m))/\beta_m$.

These are the parameter checks preceding the application of Lemma 3.1(ii)
in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, proof of Lemma 3.5.
-/

open Filter
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The narrowed spatial bins have positive width. -/
lemma staircaseBinWidth_pos {m : ℕ} (hm : 2 ≤ m) :
    0 < staircaseBinWidth m := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hthree : (0 : ℝ) < 3 * m := by positivity
  unfold staircaseBinWidth
  apply (sub_pos).2
  apply (div_lt_iff₀ hthree).2
  nlinarith [show (2 : ℝ) ≤ m by exact_mod_cast hm]

/-- Every selected narrowed-tube position has parameter $a_l>0$. -/
lemma staircaseBinTubeParameter_pos {m l : ℕ}
    (hm : 2 ≤ m) (hl : l < m) :
    0 < staircaseBinTubeParameter m l := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hthree : (0 : ℝ) < 3 * m := by positivity
  have hlreal : (l : ℝ) + 1 ≤ m := by
    exact_mod_cast (Nat.succ_le_iff.mpr hl)
  have hfrac : ((l : ℝ) + 1) / (3 * m) ≤ (1 : ℝ) / 3 := by
    apply (div_le_iff₀ hthree).2
    nlinarith
  have hupper : staircaseBinUpper m l < 0 := by
    have heq : staircaseBinUpper m l =
        -(2 : ℝ) / 3 + ((l : ℝ) + 1) / (3 * m) := by
      unfold staircaseBinUpper staircaseBinLower
      ring
    rw [heq]
    linarith
  unfold staircaseBinTubeParameter
  exact div_pos (neg_pos.mpr hupper) (staircaseBinWidth_pos hm)

/-- Every selected narrowed-tube position has parameter $a_l<1$. -/
lemma staircaseBinTubeParameter_lt_one {m l : ℕ}
    (hm : 2 ≤ m) :
    staircaseBinTubeParameter m l < 1 := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hthree : (0 : ℝ) < 3 * m := by positivity
  have hsum : staircaseBinUpper m l + staircaseBinWidth m =
      (1 : ℝ) / 3 + (l : ℝ) / (3 * m) := by
    unfold staircaseBinUpper staircaseBinLower staircaseBinWidth
    ring
  have hsumPos : 0 < staircaseBinUpper m l + staircaseBinWidth m := by
    rw [hsum]
    have : 0 ≤ (l : ℝ) / (3 * m) := by positivity
    linarith
  unfold staircaseBinTubeParameter
  apply (div_lt_iff₀ (staircaseBinWidth_pos hm)).2
  linarith

/-- For any rate strictly above $(\pi^2/2)\sigma^2$ and any $v>0$, choose
some $m\ge2$ so that the narrowed-bin rate remains above the critical rate and
$1/(3m)<v$. This is the bin-count choice in the proof of Lemma 3.5, Chapter 3
of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring*.
-/
lemma exists_staircase_bin_count
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


/-- Given $0<a<b<1$, $0\le A<1$, and $U>0$, choose one positive margin and
three nonempty intervals with the interior, lower, and upper containment bounds
used in the staircase proof of Lemma 3.5, Chapter 3 of Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*.
-/
lemma exists_staircase_windows
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


/-- For $m\ge2$ and $1/(3m)<v$, apply `exists_staircase_windows` to the
interior and endpoint ranges obtained from the narrowed bins in the proof of
Lemma 3.5, Chapter 3 of Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring*.
-/
lemma exists_staircase_geometric_margins
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



end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
