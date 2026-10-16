/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Binning.Geometry

/-!
# Admissible parameters for narrowed staircase tubes

The module-visible lemmas in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseBinWidth_pos`:
  $1-1/(3m)>0$ for $m\ge2$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseBinTubeParameter_pos`:
  the narrowed tube parameter $a_l=-b_{l+1}/(1-1/(3m))$ is positive.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseBinTubeParameter_lt_one`:
  the same parameter is less than one.

These are the parameter checks preceding the application of Lemma 3.1(ii)
in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, proof of Lemma 3.5.
-/

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

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
