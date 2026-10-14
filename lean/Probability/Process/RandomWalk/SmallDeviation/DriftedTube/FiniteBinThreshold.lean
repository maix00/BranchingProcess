/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.RealWidthLower

/-!
# One threshold for finitely many narrowed staircase tubes

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.exists_uniform_finiteRealWidthTubeProbability_ge_exp`:
  for finitely many fixed tube positions $a_l$ and fixed strict interior
  endpoint intervals $[u_l,v_l]$, one width threshold and one time-ratio
  threshold suffice for all $l$.

This is the finite-$l$ threshold selection in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5. The separate passage to a threshold uniform
over the varying temporal block index uses the width and ratio conditions
in the theorem below.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- A maximum of the finitely many integer-width and time-ratio thresholds
works for all spatial bins. -/
theorem exists_uniform_finiteRealWidthTubeProbability_ge_exp
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma d : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {m : ℕ} (a u v : Fin m → ℝ)
    (ha : ∀ l, 0 < a l) (haOne : ∀ l, a l < 1)
    (hu : ∀ l, 0 < u l) (huv : ∀ l, u l < v l)
    (hv : ∀ l, v l < 1)
    (hd : (Real.pi ^ 2 / 2) * sigma ^ 2 < d) :
    ∃ width₀ ratio₀ : ℕ,
      ∀ l : Fin m, ∀ width U V margin : ℝ,
        0 < width → 0 < margin →
        width₀ ≤ ⌊width⌋₊ → 1 / margin ≤ width →
        U + margin ≤ u l → v l + margin ≤ V →
        ∀ horizon : ℕ,
          ratio₀ * (⌊width⌋₊) ^ 2 ≤ horizon →
          ENNReal.ofReal (Real.exp
            (-d * (horizon : ℝ) / (⌊width⌋₊ : ℝ) ^ 2)) ≤
          horizontalTubeEndpointWindowProbability
            (iidSequenceLaw ν) (a l) width horizon U V := by
  classical
  have hperBin (l : Fin m) : ∃ width₀ ratio₀ : ℕ,
      ∀ width U V margin : ℝ,
        0 < width → 0 < margin →
        width₀ ≤ ⌊width⌋₊ → 1 / margin ≤ width →
        U + margin ≤ u l → v l + margin ≤ V →
        ∀ horizon : ℕ,
          ratio₀ * (⌊width⌋₊) ^ 2 ≤ horizon →
          ENNReal.ofReal (Real.exp
            (-d * (horizon : ℝ) / (⌊width⌋₊ : ℝ) ^ 2)) ≤
          horizontalTubeEndpointWindowProbability
            (iidSequenceLaw ν) (a l) width horizon U V :=
    exists_uniform_realWidthHorizontalTubeEndpointWindowProbability_ge_exp
      hν hsigma (ha l) (haOne l) (hu l) (huv l) (hv l) hd
  choose widthAt ratioAt hAt using hperBin
  let width₀ := Finset.univ.sup widthAt
  let ratio₀ := Finset.univ.sup ratioAt
  refine ⟨width₀, ratio₀, ?_⟩
  intro l width U V margin hwidth hmargin hwidth₀ hwidthMargin
    hmarginLower hmarginUpper horizon hratio
  have hwidthAt : widthAt l ≤ width₀ :=
    Finset.le_sup (Finset.mem_univ l)
  have hratioAt : ratioAt l ≤ ratio₀ :=
    Finset.le_sup (Finset.mem_univ l)
  apply hAt l width U V margin hwidth hmargin
    (hwidthAt.trans hwidth₀) hwidthMargin
    hmarginLower hmarginUpper horizon
  exact (Nat.mul_le_mul_right _ hratioAt).trans hratio

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
