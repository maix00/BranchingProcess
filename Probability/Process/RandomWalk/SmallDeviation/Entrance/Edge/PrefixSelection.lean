/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Moments.BoundedWindows

/-!
# Fixed entrance prefixes for the two edge intervals

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.exists_positive_mass_prefixes`:
  for a centered law with variance $\sigma^2>0$ and $c\ge0$, there are
  fixed positive and negative increment windows $[a_+,b_+]$ and
  $[a_-,b_-]$ of positive probability, and fixed prefix lengths
  $m_+,m_-$ with $m_+a_+>c+1$ and $m_-a_->c+1$.

This is the finite-prefix selection in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Appendix A.2, Lemma A.7, used in the proof of Chapter 3, Lemma 3.5.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- Positive-mass increment windows and fixed prefix lengths on both edges
of the entrance corridor. -/
theorem exists_positive_mass_prefixes
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) (drift : ℝ) :
    ∃ aPlus bPlus aMinus bMinus : ℝ, ∃ mPlus mMinus : ℕ,
      0 < aPlus ∧ aPlus < bPlus ∧
      0 < ν (Set.Icc aPlus bPlus) ∧
      0 < aMinus ∧ aMinus < bMinus ∧
      0 < (ν.map fun x : ℝ => -x) (Set.Icc aMinus bMinus) ∧
      drift + 1 < (mPlus : ℝ) * aPlus ∧
      drift + 1 < (mMinus : ℝ) * aMinus := by
  obtain ⟨aPlus, bPlus, haPlus, habPlus, hpPlus⟩ :=
    hν.exists_pos_Icc_measure_pos hsigma
  obtain ⟨aMinus, bMinus, haMinus, habMinus, hpMinus⟩ :=
    hν.exists_reflected_pos_Icc_measure_pos hsigma
  obtain ⟨mPlus, hmPlus⟩ := exists_nat_gt ((drift + 1) / aPlus)
  obtain ⟨mMinus, hmMinus⟩ := exists_nat_gt ((drift + 1) / aMinus)
  refine ⟨aPlus, bPlus, aMinus, bMinus, mPlus, mMinus,
    haPlus, habPlus, hpPlus, haMinus, habMinus, hpMinus, ?_, ?_⟩
  · exact (div_lt_iff₀ haPlus).mp hmPlus
  · exact (div_lt_iff₀ haMinus).mp hmMinus

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
