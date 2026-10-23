/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Scale.Basic
import Analysis.Asymptotics.Scale.Power.SmallDeviation

/-!
# A canonical scale used in the Gaussian escape-constant proof

The auxiliary declaration in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.canonicalMogulskiiScale`:
  $x_n=n^{1/4}$ tends to infinity and satisfies $x_n/\sqrt n\to0$.

This particular witness is used in the proof of the Gaussian escape
constant. The constant theorem itself accepts every `IsMogulskiiScale`.
The statement and proof follow the scale definition used in A. A. Mogul'skii,
“Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755–765; English translation, “Small Deviations in
a Space of Trajectories,” *Theory of Probability and Its Applications* 19(4)
(1975), 726–736, DOI 10.1137/1119081.
-/

open Filter
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian

/-- The choice $x_n=n^{1/4}$ is a Mogulskii scale. -/
lemma canonicalMogulskiiScale :
    IsMogulskiiScale (fun n : ℕ => Real.sqrt (Real.sqrt (n : ℝ))) := by
  rw [ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.isMogulskiiScale_iff]
  have hpow : Asymptotics.IsSmallDeviationScale
      (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ))
      (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ)) :=
    Asymptotics.isSmallDeviationScale_natCast_rpow_of_lt
      (by norm_num) (by norm_num)
  convert hpow using 1
  · funext n
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    norm_num
  · funext n
    rw [Real.sqrt_eq_rpow]

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian

end
