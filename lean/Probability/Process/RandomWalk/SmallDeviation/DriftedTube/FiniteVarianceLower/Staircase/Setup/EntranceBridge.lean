/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Staircase.Setup.FirstWindow
public import Probability.Process.RandomWalk.SmallDeviation.Entrance.RobustTransition

/-!
# From the diffusive entrance to the first staircase block

The public theorems in this file are:

- `robustEntrance_staysInTiltedTube`:
  a path in the robust entrance event stays in
  $[r_0+ct/\Delta^2,r_0+ct/\Delta^2+\Delta]$ through $t_1$.
- `robustEntrance_entersFirstCentralWindow`:
  under $t_1+2\ell\le L$ and $10c\ell<\Delta^3$, its endpoint lies in
  the central window of the first horizontal block.

These are the initial event inclusion and first-window geometry in Wang
Yiyang, *Asymptotic speed of the $N$-branching random walk with infinite
offspring*, Chapter 3, proof of Lemma 3.5, using the robust terminal
interval provided by Appendix A.2, Lemma A.7.
-/

@[expose] public section

open ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The diffusive entrance event satisfies the tilted tube constraints up
to its terminal time. -/
theorem robustEntrance_staysInTiltedTube
    {entrance : ℕ} {width drift base : ℝ}
    {increment : ℕ → ℝ}
    (hinc : increment ∈
      robustMovingTransitionEvent entrance width drift (-base)) :
    ∀ time : ℕ, 1 ≤ time → time ≤ entrance →
      base + drift * (time : ℝ) / width ^ 2 ≤
        AdditivePath.displacement time increment ∧
      AdditivePath.displacement time increment ≤
        base + drift * (time : ℝ) / width ^ 2 + width := by
  intro time htime hle
  have htimeEq : time - 1 + 1 = time := by omega
  have hpath := hinc.1.1 ⟨time - 1, by omega⟩
  simp only [htimeEq] at hpath
  constructor <;> linarith [hpath.1, hpath.2]

/-- The robust endpoint of Wang Yiyang's Lemma A.7 lies in the first horizontal
block's central window. -/
theorem robustEntrance_entersFirstCentralWindow
    {entrance horizon blockLength : ℕ}
    {width drift base : ℝ}
    (hremaining : entrance + 2 * blockLength ≤ horizon)
    (hblockLength : 0 < blockLength)
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (hcost : 10 * drift * (blockLength : ℝ) < width ^ 3)
    {increment : ℕ → ℝ}
    (hinc : increment ∈
      robustMovingTransitionEvent entrance width drift (-base)) :
    AdditivePath.displacement entrance increment ∈
      Set.Icc
        (staircaseLowerEdge base drift width
          (staircaseBlockStart entrance horizon blockLength) 0 +
          staircaseTubeWidth width drift
            (staircaseBlockLength entrance horizon blockLength) 0 / 3)
        (staircaseLowerEdge base drift width
          (staircaseBlockStart entrance horizon blockLength) 0 +
          2 * staircaseTubeWidth width drift
            (staircaseBlockLength entrance horizon blockLength) 0 / 3) := by
  apply staircaseFirstInteriorWindow hremaining hblockLength hwidth
    hdrift hcost
  exact ⟨by linarith [hinc.2.1], by linarith [hinc.2.2]⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
