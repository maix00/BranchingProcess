/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Scale.Basic
public import Probability.BranchingRandomWalk.Spine.RandomWalk.IncrementProcess
public import Probability.BranchingRandomWalk.Spine.Tube.MRCA.Expansion
public import Probability.Process.RandomWalk.SmallDeviation.Entrance.FiniteVariance.EndpointCorridor
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.BlockLength

/-!
# Finite variance spine corridors

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.endpointCorridorEvent_eq_affineCorridorThrough`
  identifies the finite-variance endpoint event with the affine-history event:
  `InClosedInterval (-ratio * D) 0 n 0 increment ∧ S_n ∈ [−ratio * D, (1 − ratio) * D]`
  iff `history n 0 increment ∈ affineCorridorThrough n ...`.
* `ProbabilityTheory.BranchingRandomWalk.Spine.exists_eventually_tiltedIncrementFieldLaw_affineCorridor_lowerBound_of_centeredSecondMoment`
  assumes a centered tilted law with variance `sigma² > 0`, a Mogulskii scale,
  and `ratio > 1`; for all sufficiently large `n` it gives an explicit
  lower bound for the tilted probability of
  `G_n := {increment | history n 0 increment ∈ affineCorridorThrough n
  (-ratio * scale n) 0 (ratio * scale n) ((-ratio + 1) * scale n)}`.
  More precisely, for some `C < 0`, `q > 0`, and `A > 0`, put
  `B_n := stableBlockLength 2 ν A² scale n` and
  `R_n := balancedBlockCount (finiteVarianceBridgeLength scale n - B_n) B_n + 1`;
  then `exp (((C / (ratio / 2 - 13 / 60)² - 1) * A²)) ^ R_n *
  (q / finiteVarianceEntranceLength scale n) ≤ P_tilted(G_n)` eventually.

The entrance and stable endpoint bridge probability is rewritten as the
affine corridor event used by the branching random walk path count.

The endpoint window is the lower-window form of Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(master's thesis, Fudan University, 2026), Chapter 4, Lemma 4.3. Its path-rate
constant follows the finite-variance case of A. A. Mogul'skii, Theorem 3,
Section 4, p. 764, “Small deviations in the sample function space,”
*Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755–765; English
translation, “Small Deviations in a Space of Trajectories,” *Theory of
Probability and Its Applications* 19(4) (1975), 726–736,
DOI 10.1137/1119081.

Write \(\nu=\operatorname{tiltedPotentialLaw}(\varphi,-1,\mu)\) and
\(P_{\mathrm{tilt}}=\operatorname{tiltedIncrementFieldLaw}(\varphi,\mu)\).
For \(G_n=\{z:\operatorname{history}_n(0,z)\in
\operatorname{affineCorridorThrough}(n,-rL_n,0,rL_n,(-r+1)L_n)\}\),
the event conversion identifies the fixed-window entrance event with \(G_n\).
Given the centered second moment \(\sigma^2>0\), a Mogulskii scale \(L_n\),
and \(r>1\), there are \(C<0,\ q>0,\ A>0\) and \(n_0\) such that, for
\(n\ge n_0\), putting
\(B_n=\operatorname{stableBlockLength}(2,\nu,A^2,L_n,n)\) and
\(R_n=\operatorname{balancedBlockCount}
(\operatorname{finiteVarianceBridgeLength}(L_n,n)-B_n,B_n)+1\), one has
\[
 \exp\!\left(\left(\frac{C}{(r/2-13/60)^2}-1\right)A^2R_n\right)
 \frac{q}{\operatorname{finiteVarianceEntranceLength}(L_n,n)}
\le P_{\mathrm{tilt}}(G_n).
\]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
open ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The fixed-window event from the finite-variance random-walk corridor
estimate is exactly the affine path corridor used in the spine pair expansion. -/
theorem endpointCorridorEvent_eq_affineCorridorThrough
    (n : ℕ) (D ratio : ℝ) :
    {increment : ℕ → ℝ |
      InClosedInterval (-ratio * D) 0 n 0 increment ∧
        AdditivePath.displacement n increment ∈
          Set.Icc (-ratio * D) ((-ratio + 1) * D)} =
    {increment : ℕ → ℝ |
      RandomWalk.history n 0 increment ∈
        affineCorridorThrough n (-ratio * D) 0 (ratio * D)
          ((-ratio + 1) * D)} := by
  ext increment
  simp only [Set.mem_ofPred_eq, InClosedInterval, InWindows,
    affineCorridorThrough]
  have hwidth : -ratio * D + ratio * D = 0 := by ring
  have hlast : RandomWalk.history n 0 increment
      ⟨n, Nat.lt_succ_self n⟩ = AdditivePath.displacement n increment := by
    simp [history_eq_fromIncrements, AdditivePath.fromIncrements]
  constructor
  · rintro ⟨hpath, hend⟩
    constructor
    · intro k
      rcases Set.mem_Icc.mp (hpath k) with ⟨hlo, hhi⟩
      constructor
      · simpa only [zero_mul, add_zero] using hlo
      · simpa only [zero_mul, add_zero, hwidth] using hhi
    · simpa only [hlast] using hend.2
  · rintro ⟨hpath, hend⟩
    constructor
    · intro k
      rcases hpath k with ⟨hlo, hhi⟩
      have hupper : history n 0 increment k ≤ 0 := by
        simpa only [zero_mul, add_zero, hwidth] using hhi
      exact Set.mem_Icc.mpr
        ⟨by simpa only [zero_mul, add_zero] using hlo, hupper⟩
    · have hlastPath := hpath ⟨n, Nat.lt_succ_self n⟩
      have hlower : -ratio * D ≤ AdditivePath.displacement n increment := by
        calc
          -ratio * D = -ratio * D + 0 * (n : ℝ) := by ring
          _ ≤ history n 0 increment ⟨n, Nat.lt_succ_self n⟩ := hlastPath.1
          _ = AdditivePath.displacement n increment := hlast
      have hupper : AdditivePath.displacement n increment ≤ (-ratio + 1) * D := by
        calc
          AdditivePath.displacement n increment =
              history n 0 increment ⟨n, Nat.lt_succ_self n⟩ := hlast.symm
          _ ≤ (-ratio + 1) * D := hend
      exact ⟨hlower, hupper⟩

/-- Finite variance gives an explicit lower bound on the tilted-spine
probability of the affine corridor. The lower bound is the entrance factor
times the stable cell-bridge factor, with every stable-process input derived
inside the random-walk theorem from the centered second moment. -/
theorem exists_eventually_tiltedIncrementFieldLaw_affineCorridor_lowerBound_of_centeredSecondMoment
    {ι : Type*} [Countable ι] {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ι X))
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw φ (-1) μ)
    {sigma : ℝ} (hνMoment : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) {scale : ℕ → ℝ}
    (hscale : Asymptotics.IsSmallDeviationScale scale
      (fun n => Real.sqrt n))
    (ratio : ℝ) (hratio : 1 < ratio) :
    ∃ C : ℝ, C < 0 ∧ ∃ q : ℝ≥0∞, 0 < q ∧
      ∃ amplitude : ℝ, 0 < amplitude ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ENNReal.ofReal (Real.exp
          ((C / ((ratio / 2 - 13 / 60) ^ (2 : ℝ)) - 1) *
            amplitude ^ (2 : ℝ))) ^
            (Combinatorics.Sequence.balancedBlockCount
              (finiteVarianceBridgeLength scale n -
                stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) scale n)
              (stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) scale n) + 1) *
            (q / (finiteVarianceEntranceLength scale n : ℝ≥0∞)) ≤
          tiltedIncrementFieldLaw φ μ
            {increment : ℕ → ℝ |
              RandomWalk.history n 0 increment ∈
                affineCorridorThrough n (-ratio * scale n) 0
                  (ratio * scale n) ((-ratio + 1) * scale n)} := by
  obtain ⟨C, hC, q, hq, amplitude, hamplitude, n₀, hbound⟩ :=
    exists_eventually_iidSequenceLaw_endpointCorridor_lowerBound_of_centeredSecondMoment
      hνMoment hsigma hscale ratio hratio
  refine ⟨C, hC, q, hq, amplitude, hamplitude, n₀, ?_⟩
  intro n hn
  have hevent := endpointCorridorEvent_eq_affineCorridorThrough n (scale n) ratio
  have hlaw : tiltedIncrementFieldLaw φ μ = iidSequenceLaw ν := by
    rw [hν]
    rfl
  have hbound' := hbound n hn
  rw [hevent, ← hlaw] at hbound'
  exact hbound'

end ProbabilityTheory.BranchingRandomWalk.Spine

end
