/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLimit.Block
public import Probability.Process.RandomWalk.Path.Block.Corridor.CoreReturn
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.BlockLength
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Basic
public import Probability.Distributions.Stable.Attraction.Norming.Basic
public import Combinatorics.Sequence.BalancedPartition
public import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Transfer
import all Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.Endpoint.BandTransfer.Lower.Lemmas.StableReturnBlocks

/-!
# Stable discrete endpoint-core return lower bound

## Public declarations

- `exists_eventually_iidSequenceLaw_inOpenPartialSumCoreReturn_ge_exp_of_stableEscapeRate`:
  there is $a>0$ such that, with
  $p(a)=\exp((C/R^\alpha-\delta)a^\alpha)$, eventually
  \[
    p(a)^{\operatorname{balancedBlockCount}(N_n-b_n,b_n)+1}
      \leq \mathbb{P}_\nu(E_n),
  \]
  where $R$ is the half-width of the narrowed corridor, $b_n$ is the stable
  block length, and $E_n$ is the open partial-sum core-return event in the
  theorem statement.

This is the discrete endpoint-core conclusion used by multiple stable
small-deviation clients. Its one-use endpoint-mass, path-limit, and balanced
partition derivations live under `Lower/Lemmas/`.

It formalizes the finite endpoint-return step in the proof of A. A. Mogul'skii,
Theorem 3, Section 4, p. 764, “Small deviations in the sample function space,”
*Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755–765; English
translation, “Small Deviations in a Space of Trajectories,” *Theory of
Probability and Its Applications* 19(4) (1975), 726–736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

@[expose] public section

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- Stable escape and block convergence give the required lower bound for a
single robust endpoint-core event. The spatial margin makes the killed path
event a subset of the open block corridor; the smaller terminal window lies
inside the prescribed increase of endpoint-core radius. -/
theorem exists_eventually_iidSequenceLaw_inOpenPartialSumCoreReturn_ge_exp_of_stableEscapeRate
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    {innerLower innerUpper startCenter startRadius endCenter endRadius : ℝ}
    {lower upper epsilon margin delta duration : ℝ}
    (hlower : lower = innerLower + startRadius + margin - startCenter)
    (hupper : upper = innerUpper - startRadius - margin - startCenter)
    (hmargin : 0 < margin)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta)
    (hendpointBand : 3 * epsilon < (endRadius - startRadius) / 2)
    (hreturnWindows : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lower + 4 * epsilon < (((i : ℝ) - 1) * epsilon) ∧
        ((i : ℝ) + 1) * epsilon < upper - 4 * epsilon)
    (hbridgeWindows :
      lower + 4 * epsilon < endCenter - startCenter - 4 * epsilon ∧
        endCenter - startCenter + 4 * epsilon < upper - 4 * epsilon)
    (total : ℕ → ℕ) (hduration : 0 < duration)
    (htotal : Tendsto (fun n => (total n : ℝ) / (n : ℝ))
      atTop (nhds duration)) :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (Real.exp
          ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
            amplitude ^ α)) ^
              (Combinatorics.Sequence.balancedBlockCount
                (total n - stableBlockLength α ν (amplitude ^ α) scale n)
                (stableBlockLength α ν (amplitude ^ α) scale n) + 1) ≤
          iidSequenceLaw ν
            {increment : ℕ → ℝ |
              ProbabilityTheory.RandomWalk.InOpenPartialSumCoreReturn
                  (scale n * innerLower) (scale n * innerUpper)
                  (scale n * startCenter) (scale n * startRadius)
                  (scale n * endCenter) (scale n * endRadius)
                  (Combinatorics.Sequence.blockCoordinates 0 (total n) increment)} := by
  have hreturnLower := hreturnWindows (-3) (by norm_num)
  have hreturnUpper := hreturnWindows 3 (by norm_num)
  have hlower' : lower + 4 * epsilon < 0 := by
    have hi : ((-3 : ℤ) : ℝ) - 1 = -4 := by norm_num
    rw [hi] at hreturnLower
    nlinarith [hreturnLower.1, hepsilon]
  have hupper' : 0 < upper - 4 * epsilon := by
    have hi : ((3 : ℤ) : ℝ) + 1 = 4 := by norm_num
    rw [hi] at hreturnUpper
    nlinarith [hreturnUpper.2, hepsilon]
  obtain ⟨amplitude, hamplitude, hcellEventually⟩ :=
    exists_eventually_endpointCoreCellBridgeLowerBound_of_stableEscapeRate
      hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase
      hlower' hupper' hepsilon hdelta hreturnWindows startCenter endCenter
      hbridgeWindows total hduration htotal
  have hscalePositive : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    IsStableMogulskiiScale.eventually_scale_pos hscale
  refine ⟨amplitude, hamplitude, ?_⟩
  filter_upwards [hcellEventually, hscalePositive] with n hcellN hscaleN
  have hx : startCenter * scale n ∈
      Set.Icc (startCenter * scale n - 3 * (epsilon * scale n))
        (startCenter * scale n + 3 * (epsilon * scale n)) := by
    constructor <;> nlinarith [mul_pos (by positivity : 0 < 3 * epsilon) hscaleN]
  have hcell := hcellN ⟨startCenter * scale n, hx⟩
  have hzeroLower : innerLower + startRadius - startCenter < 0 := by
    rw [hlower] at hlower'
    nlinarith [hlower', hmargin]
  have hzeroUpper : 0 < innerUpper - startRadius - startCenter := by
    rw [hupper] at hupper'
    nlinarith [hupper', hmargin]
  have hsubset :
      {increment : ℕ → ℝ |
        RandomWalk.StaysIn
            (Set.Icc ((startCenter + lower) * scale n)
              ((startCenter + upper) * scale n))
            (total n) (startCenter * scale n) increment ∧
          startCenter * scale n + AdditivePath.displacement (total n) increment ∈
            Set.Icc (endCenter * scale n - 3 * (epsilon * scale n))
              (endCenter * scale n + 3 * (epsilon * scale n))} ⊆
      {increment : ℕ → ℝ |
        ProbabilityTheory.RandomWalk.InOpenPartialSumCoreReturn
            (scale n * innerLower) (scale n * innerUpper)
            (scale n * startCenter) (scale n * startRadius)
            (scale n * endCenter) (scale n * endRadius)
            (Combinatorics.Sequence.blockCoordinates 0 (total n) increment)} := by
    intro increment hevent
    have hpath : RandomWalk.StaysIn
        (Set.Icc (scale n * (innerLower + startRadius + margin))
          (scale n * (innerUpper - startRadius - margin)))
        (total n) (scale n * startCenter) increment := by
      have hlow : (startCenter + lower) * scale n =
          scale n * (innerLower + startRadius + margin) := by
        rw [hlower]
        ring
      have hupp : (startCenter + upper) * scale n =
          scale n * (innerUpper - startRadius - margin) := by
        rw [hupper]
        ring
      rw [← hlow, ← hupp]
      convert hevent.1 using 1
      ring_nf
    have hend : scale n * startCenter +
        AdditivePath.displacement (total n) increment ∈
          Set.Icc (scale n * (endCenter - 3 * epsilon))
            (scale n * (endCenter + 3 * epsilon)) := by
      convert hevent.2 using 1 <;> ring_nf
    exact ProbabilityTheory.RandomWalk.inOpenPartialSumCoreReturn_of_staysIn_endsIn
        hscaleN hmargin hzeroLower hzeroUpper hendpointBand hpath hend
  calc
    _ ≤ iidSequenceLaw ν
        {increment : ℕ → ℝ |
          RandomWalk.StaysIn
              (Set.Icc ((startCenter + lower) * scale n)
                ((startCenter + upper) * scale n))
              (total n) (startCenter * scale n) increment ∧
            startCenter * scale n + AdditivePath.displacement (total n) increment ∈
              Set.Icc (endCenter * scale n - 3 * (epsilon * scale n))
                (endCenter * scale n + 3 * (epsilon * scale n))} := hcell
    _ ≤ _ := measure_mono hsubset


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end

end
