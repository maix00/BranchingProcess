/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.BrownianMotion.Basic
public import Probability.Process.Brownian.SmallDeviation.Range.UpperRate
public import Probability.Process.RandomWalk.Path.Block.Oscillation
public import Probability.Process.RandomWalk.SmallDeviation.Range.BlockDonsker
public import Probability.Sequence.IID.Basic

/-!
# Finite-cover upper bounds for random-walk block oscillations

Let $L_n\to\infty$ be block lengths, and suppose the oscillation width $w_n$
satisfies $w_n/\sqrt{L_n}\le u$ eventually. For a fixed finite-cover count
$m$, if `finiteCoverCorridorExponential m u < 1/2`, then the IID block event
is eventually bounded by $2B_m(u)$:

\[
  \mathbb P\{\operatorname{osc}(S_0,\ldots,S_{L_n})\le w_n\}
  \le 2 B_m(u),
\]
where $B_m(u)$ is the explicit Brownian finite-cover bound defined in
`Probability.Process.Brownian.SmallDeviation.Range.UpperRate`.

The proof combines the closed-set block Donsker bound with the Brownian
finite-corridor estimate. The finite-cover route is used in A. A. Mogul'skii,
Theorem 3, Section 4, p. 764, “Small deviations in the sample function
space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765;
English translation, “Small Deviations in a Space of Trajectories,” *Theory
of Probability and Its Applications* 19(4) (1975), 726--736, DOI
10.1137/1119081. The Donsker input corresponds to Theorem 4.20 in I. Karatzas
and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed.,
Graduate Texts in Mathematics 113, Springer (1991), DOI
10.1007/978-1-4612-0949-2.

## Public declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.Range.eventually_iidSequenceLaw_blockOscillationProbability_le_of_fixedCover`:
  the uniform eventual one-block probability bound stated above.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Range

open ProbabilityTheory.Process.Brownian.SmallDeviation.Range

open ProbabilityTheory.Process.Path

/-- A one-block oscillation estimate for any diverging sequence of block
lengths. The block widths need only be eventually bounded after diffusive
normalization; in particular, this interface does not impose a relation to a
separate ambient time index. -/
theorem eventually_iidSequenceLaw_blockOscillationProbability_le_of_fixedCover
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x : ℝ, x ∂ν = 0)
    (hsecondMoment : ∫ x : ℝ, x ^ 2 ∂ν = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {length : ℕ → ℕ} (hlength : Tendsto length atTop atTop)
    {blockWidth : ℕ → ℝ} {width : ℝ}
    (hwidth : ∀ᶠ n : ℕ in atTop,
      blockWidth n / Real.sqrt (length n) ≤ width)
    (hwidthPos : 0 < width) {count : ℕ} (hcount : 0 < count)
    (hspectral : finiteCoverCorridorExponential count width < 1 / 2) :
    ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν {increment : ℕ → ℝ |
        blockOscillationEvent (blockWidth n) (length n)
          (Combinatorics.Sequence.blockCoordinates 0 (length n) increment)} ≤
      ENNReal.ofReal (2 * finiteCoverRangeBound count width) := by
  let spectralBound : ℝ := finiteCoverRangeBound count width
  let upperBound : ℝ := 2 * spectralBound
  let mass : ENNReal := rangeOscillationMass (P := P) hcontinuous width
  have hspectral' : Real.exp (-(Real.pi ^ 2) /
      (2 * ((1 + 3 / (count : ℝ)) * width) ^ 2)) < 1 / 2 := by
    simpa [finiteCoverCorridorExponential] using hspectral
  have hmassBound := brownianRangeOscillationMass_le_smallWidthExponential
    hB hcontinuous hmeasurable hwidthPos hcount hspectral'
  have hspectralPos : 0 < spectralBound := by
    dsimp [spectralBound, finiteCoverRangeBound,
      finiteCoverCorridorExponential]
    positivity
  have hupperPos : 0 < upperBound := by
    dsimp [upperBound]
    positivity
  have hmassBound' : mass ≤ ENNReal.ofReal spectralBound := by
    simpa [mass, spectralBound, finiteCoverRangeBound,
      finiteCoverCorridorExponential] using hmassBound
  have hmassStrict : mass < ENNReal.ofReal upperBound := by
    have hlt : ENNReal.ofReal spectralBound < ENNReal.ofReal upperBound := by
      apply (ENNReal.ofReal_lt_ofReal_iff hupperPos).2
      dsimp [upperBound]
      nlinarith
    exact hmassBound'.trans_lt hlt
  have hlimsup := limsup_iidSequenceLaw_blockOscillation_le_brownianRangeOscillationMass
    ν hcentered hsecondMoment hB hcontinuous hmeasurable hlength hwidth
  have hlimsupStrict := hlimsup.trans_lt hmassStrict
  have hprobBounded : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => iidSequenceLaw ν {increment : ℕ → ℝ |
        blockOscillationEvent (blockWidth n) (length n)
          (Combinatorics.Sequence.blockCoordinates 0 (length n) increment)}) := by
    apply Filter.isBoundedUnder_of_eventually_le (a := 1)
    exact Eventually.of_forall fun n : ℕ => by
      calc
        _ ≤ iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
  have heventually := eventually_lt_of_limsup_lt hlimsupStrict hprobBounded
  filter_upwards [heventually] with n hn
  exact hn.le


end ProbabilityTheory.RandomWalk.SmallDeviation.Range
