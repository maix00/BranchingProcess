/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.RandomWalkBounds.Horizontal
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.FromIncrementLaw.HorizontalTube

/-!
# Uniform block bounds for horizontal tubes

For an interval of width `Δ`, translating the starting point `x` identifies
its killed-walk survival probability with a horizontal-tube probability. A
uniform one-block bound therefore gives a uniform bound for the killed kernel.
Iterating that kernel estimate yields a finite-horizon horizontal-tube bound.

The public theorems in this module are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.killedIntervalBlockProbability_eq_shiftedHorizontalTube`: for
  `x∈[-aΔ,(1-a)Δ]`, the killed-interval survival probability from `x` over
  `L` steps equals the horizontal-tube probability with offset `a+x/Δ`.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.killedIntervalBlockProbability_le_of_uniformTubeBound`: if every
  translated tube with offset in `[0,1]` has one-block probability at most
  `q`, then every starting point in the interval has killed-kernel mass at
  most `q` after that block.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.horizontalTubeProbability_le_exp_of_uniformTubeBlockBound`: if every
  translated block of length `ℓ` has probability at most
  `exp(-dℓ/Δ²)` and `dℓ/Δ²≤r`, then the `L`-step tube probability is at most
  `exp(r-dL/Δ²)`.
-/

open Filter MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

/-- A killed interval walk started at `x` is the centered tube walk whose
left endpoint is shifted by `x`. -/
theorem killedIntervalBlockProbability_eq_shiftedHorizontalTube
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {a width : ℝ} (hwidth : 0 < width) (length : ℕ)
    (x : Set.Icc (-a * width) ((1 - a) * width)) :
    Kernel.remainingMass
        (RandomWalk.killedIncrementKernelOn ν
          (Set.Icc (-a * width) ((1 - a) * width)) measurableSet_Icc)
        length x =
      horizontalTubeProbability (iidSequenceLaw ν)
        (a + (x : ℝ) / width) width length := by
  have hlower : -(a + (x : ℝ) / width) * width = -a * width - (x : ℝ) := by
    field_simp [ne_of_gt hwidth]
    ring
  have hupper : (1 - (a + (x : ℝ) / width)) * width =
      (1 - a) * width - (x : ℝ) := by
    field_simp [ne_of_gt hwidth]
    ring
  have hevent :
      {increment : ℕ → ℝ | RandomWalk.StaysIn
        (Set.Icc (-a * width) ((1 - a) * width)) length (x : ℝ) increment} =
      {increment | InHorizontalTube (a + (x : ℝ) / width)
        width length increment} := by
    ext increment
    change (∀ j : Fin length,
        (x : ℝ) + AdditivePath.displacement (j + 1) increment ∈
          Set.Icc (-a * width) ((1 - a) * width)) ↔
      InHorizontalTube (a + (x : ℝ) / width) width length increment
    simp only [Set.mem_Icc, InHorizontalTube]
    constructor <;> intro h j
    · have hj := h j
      rw [hlower, hupper]
      constructor <;> linarith
    · have hj := h j
      constructor <;> linarith [hlower, hupper]
  rw [RandomWalk.killedIncrementKernelOn_remainingMass_eq_iidSequenceLaw]
  change (iidSequenceLaw ν
      {increment | RandomWalk.StaysIn
        (Set.Icc (-a * width) ((1 - a) * width)) length (x : ℝ) increment}) = _
  rw [hevent]
  rfl

/-- A uniform translated-tube estimate gives a uniform upper bound for every
row of the killed interval kernel. -/
theorem killedIntervalBlockProbability_le_of_uniformTubeBound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {a width : ℝ} (hwidth : 0 < width) (length : ℕ) {upper : ENNReal}
    (htube : ∀ b ∈ Set.Icc (0 : ℝ) 1,
      horizontalTubeProbability (iidSequenceLaw ν) b width length ≤ upper) :
    ∀ x : Set.Icc (-a * width) ((1 - a) * width),
      Kernel.remainingMass
        (RandomWalk.killedIncrementKernelOn ν
          (Set.Icc (-a * width) ((1 - a) * width)) measurableSet_Icc)
        length x ≤ upper := by
  intro x
  rw [killedIntervalBlockProbability_eq_shiftedHorizontalTube
    ν hwidth length x]
  apply htube
  have hxLower : -a ≤ (x : ℝ) / width :=
    (le_div_iff₀ hwidth).2 x.property.1
  have hxUpper : (x : ℝ) / width ≤ 1 - a :=
    (div_le_iff₀ hwidth).2 x.property.2
  constructor <;> linarith

/-- A uniform bound for every translated one-block tube iterates through the
killed interval kernel. The incomplete block contributes at most the stated
remainder. -/
theorem horizontalTubeProbability_le_exp_of_uniformTubeBlockBound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {a width d remainder : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hwidth : 0 < width) (hd : 0 < d)
    (length horizon : ℕ) (hlength : 0 < length)
    (hblockRemainder : d * ((length : ℝ) / width ^ 2) ≤ remainder)
    (hblock : ∀ b ∈ Set.Icc (0 : ℝ) 1,
      horizontalTubeProbability (iidSequenceLaw ν) b width length ≤
        ENNReal.ofReal (Real.exp (-d * ((length : ℝ) / width ^ 2)))) :
    horizontalTubeProbability (iidSequenceLaw ν) a width horizon ≤
      ENNReal.ofReal (Real.exp
        (remainder - d * ((horizon : ℝ) / width ^ 2))) := by
  let interval := Set.Icc (-a * width) ((1 - a) * width)
  let kernel := RandomWalk.killedIncrementKernelOn ν interval measurableSet_Icc
  let upper := ENNReal.ofReal (Real.exp (-d * ((length : ℝ) / width ^ 2)))
  have hrow : ∀ x : Set.Icc (-a * width) ((1 - a) * width),
      Kernel.remainingMass kernel length x ≤ upper := by
    simpa [kernel, interval, upper] using
      killedIntervalBlockProbability_le_of_uniformTubeBound ν hwidth length hblock
  let blocks := horizon / length
  have hpow := Kernel.remainingMass_le_pow_div kernel length horizon
    ⟨0, by constructor <;> nlinarith [ha0, ha1, hwidth]⟩ upper hrow
  have hdecomp : blocks * length + horizon % length = horizon := by
    dsimp [blocks]
    calc
      horizon / length * length + horizon % length =
          length * (horizon / length) + horizon % length := by rw [Nat.mul_comm]
      _ = horizon := Nat.div_add_mod horizon length
  have hrem : horizon % length < length := Nat.mod_lt _ hlength
  have hcost : 0 < d / width ^ 2 := div_pos hd (sq_pos_of_pos hwidth)
  have hblockCost : d * ((length : ℝ) / width ^ 2) ≤ remainder := hblockRemainder
  have hblockCost' : (d / width ^ 2) * length ≤ remainder := by
    calc
      (d / width ^ 2) * length = d * ((length : ℝ) / width ^ 2) := by
        field_simp [ne_of_gt hwidth]
      _ ≤ remainder := hblockRemainder
  have hcoverageNat : horizon ≤ blocks * length + length := by omega
  have hcoverage : (horizon : ℝ) ≤ (blocks : ℝ) * length + length := by
    exact_mod_cast hcoverageNat
  have htotalCost : (d / width ^ 2) * horizon ≤
      (d / width ^ 2) * ((blocks : ℝ) * length) + remainder := by
    calc
      (d / width ^ 2) * horizon ≤
          (d / width ^ 2) * ((blocks : ℝ) * length + length) :=
        mul_le_mul_of_nonneg_left hcoverage hcost.le
      _ = (d / width ^ 2) * ((blocks : ℝ) * length) +
          (d / width ^ 2) * length := by ring
      _ ≤ (d / width ^ 2) * ((blocks : ℝ) * length) + remainder := by
        nlinarith [hblockCost']
  have hlengthCost : d * ((length : ℝ) / width ^ 2) =
      (d / width ^ 2) * length := by
    field_simp [ne_of_gt hwidth]
  have hhorizonCost : d * ((horizon : ℝ) / width ^ 2) =
      (d / width ^ 2) * horizon := by
    field_simp [ne_of_gt hwidth]
  have hexponent :
      (-d * ((length : ℝ) / width ^ 2)) * (blocks : ℝ) ≤
        remainder - d * ((horizon : ℝ) / width ^ 2) := by
    have hlengthNeg : -d * ((length : ℝ) / width ^ 2) =
        -((d / width ^ 2) * length) := by
      calc
        -d * ((length : ℝ) / width ^ 2) =
            -(d * ((length : ℝ) / width ^ 2)) := by ring
        _ = -((d / width ^ 2) * length) := by rw [hlengthCost]
    have hhorizonNeg : -d * ((horizon : ℝ) / width ^ 2) =
        -((d / width ^ 2) * horizon) := by
      calc
        -d * ((horizon : ℝ) / width ^ 2) =
            -(d * ((horizon : ℝ) / width ^ 2)) := by ring
        _ = -((d / width ^ 2) * horizon) := by rw [hhorizonCost]
    rw [hlengthNeg, hhorizonCost]
    have hblocksCost : (d / width ^ 2) * ((blocks : ℝ) * length) =
        ((d / width ^ 2) * length) * (blocks : ℝ) := by ring
    nlinarith [htotalCost]
  have hexpPow : upper ^ blocks = ENNReal.ofReal (Real.exp
      ((-d * ((length : ℝ) / width ^ 2)) * (blocks : ℝ))) := by
    dsimp [upper]
    rw [← ENNReal.ofReal_pow (Real.exp_nonneg _) blocks,
      ← Real.exp_nat_mul]
    congr 1
    ring_nf
  have hfinal : ENNReal.ofReal (Real.exp
        ((-d * ((length : ℝ) / width ^ 2)) * (blocks : ℝ))) ≤
      ENNReal.ofReal (Real.exp
        (remainder - d * ((horizon : ℝ) / width ^ 2))) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent)
  rw [← remainingMass_killedIncrementKernelOn_Icc_eq_horizontalTubeProbability
    ν a width ha0 ha1 hwidth.le horizon]
  calc
    Kernel.remainingMass kernel horizon
        ⟨0, by constructor <;> nlinarith [ha0, ha1, hwidth]⟩ ≤ upper ^ blocks := hpow
    _ = ENNReal.ofReal (Real.exp
        ((-d * ((length : ℝ) / width ^ 2)) * (blocks : ℝ))) := hexpPow
    _ ≤ ENNReal.ofReal (Real.exp
        (remainder - d * ((horizon : ℝ) / width ^ 2))) := hfinal


end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

end
