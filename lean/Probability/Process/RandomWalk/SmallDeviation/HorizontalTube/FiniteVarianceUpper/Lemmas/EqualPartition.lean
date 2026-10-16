/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.RandomWalkBounds.Horizontal
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.FromIncrementLaw.HorizontalTube
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Equal-partition inputs for the horizontal-tube upper bound

Write
\[
  T_{a,\Delta,L}:=\{\omega:\ -a\Delta\le S_j(\omega)
    \le(1-a)\Delta\ \text{for }1\le j\le L\},\qquad
  \alpha_{m,j}:=\frac{1-j/m}{1+1/m}.
\]
Here `S_j` is the partial sum of the IID increments with centered law `ν`.

The proof-specific module-visible declarations are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.partitionTubeParameter`,
  `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.partitionTubeWidth`, and
  `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.partitionTubeEvent`:
  the fixed translated corridors used to cover the offsets $a\in[0,1]$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.smallDeviationBlockFactor` and
  `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.smallDeviationBlockLength`:
  the factor and block length in the finite-width iteration.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.horizontalTube_subset_some_partitionTubeEvent`: for `m≥1`, `a∈[0,1]`,
  and `Δ>0`, some `j∈{0,…,m−1}` satisfies
  \(T_{a,\Delta,L}\subseteq T_{\alpha_{m,j},(1+1/m)\Delta,L}\).
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.horizontalTubeProbability_le_one_partitionTube`: for the same parameters,
  \(\exists j,\ \mathbb P_\nu(T_{a,\Delta,L})
    \le\mathbb P_\nu(T_{\alpha_{m,j},(1+1/m)\Delta,L})\).
These are the proof inputs for Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.2 and
its following remark. The finite-width argument follows Aïdékon and Hu, *Average-weight
percolation on the complete graph*, Lemma 4.1 (arXiv:2512.23266): it partitions
the translations into equal intervals, selects one fixed corridor, and
iterates the uniform one-block bound.
-/

open Filter MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

/-- Parameter of the `k`-th fixed corridor in an equal partition. -/
noncomputable def partitionTubeParameter (m : ℕ) (k : Fin m) : ℝ :=
  (1 - (k : ℝ) / m) / (1 + 1 / m)

/-- Width of the fixed corridor obtained by enlarging a tube by the factor
`1 + 1/m`. -/
noncomputable def partitionTubeWidth (m : ℕ) (width : ℝ) : ℝ :=
  (1 + 1 / m) * width

/-- The fixed corridor event associated with one cell of the equal partition. -/
def partitionTubeEvent (m : ℕ) (k : Fin m) (width : ℝ) (length : ℕ) :
    Set (ℕ → ℝ) :=
  {increment | InHorizontalTube (partitionTubeParameter m k)
    (partitionTubeWidth m width) length increment}

/-- Integer block length at width index `n` and remainder coefficient `u`.
The factor `1/2` leaves room for the floor rounding while retaining the
remainder `u * Δ^v`. -/
noncomputable def smallDeviationBlockFactor (u v d : ℝ) (n : ℕ) : ℕ :=
  ⌊u * (n : ℝ) ^ v / (2 * d)⌋₊ + 1

noncomputable def smallDeviationBlockLength (u v d : ℝ) (n : ℕ) : ℕ :=
  n ^ 2 * smallDeviationBlockFactor u v d n

/-- A point of `[0,1]` lies in one of the `m` closed equal subintervals. -/
private theorem exists_equalPartition_index {m : ℕ} (hm : 0 < m)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∃ k : Fin m, (k : ℝ) / m ≤ x ∧ x ≤ ((k : ℝ) + 1) / m := by
  let q := Nat.floor ((m : ℝ) * x)
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  have harg : 0 ≤ (m : ℝ) * x := mul_nonneg hmReal.le hx0
  have hqFloor : (q : ℝ) ≤ (m : ℝ) * x := Nat.floor_le harg
  have hqSucc : (m : ℝ) * x < (q : ℝ) + 1 := Nat.lt_floor_add_one _
  have hargUpper : (m : ℝ) * x ≤ m := by
    nlinarith [mul_le_mul_of_nonneg_left hx1 hmReal.le]
  have hqLe : q ≤ m := Nat.floor_le_of_le hargUpper
  by_cases hq : q < m
  · refine ⟨⟨q, hq⟩, ?_, ?_⟩
    · apply (div_le_iff₀ hmReal).2
      nlinarith [hqFloor]
    · apply (le_div_iff₀ hmReal).2
      nlinarith [hqSucc]
  · have hqEq : q = m := Nat.le_antisymm hqLe (Nat.le_of_not_gt hq)
    have hxEq : x = 1 := by
      have hmLe : (m : ℝ) ≤ (m : ℝ) * x := by
        simpa [hqEq, q] using hqFloor
      nlinarith [hmReal]
    have hmOne : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm.ne'
    let k : Fin m := ⟨m - 1, by omega⟩
    refine ⟨k, ?_, ?_⟩
    · have hcast : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast (Nat.sub_le m 1)
      apply (div_le_iff₀ hmReal).2
      simp [hxEq]
    · rw [hxEq]
      have hsub : m - 1 + 1 = m := Nat.sub_add_cancel hmOne
      have hnum : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
        exact_mod_cast hsub
      change 1 ≤ (((m - 1 : ℕ) : ℝ) + 1) / (m : ℝ)
      rw [hnum]
      exact (div_self hmReal.ne').symm.le

/-- Every horizontal tube whose interval contains zero lies in one of the
fixed corridors from the equal partition. The corridor boundaries are
`(-1+k/m) width` and `(k+1) width/m`. -/
theorem horizontalTube_subset_some_partitionTubeEvent
    {m length : ℕ} (hm : 0 < m) {a width : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hwidth : 0 < width) :
    ∃ k : Fin m,
      {increment : ℕ → ℝ | InHorizontalTube a width length increment} ⊆
        partitionTubeEvent m k width length := by
  let x := 1 - a
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hx1 : x ≤ 1 := by dsimp [x]; linarith
  obtain ⟨k, hk0, hk1⟩ := exists_equalPartition_index hm hx0 hx1
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hfactor : 0 < 1 + 1 / (m : ℝ) := by positivity
  have hwidthEq : partitionTubeWidth m width =
      (1 + 1 / (m : ℝ)) * width := by rfl
  have hlowerEq : -partitionTubeParameter m k * partitionTubeWidth m width =
      (-1 + (k : ℝ) / m) * width := by
    dsimp [partitionTubeParameter, partitionTubeWidth]
    field_simp [ne_of_gt hmReal]
    ring
  have hupperEq : (1 - partitionTubeParameter m k) *
      partitionTubeWidth m width = (((k : ℝ) + 1) / m) * width := by
    dsimp [partitionTubeParameter, partitionTubeWidth]
    field_simp [ne_of_gt hmReal]
    ring
  have hlowerCoeff : -1 + (k : ℝ) / m ≤ x - 1 := by
    dsimp [x]
    linarith
  have hupperCoeff : x ≤ ((k : ℝ) + 1) / m := by
    exact hk1
  have hlowerBoundary :
      (-1 + (k : ℝ) / m) * width ≤ -a * width := by
    have hlowerCoeff' : -1 + (k : ℝ) / m ≤ -a := by
      simpa [x] using hlowerCoeff
    exact mul_le_mul_of_nonneg_right hlowerCoeff' hwidth.le
  have hupperBoundary : (1 - a) * width ≤
      (((k : ℝ) + 1) / m) * width := by
    have hxEq : x = 1 - a := rfl
    rw [← hxEq]
    exact mul_le_mul_of_nonneg_right hupperCoeff hwidth.le
  refine ⟨k, ?_⟩
  intro increment htube
  change InHorizontalTube (partitionTubeParameter m k)
    (partitionTubeWidth m width) length increment
  intro j
  have hj := htube j
  rw [hlowerEq, hupperEq]
  constructor
  · exact le_trans hlowerBoundary hj.1
  · exact le_trans hj.2 hupperBoundary

/-- A translated tube is contained in one fixed corridor from the finite
equal partition, with the index depending only on its translation. -/
theorem horizontalTubeProbability_le_one_partitionTube
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {m length : ℕ} (hm : 0 < m) {a width : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hwidth : 0 < width) :
    ∃ k : Fin m,
      horizontalTubeProbability (iidSequenceLaw ν) a width length ≤
        horizontalTubeProbability (iidSequenceLaw ν)
          (partitionTubeParameter m k) (partitionTubeWidth m width) length := by
  obtain ⟨k, hsub⟩ := horizontalTube_subset_some_partitionTubeEvent hm ha0 ha1 hwidth
  refine ⟨k, ?_⟩
  calc
    horizontalTubeProbability (iidSequenceLaw ν) a width length ≤
        (iidSequenceLaw ν) (partitionTubeEvent m k width length) :=
      measure_mono hsub
    _ = horizontalTubeProbability (iidSequenceLaw ν)
        (partitionTubeParameter m k) (partitionTubeWidth m width) length := by
      simp [partitionTubeEvent, horizontalTubeProbability]


end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

end
