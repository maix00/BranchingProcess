/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.AdditivePath.Basic
public import Probability.Distributions.Moments.Real
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
public import Probability.Sequence.IID.Basic
import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.FiniteVarianceUpper.Lemmas.Rate

/-!
# Finite-variance horizontal-tube upper bound

The public theorems in this file formalize Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.2
and its following remark. The equal-partition proof follows Elie Aïdékon and
Yueyun Hu, *Average-weight percolation on the complete graph*, Lemma 4.1
(2025, arXiv:2512.23266). The one-block rate is Theorem 3, Section 4,
p. 764 of A. A. Mogul'skii, “Small deviations in the sample function space,”
*Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English
translation, “Small Deviations in a Space of Trajectories,” *Theory of
Probability and Its Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081.

- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.horizontalTubeProbability_le_exp_of_finiteVariance_withRemainder`:
  $\mathbb P(T_{a,\Delta,L})\le
  \exp(u\Delta^v-dL/\Delta^2)$ for $u,v>0$ and
  $0<d<\pi^2\sigma^2/2$, uniformly over $a\in[0,1]$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.horizontalTubeProbability_le_exp_of_finiteVariance`: the same bound
  with $u=1$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.iidSequenceLaw_intervalProbability_le_exp_of_finiteVariance_withRemainder`:
  the corresponding bound for a translated interval $[r_0,r_0+\Delta]$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.iidSequenceLaw_intervalProbability_le_exp_of_finiteVariance`:
  the translated-interval bound with $u=1$.

The reusable uniform one-block-to-horizon estimate is in
`HorizontalTube/BlockIteration.lean`. The proof-specific equal-partition and
rate-assembly steps are in
`FiniteVarianceUpper/Lemmas/EqualPartition.lean` and
`FiniteVarianceUpper/Lemmas/Rate.lean`.
-/

open Filter MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

/-- The arbitrary-remainder form of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.2 and
its following remark. The equal-partition iteration is the proof of Elie
Aïdékon and Yueyun Hu, *Average-weight percolation on the complete graph*,
Lemma 4.1 (2025, arXiv:2512.23266). The one-block rate is Theorem 3,
Section 4, p. 764 of A. A. Mogul'skii, “Small deviations in the sample
function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755--765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726--736, DOI
10.1137/1119081. -/
theorem horizontalTubeProbability_le_exp_of_finiteVariance_withRemainder
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x : ℝ, x ^ 2 ∂ν)
    {u v d : ℝ} (hu : 0 < u) (hv : 0 < v) (hd : 0 < d)
    (hcritical : d < (Real.pi ^ 2 / 2) * (∫ x : ℝ, x ^ 2 ∂ν)) :
    ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ Δ : ℝ, Δ₀ ≤ Δ → ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ L : ℕ,
        1 ≤ L →
        horizontalTubeProbability (iidSequenceLaw ν) a Δ L ≤
          ENNReal.ofReal (Real.exp (u * Δ ^ v - d * ((L : ℝ) / Δ ^ 2))) := by
  let critical : ℝ := (Real.pi ^ 2 / 2) * (∫ x : ℝ, x ^ 2 ∂ν)
  obtain ⟨m, hm, hmRate⟩ := exists_partition_size_for_rate (by
    simpa [critical] using hcritical)
  let partitionScale : ℝ := 1 + 1 / (m : ℝ)
  let rate : ℝ := (d * partitionScale ^ 2 + critical) / 2
  have hpartitionScale : 0 < partitionScale := by positivity
  have hpartitionCost : d * partitionScale ^ 2 < critical := by
    simpa [partitionScale] using hmRate
  have hratePos : 0 < rate := by
    dsimp [rate]
    positivity
  have hrateCritical : rate < critical := by
    dsimp [rate]
    linarith
  have hpartitionRate : d * partitionScale ^ 2 < rate := by
    dsimp [rate]
    linarith
  have hrateBand := eventually_uniform_partitionTube_rateBound ν hcentered
    hsquare hvariance hu hv hd hm hratePos (by
      simpa [critical] using hrateCritical)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hrateBand
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hsum : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hinv
  have hcoefficientLimit : Tendsto
      (fun n : ℕ => d * partitionScale ^ 2 * (1 + 1 / (n : ℝ)) ^ 2)
      atTop (𝓝 (d * partitionScale ^ 2)) := by
    simpa using tendsto_const_nhds.mul (hsum.pow 2)
  have hcoefficientEventually : ∀ᶠ n : ℕ in atTop,
      d * partitionScale ^ 2 * (1 + 1 / (n : ℝ)) ^ 2 < rate :=
    hcoefficientLimit.eventually (eventually_lt_nhds hpartitionRate)
  obtain ⟨Kcoefficient, hKcoefficient⟩ :=
    eventually_atTop.1 hcoefficientEventually
  have hpowerTop : Tendsto (fun n : ℕ => (n : ℝ) ^ v) atTop atTop :=
    (tendsto_rpow_atTop hv).comp tendsto_natCast_atTop_atTop
  have hscaledPowerTop : Tendsto (fun n : ℕ => u * (n : ℝ) ^ v) atTop atTop :=
    hpowerTop.const_mul_atTop hu
  have hroundingEventually : ∀ᶠ n : ℕ in atTop,
      2 * d ≤ u * (n : ℝ) ^ v :=
    hscaledPowerTop.eventually (eventually_ge_atTop (2 * d))
  obtain ⟨Krounding, hKrounding⟩ := eventually_atTop.1 hroundingEventually
  let N : ℕ := max (K + 1) (max Kcoefficient Krounding)
  have hNK : K + 1 ≤ N := Nat.le_max_left _ _
  have hNposNat : 0 < N := lt_of_lt_of_le (Nat.succ_pos K) hNK
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNposNat
  refine ⟨(N : ℝ), hNpos, ?_⟩
  intro Δ hΔ a ha L hL
  have hΔpos : 0 < Δ := lt_of_lt_of_le hNpos hΔ
  let n := Nat.floor Δ
  have hnFloor : (n : ℝ) ≤ Δ := by
    dsimp [n]
    exact Nat.floor_le hΔpos.le
  have hΔFloor : Δ < (n : ℝ) + 1 := by
    dsimp [n]
    exact Nat.lt_floor_add_one Δ
  have hnLower : N ≤ n := by
    apply Nat.le_floor
    exact_mod_cast hΔ
  have hnKsucc : K + 1 ≤ n := le_trans (Nat.le_max_left _ _) hnLower
  have hnOne : 1 ≤ n := by omega
  have hnRate : K ≤ n - 1 := by omega
  have hnCoefficient : Kcoefficient ≤ n := le_trans
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hnLower
  have hnRounding : Krounding ≤ n := le_trans
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hnLower
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast hnOne
  have hcoeffN := hKcoefficient n hnCoefficient
  have hroundN := hKrounding n hnRounding
  have hrateN : ∀ j : Fin m,
      horizontalTubeProbability (iidSequenceLaw ν) (partitionTubeParameter m j)
        (partitionTubeWidth m ((n : ℝ) + 1))
        (smallDeviationBlockLength u v d n) ≤
        ENNReal.ofReal (Real.exp (-rate *
          ((smallDeviationBlockLength u v d n : ℝ) /
            (partitionTubeWidth m ((n : ℝ) + 1)) ^ 2))) := by
    have h := hK (n - 1) hnRate
    have hplus : n - 1 + 2 = n + 1 := by omega
    simpa [hplus, Nat.sub_add_cancel hnOne] using h
  have hcoeffN' : d * (1 + 1 / (m : ℝ)) ^ 2 *
      (1 + 1 / (n : ℝ)) ^ 2 < rate := by
    simpa [partitionScale] using hcoeffN
  exact horizontalTubeProbability_le_exp_of_partitionIndex ν hu hv hd hm hratePos
    hΔpos hnPos hnFloor hΔFloor
    hcoeffN' hroundN hrateN a ha L

/-- Coefficient-one case of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.2. Its equal-partition
argument is Aïdékon and Hu, *Average-weight percolation on the complete graph*,
Lemma 4.1 (2025, arXiv:2512.23266); its one-block rate is Theorem 3, Section 4,
p. 764 of A. A. Mogul'skii, “Small deviations in the sample function space,”
*Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English
translation, “Small Deviations in a Space of Trajectories,” *Theory of
Probability and Its Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081.
-/
theorem horizontalTubeProbability_le_exp_of_finiteVariance
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x : ℝ, x ^ 2 ∂ν)
    {v d : ℝ} (hv : 0 < v) (hd : 0 < d)
    (hcritical : d < (Real.pi ^ 2 / 2) * (∫ x : ℝ, x ^ 2 ∂ν)) :
    ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ Δ : ℝ, Δ₀ ≤ Δ → ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ L : ℕ,
        1 ≤ L →
        horizontalTubeProbability (iidSequenceLaw ν) a Δ L ≤
          ENNReal.ofReal (Real.exp (Δ ^ v - d * ((L : ℝ) / Δ ^ 2))) := by
  simpa using
    (horizontalTubeProbability_le_exp_of_finiteVariance_withRemainder
      (u := 1) ν hcentered hsquare hvariance one_pos hv hd hcritical)

/-- The translated-interval form of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.2 and
its following remark. The event identity transfers the centered-tube estimate;
the equal-partition iteration is Aïdékon and Hu, *Average-weight percolation on
the complete graph*, Lemma 4.1 (2025, arXiv:2512.23266). The block rate is
Theorem 3, Section 4, p. 764 of A. A. Mogul'skii, “Small deviations in the
sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755--765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726--736, DOI
10.1137/1119081. -/
theorem iidSequenceLaw_intervalProbability_le_exp_of_finiteVariance_withRemainder
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x : ℝ, x ^ 2 ∂ν)
    {u v d : ℝ} (hu : 0 < u) (hv : 0 < v) (hd : 0 < d)
    (hcritical : d < (Real.pi ^ 2 / 2) * (∫ x : ℝ, x ^ 2 ∂ν)) :
    ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ Δ : ℝ, Δ₀ ≤ Δ → ∀ r₀ : ℝ,
        r₀ ≤ 0 → 0 ≤ r₀ + Δ → ∀ L : ℕ, 1 ≤ L →
        (iidSequenceLaw ν)
          {increment : ℕ → ℝ | ∀ j : Fin L,
            AdditivePath.displacement (j + 1) increment ∈
              Set.Icc r₀ (r₀ + Δ)} ≤
          ENNReal.ofReal (Real.exp (u * Δ ^ v - d * ((L : ℝ) / Δ ^ 2))) := by
  obtain ⟨Δ₀, hΔ₀, hbound⟩ :=
    horizontalTubeProbability_le_exp_of_finiteVariance_withRemainder
      ν hcentered hsquare hvariance hu hv hd hcritical
  refine ⟨Δ₀, hΔ₀, ?_⟩
  intro Δ hΔ r₀ hr₀ hupper L hL
  have hwidth : 0 < Δ := lt_of_lt_of_le hΔ₀ hΔ
  have hbridge (increment : ℕ → ℝ) :=
    RandomWalk.inHorizontalTube_iff_Icc hwidth hr₀ hupper
      (n := L) (increment := increment)
  have hevent :
      {increment : ℕ → ℝ | ∀ j : Fin L,
        AdditivePath.displacement (j + 1) increment ∈ Set.Icc r₀ (r₀ + Δ)} =
      {increment | InHorizontalTube (-r₀ / Δ) Δ L increment} := by
    ext increment
    simp only [Set.mem_ofPred_eq]
    exact (hbridge increment).2.2.symm
  calc
    (iidSequenceLaw ν)
        {increment : ℕ → ℝ | ∀ j : Fin L,
          AdditivePath.displacement (j + 1) increment ∈ Set.Icc r₀ (r₀ + Δ)} =
        horizontalTubeProbability (iidSequenceLaw ν) (-r₀ / Δ) Δ L := by
      rw [hevent]
      rfl
    _ ≤ ENNReal.ofReal (Real.exp (u * Δ ^ v - d * ((L : ℝ) / Δ ^ 2))) :=
      hbound Δ hΔ (-r₀ / Δ)
        ⟨(hbridge (fun _ : ℕ => 0)).1, (hbridge (fun _ : ℕ => 0)).2.1⟩ L hL

/-- Translated-interval, coefficient-one form of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3,
Lemma 3.2 and its following remark. The block iteration follows Aïdékon and
Hu, *Average-weight percolation on the complete graph*, Lemma 4.1 (2025,
arXiv:2512.23266); the rate is Theorem 3, Section 4, p. 764 of A. A.
Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081. -/
theorem iidSequenceLaw_intervalProbability_le_exp_of_finiteVariance
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x : ℝ, x ^ 2 ∂ν)
    {v d : ℝ} (hv : 0 < v) (hd : 0 < d)
    (hcritical : d < (Real.pi ^ 2 / 2) * (∫ x : ℝ, x ^ 2 ∂ν)) :
    ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ Δ : ℝ, Δ₀ ≤ Δ → ∀ r₀ : ℝ,
        r₀ ≤ 0 → 0 ≤ r₀ + Δ → ∀ L : ℕ, 1 ≤ L →
        (iidSequenceLaw ν)
          {increment : ℕ → ℝ | ∀ j : Fin L,
            AdditivePath.displacement (j + 1) increment ∈
              Set.Icc r₀ (r₀ + Δ)} ≤
          ENNReal.ofReal (Real.exp (Δ ^ v - d * ((L : ℝ) / Δ ^ 2))) := by
  simpa using
    (iidSequenceLaw_intervalProbability_le_exp_of_finiteVariance_withRemainder
      (u := 1) ν hcentered hsquare hvariance one_pos hv hd hcritical)

end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

end
