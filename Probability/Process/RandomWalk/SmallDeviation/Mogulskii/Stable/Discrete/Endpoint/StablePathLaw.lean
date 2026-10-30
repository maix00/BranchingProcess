/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep.Block
public import Probability.Process.Path.Skorokhod.Corridor.Basic
public import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Basic
public import Probability.Process.Stable.Levy
public import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.PathLawTransfer
public import Probability.Sequence.IID.Basic
public import Mathlib.Probability.CDF
import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Transfer

/-!
# Stable-process path law to endpoint-window tube bound

## Public declarations

`ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.eventually_horizontalTubeProbability_ge_pow_of_stablePathLawLimit`
packages the stable-process endpoint-corridor mass bound and the general
endpoint-window path-law transfer. Under a stable clock path law matching a
stable Lévy process, the CDF sign condition, and an IID block-path limit, it
produces $r\in(0,1/2)$ and $q>0$ such that eventually
$q^{\lfloor N_n/L_n\rfloor+1}$ bounds the corresponding centered tube
probability from below.

This stable specialization supplies the path-law input to the endpoint-return
lower-bound argument of A. A. Mogul'skii, Theorem 3, Section 4, p. 764,
“Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755--765; English translation, “Small Deviations
in a Space of Trajectories,” *Theory of Probability and Its Applications*
19(4) (1975), 726--736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow

private abbrev EndpointBandIndex :=
  {i : ℤ // i ∈ Finset.Icc (-3 : ℤ) 3}

private instance : Nonempty EndpointBandIndex :=
  ⟨⟨0, by norm_num⟩⟩

/-- In the stable domain-of-attraction setting, the seven open endpoint
corridors needed by the discrete return estimate have a common positive
mass. The smaller closed-right windows are supplied by the stable-process
entrance estimate and transferred to the limiting càdlàg path law through its
rational-coordinate law. -/
theorem eventually_horizontalTubeProbability_ge_pow_of_stablePathLawLimit
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (blockLength horizon : ℕ → ℕ)
    {α : ℝ} {μ : Measure ℝ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : Ω → CadlagPath unitInterval ℝ)
    {X : ℝ≥0 → Ω' → ℝ} {Q : Measure Ω'} [IsProbabilityMeasure Q]
    (hP : IsStableClockProcessLaw α μ unitInterval.clock (P.map Z))
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale blockLength)
      atTop Z (fun _ => iidSequenceLaw ν) P)
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hblock : ∀ᶠ n in atTop, 0 < blockLength n) :
    ∃ radius : ℝ, ∃ lowerBound : ENNReal,
      0 < radius ∧ radius < 1 / 2 ∧ 0 < lowerBound ∧
      ∀ᶠ n in atTop,
        lowerBound ^ (horizon n / blockLength n + 1) ≤
          horizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
            (2 * (radius + 4 * (radius / 16)) * scale n)
            (horizon n) := by
  let innerLower (i : EndpointBandIndex) : ℝ :=
    ((i.val : ℝ) - 1 / 2) * (1 / 16)
  let innerUpper (i : EndpointBandIndex) : ℝ :=
    ((i.val : ℝ) + 1 / 2) * (1 / 16)
  let outerLower (i : EndpointBandIndex) : ℝ :=
    ((i.val : ℝ) - 1) * (1 / 16)
  let outerUpper (i : EndpointBandIndex) : ℝ :=
    ((i.val : ℝ) + 1) * (1 / 16)
  have hstableLower : ∀ i : EndpointBandIndex,
      -1 ≤ (1 + 1 / 16 : ℝ) * innerLower i := by
    intro i
    have hi : |(i.val : ℝ)| ≤ 3 := by
      rw [abs_le]
      constructor
      · exact_mod_cast (Finset.mem_Icc.mp i.property).1
      · exact_mod_cast (Finset.mem_Icc.mp i.property).2
    have hi' := abs_le.mp hi
    dsimp [innerLower]
    norm_num
    nlinarith [hi'.1, hi'.2]
  have hinner : ∀ i : EndpointBandIndex, innerLower i < innerUpper i := by
    intro i
    dsimp [innerLower, innerUpper]
    norm_num
    linarith
  have hstableUpper : ∀ i : EndpointBandIndex,
      (1 + 1 / 16 : ℝ) * innerUpper i ≤ 1 := by
    intro i
    have hi : |(i.val : ℝ)| ≤ 3 := by
      rw [abs_le]
      constructor
      · exact_mod_cast (Finset.mem_Icc.mp i.property).1
      · exact_mod_cast (Finset.mem_Icc.mp i.property).2
    have hi' := abs_le.mp hi
    dsimp [innerUpper]
    norm_num
    nlinarith [hi'.1, hi'.2]
  have houterLower : ∀ i : EndpointBandIndex, outerLower i < innerLower i := by
    intro i
    dsimp [outerLower, innerLower]
    norm_num
  have houterUpper : ∀ i : EndpointBandIndex, innerUpper i < outerUpper i := by
    intro i
    dsimp [innerUpper, outerUpper]
    norm_num
  obtain ⟨β, q, hβ, hβsmall, hq, hqle⟩ :=
    hP.exists_finite_openEndpointCorridor_lowerBound hX hcdf
      innerLower innerUpper outerLower outerUpper
      hstableLower hinner hstableUpper houterLower houterUpper
  have hqfinite : q ≠ ∞ := by
    have hle := hqle ⟨0, by norm_num⟩
    exact ne_of_lt (lt_of_le_of_lt hle (measure_lt_top (P.map Z) _))
  have hqhalfpos : 0 < q / 2 := ENNReal.half_pos hq.ne'
  have hqhalf : q / 2 < q := ENNReal.half_lt_self hq.ne' hqfinite
  have hbelow : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      q / 2 < P.map Z
        (Skorokhod.rangeInOpenIntervalEndsIn (-β) β
          (((i : ℝ) - 1) * (β / 16)) (((i : ℝ) + 1) * (β / 16))) := by
    intro i hi
    have hmass := hqle ⟨i, hi⟩
    have hrewritten :
        P.map Z (Skorokhod.rangeInOpenIntervalEndsIn (-β) β
          (β * outerLower ⟨i, hi⟩) (β * outerUpper ⟨i, hi⟩)) =
        P.map Z
          (Skorokhod.rangeInOpenIntervalEndsIn (-β) β
            (((i : ℝ) - 1) * (β / 16)) (((i : ℝ) + 1) * (β / 16))) := by
      congr 1
      all_goals dsimp [outerLower, outerUpper]
      all_goals ring_nf
    rw [hrewritten] at hmass
    exact hqhalf.trans_le hmass
  have hbound := eventually_horizontalTubeProbability_ge_pow_of_pathLawLimit
    ν scale blockLength horizon Z hlimit hscale hblock hβ (by positivity)
    (q / 2) hbelow
  refine ⟨β, q / 2, hβ, hβsmall, hqhalfpos, ?_⟩
  simpa using hbound

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
