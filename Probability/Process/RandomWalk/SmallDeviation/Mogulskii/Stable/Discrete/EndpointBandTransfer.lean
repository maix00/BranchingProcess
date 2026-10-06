/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep.Block
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.EndpointReturn
public import Probability.Process.Path.Skorokhod.Corridor
public import Probability.Sequence.IID

/-!
# Portmanteau transfer for stable endpoint bands

An open corridor with an open endpoint window transfers a strict positive
limit mass to an eventual lower bound for the corresponding finite endpoint
band. This is the path-law input to the discrete return-kernel estimate.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- Rescaling every coordinate of an i.i.d. sequence turns the finite
normalized tube and endpoint event into the endpoint-band event used by the
discrete return estimate. -/
theorem iidSequenceLaw_normalizedEndpointBand_eq
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (n length : ℕ) (hscale : 0 < scale n)
    (radius ε : ℝ) (i : ℤ) :
    iidSequenceLaw ν {increment |
      InOpenHorizontalTube (1 / 2) (2 * radius * scale n) length increment ∧
        AdditivePath.displacement length increment / scale n ∈
          Set.Ioo (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε)} =
      iidSequenceLaw (ν.map fun x : ℝ => x / scale n)
        (endpointBandBlockEvent radius ε i length) := by
  let normalize : (ℕ → ℝ) → (ℕ → ℝ) := fun sequence k => sequence k / scale n
  have hwidth : (2 * radius * scale n) / scale n = 2 * radius := by
    field_simp [hscale.ne']
  have hsum (sequence : ℕ → ℝ) :
      AdditivePath.displacement length (normalize sequence) =
        AdditivePath.displacement length sequence / scale n := by
    simp [normalize, AdditivePath.displacement, div_eq_mul_inv, Finset.sum_mul]
  have hset :
      {increment | InOpenHorizontalTube (1 / 2)
          (2 * radius * scale n) length increment ∧
        AdditivePath.displacement length increment / scale n ∈
          Set.Ioo (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε)} =
        normalize ⁻¹' endpointBandBlockEvent radius ε i length := by
    ext increment
    change (InOpenHorizontalTube (1 / 2) (2 * radius * scale n)
        length increment ∧
      AdditivePath.displacement length increment / scale n ∈
        Set.Ioo (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε)) ↔
      InOpenHorizontalTube (1 / 2) (2 * radius) length (normalize increment) ∧
        AdditivePath.displacement length (normalize increment) ∈
          Set.Ioo (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε)
    have htube := inOpenHorizontalTube_div_iff (1 / 2)
      (2 * radius * scale n) length increment hscale
    rw [hwidth] at htube
    constructor
    · rintro ⟨htube', hend⟩
      exact ⟨htube.mpr htube', by simpa [hsum] using hend⟩
    · rintro ⟨htube', hend⟩
      exact ⟨htube.mp htube', by simpa [hsum] using hend⟩
  have hnormalize : Measurable normalize :=
    Measurable.of_eval fun k =>
      (measurable_id.div_const (scale n)).comp (measurable_pi_apply k)
  rw [← iidSequenceLaw_map_coordinatewise ν
    (fun x : ℝ => x / scale n) (measurable_id.div_const (scale n)),
    Measure.map_apply hnormalize
      (measurableSet_endpointBandBlockEvent radius ε i length), hset]

/-- A strict positive mass for each of the seven open endpoint corridors in
the limiting path law gives a common eventual lower bound for the seven
normalized one-block endpoint-band probabilities. The only limit input is
the stated path-law convergence; no boundary-nullity assumption is needed
for this lower bound. -/
theorem eventually_forall_normalizedEndpointBandProbability_ge_of_pathLawLimit
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (blockLength : ℕ → ℕ)
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : Ω → CadlagPath unitInterval ℝ)
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale blockLength)
      atTop Z (fun _ => iidSequenceLaw ν) P)
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hblock : ∀ᶠ n in atTop, 0 < blockLength n)
    {radius ε : ℝ} (hradius : 0 < radius) (lowerBound : ENNReal)
    (hbelow : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound < P.map Z
        (Skorokhod.rangeInOpenIntervalEndsIn (-radius) radius
          (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε))) :
    ∀ᶠ n in atTop, ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw (ν.map fun x : ℝ => x / scale n)
        (endpointBandBlockEvent radius ε i (blockLength n)) := by
  apply (Finset.Icc (-3 : ℤ) 3).eventually_all.2
  intro i hi
  let corridor : Set (CadlagPath unitInterval ℝ) :=
    Skorokhod.rangeInOpenIntervalEndsIn
      (-(2 * radius / 2)) (2 * radius / 2)
      (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε)
  have hport := hlimit.measure_skorokhodCorridorEndsIn_le_liminf
    (-(2 * radius / 2)) (2 * radius / 2)
    (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε)
  have hbelow' : lowerBound < P.map Z corridor := by
    simpa [corridor, show -(2 * radius / 2) = -radius by ring,
      show 2 * radius / 2 = radius by ring] using hbelow i hi
  have hstrict : lowerBound < atTop.liminf
      (fun n => RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n corridor) :=
    hbelow'.trans_le (by
      simpa [corridor, ProbabilityTheory.RandomWalk.normalizedStepBlockPathLaw] using hport)
  have hbounded : Filter.IsBoundedUnder (· ≥ ·) atTop
      (fun n => RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n corridor) :=
    Filter.isBoundedUnder_of_eventually_ge
      (Eventually.of_forall fun _ => bot_le)
  have heventuallyPath := eventually_lt_of_lt_liminf hstrict hbounded
  have heventuallyEq : ∀ᶠ n in atTop,
      RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n corridor =
        iidSequenceLaw (ν.map fun x : ℝ => x / scale n)
          (endpointBandBlockEvent radius ε i (blockLength n)) := by
    filter_upwards [hscale, hblock] with n hs hn
    rw [ProbabilityTheory.RandomWalk.normalizedStepBlockPathLaw_apply_centeredOpenIntervalEndsIn
      ν scale blockLength n hn hs (by positivity)]
    simpa [corridor, show -(2 * radius / 2) = -radius by ring,
      show 2 * radius / 2 = radius by ring] using
      iidSequenceLaw_normalizedEndpointBand_eq ν scale n (blockLength n)
        hs radius ε i
  filter_upwards [heventuallyPath, heventuallyEq] with n hpath heq
  rw [heq] at hpath
  exact hpath.le

/-- The open-endpoint Portmanteau transfer supplies the seven band inputs to
the stable-block return-kernel iteration. Thus a path-law limit and strict
positive limiting endpoint-corridor masses imply the discrete lower bound
for every horizon, with the source quotient block count. -/
theorem eventually_horizontalTubeProbability_ge_pow_of_pathLawLimit
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (blockLength horizon : ℕ → ℕ)
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : Ω → CadlagPath unitInterval ℝ)
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale blockLength)
      atTop Z (fun _ => iidSequenceLaw ν) P)
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hblock : ∀ᶠ n in atTop, 0 < blockLength n)
    {radius ε : ℝ} (hradius : 0 < radius) (hε : 0 < ε)
    (lowerBound : ENNReal)
    (hbelow : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound < P.map Z
        (Skorokhod.rangeInOpenIntervalEndsIn (-radius) radius
          (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε))) :
    ∀ᶠ n in atTop,
      lowerBound ^ (horizon n / blockLength n + 1) ≤
        horizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
          (2 * (radius + 4 * ε) * scale n) (horizon n) := by
  have hbands := eventually_forall_normalizedEndpointBandProbability_ge_of_pathLawLimit
    ν scale blockLength Z hlimit hscale hblock hradius lowerBound hbelow
  filter_upwards [hbands, hscale, hblock] with n hbandsN hscaleN hblockN
  let length := blockLength n
  have hdecomp : horizon n = horizon n / length * length + horizon n % length := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod (horizon n) length).symm
  have hcover : horizon n ≤ (horizon n / length + 1) * length := by
    calc
      horizon n = horizon n / length * length + horizon n % length := hdecomp
      _ ≤ horizon n / length * length + length :=
        Nat.add_le_add_left (Nat.mod_lt (horizon n) hblockN).le _
      _ = (horizon n / length + 1) * length := by simp [Nat.add_mul]
  have hnormalized := horizontalTubeProbability_ge_pow_endpointBands_of_horizon_le
    (ν.map fun x : ℝ => x / scale n) hε (horizon n / length + 1)
    length (horizon n) hcover lowerBound hbandsN
  have hmap := horizontalTubeProbability_map_div
    ν (1 / 2) (2 * (radius + 4 * ε) * scale n) (horizon n) hscaleN
  have hwidth :
      (2 * (radius + 4 * ε) * scale n) / scale n = 2 * (radius + 4 * ε) := by
    field_simp [hscaleN.ne']
  rw [hwidth] at hmap
  exact hnormalized.trans_eq hmap

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
