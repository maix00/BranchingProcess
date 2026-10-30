/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep.Block
public import Probability.Process.Path.Skorokhod.Corridor.Basic
public import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.Basic
import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.Iteration
public import Probability.Sequence.IID.Basic
import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.Scale

/-!
# Path-law transfer for endpoint-window blocks

## Public declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.eventually_forall_endpointWindowReturnBlockProbability_ge_of_pathLawLimit`:
  for any finite set of integer endpoint indices, strict positive mass of the
  corresponding open corridor-and-window events under a limiting path law
  gives one common eventual lower bound for the discrete return-block events.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.eventually_forall_endpointWindowBlockProbability_ge_of_pathLawLimit`:
  for any finite set of integer endpoint indices, the same path-law limit
  gives an eventual lower bound for the centered endpoint-window block events
  under the scaled increment law.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.eventually_horizontalTubeProbability_ge_pow_of_pathLawLimit`:
  strict positive mass for the seven return windows indexed by $-3,ldots,3$
  gives the eventual tube lower bound
  $q^{\lfloor N_n/L_n\rfloor+1}\leq\mathbb P(\text{tube through }N_n)$.

The first two transfers require only a finite family of endpoint windows and
an IID block-path limit. The seven-window product estimate is the specialization
used in the discrete endpoint-return argument of A. A. Mogul'skii, Theorem 3,
Section 4, p. 764, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow

/-- Open-set Portmanteau transfers every fixed family of shifted-corridor
endpoint bands to the corresponding discrete blocks. The corridor and band
are stated in the scale of the whole walk; normalizing a block turns them
into fixed open path events. -/
theorem eventually_forall_endpointWindowReturnBlockProbability_ge_of_pathLawLimit
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
    (indices : Finset ℤ)
    {lower upper ε : ℝ}
    (hlower : lower + 4 * ε < 0) (hupper : 0 < upper - 4 * ε)
    (lowerBound : ENNReal)
    (hbelow : ∀ i ∈ indices,
      lowerBound < P.map Z
        (Skorokhod.rangeInOpenIntervalEndsIn
          (lower + 4 * ε) (upper - 4 * ε)
          (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε))) :
    ∀ᶠ n in atTop, ∀ i ∈ indices,
      lowerBound ≤ iidSequenceLaw ν
        (endpointWindowReturnBlockEvent (lower * scale n) (upper * scale n)
          (ε * scale n) (ε * scale n) i (blockLength n)) := by
  apply indices.eventually_all.2
  intro i hi
  let corridor : Set (CadlagPath unitInterval ℝ) :=
    Skorokhod.rangeInOpenIntervalEndsIn
      (lower + 4 * ε) (upper - 4 * ε)
      (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε)
  have hport := hlimit.measure_skorokhodCorridorEndsIn_le_liminf
    (lower + 4 * ε) (upper - 4 * ε)
    (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε)
  have hbelow' : lowerBound < P.map Z corridor := by
    simpa [corridor] using hbelow i hi
  have hstrict : lowerBound < atTop.liminf
      (fun n => RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n corridor) :=
    hbelow'.trans_le (by
      simpa [corridor, ProbabilityTheory.RandomWalk.normalizedStepBlockPathLaw] using hport)
  have hbounded : Filter.IsBoundedUnder (· ≥ ·) atTop
      (fun n => RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n corridor) :=
    Filter.isBoundedUnder_of_eventually_ge
      (Eventually.of_forall fun _ => bot_le)
  have heventuallyPath := eventually_lt_of_lt_liminf hstrict hbounded
  have hsetEq : ∀ᶠ n in atTop,
      {increment : ℕ → ℝ |
        InOpenPartialSumCorridor
            ((lower + 4 * ε) * scale n) ((upper - 4 * ε) * scale n)
            (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment) ∧
          Fin.partialSum
              (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)
              (Fin.last (blockLength n)) / scale n ∈
            Set.Ioo (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε)} =
      endpointWindowReturnBlockEvent (lower * scale n) (upper * scale n)
        (ε * scale n) (ε * scale n) i (blockLength n) := by
    filter_upwards [hscale] with n hs
    ext increment
    change
      (InOpenPartialSumCorridor
          ((lower + 4 * ε) * scale n) ((upper - 4 * ε) * scale n)
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment) ∧
        Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)
            (Fin.last (blockLength n)) / scale n ∈
          Set.Ioo (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε)) ↔
      (InOpenPartialSumCorridor
          (lower * scale n + 3 * (ε * scale n) + (ε * scale n))
          (upper * scale n - 3 * (ε * scale n) - (ε * scale n))
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment) ∧
        Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)
            (Fin.last (blockLength n)) ∈
          Set.Ioo ((i : ℝ) * (ε * scale n) - (ε * scale n))
            ((i : ℝ) * (ε * scale n) + (ε * scale n)))
    have hlow : (lower + 4 * ε) * scale n =
        lower * scale n + 3 * (ε * scale n) + (ε * scale n) := by ring
    have hupp : (upper - 4 * ε) * scale n =
        upper * scale n - 3 * (ε * scale n) - (ε * scale n) := by ring
    have hbandLow : (((i : ℝ) - 1) * ε) * scale n =
        (i : ℝ) * (ε * scale n) - (ε * scale n) := by ring
    have hbandUpp : (((i : ℝ) + 1) * ε) * scale n =
        (i : ℝ) * (ε * scale n) + (ε * scale n) := by ring
    constructor
    · rintro ⟨hpath, hend⟩
      refine ⟨?_, ?_⟩
      · simpa [hlow, hupp] using hpath
      · constructor
        · rw [← hbandLow]
          exact (lt_div_iff₀ hs).mp hend.1
        · rw [← hbandUpp]
          exact (div_lt_iff₀ hs).mp hend.2
    · rintro ⟨hpath, hend⟩
      refine ⟨?_, ?_⟩
      · simpa [hlow, hupp] using hpath
      · constructor
        · apply (lt_div_iff₀ hs).mpr
          rw [hbandLow]
          exact hend.1
        · apply (div_lt_iff₀ hs).mpr
          rw [hbandUpp]
          exact hend.2
  have hpathLawEq : ∀ᶠ n in atTop,
      RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n corridor =
        iidSequenceLaw ν
          (endpointWindowReturnBlockEvent (lower * scale n) (upper * scale n)
            (ε * scale n) (ε * scale n) i (blockLength n)) := by
    filter_upwards [hblock, hscale, hsetEq] with n hn hs hset
    rw [RandomWalk.normalizedStepBlockPathLaw_apply_shiftedCorridorEndsIn
      ν scale blockLength n hn hs hlower hupper]
    simpa [corridor] using congrArg (iidSequenceLaw ν) hset
  filter_upwards [heventuallyPath, hpathLawEq] with n hpath heq
  rw [heq] at hpath
  exact hpath.le

/-- A strict positive mass for each of the seven open endpoint corridors in
the limiting path law gives a common eventual lower bound for the seven
normalized one-block endpoint-band probabilities. The only limit input is
the stated path-law convergence; no boundary-nullity assumption is needed
for this lower bound. -/
theorem eventually_forall_endpointWindowBlockProbability_ge_of_pathLawLimit
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
    (indices : Finset ℤ)
    {radius ε : ℝ} (hradius : 0 < radius) (lowerBound : ENNReal)
    (hbelow : ∀ i ∈ indices,
      lowerBound < P.map Z
        (Skorokhod.rangeInOpenIntervalEndsIn (-radius) radius
          (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε))) :
    ∀ᶠ n in atTop, ∀ i ∈ indices,
      lowerBound ≤ iidSequenceLaw (ν.map fun x : ℝ => x / scale n)
        (endpointWindowBlockEvent radius ε ε i (blockLength n)) := by
  apply indices.eventually_all.2
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
          (endpointWindowBlockEvent radius ε ε i (blockLength n)) := by
    filter_upwards [hscale, hblock] with n hs hn
    rw [ProbabilityTheory.RandomWalk.normalizedStepBlockPathLaw_apply_centeredOpenIntervalEndsIn
      ν scale blockLength n hn hs (by positivity)]
    simpa [corridor, show -(2 * radius / 2) = -radius by ring,
      show 2 * radius / 2 = radius by ring,
      show ((i : ℝ) - 1) * ε = (i : ℝ) * ε - ε by ring,
      show ((i : ℝ) + 1) * ε = (i : ℝ) * ε + ε by ring] using
      iidSequenceLaw_endpointWindowBlockEvent_scale ν scale n (blockLength n)
        hs radius ε ε i
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
  have hbands := eventually_forall_endpointWindowBlockProbability_ge_of_pathLawLimit
    ν scale blockLength Z hlimit hscale hblock (Finset.Icc (-3 : ℤ) 3)
    hradius lowerBound hbelow
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
  have hnormalized := horizontalTubeProbability_ge_pow_endpointWindows_of_horizon_le
    (ν.map fun x : ℝ => x / scale n) hε hε (by linarith [hε])
    (horizon n / length + 1) length (horizon n) hcover lowerBound hbandsN
  have hmap := horizontalTubeProbability_map_div
    ν (1 / 2) (2 * (radius + 4 * ε) * scale n) (horizon n) hscaleN
  have hwidth :
      (2 * (radius + 4 * ε) * scale n) / scale n = 2 * (radius + 4 * ε) := by
    field_simp [hscaleN.ne']
  rw [hwidth] at hmap
  have hnormalized' : lowerBound ^ (horizon n / blockLength n + 1) ≤
      horizontalTubeProbability (iidSequenceLaw (ν.map fun x : ℝ => x / scale n))
        (1 / 2) (2 * (radius + 4 * ε)) (horizon n) := by
    simpa only [show radius + 3 * ε + ε = radius + 4 * ε by ring] using hnormalized
  exact hnormalized'.trans_eq hmap

end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow

end
