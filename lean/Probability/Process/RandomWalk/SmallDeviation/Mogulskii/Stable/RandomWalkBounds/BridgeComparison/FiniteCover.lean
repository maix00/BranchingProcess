/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.NegativeRatio
public import Probability.ConvergenceInDistribution.Portmanteau
public import Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep.Block
public import Probability.Process.RandomWalk.Path.Block.Corridor.Comparison
public import Probability.Sequence.IID

/-! # Generic finite-cell bridge comparison

Finite prefix covers and open-set path-law limits yield a uniform bridge
lower bound and the corresponding IID finite-cover estimate. -/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- The finite prefix cells and their source-specific gluing into a target
event.  The two block lengths may vary with the outer parameter. -/
structure SourceFiniteBridgeGeometry
    (ι : Type*) (F : Finset ι)
    (prefixLength bridgeLength : ℕ → ℕ)
    (U T : ℕ → Set (ℕ → ℝ)) where
  prefixCell : (n : ℕ) → ι → Set (Fin (prefixLength n) → ℝ)
  bridgeCell : (n : ℕ) → ι → Set (Fin (bridgeLength n) → ℝ)
  prefixCell_measurable : ∀ n i, i ∈ F → MeasurableSet (prefixCell n i)
  bridgeCell_measurable : ∀ n i, i ∈ F → MeasurableSet (bridgeCell n i)
  prefix_cover : ∀ n, U n ⊆ ⋃ i ∈ F,
    {increment : ℕ → ℝ |
      Combinatorics.Sequence.blockCoordinates 0 (prefixLength n) increment ∈
        prefixCell n i}
  bridge_glue : ∀ n i, i ∈ F →
    {increment : ℕ → ℝ |
      Combinatorics.Sequence.blockCoordinates 0 (prefixLength n) increment ∈
          prefixCell n i ∧
        Combinatorics.Sequence.blockCoordinates (prefixLength n)
          (bridgeLength n) increment ∈ bridgeCell n i} ⊆ T n

/-- An open bridge family of positive limiting mass supplies one common
eventual lower bound for all cells in a finite family.  The last hypothesis
identifies each source's finite-block event with the corresponding event of
the normalized block path; it is where an application proves its concrete
corridor geometry. -/
theorem eventually_uniform_bridge_lower_bound_of_open_path_limit
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {ι : Type*} (F : Finset ι) (bridgeLength : ℕ → ℕ)
    (spatialScale : ℕ → ℝ)
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : Ω → CadlagPath unitInterval ℝ)
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc spatialScale bridgeLength)
      atTop Z (fun _ => iidSequenceLaw ν) P)
    (bridgeCell : (n : ℕ) → ι → Set (Fin (bridgeLength n) → ℝ))
    (bridgePathEvent : ι → Set (CadlagPath unitInterval ℝ))
    (lowerBound : ℝ)
    (hopen : ∀ i, i ∈ F → IsOpen (bridgePathEvent i))
    (hmass : ∀ i, i ∈ F →
      ENNReal.ofReal lowerBound < P.map Z (bridgePathEvent i))
    (hbridgeLaw : ∀ᶠ n in atTop, ∀ i, i ∈ F →
      RandomWalk.normalizedStepBlockPathLaw ν spatialScale bridgeLength n
          (bridgePathEvent i) =
        iidSequenceLaw ν
          {increment : ℕ → ℝ |
            Combinatorics.Sequence.blockCoordinates 0 (bridgeLength n)
              increment ∈ bridgeCell n i}) :
    ∀ᶠ n in atTop, ∀ i, i ∈ F →
      ENNReal.ofReal lowerBound ≤ iidSequenceLaw ν
        {increment : ℕ → ℝ |
          Combinatorics.Sequence.blockCoordinates 0 (bridgeLength n)
            increment ∈ bridgeCell n i} := by
  classical
  apply F.eventually_all.2
  intro i hi
  have hport := hlimit.measure_map_le_liminf_of_isOpen (hopen i hi)
  have hstrict : ENNReal.ofReal lowerBound < atTop.liminf
      (fun n => RandomWalk.normalizedStepBlockPathLaw ν spatialScale
        bridgeLength n (bridgePathEvent i)) :=
    (hmass i hi).trans_le (by
      simpa [RandomWalk.normalizedStepBlockPathLaw] using hport)
  have hbounded : Filter.IsBoundedUnder (· ≥ ·) atTop
      (fun n => RandomWalk.normalizedStepBlockPathLaw ν spatialScale
        bridgeLength n (bridgePathEvent i)) :=
    Filter.isBoundedUnder_of_eventually_ge
      (Eventually.of_forall fun _ => bot_le)
  have heventuallyPath := eventually_lt_of_lt_liminf hstrict hbounded
  filter_upwards [heventuallyPath, hbridgeLaw] with n hn hbridgeLawN
  rw [hbridgeLawN i hi] at hn
  exact hn.le

/-- The generic IID finite-cover estimate applied to the supplied source
geometry.  Its only probabilistic input is the uniform bridge lower bound;
all event measurability and pathwise gluing obligations are explicit in the
geometry structure. -/
theorem eventually_source_finite_bridge_comparison
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {ι : Type*} (F : Finset ι)
    (prefixLength bridgeLength : ℕ → ℕ)
    (U T : ℕ → Set (ℕ → ℝ))
    (geometry : SourceFiniteBridgeGeometry ι F prefixLength bridgeLength U T)
    (lowerBound : ℝ)
    (hbridge : ∀ᶠ n in atTop, ∀ i, i ∈ F →
      ENNReal.ofReal lowerBound ≤ iidSequenceLaw ν
        {increment : ℕ → ℝ |
          Combinatorics.Sequence.blockCoordinates 0 (bridgeLength n)
            increment ∈ geometry.bridgeCell n i}) :
    ∀ᶠ n in atTop,
      ENNReal.ofReal lowerBound * iidSequenceLaw ν (U n) ≤
        (F.card : ℝ≥0∞) * iidSequenceLaw ν (T n) := by
  filter_upwards [hbridge] with n hbridgeN
  exact ProbabilityTheory.RandomWalk.iidSequenceLaw_measure_mul_le_card_mul_of_finite_block_cover
    ν F (prefixLength n) (bridgeLength n) (U n) (T n)
    (fun i => geometry.prefixCell n i) (fun i => geometry.bridgeCell n i)
    (ENNReal.ofReal lowerBound)
    (fun i hi => geometry.prefixCell_measurable n i hi)
    (fun i hi => geometry.bridgeCell_measurable n i hi)
    (geometry.prefix_cover n)
    (fun i hi => hbridgeN i hi)
    (fun i hi => geometry.bridge_glue n i hi)

/-- Composition form of the source's equation (34): open limiting bridge
events yield the eventual finite-cover comparison, which gives the lower
logarithmic-ratio bound.  The source-specific geometry, positive limiting
bridge masses, event identification, base-event positivity, and target-event
decay are hypotheses, not axioms or conclusions of this adapter. -/
theorem eventually_one_sub_le_log_ratio_of_source_bridge_comparison
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {ι : Type*} (F : Finset ι) (hF : F.Nonempty)
    (prefixLength bridgeLength : ℕ → ℕ)
    (U T : ℕ → Set (ℕ → ℝ))
    (geometry : SourceFiniteBridgeGeometry ι F prefixLength bridgeLength U T)
    (spatialScale : ℕ → ℝ)
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : Ω → CadlagPath unitInterval ℝ)
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc spatialScale bridgeLength)
      atTop Z (fun _ => iidSequenceLaw ν) P)
    (bridgePathEvent : ι → Set (CadlagPath unitInterval ℝ))
    (lowerBound : ℝ) (hlowerBound : 0 < lowerBound)
    (hopen : ∀ i, i ∈ F → IsOpen (bridgePathEvent i))
    (hmass : ∀ i, i ∈ F →
      ENNReal.ofReal lowerBound < P.map Z (bridgePathEvent i))
    (hbridgeLaw : ∀ᶠ n in atTop, ∀ i, i ∈ F →
      RandomWalk.normalizedStepBlockPathLaw ν spatialScale bridgeLength n
          (bridgePathEvent i) =
        iidSequenceLaw ν
          {increment : ℕ → ℝ |
            Combinatorics.Sequence.blockCoordinates 0 (bridgeLength n)
              increment ∈ geometry.bridgeCell n i})
    (hU : ∀ᶠ n in atTop, 0 < (iidSequenceLaw ν (U n)).toReal)
    (hT : ∀ᶠ n in atTop, 0 < (iidSequenceLaw ν (T n)).toReal)
    (hTzero : Tendsto (fun n => (iidSequenceLaw ν (T n)).toReal)
      atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      1 - ε ≤ Real.log ((iidSequenceLaw ν (U n)).toReal) /
        Real.log ((iidSequenceLaw ν (T n)).toReal) := by
  have hbridge := eventually_uniform_bridge_lower_bound_of_open_path_limit
    F bridgeLength spatialScale Z hlimit geometry.bridgeCell bridgePathEvent
    lowerBound hopen hmass hbridgeLaw
  have hcomparison := eventually_source_finite_bridge_comparison
    F prefixLength bridgeLength U T geometry lowerBound hbridge
  let C : ℝ := (F.card : ℝ) / lowerBound
  have hC : 0 < C := by
    dsimp [C]
    exact div_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr hF)) hlowerBound
  have hrealComparison :
      (fun n => (iidSequenceLaw ν (U n)).toReal) ≤ᶠ[atTop]
        (fun n => C * (iidSequenceLaw ν (T n)).toReal) := by
    filter_upwards [hcomparison] with n hcomparisonN
    have hleftTop : ENNReal.ofReal lowerBound * iidSequenceLaw ν (U n) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    have hrightTop : (F.card : ℝ≥0∞) * iidSequenceLaw ν (T n) ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
    have hreal := (ENNReal.toReal_le_toReal hleftTop hrightTop).2 hcomparisonN
    have hreal' : lowerBound * (iidSequenceLaw ν (U n)).toReal ≤
        (F.card : ℝ) * (iidSequenceLaw ν (T n)).toReal := by
      simpa [ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal hlowerBound.le] using hreal
    have hdiv : (iidSequenceLaw ν (U n)).toReal ≤
        ((F.card : ℝ) * (iidSequenceLaw ν (T n)).toReal) / lowerBound := by
      apply (le_div_iff₀ hlowerBound).2
      simpa [mul_comm] using hreal'
    simpa [C, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
  exact Asymptotics.eventually_one_sub_le_log_ratio_of_mul_bound
    C hC hrealComparison hU hT hTzero ε hε


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
