/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.BridgeComparison.SourceGeometry
public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.FeedbackEntrance
public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.FeedbackEntranceIndexOne
public import Probability.Distributions.Stable.Sign
public import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw

/-! # Stable bridge probabilities for source equation (34)

The source entrance estimate gives positive limiting bridge masses. Portmanteau
then yields a uniform finite-family bridge bound, which combines with the
source-specific cells to prove the finite probability comparison. -/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- The actual source bridge corridor is strictly positive in the limiting
stable path law.  The proof reuses the unit-time stable entrance estimate and
the existing identification of stable process and càdlàg path-law events. -/
theorem sourceBridgeLimitMass_pos
    {Ω' : Type*} [MeasurableSpace Ω']
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω' → ℝ}
    {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hX : IsStableLevyProcess α μ X Q)
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (radius x y : ℝ)
    (hentrance : 0 < Q (fullSegmentCorridorReturnEvent X 0 1
      (-1 - x) (1 - x) (y - x - radius) (y - x + radius))) :
    0 < P.map id
      (Skorokhod.rangeInOpenIntervalEndsIn
        (-1 - x) (1 - x) (y - x - radius) (y - x + radius)) := by
  simp only [Measure.map_id]
  rw [hP.measure_corridorReturnEvent_eq hX
    (-1 - x) (1 - x) (y - x - radius) (y - x + radius)]
  simpa using hentrance

/-- The stable source entrance estimate supplies the exact bridge positivity
input for the source geometry at every center. -/
theorem sourceBridgeEntrance_pos_of_cdf
    {Ω' : Type*} [MeasurableSpace Ω']
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω' → ℝ}
    {Q : Measure Ω'} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (radius x y : ℝ) (hradius : 0 < radius)
    (hx : -1 < x ∧ x < 1) (hy : -1 < y ∧ y < 1)
    (hlow : α < 1 →
      0 < Q (fullSegmentCorridorReturnEvent X 0 1
        (-1 - x) (1 - x) (y - x - radius) (y - x + radius))) :
    0 < Q (fullSegmentCorridorReturnEvent X 0 1
      (-1 - x) (1 - x) (y - x - radius) (y - x + radius)) := by
  -- The source's fixed unit-time entrance estimate. The `α < 1` case is
  -- currently an explicit input because its Poisson construction lives in a
  -- legacy-import-only module.
  by_cases hα : 1 < α
  · convert hX.measure_fullEntrance_pos_of_cdfAtZero hα hcdf (-y) (-x)
      radius (by constructor <;> linarith [hy.1, hy.2])
      (by constructor <;> linarith [hx.1, hx.2]) hradius using 1; ring_nf
  · by_cases hαone : α = 1
    · subst α
      convert hX.measure_fullEntrance_pos_indexOne (-y) (-x) radius
        (by constructor <;> linarith [hy.1, hy.2])
        (by constructor <;> linarith [hx.1, hx.2]) hradius using 1; ring_nf
    · have hle : α ≤ 1 := le_of_not_gt hα
      have hlt : α < 1 := lt_of_le_of_ne hle hαone
      exact hlow hlt

/-- The stable process entrance estimate makes a finite family of source
bridge corridors uniformly positive.  The finite infimum is converted to a
strict real lower bound, which is the form required by open-set Portmanteau. -/
theorem exists_source_uniform_bridge_path_mass_lowerBound
    {Ω' : Type*} [MeasurableSpace Ω']
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω' → ℝ}
    {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hX : IsStableLevyProcess α μ X Q)
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    {F : Finset SourceBridgeCenter} (hF : F.Nonempty)
    (radius y : ℝ)
    (hentrance : ∀ x ∈ F,
      0 < Q (fullSegmentCorridorReturnEvent X 0 1
        (-1 - x.1) (1 - x.1) (y - x.1 - radius) (y - x.1 + radius))) :
    ∃ lowerBound : ℝ, 0 < lowerBound ∧
      ∀ x ∈ F,
        ENNReal.ofReal lowerBound < P.map id
          (Skorokhod.rangeInOpenIntervalEndsIn
            (-1 - x.1) (1 - x.1)
            (y - x.1 - radius) (y - x.1 + radius)) := by
  classical
  let bridgeEvent (x : SourceBridgeCenter) : Set (CadlagPath unitInterval ℝ) :=
    Skorokhod.rangeInOpenIntervalEndsIn
      (-1 - x.1) (1 - x.1) (y - x.1 - radius) (y - x.1 + radius)
  let bridgeMass (x : SourceBridgeCenter) : ℝ≥0∞ := (P.map id) (bridgeEvent x)
  have hmassPos (x : SourceBridgeCenter) (hx : x ∈ F) :
      0 < bridgeMass x := by
    have h := sourceBridgeLimitMass_pos hX hP radius x.1 y (hentrance x hx)
    simpa [bridgeMass, bridgeEvent] using h
  have hmassLeOne (x : SourceBridgeCenter) : bridgeMass x ≤ 1 := by
    dsimp [bridgeMass, bridgeEvent]
    rw [Measure.map_id]
    calc
      P (Skorokhod.rangeInOpenIntervalEndsIn
          (-1 - x.1) (1 - x.1)
          (y - x.1 - radius) (y - x.1 + radius)) ≤ P Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  let q : ℝ≥0∞ := F.inf' hF bridgeMass
  have hqpos : 0 < q := by
    dsimp [q]
    rw [Finset.lt_inf'_iff]
    intro x hx
    exact hmassPos x hx
  have hqle (x : SourceBridgeCenter) (hx : x ∈ F) : q ≤ bridgeMass x :=
    Finset.inf'_le bridgeMass hx
  obtain ⟨x₀, hx₀⟩ := hF
  have hqleOne : q ≤ 1 := (hqle x₀ hx₀).trans (hmassLeOne x₀)
  have hqTop : q ≠ ⊤ := ne_top_of_le_ne_top (by simp) hqleOne
  have hqReal : 0 < q.toReal := ENNReal.toReal_pos hqpos.ne' hqTop
  let lowerBound : ℝ := q.toReal / 2
  have hlower : 0 < lowerBound := by
    dsimp [lowerBound]
    linarith
  have hstrict : ENNReal.ofReal lowerBound < q := by
    rw [← ENNReal.ofReal_toReal hqTop]
    apply (ENNReal.ofReal_lt_ofReal_iff hqReal).2
    dsimp [lowerBound]
    linarith
  refine ⟨lowerBound, hlower, ?_⟩
  intro x hx
  exact hstrict.trans_le (hqle x hx)

/-- Source-specific equation (34) comparison for finite prefix bins.  This
version derives the uniform eventual bridge lower bound from a stable
variable-block path limit and the stable process entrance probabilities;
the finite cover, block-event identification, and bridge gluing are the
concrete source definitions in this file. -/
theorem eventually_source_equation34_finite_bridge_comparison
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {Ω' : Type*} [MeasurableSpace Ω']
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω' → ℝ}
    {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hX : IsStableLevyProcess α μ X Q)
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (F : Finset SourceBridgeCenter) (hF : F.Nonempty)
    (radius ε c b y : ℝ)
    (hFcover : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      ∃ x ∈ F, z ∈ Set.Ioo (x.1 - radius) (x.1 + radius))
    (scale : ℕ → ℝ) (bridgeLength : ℕ → ℕ)
    (hscale : ∀ n, 0 < scale n)
    (hbridgeLe : ∀ n, bridgeLength n ≤ n)
    (hbridgePos : ∀ᶠ n in atTop, 0 < bridgeLength n)
    (hradius : 0 < radius)
    (h2rε : 2 * radius < ε)
    (h2rc : 2 * radius < y - c) (h2rb : 2 * radius < b - y)
    (hentrance : ∀ x ∈ F,
      0 < Q (fullSegmentCorridorReturnEvent X 0 1
        (-1 - x.1) (1 - x.1) (y - x.1 - radius) (y - x.1 + radius)))
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale bridgeLength)
      atTop id (fun _ => iidSequenceLaw ν) P) :
    ∃ lowerBound : ℝ, 0 < lowerBound ∧
      ∀ᶠ n in atTop,
        ENNReal.ofReal lowerBound * iidSequenceLaw ν
          (sourceBaseCorridorEvent (scale n) n) ≤
          (F.card : ℝ≥0∞) * iidSequenceLaw ν
            (sourceEndpointCorridorEvent (scale n) ε c b n) := by
  obtain ⟨lowerBound, hlowerBound, hmass⟩ :=
    exists_source_uniform_bridge_path_mass_lowerBound hX hP hF radius y hentrance
  let geometry := sourceFiniteBridgeGeometry_of_centerCover
    F radius hFcover scale bridgeLength ε c b y hscale hbridgeLe
    hradius h2rε h2rc h2rb
  let bridgePathEvent (x : SourceBridgeCenter) :=
    Skorokhod.rangeInOpenIntervalEndsIn
      (-1 - x.1) (1 - x.1) (y - x.1 - radius) (y - x.1 + radius)
  have hopen (x : SourceBridgeCenter) (_ : x ∈ F) : IsOpen (bridgePathEvent x) :=
    Skorokhod.isOpen_rangeInOpenIntervalEndsIn
      (-1 - x.1) (1 - x.1) (y - x.1 - radius) (y - x.1 + radius)
  have hbridgeLaw : ∀ᶠ n in atTop, ∀ x, x ∈ F →
      RandomWalk.normalizedStepBlockPathLaw ν scale bridgeLength n
          (bridgePathEvent x) =
        iidSequenceLaw ν
          {increment : ℕ → ℝ |
            Combinatorics.Sequence.blockCoordinates 0 (bridgeLength n)
              increment ∈ geometry.bridgeCell n x} := by
    filter_upwards [hbridgePos, Filter.Eventually.of_forall hscale] with n hbn hsn
    intro x hx
    rw [normalizedStepBlockPathLaw_apply_shiftedCorridorEndsIn
      ν scale bridgeLength n hbn hsn (by linarith [x.2.1])
      (by linarith [x.2.2])]
    simp [geometry, sourceFiniteBridgeGeometry_of_centerCover,
      sourceBridgeCell]
  have hcomparison := eventually_source_finite_bridge_comparison
    F (fun n => n - bridgeLength n) bridgeLength
    (fun n => sourceBaseCorridorEvent (scale n) n)
    (fun n => sourceEndpointCorridorEvent (scale n) ε c b n)
    geometry lowerBound
    (eventually_uniform_bridge_lower_bound_of_open_path_limit
      F bridgeLength scale id hlimit geometry.bridgeCell bridgePathEvent
      lowerBound hopen hmass hbridgeLaw)
  refine ⟨lowerBound, hlowerBound, ?_⟩
  simpa [geometry] using hcomparison

/-- The source CDF assumption supplies all entrance masses when `α ≥ 1`.
For `α < 1`, `hlow` is the remaining bridge entrance input at this
module boundary; the available Poisson construction is in a legacy-import-only
module. -/
theorem eventually_source_equation34_finite_bridge_comparison_of_cdf
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {Ω' : Type*} [MeasurableSpace Ω']
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω' → ℝ}
    {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hX : IsStableLevyProcess α μ X Q)
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (F : Finset SourceBridgeCenter) (hF : F.Nonempty)
    (radius ε c b y : ℝ)
    (hy : -1 < y ∧ y < 1)
    (hFcover : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      ∃ x ∈ F, z ∈ Set.Ioo (x.1 - radius) (x.1 + radius))
    (scale : ℕ → ℝ) (bridgeLength : ℕ → ℕ)
    (hscale : ∀ n, 0 < scale n)
    (hbridgeLe : ∀ n, bridgeLength n ≤ n)
    (hbridgePos : ∀ᶠ n in atTop, 0 < bridgeLength n)
    (hradius : 0 < radius)
    (h2rε : 2 * radius < ε)
    (h2rc : 2 * radius < y - c) (h2rb : 2 * radius < b - y)
    (hlow : α < 1 → ∀ x ∈ F,
      0 < Q (fullSegmentCorridorReturnEvent X 0 1
        (-1 - x.1) (1 - x.1) (y - x.1 - radius) (y - x.1 + radius)))
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale bridgeLength)
      atTop id (fun _ => iidSequenceLaw ν) P) :
    ∃ lowerBound : ℝ, 0 < lowerBound ∧
      ∀ᶠ n in atTop,
        ENNReal.ofReal lowerBound * iidSequenceLaw ν
          (sourceBaseCorridorEvent (scale n) n) ≤
          (F.card : ℝ≥0∞) * iidSequenceLaw ν
            (sourceEndpointCorridorEvent (scale n) ε c b n) := by
  apply eventually_source_equation34_finite_bridge_comparison
    hX hP F hF radius ε c b y hFcover scale bridgeLength hscale hbridgeLe
    hbridgePos hradius h2rε h2rc h2rb
  · intro x hx
    exact sourceBridgeEntrance_pos_of_cdf hX hcdf radius x.1 y hradius x.2 hy
      (fun hα => hlow hα x hx)
  · exact hlimit

/-- A finite cover and one source entrance estimate instantiate the source
finite-cell comparison. The radius and interior target are chosen explicitly
from the source endpoint interval `c < b`. -/
theorem exists_source_equation34_finite_bridge_comparison_of_cdf
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {Ω' : Type*} [MeasurableSpace Ω']
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω' → ℝ}
    {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hX : IsStableLevyProcess α μ X Q)
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (ε c b : ℝ) (hε : 0 < ε)
    (hc : -1 < c) (hcb : c < b) (hb : b < 1)
    (scale : ℕ → ℝ) (bridgeLength : ℕ → ℕ)
    (hscale : ∀ n, 0 < scale n)
    (hbridgeLe : ∀ n, bridgeLength n ≤ n)
    (hbridgePos : ∀ᶠ n in atTop, 0 < bridgeLength n)
    (hlow : α < 1 → ∀ radius y : ℝ, 0 < radius → -1 < y → y < 1 →
      ∀ x : SourceBridgeCenter,
        0 < Q (fullSegmentCorridorReturnEvent X 0 1
          (-1 - x.1) (1 - x.1) (y - x.1 - radius) (y - x.1 + radius)))
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale bridgeLength)
      atTop id (fun _ => iidSequenceLaw ν) P) :
    ∃ F : Finset SourceBridgeCenter, ∃ lowerBound : ℝ,
      F.Nonempty ∧ 0 < lowerBound ∧
      ∀ᶠ n in atTop,
        ENNReal.ofReal lowerBound * iidSequenceLaw ν
          (sourceBaseCorridorEvent (scale n) n) ≤
          (F.card : ℝ≥0∞) * iidSequenceLaw ν
            (sourceEndpointCorridorEvent (scale n) ε c b n) := by
  let y : ℝ := (b + c) / 2
  let radius : ℝ := min (ε / 4) ((b - c) / 8)
  have hy : -1 < y ∧ y < 1 := by
    dsimp [y]
    constructor <;> linarith
  have hradius : 0 < radius := by
    dsimp [radius]
    exact lt_min (by positivity) (by linarith)
  have hradiusTwo : radius < 2 := by
    dsimp [radius]
    have hbc : b - c < 2 := by linarith
    exact (min_le_right _ _).trans_lt (by linarith)
  have h2rε : 2 * radius < ε := by
    dsimp [radius]
    have hle : min (ε / 4) ((b - c) / 8) ≤ ε / 4 := min_le_left _ _
    nlinarith
  have h2rc : 2 * radius < y - c := by
    dsimp [radius, y]
    have hle : min (ε / 4) ((b - c) / 8) ≤ (b - c) / 8 := min_le_right _ _
    nlinarith
  have h2rb : 2 * radius < b - y := by
    dsimp [radius, y]
    have hle : min (ε / 4) ((b - c) / 8) ≤ (b - c) / 8 := min_le_right _ _
    nlinarith
  obtain ⟨F, hFcover⟩ := exists_sourceFiniteCenterCover hradius hradiusTwo
  have hF : F.Nonempty := by
    obtain ⟨x, hx, _⟩ := hFcover 0 (by norm_num)
    exact ⟨x, hx⟩
  have hlowF : α < 1 → ∀ x ∈ F,
      0 < Q (fullSegmentCorridorReturnEvent X 0 1
        (-1 - x.1) (1 - x.1) (y - x.1 - radius) (y - x.1 + radius)) := by
    intro hα x hx
    exact hlow hα radius y hradius hy.1 hy.2 x
  obtain ⟨lowerBound, hlowerBound, hcomparison⟩ :=
    eventually_source_equation34_finite_bridge_comparison_of_cdf
      hX hP hcdf F hF radius ε c b y hy hFcover scale bridgeLength hscale hbridgeLe
      hbridgePos hradius h2rε h2rc h2rb hlowF hlimit
  exact ⟨F, lowerBound, hF, hlowerBound, hcomparison⟩


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
