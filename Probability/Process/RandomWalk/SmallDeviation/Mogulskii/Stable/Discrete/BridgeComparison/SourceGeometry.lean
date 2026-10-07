/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep.Block
public import Probability.Process.RandomWalk.Path.Block.Corridor.Measure
public import Probability.Process.RandomWalk.Path.Block.Partition.Basic
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal
public import Probability.Sequence.IID
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.BridgeComparison.FiniteCover

/-! # Source corridor cells and finite bridge geometry

This module defines the source's prefix and bridge cells, identifies them
with normalized block-path events, and proves their finite cover and gluing. -/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- A finite cover center is kept strictly inside the unit interval.  This is
needed because the source's stable entrance estimate is stated for an
interior starting point. -/
abbrev SourceBridgeCenter := {x : ℝ // -1 < x ∧ x < 1}

/-- Prefix cells for the source's equation (34): the prefix stays in the unit
corridor, and its normalized endpoint lies in the bin around `x`. -/
def sourcePrefixCell (length : ℕ) (scale radius x : ℝ) :
    Set (Fin length → ℝ) :=
  {block | InOpenPartialSumCorridor (-scale) scale block ∧
    Fin.partialSum block (Fin.last length) / scale ∈ Set.Ioo (x - radius) (x + radius)}

/-- The source bridge cell starts its increments at zero, but its corridor is
translated by the chosen prefix center. -/
def sourceBridgeCell (length : ℕ) (scale radius x y : ℝ) :
    Set (Fin length → ℝ) :=
  {block | InOpenPartialSumCorridor ((-1 - x) * scale) ((1 - x) * scale) block ∧
    Fin.partialSum block (Fin.last length) / scale ∈
      Set.Ioo (y - x - radius) (y - x + radius)}

/-- The open unit-corridor event on the full increment path. -/
def sourceBaseCorridorEvent (scale : ℝ) (horizon : ℕ) : Set (ℕ → ℝ) :=
  {increment | InOpenHorizontalTube (1 / 2) (2 * scale) horizon increment}

/-- The widened source target event with its original `Ioc` endpoint
convention. -/
def sourceEndpointCorridorEvent (scale ε c b : ℝ) (horizon : ℕ) :
    Set (ℕ → ℝ) :=
  {increment | InOpenHorizontalTube (1 / 2) (2 * (1 + ε) * scale)
      horizon increment ∧
    AdditivePath.displacement horizon increment / scale ∈ Set.Ioc c b}

theorem exists_sourceFiniteCenterCover
    {radius : ℝ} (hradius : 0 < radius) (hradiusTwo : radius < 2) :
    ∃ F : Finset SourceBridgeCenter,
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        ∃ x ∈ F, z ∈ Set.Ioo (x.1 - radius) (x.1 + radius) := by
  let W : SourceBridgeCenter → Set ℝ := fun x =>
    Set.Ioo (x.1 - radius) (x.1 + radius)
  have hopen : ∀ x : SourceBridgeCenter, IsOpen (W x) := fun _ => isOpen_Ioo
  have hcover : Set.Icc (-1 : ℝ) 1 ⊆ ⋃ x : SourceBridgeCenter, W x := by
    intro z hz
    let q : ℝ := 1 - radius / 2
    have hqpos : 0 < q := by dsimp [q]; linarith
    have hqle : q ≤ 1 := by dsimp [q]; linarith
    have hzabs : |z| ≤ 1 := abs_le.mpr hz
    have hxabs : |q * z| < 1 := by
      calc
        |q * z| = q * |z| := abs_mul q z ▸ by rw [abs_of_pos hqpos]
        _ ≤ q := mul_le_of_le_one_right hqpos.le hzabs
        _ < 1 := by dsimp [q]; linarith
    have hxmem : -1 < q * z ∧ q * z < 1 := abs_lt.mp hxabs
    let x : SourceBridgeCenter := ⟨q * z, hxmem⟩
    have hclose : |z - x.1| < radius := by
      have hdiff : z - q * z = (radius / 2) * z := by
        dsimp [q]
        ring
      rw [show z - x.1 = z - q * z by rfl, hdiff]
      calc
        |radius / 2 * z| = radius / 2 * |z| := by
          rw [abs_mul, abs_of_pos (div_pos hradius (by norm_num : (0 : ℝ) < 2))]
        _ ≤ radius / 2 := mul_le_of_le_one_right
          (div_nonneg hradius.le (by norm_num)) hzabs
        _ < radius := by linarith
    refine Set.mem_iUnion.mpr ⟨x, ?_⟩
    change x.1 - radius < z ∧ z < x.1 + radius
    have habs := abs_lt.mp hclose
    constructor <;> linarith
  obtain ⟨F, hF⟩ := isCompact_Icc.elim_finite_subcover W hopen hcover
  refine ⟨F, ?_⟩
  intro z hz
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hF hz)
  obtain ⟨hxin, hxW⟩ := Set.mem_iUnion.mp hx
  exact ⟨x, hxin, by simpa [W] using hxW⟩

theorem source_openPartialSumCorridor_iff_nonempty
    {length : ℕ} {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper)
    (block : Fin length → ℝ) :
    InOpenPartialSumCorridor lower upper block ↔
      ∀ k : Fin length,
        lower < Fin.partialSum block k.succ ∧
          Fin.partialSum block k.succ < upper := by
  constructor
  · intro h k
    exact h k.succ
  · intro h k
    refine Fin.induction ?_ ?_ k
    · simp [hlower, hupper]
    · intro k ih
      exact h k

/-- The finite source corridor cells are measurable in their product
coordinate sigma algebra. -/
theorem measurableSet_sourcePrefixCell
    (length : ℕ) (scale radius x : ℝ) :
    MeasurableSet (sourcePrefixCell length scale radius x) := by
  rw [show sourcePrefixCell length scale radius x =
      {block | InOpenPartialSumCorridor (-scale) scale block} ∩
        {block | Fin.partialSum block (Fin.last length) / scale ∈
          Set.Ioo (x - radius) (x + radius)} by
    ext block
    rfl]
  exact measurableSet_inOpenPartialSumCorridor (-scale) scale |>.inter <|
    measurableSet_Ioo.preimage (by fun_prop)

theorem measurableSet_sourceBridgeCell
    (length : ℕ) (scale radius x y : ℝ) :
    MeasurableSet (sourceBridgeCell length scale radius x y) := by
  rw [show sourceBridgeCell length scale radius x y =
      {block | InOpenPartialSumCorridor ((-1 - x) * scale) ((1 - x) * scale) block} ∩
        {block | Fin.partialSum block (Fin.last length) / scale ∈
          Set.Ioo (y - x - radius) (y - x + radius)} by
    ext block
    rfl]
  exact measurableSet_inOpenPartialSumCorridor _ _ |>.inter <|
    measurableSet_Ioo.preimage (by fun_prop)

/-- An arbitrary shifted open corridor with an open endpoint window has the
expected finite-coordinate event under the normalized variable-block path
law.  Unlike the centered adapter, this is the form used by the finite cover. -/
theorem normalizedStepBlockPathLaw_apply_shiftedCorridorEndsIn
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (blockLength : ℕ → ℕ) (n : ℕ)
    (hblock : 0 < blockLength n) (hscale : 0 < scale n)
    {lower upper endpointLower endpointUpper : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper) :
    RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n
        (Skorokhod.rangeInOpenIntervalEndsIn
          lower upper endpointLower endpointUpper) =
      iidSequenceLaw ν {increment : ℕ → ℝ |
        InOpenPartialSumCorridor (lower * scale n) (upper * scale n)
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment) ∧
    Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)
          (Fin.last (blockLength n)) / scale n ∈
            Set.Ioo endpointLower endpointUpper} := by
  rw [RandomWalk.normalizedStepBlockPathLaw, Measure.map_apply]
  · congr 1
    ext increment
    change RandomWalk.normalizedStepBlockCadlagPathIcc scale blockLength n increment ∈
        Skorokhod.rangeInOpenIntervalEndsIn
          lower upper endpointLower endpointUpper ↔ _
    rw [Skorokhod.mem_rangeInOpenIntervalEndsIn_iff]
    constructor
    · rintro ⟨hgrid, hend⟩
      have hcorridor : InOpenPartialSumCorridor
          (lower * scale n) (upper * scale n)
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment) := by
        apply (source_openPartialSumCorridor_iff_nonempty
          (mul_neg_of_neg_of_pos hlower hscale)
          (mul_pos hupper hscale)
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)).2
        have hgrid' := (RandomWalk.normalizedStepBlockCadlagPathIcc_mem_rangeInOpenInterval_iff_grid
          scale blockLength hblock hscale hlower hupper increment).1 hgrid
        intro k
        have hk := hgrid' k
        have hsum := RandomWalk.partialSum_blockCoordinates 0 increment k.succ
        have hsum' : Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)
            k.succ = AdditivePath.displacement (k + 1) increment := by
          rw [hsum, AdditivePath.blockSum_eq_displacement_natAdd]
          simp
        rw [hsum']
        exact hk
      have hlast : Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)
          (Fin.last (blockLength n)) = AdditivePath.displacement (blockLength n) increment := by
        rw [RandomWalk.partialSum_blockCoordinates,
          AdditivePath.blockSum_eq_displacement_natAdd]
        simp
      refine ⟨hcorridor, ?_⟩
      change endpointLower <
          RandomWalk.normalizedStepBlockCadlagPathIcc scale blockLength n increment ⊤ ∧
        RandomWalk.normalizedStepBlockCadlagPathIcc scale blockLength n increment ⊤ <
          endpointUpper at hend
      simpa [RandomWalk.normalizedStepBlockCadlagPathIcc,
        RandomWalk.normalizedStepCadlagPathIcc_apply,
        RandomWalk.normalizedStepPath_one, hlast, div_eq_mul_inv, mul_comm] using hend
    · rintro ⟨hcell, hend⟩
      have hgrid : ∀ k : Fin (blockLength n),
          lower * scale n < AdditivePath.displacement (k + 1) increment ∧
            AdditivePath.displacement (k + 1) increment < upper * scale n := by
        intro k
        have hk := (source_openPartialSumCorridor_iff_nonempty
          (mul_neg_of_neg_of_pos hlower hscale)
          (mul_pos hupper hscale)
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)).1 hcell k
        have hsum := RandomWalk.partialSum_blockCoordinates 0 increment k.succ
        rw [hsum, AdditivePath.blockSum_eq_displacement_natAdd] at hk
        simpa using hk
      have hlast : Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)
          (Fin.last (blockLength n)) = AdditivePath.displacement (blockLength n) increment := by
        rw [RandomWalk.partialSum_blockCoordinates,
          AdditivePath.blockSum_eq_displacement_natAdd]
        simp
      refine ⟨?_, ?_⟩
      · exact (RandomWalk.normalizedStepBlockCadlagPathIcc_mem_rangeInOpenInterval_iff_grid
          scale blockLength hblock hscale hlower hupper increment).2 hgrid
      · simpa [RandomWalk.normalizedStepBlockCadlagPathIcc,
          RandomWalk.normalizedStepCadlagPathIcc_apply,
          RandomWalk.normalizedStepPath_one, hlast, div_eq_mul_inv, mul_comm] using hend
  · exact RandomWalk.measurable_normalizedStepCadlagPathIcc
      (fun _ => scale n) (blockLength n)
  · exact Skorokhod.measurableSet_rangeInOpenIntervalEndsIn
      lower upper endpointLower endpointUpper

/-- The finite source cells glue: after a prefix endpoint lies in the bin at
`x`, the shifted bridge stays inside the widened corridor and ends in the
source endpoint window. -/
theorem sourceBridge_glue
    {n prefixLength bridgeLength : ℕ}
    (hpartition : prefixLength + bridgeLength = n)
    {scale radius ε c b x y : ℝ}
    (hscale : 0 < scale) (hradius : 0 < radius)
    (h2rε : 2 * radius < ε)
    (h2rc : 2 * radius < y - c) (h2rb : 2 * radius < b - y)
    (increment : ℕ → ℝ)
    (hprefix : Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈
      sourcePrefixCell prefixLength scale radius x)
    (hbridge : Combinatorics.Sequence.blockCoordinates prefixLength bridgeLength increment ∈
      sourceBridgeCell bridgeLength scale radius x y) :
    increment ∈ sourceEndpointCorridorEvent scale ε c b n := by
  rcases hprefix with ⟨hpreTube, hpreEnd⟩
  rcases hbridge with ⟨hbridgeTube, hbridgeEnd⟩
  have hpreEnd' :
      AdditivePath.displacement prefixLength increment / scale ∈
        Set.Ioo (x - radius) (x + radius) := by
    simpa [RandomWalk.partialSum_blockCoordinates,
      AdditivePath.blockSum_eq_displacement_natAdd] using hpreEnd
  have hbridgeEnd' :
      AdditivePath.blockSum prefixLength bridgeLength increment / scale ∈
        Set.Ioo (y - x - radius) (y - x + radius) := by
    simpa [RandomWalk.partialSum_blockCoordinates] using hbridgeEnd
  have hpartial (k : Fin n) :
      -(1 + ε) * scale < AdditivePath.displacement (k + 1) increment ∧
        AdditivePath.displacement (k + 1) increment < (1 + ε) * scale := by
    by_cases hk : (k : ℕ) + 1 ≤ prefixLength
    · have hidx : (k : ℕ) < prefixLength := by omega
      have h := hpreTube ⟨(k : ℕ) + 1, by omega⟩
      have hsum := RandomWalk.partialSum_blockCoordinates 0 increment
        (⟨(k : ℕ) + 1, by omega⟩ : Fin (prefixLength + 1))
      have hsum' : AdditivePath.displacement (k + 1) increment =
          Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment)
              ⟨(k : ℕ) + 1, by omega⟩ := by
        rw [hsum]
        simp [AdditivePath.blockSum_eq_displacement_natAdd]
      have hsum'' : AdditivePath.displacement (k + 1) increment =
          AdditivePath.blockSum 0 (k + 1) increment := by
        rw [AdditivePath.blockSum_eq_displacement_natAdd]
        simp
      rw [hsum'']
      constructor <;> nlinarith [h.1, h.2, hscale, hradius, h2rε]
    · have hk' : prefixLength < (k : ℕ) + 1 := by omega
      have hrem : (k : ℕ) + 1 = prefixLength + ((k : ℕ) + 1 - prefixLength) := by omega
      have hremPos : 0 < (k : ℕ) + 1 - prefixLength := by omega
      have hjlt : (k : ℕ) + 1 - prefixLength - 1 < bridgeLength := by omega
      let j : Fin bridgeLength := ⟨(k : ℕ) + 1 - prefixLength - 1, hjlt⟩
      have hjval : j.val + 1 = (k : ℕ) + 1 - prefixLength := by
        dsimp [j]
        omega
      have hbridgeAt := hbridgeTube j.succ
      have hdisp : AdditivePath.displacement (k + 1) increment =
          AdditivePath.displacement prefixLength increment +
            AdditivePath.blockSum prefixLength (j.val + 1) increment := by
        rw [hrem, AdditivePath.displacement_add_eq_add_blockSum]
        rw [hjval]
      have hbridgeAt' :
          (-1 - x) * scale < AdditivePath.blockSum prefixLength (j.val + 1) increment ∧
            AdditivePath.blockSum prefixLength (j.val + 1) increment < (1 - x) * scale := by
        have hsum := RandomWalk.partialSum_blockCoordinates prefixLength increment j.succ
        rw [hsum] at hbridgeAt
        simpa [hjval] using hbridgeAt
      have hprelo := hpreEnd'.1
      have hprehi := hpreEnd'.2
      have hblo : (-1 - x) * scale <
          AdditivePath.blockSum prefixLength (j.val + 1) increment := by
        exact hbridgeAt'.1
      have hbhi : AdditivePath.blockSum prefixLength (j.val + 1) increment <
          (1 - x) * scale := by
        exact hbridgeAt'.2
      have hpreloRaw : (x - radius) * scale <
          AdditivePath.displacement prefixLength increment :=
        (lt_div_iff₀ hscale).mp hprelo
      have hprehiRaw : AdditivePath.displacement prefixLength increment <
          (x + radius) * scale :=
        (div_lt_iff₀ hscale).mp hprehi
      rw [hdisp]
      constructor
      · nlinarith [hpreloRaw, hblo, h2rε]
      · nlinarith [hprehiRaw, hbhi, h2rε]
  have hendpoint : AdditivePath.displacement n increment / scale ∈ Set.Ioc c b := by
    have hsum : AdditivePath.displacement n increment =
        AdditivePath.displacement prefixLength increment +
          AdditivePath.blockSum prefixLength bridgeLength increment := by
      rw [← hpartition, AdditivePath.displacement_add_eq_add_blockSum]
    have hsumDiv : AdditivePath.displacement n increment / scale =
        AdditivePath.displacement prefixLength increment / scale +
          AdditivePath.blockSum prefixLength bridgeLength increment / scale := by
      rw [hsum, add_div]
    rw [hsumDiv]
    have hlo := hpreEnd'.1
    have hhi := hpreEnd'.2
    have hblo := hbridgeEnd'.1
    have hbhi := hbridgeEnd'.2
    constructor
    · nlinarith [hlo, hblo, h2rc]
    · nlinarith [hhi, hbhi, h2rb]
  constructor
  · intro k
    have hk := hpartial k
    change -(1 / 2 : ℝ) * (2 * (1 + ε) * scale) <
        AdditivePath.displacement (k + 1) increment ∧
      AdditivePath.displacement (k + 1) increment <
        (1 - (1 / 2 : ℝ)) * (2 * (1 + ε) * scale)
    constructor <;> nlinarith [hk.1, hk.2]
  · exact hendpoint


/-- A source-specific finite cover of unit-corridor prefix endpoints gives the
finite-cell geometry required in equation (34). -/
noncomputable def sourceFiniteBridgeGeometry_of_centerCover
    (F : Finset SourceBridgeCenter)
    (radius : ℝ)
    (hFcover : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      ∃ x ∈ F, z ∈ Set.Ioo (x.1 - radius) (x.1 + radius))
    (scale : ℕ → ℝ) (bridgeLength : ℕ → ℕ)
    (ε c b y : ℝ)
    (hscale : ∀ n, 0 < scale n)
    (hbridgeLe : ∀ n, bridgeLength n ≤ n)
    (hradius : 0 < radius)
    (h2rε : 2 * radius < ε)
    (h2rc : 2 * radius < y - c) (h2rb : 2 * radius < b - y) :
    SourceFiniteBridgeGeometry SourceBridgeCenter F
      (fun n => n - bridgeLength n) bridgeLength
      (fun n => sourceBaseCorridorEvent (scale n) n)
      (fun n => sourceEndpointCorridorEvent (scale n) ε c b n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n x => sourcePrefixCell (n - bridgeLength n) (scale n) radius x.1
  · exact fun n x => sourceBridgeCell (bridgeLength n) (scale n) radius x.1 y
  · intro n x hx
    exact measurableSet_sourcePrefixCell _ _ _ _
  · intro n x hx
    exact measurableSet_sourceBridgeCell _ _ _ _ _
  · intro n increment hincrement
    change InOpenHorizontalTube (1 / 2) (2 * scale n) n increment at hincrement
    let m := n - bridgeLength n
    have hmle : m ≤ n := Nat.sub_le _ _
    have hprefixTube : InOpenHorizontalTube (1 / 2) (2 * scale n) m increment := by
      intro k
      have hk := hincrement ⟨k, lt_of_lt_of_le k.isLt hmle⟩
      exact hk
    have hsumBounds : ∀ k : Fin m,
        -scale n < AdditivePath.displacement (k + 1) increment ∧
          AdditivePath.displacement (k + 1) increment < scale n := by
      intro k
      have hk := hprefixTube k
      change -(1 / 2 : ℝ) * (2 * scale n) < _ ∧
        _ < (1 - (1 / 2 : ℝ)) * (2 * scale n) at hk
      constructor <;> nlinarith
    have hprefixCorridor : InOpenPartialSumCorridor (-scale n) (scale n)
        (Combinatorics.Sequence.blockCoordinates 0 m increment) := by
      apply (source_openPartialSumCorridor_iff_nonempty
        (neg_neg_of_pos (hscale n)) (hscale n)
        (Combinatorics.Sequence.blockCoordinates 0 m increment)).2
      intro k
      have hk := hsumBounds k
      have hsum := RandomWalk.partialSum_blockCoordinates 0 increment k.succ
      have hsum' : Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates 0 m increment) k.succ =
          AdditivePath.displacement (k + 1) increment := by
        rw [hsum, AdditivePath.blockSum_eq_displacement_natAdd]
        simp
      rw [hsum']
      exact hk
    have hprefixEndpoint :
        Fin.partialSum (Combinatorics.Sequence.blockCoordinates 0 m increment)
          (Fin.last m) / scale n ∈ Set.Icc (-1) 1 := by
      have hlast : Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates 0 m increment) (Fin.last m) =
            AdditivePath.displacement m increment := by
        rw [RandomWalk.partialSum_blockCoordinates,
          AdditivePath.blockSum_eq_displacement_natAdd]
        simp
      rw [hlast]
      by_cases hm : m = 0
      · rw [hm]
        simp [AdditivePath.displacement]
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        have hlastBound : AdditivePath.displacement m increment ∈
            Set.Ioo (-scale n) (scale n) := by
          have hk := hsumBounds ⟨m - 1, by omega⟩
          have hindex : m - 1 + 1 = m := by omega
          rw [hindex] at hk
          exact hk
        constructor
        · have hlo : -1 < AdditivePath.displacement m increment / scale n :=
            (lt_div_iff₀ (hscale n)).2 (by nlinarith [hlastBound.1])
          exact hlo.le
        · have hhi : AdditivePath.displacement m increment / scale n < 1 :=
            (div_lt_iff₀ (hscale n)).2 (by nlinarith [hlastBound.2])
          exact hhi.le
    obtain ⟨x, hxF, hxbin⟩ := hFcover
      (Fin.partialSum
        (Combinatorics.Sequence.blockCoordinates 0 m increment) (Fin.last m) / scale n)
      hprefixEndpoint
    refine Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hxF, ?_⟩⟩
    change Combinatorics.Sequence.blockCoordinates 0 m increment ∈
      sourcePrefixCell m (scale n) radius x.1
    exact ⟨hprefixCorridor, hxbin⟩
  · intro n x hx increment hpair
    rcases hpair with ⟨hpre, hbridge⟩
    have hpartition : (n - bridgeLength n) + bridgeLength n = n :=
      Nat.sub_add_cancel (hbridgeLe n)
    exact sourceBridge_glue hpartition (hscale n) hradius h2rε h2rc h2rb
      increment hpre hbridge


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
