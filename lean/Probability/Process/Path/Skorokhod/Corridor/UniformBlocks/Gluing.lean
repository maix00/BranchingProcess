module

public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Prefix

/-!
# Gluing a block into a spatial corridor

A block increment is added to the displacement at the block's left endpoint.
Endpoint bins allow one fixed next-block corridor to work for every prefix
whose endpoint lies in the same bin.
-/

@[expose] public section

namespace ProbabilityTheory

open scoped NNReal

/-- A spatial corridor for a path on rational unit time. -/
def rationalCoordinateCorridor (lower upper : ℝ) :
    Set (↑Skorokhod.RationalunitInterval → ℝ) :=
  ⋂ q : ↑Skorokhod.RationalunitInterval,
    {x | x q ∈ Set.Ioo lower upper}

theorem measurableSet_rationalCoordinateCorridor (lower upper : ℝ) :
    MeasurableSet (rationalCoordinateCorridor lower upper) := by
  unfold rationalCoordinateCorridor
  apply MeasurableSet.iInter
  intro q
  exact measurableSet_Ioo.preimage (measurable_pi_apply q)

/-- A block corridor together with a return window for its endpoint. -/
def rationalCoordinateCorridorReturn
    (lower upper coreLower coreUpper : ℝ) :
    Set (↑Skorokhod.RationalunitInterval → ℝ) :=
  rationalCoordinateCorridor lower upper ∩
    {x | x ⊤ ∈ Set.Ioo coreLower coreUpper}

theorem measurableSet_rationalCoordinateCorridorReturn
    (lower upper coreLower coreUpper : ℝ) :
    MeasurableSet
      (rationalCoordinateCorridorReturn lower upper coreLower coreUpper) := by
  exact (measurableSet_rationalCoordinateCorridor lower upper).inter
    (measurableSet_Ioo.preimage (measurable_pi_apply ⊤))

/-- A spatial corridor imposed on the first `m` uniform blocks of a rational
coordinate path. The path is already normalized relative to its initial
position. -/
def rationalUniformPrefixCorridorSet (lower upper : ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) (m : ℕ) :
    Set (↑Skorokhod.RationalunitInterval → ℝ) :=
  ⋂ k : Fin blocks,
    if k.val < m then
      ⋂ q : ↑Skorokhod.RationalunitInterval,
        {x | x (rationalUniformBlockTime hblocks k q) ∈ Set.Ioo lower upper}
    else Set.univ

theorem measurableSet_rationalUniformPrefixCorridorSet
    (lower upper : ℝ) {blocks : ℕ} (hblocks : 0 < blocks) (m : ℕ) :
    MeasurableSet (rationalUniformPrefixCorridorSet lower upper hblocks m) := by
  unfold rationalUniformPrefixCorridorSet
  apply MeasurableSet.iInter
  intro k
  split_ifs
  · apply MeasurableSet.iInter
    intro q
    exact measurableSet_Ioo.preimage (measurable_pi_apply _)
  · exact MeasurableSet.univ

/-- At every time of an earlier block, the stopped prefix path agrees with
the original path relative to its initial position. -/
theorem rationalUniformPrefixPath_blockValue_eq
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) (m : ℕ) (k : Fin blocks)
    (hkm : k.val < m) (q : ↑Skorokhod.RationalunitInterval) (ω : Ω) :
    rationalUniformPrefixPath X blocks m hblocks ω
        (rationalUniformBlockTime hblocks k q) =
      X (rationalUniformBlockAbsoluteTime hblocks k q) ω - X 0 ω := by
  have hq := rationalUniformBlockAbsoluteTime_le_boundary hblocks k m hkm q
  change rationalUnitTime (rationalUniformBlockTime hblocks k q) ≤ _ at hq
  simp only [rationalUniformPrefixPath, rationalUniformBlockAbsoluteTime,
    min_eq_left hq]

/-- The event that all positions in the first `m` blocks stay in a spatial
corridor, relative to the initial position. -/
def rationalUniformPrefixCorridorEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (lower upper : ℝ) {blocks : ℕ} (hblocks : 0 < blocks) (m : ℕ) : Set Ω :=
  ⋂ k : Fin blocks,
    if k.val < m then
      ⋂ q : ↑Skorokhod.RationalunitInterval,
        {ω | X (rationalUniformBlockAbsoluteTime hblocks k q) ω - X 0 ω ∈
          Set.Ioo lower upper}
    else Set.univ

/-- A blockwise corridor event with its current endpoint in an interior
return window. -/
def rationalUniformPrefixCorridorReturnEvent {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (lower upper coreLower coreUpper : ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) (m : ℕ) : Set Ω :=
  rationalUniformPrefixCorridorEvent X lower upper hblocks m ∩
    {ω | rationalUniformPrefixPath X blocks m hblocks ω ⊤ ∈
      Set.Ioo coreLower coreUpper}

@[simp]
theorem rationalUniformPrefixCorridorReturnEvent_zero
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (lower upper coreLower coreUpper : ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks)
    (hcore : coreLower < 0 ∧ 0 < coreUpper) :
    rationalUniformPrefixCorridorReturnEvent X
      lower upper coreLower coreUpper hblocks 0 = Set.univ := by
  have hboundary0 : rationalUniformBlockBoundary blocks 0 hblocks = 0 := by
    apply NNReal.coe_injective
    simp [rationalUniformBlockBoundary]
    rfl
  unfold rationalUniformPrefixCorridorReturnEvent
  rw [show rationalUniformPrefixCorridorEvent X lower upper hblocks 0 = Set.univ by
    simp [rationalUniformPrefixCorridorEvent]]
  ext ω
  have hpath0 : rationalUniformPrefixPath X blocks 0 hblocks ω ⊤ = 0 := by
    rw [rationalUniformPrefixPath_top X hblocks 0 (Nat.zero_le _) ω,
      hboundary0]
    ring
  simp [hpath0, hcore]

@[simp]
theorem rationalUniformPrefixCorridorEvent_zero
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (lower upper : ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) :
    rationalUniformPrefixCorridorEvent X lower upper hblocks 0 = Set.univ := by
  simp [rationalUniformPrefixCorridorEvent]

/-- The blockwise corridor is determined by the stopped prefix path. -/
theorem rationalUniformPrefixCorridorEvent_eq_preimage
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (lower upper : ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) (m : ℕ) :
    rationalUniformPrefixCorridorEvent X lower upper hblocks m =
      rationalUniformPrefixPath X blocks m hblocks ⁻¹'
        rationalUniformPrefixCorridorSet lower upper hblocks m := by
  ext ω
  simp only [rationalUniformPrefixCorridorEvent,
    rationalUniformPrefixCorridorSet, Set.mem_iInter, Set.mem_preimage]
  apply forall_congr'
  intro k
  by_cases hk : k.val < m
  · simp only [hk, ↓reduceIte, Set.mem_iInter, Set.mem_ofPred_eq]
    apply forall_congr'
    intro q
    rw [rationalUniformPrefixPath_blockValue_eq X hblocks m k hk q ω]
  · simp [hk]

/-- One more block is added to a prefix corridor exactly when every point of
that block is also in the corridor. -/
theorem rationalUniformPrefixCorridorEvent_succ
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (lower upper : ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) (j : Fin blocks) :
    rationalUniformPrefixCorridorEvent X lower upper hblocks (j.val + 1) =
      rationalUniformPrefixCorridorEvent X lower upper hblocks j.val ∩
        {ω | ∀ q : ↑Skorokhod.RationalunitInterval,
          X (rationalUniformBlockAbsoluteTime hblocks j q) ω - X 0 ω ∈
            Set.Ioo lower upper} := by
  ext ω
  simp only [rationalUniformPrefixCorridorEvent, Set.mem_iInter,
    Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · intro h
    constructor
    · intro k
      by_cases hk : k.val < j.val
      · have hk' : k.val < j.val + 1 := by omega
        simpa [hk, hk'] using h k
      · simp [hk]
    · have hj := h j
      simpa using hj
  · rintro ⟨hp, hj⟩ k
    by_cases hk : k.val < j.val
    · have hk' : k.val < j.val + 1 := by omega
      simpa [hk, hk'] using hp k
    · by_cases hkj : k = j
      · simpa [hkj] using hj
      · have hnot : ¬ k.val < j.val + 1 := by
          have : k.val ≠ j.val := fun heq => hkj (Fin.ext heq)
          omega
        simp [hnot]

/-- The global displacement at a block time is its left-endpoint displacement
plus the translated block increment. -/
theorem rationalUniformBlock_displacement_eq_endpoint_add_increment
    {blocks : ℕ} (hblocks : 0 < blocks) (j : Fin blocks)
    (x : ↑Skorokhod.RationalunitInterval → ℝ)
    (q : ↑Skorokhod.RationalunitInterval) :
    x (rationalUniformBlockTime hblocks j q) - x ⊥ =
      (x (rationalUniformBlockTime hblocks j ⊥) - x ⊥) +
        rationalTubeBlockIncrement hblocks j x q := by
  unfold rationalTubeBlockIncrement
  ring

/-- The endpoint of the stopped prefix is exactly the displacement at the
left endpoint of the next block. -/
theorem rationalUniformPrefixPath_top_eq_blockStart
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) (j : Fin blocks) (ω : Ω) :
    rationalUniformPrefixPath X blocks j.val hblocks ω ⊤ =
      X (rationalUniformBlockAbsoluteTime hblocks j ⊥) ω - X 0 ω := by
  rw [rationalUniformPrefixPath_top X hblocks j.val j.isLt.le ω,
    rationalUniformBlockBoundary_eq_start hblocks j]

/-- The new endpoint equals the old endpoint plus the translated increment
at the end of the next block. -/
theorem rationalUniformPrefixPath_top_succ
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) (j : Fin blocks) (ω : Ω) :
    rationalUniformPrefixPath X blocks (j.val + 1) hblocks ω ⊤ =
      rationalUniformPrefixPath X blocks j.val hblocks ω ⊤ +
        rationalTubeBlockIncrement hblocks j
          (fun t => X (rationalUnitTime t) ω) ⊤ := by
  rw [rationalUniformPrefixPath_top X hblocks (j.val + 1)
      (Nat.succ_le_of_lt j.isLt) ω,
    rationalUniformBlockBoundary_succ_eq_end hblocks j,
    rationalUniformPrefixPath_top_eq_blockStart X hblocks j ω]
  simp only [rationalTubeBlockIncrement, rationalUniformBlockAbsoluteTime]
  ring

/-- A spatial bin for the old endpoint and a translated corridor for the new
block imply that every point of the new block remains in the global corridor.
The bin may depend on the previously observed path. -/
theorem rationalUniformBlock_corridor_of_endpoint_bin
    {blocks : ℕ} (hblocks : 0 < blocks) (j : Fin blocks)
    (x : ↑Skorokhod.RationalunitInterval → ℝ)
    (lower upper binLower binUpper : ℝ)
    (hleft : binLower ≤ x (rationalUniformBlockTime hblocks j ⊥) - x ⊥)
    (hright : x (rationalUniformBlockTime hblocks j ⊥) - x ⊥ ≤ binUpper)
    (hblock : ∀ q : ↑Skorokhod.RationalunitInterval,
      lower - binLower < rationalTubeBlockIncrement hblocks j x q ∧
        rationalTubeBlockIncrement hblocks j x q < upper - binUpper) :
    ∀ q : ↑Skorokhod.RationalunitInterval,
      lower < x (rationalUniformBlockTime hblocks j q) - x ⊥ ∧
        x (rationalUniformBlockTime hblocks j q) - x ⊥ < upper := by
  intro q
  rw [rationalUniformBlock_displacement_eq_endpoint_add_increment]
  obtain ⟨hlo, hhi⟩ := hblock q
  constructor <;> linarith

/-- The process form of corridor gluing: an observed prefix endpoint chooses
a bin, and one translated block corridor ensures every new position stays
inside the global corridor. -/
theorem rationalUniformBlockProcess_corridor_of_prefix_bin
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) (j : Fin blocks) (ω : Ω)
    (lower upper binLower binUpper : ℝ)
    (hleft : binLower ≤ rationalUniformPrefixPath X blocks j.val hblocks ω ⊤)
    (hright : rationalUniformPrefixPath X blocks j.val hblocks ω ⊤ ≤ binUpper)
    (hblock : ∀ q : ↑Skorokhod.RationalunitInterval,
      lower - binLower <
        rationalTubeBlockIncrement hblocks j (fun t => X (rationalUnitTime t) ω) q ∧
      rationalTubeBlockIncrement hblocks j (fun t => X (rationalUnitTime t) ω) q <
        upper - binUpper) :
    ∀ q : ↑Skorokhod.RationalunitInterval,
      lower < X (rationalUniformBlockAbsoluteTime hblocks j q) ω - X 0 ω ∧
        X (rationalUniformBlockAbsoluteTime hblocks j q) ω - X 0 ω < upper := by
  have hstart : (fun t => X (rationalUnitTime t) ω)
      (rationalUniformBlockTime hblocks j ⊥) -
        (fun t => X (rationalUnitTime t) ω) ⊥ =
      rationalUniformPrefixPath X blocks j.val hblocks ω ⊤ := by
    rw [rationalUniformPrefixPath_top_eq_blockStart X hblocks j ω]
    simp [rationalUniformBlockAbsoluteTime, rationalUnitTime_bot]
  have hglue := rationalUniformBlock_corridor_of_endpoint_bin hblocks j
    (fun t => X (rationalUnitTime t) ω) lower upper binLower binUpper
    (hstart ▸ hleft) (hstart ▸ hright) hblock
  intro q
  simpa [rationalUniformBlockAbsoluteTime, rationalUnitTime_bot] using hglue q

end ProbabilityTheory
