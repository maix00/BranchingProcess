module

public import Probability.Process.Stable.SmallDeviation.Blocks.Factorization

/-!
# Uniform-block upper bound for stable processes

The prefix factorization gives the full finite product. Equal translated-block
laws then turn the product into the power in the Mogulskii upper estimate.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

private theorem prefixTubeEvent_succ {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (width : ℝ) {blocks : ℕ} (hblocks : 0 < blocks)
    (m : ℕ) (hm : m < blocks) :
    rationalUniformPrefixTubeEvent X width hblocks (m + 1) =
      rationalUniformPrefixTubeEvent X width hblocks m ∩
        rationalUniformBlockTubeEvent X width hblocks ⟨m, hm⟩ := by
  ext ω
  simp only [rationalUniformPrefixTubeEvent, Set.mem_iInter, Set.mem_inter_iff]
  constructor
  · intro h
    constructor
    · intro k
      by_cases hk : k.val < m
      · have hk' : k.val < m + 1 := by omega
        simpa [hk, hk'] using h k
      · simp [hk]
    · have h' := h ⟨m, hm⟩
      simpa using h'
  · rintro ⟨hp, hmEvent⟩ k
    by_cases hk : k.val < m
    · simpa [hk, Nat.lt_succ_of_lt hk] using hp k
    · by_cases hkm : k.val = m
      · have heq : k = ⟨m, hm⟩ := Fin.ext hkm
        simpa [hkm, heq] using hmEvent
      · have hnot : ¬ k.val < m + 1 := by omega
        simp [hnot]

private theorem prefixTubeEvent_zero {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (width : ℝ) {blocks : ℕ} (hblocks : 0 < blocks) :
    rationalUniformPrefixTubeEvent X width hblocks 0 = Set.univ := by
  simp [rationalUniformPrefixTubeEvent]

def blockTubeProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (width : ℝ) {blocks : ℕ} (hblocks : 0 < blocks) (m : ℕ) : ENNReal :=
  if hm : m < blocks then
    P (rationalUniformBlockTubeEvent X width hblocks ⟨m, hm⟩)
  else 1

/-- The first `m` tube events factor into the probabilities of individual
blocks. This is proved from stopped-prefix independence, not assumed as a
finite-family independence hypothesis. -/
theorem IsStableLevyProcess.measure_rationalPrefixTube_eq_prod
    {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (blocks : ℕ) (hblocks : 0 < blocks)
    (width : ℝ) (m : ℕ) (hm : m ≤ blocks) :
    P (rationalUniformPrefixTubeEvent X width hblocks m) =
      ∏ k ∈ Finset.range m, blockTubeProbability P X width hblocks k := by
  induction m with
  | zero =>
      simp [prefixTubeEvent_zero, measure_univ]
  | succ m ih =>
      have hmlt : m < blocks := by omega
      rw [prefixTubeEvent_succ X width hblocks m hmlt]
      rw [h.measure_prefixTube_inter_nextBlock blocks hblocks ⟨m, hmlt⟩ width]
      rw [ih (by omega)]
      simp [Finset.prod_range_succ, blockTubeProbability, hmlt]

/-- The original stable-process block upper inequality follows directly from
independent increments and equality of translated-block laws. -/
theorem IsStableLevyProcess.measure_rationalTube_le_pow_uniformBlocks
    {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (blocks : ℕ) (hblocks : 0 < blocks)
    (width : ℝ) :
    P ((fun ω q => X (rationalUnitTime q) ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width) ≤
      (P (rationalUniformBlockTubeEvent X width hblocks ⟨0, hblocks⟩)) ^ blocks := by
  have hsubset :
      (fun ω q => X (rationalUnitTime q) ω) ⁻¹'
          Skorokhod.rationalCoordinateOscillationTube width ⊆
        rationalUniformPrefixTubeEvent X width hblocks blocks := by
    intro ω hω
    have hpath : ∀ k : Fin blocks,
        (fun q => X (rationalUnitTime q) ω) ∈
          rationalTubeBlockEvent width hblocks k := by
      exact Set.mem_iInter.mp
        (rationalCoordinateOscillationTube_subset_iInter_uniformBlockEvents
          width hblocks hω)
    simp only [rationalUniformPrefixTubeEvent, Set.mem_iInter]
    intro k
    have hk : k.val < blocks := k.isLt
    have hblock := hpath k
    simp only [hk, ↓reduceIte, rationalUniformBlockTubeEvent, Set.mem_preimage]
    change rationalTubeBlockIncrement hblocks k
      (fun q => X (rationalUnitTime q) ω) ∈
        Skorokhod.rationalCoordinateOscillationTube width at hblock
    convert hblock using 1
    funext q
    rfl
  calc
    P ((fun ω q => X (rationalUnitTime q) ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width) ≤
        P (rationalUniformPrefixTubeEvent X width hblocks blocks) := measure_mono hsubset
    _ = ∏ k ∈ Finset.range blocks, blockTubeProbability P X width hblocks k :=
      h.measure_rationalPrefixTube_eq_prod blocks hblocks width blocks le_rfl
    _ = (P (rationalUniformBlockTubeEvent X width hblocks ⟨0, hblocks⟩)) ^ blocks := by
      have hterm : ∀ k ∈ Finset.range blocks,
          blockTubeProbability P X width hblocks k =
            P (rationalUniformBlockTubeEvent X width hblocks ⟨0, hblocks⟩) := by
        intro k hk
        have hklt : k < blocks := Finset.mem_range.mp hk
        simp only [blockTubeProbability, dif_pos hklt]
        have hlaw := h.rationalUniformBlockProcess_identDistrib blocks hblocks
          ⟨k, hklt⟩ ⟨0, hblocks⟩
        exact hlaw.measure_preimage_eq
          (Skorokhod.measurableSet_rationalCoordinateOscillationTube width)
      rw [Finset.prod_congr rfl hterm]
      simp

end ProbabilityTheory
