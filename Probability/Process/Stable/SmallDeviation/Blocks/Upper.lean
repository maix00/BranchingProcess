module

public import Probability.Process.Stable.SmallDeviation.Blocks.Factorization
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Probability

/-!
# Uniform-block upper bound for stable processes

The prefix factorization gives the full finite product. Equal translated-block
laws then turn the product into the power in the Mogulskii upper estimate.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The first `m` tube events factor into the probabilities of individual
blocks. This is proved from stopped-prefix independence, not assumed as a
finite-family independence hypothesis. -/
theorem IsStableLevyProcess.measure_rationalPrefixTube_eq_prod
    {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (blocks : ℕ) (hblocks : 0 < blocks)
    (width : ℝ) (m : ℕ) (hm : m ≤ blocks) :
    P (rationalUniformPrefixTubeEvent X width hblocks m) =
      ∏ k ∈ Finset.range m,
        rationalUniformBlockTubeProbability P X width hblocks k := by
  induction m with
  | zero =>
      simp [measure_univ]
  | succ m ih =>
      have hmlt : m < blocks := by omega
      rw [rationalUniformPrefixTubeEvent_succ X width hblocks m hmlt]
      rw [h.measure_prefixTube_inter_nextBlock blocks hblocks ⟨m, hmlt⟩ width]
      rw [ih (by omega)]
      simp [Finset.prod_range_succ, rationalUniformBlockTubeProbability, hmlt]

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
    _ = ∏ k ∈ Finset.range blocks,
        rationalUniformBlockTubeProbability P X width hblocks k :=
      h.measure_rationalPrefixTube_eq_prod blocks hblocks width blocks le_rfl
    _ = (P (rationalUniformBlockTubeEvent X width hblocks ⟨0, hblocks⟩)) ^ blocks := by
      have hterm : ∀ k ∈ Finset.range blocks,
          rationalUniformBlockTubeProbability P X width hblocks k =
            P (rationalUniformBlockTubeEvent X width hblocks ⟨0, hblocks⟩) := by
        intro k hk
        have hklt : k < blocks := Finset.mem_range.mp hk
        simp only [rationalUniformBlockTubeProbability, dite_eq_left hklt]
        have hlaw := h.rationalUniformBlockProcess_identDistrib blocks hblocks
          ⟨k, hklt⟩ ⟨0, hblocks⟩
        exact hlaw.measure_preimage_eq
          (Skorokhod.measurableSet_rationalCoordinateOscillationTube width)
      rw [Finset.prod_congr rfl hterm]
      simp

/-- Rational-coordinate counterpart of Lemma 2(c), equation (23): a full
unit-time range tube is bounded by a power of the short-block tube. The
paper's statement is on càdlàg path sets and uses `X(0,c) J₁`; that bridge
is separate. -/
theorem IsStableLevyProcess.measure_rationalHorizonTube_le_pow_shortHorizon
    {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (blocks : ℕ) (hblocks : 0 < blocks)
    (width : ℝ) :
    P (rationalHorizonTubeEvent X 1 width) ≤
      (P (rationalHorizonTubeEvent X
        (rationalUniformBlockBoundary blocks 1 hblocks) width)) ^ blocks := by
  have hone : rationalHorizonTubeEvent X 1 width =
      (fun ω q => X (rationalUnitTime q) ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width := by
    ext ω
    change (fun q => X (1 * rationalUnitTime q) ω) ∈
      Skorokhod.rationalCoordinateOscillationTube width ↔
      (fun q => X (rationalUnitTime q) ω) ∈
        Skorokhod.rationalCoordinateOscillationTube width
    simp
  rw [hone, ← rationalUniformBlockTubeEvent_zero_eq_horizon X width hblocks]
  exact h.measure_rationalTube_le_pow_uniformBlocks blocks hblocks width

end ProbabilityTheory
