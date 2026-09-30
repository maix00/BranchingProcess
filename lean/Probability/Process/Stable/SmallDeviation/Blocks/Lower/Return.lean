module

public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.Concatenation

/-!
# Corridor blocks returning to an interior core

The return condition keeps the observed endpoint away from the outer corridor
boundary. It is the nondegenerate form of the block lower recurrence used in
the original Mogulskii argument.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

theorem IsStableLevyProcess.measure_prefixCorridorReturn_succ_ge_mul
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks) (j : Fin blocks)
    (lower upper coreLower coreUpper : ℝ) (I : ι → Set ℝ)
    (binLower binUpper : ι → ℝ) (c : ENNReal)
    (hI : ∀ i, MeasurableSet (I i))
    (hdisj : Pairwise (fun i k => Disjoint (I i) (I k)))
    (hbin : ∀ i b, b ∈ I i → binLower i ≤ b ∧ b ≤ binUpper i)
    (hcover : ∀ ω ∈ rationalUniformPrefixCorridorReturnEvent X
      lower upper coreLower coreUpper hblocks j.val,
      ∃ i, rationalUniformPrefixPath X blocks j.val hblocks ω ⊤ ∈ I i)
    (hc : ∀ i, c ≤ P ((fun ω q =>
      rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹'
        rationalCoordinateCorridorReturn
          (lower - binLower i) (upper - binUpper i)
          (coreLower - binLower i) (coreUpper - binUpper i))) :
    c * P (rationalUniformPrefixCorridorReturnEvent X
        lower upper coreLower coreUpper hblocks j.val) ≤
      P (rationalUniformPrefixCorridorReturnEvent X
        lower upper coreLower coreUpper hblocks (j.val + 1)) := by
  let U : ι → Set (↑Skorokhod.RationalunitInterval → ℝ) :=
    fun i => (rationalUniformPrefixCorridorSet lower upper hblocks j.val ∩
      {x | x ⊤ ∈ Set.Ioo coreLower coreUpper}) ∩ {x | x ⊤ ∈ I i}
  let V : ι → Set (↑Skorokhod.RationalunitInterval → ℝ) :=
    fun i => rationalCoordinateCorridorReturn
      (lower - binLower i) (upper - binUpper i)
      (coreLower - binLower i) (coreUpper - binUpper i)
  have hU : ∀ i, MeasurableSet (U i) := by
    intro i
    exact ((measurableSet_rationalUniformPrefixCorridorSet lower upper hblocks j.val).inter
      (measurableSet_Ioo.preimage (measurable_pi_apply ⊤))).inter
      ((hI i).preimage (measurable_pi_apply ⊤))
  have hV : ∀ i, MeasurableSet (V i) := by
    intro i
    exact measurableSet_rationalCoordinateCorridorReturn _ _ _ _
  have hUdisj : Pairwise (fun i k => Disjoint (U i) (U k)) := by
    intro i k hik
    apply Set.disjoint_left.mpr
    intro x hxi hxk
    exact Set.disjoint_left.mp (hdisj hik) hxi.2 hxk.2
  have hunion :
      (⋃ i, rationalUniformPrefixPath X blocks j.val hblocks ⁻¹' U i) =
        rationalUniformPrefixCorridorReturnEvent X
          lower upper coreLower coreUpper hblocks j.val := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_preimage, U,
      rationalUniformPrefixCorridorReturnEvent,
      rationalUniformPrefixCorridorEvent_eq_preimage]
    constructor
    · rintro ⟨i, ⟨hprefix, hcore⟩, _⟩
      exact ⟨hprefix, hcore⟩
    · rintro ⟨hprefix, hcore⟩
      have hpast : ω ∈ rationalUniformPrefixCorridorReturnEvent X
          lower upper coreLower coreUpper hblocks j.val := by
        exact ⟨by rw [rationalUniformPrefixCorridorEvent_eq_preimage]; exact hprefix,
          hcore⟩
      obtain ⟨i, hi⟩ := hcover ω hpast
      exact ⟨i, ⟨hprefix, hcore⟩, hi⟩
  have hfactor := h.measure_prefixBin_nextBlock_ge_mul blocks hblocks j U V c
    hU hV hUdisj hc
  rw [hunion] at hfactor
  have hglue :
      (⋃ i, (rationalUniformPrefixPath X blocks j.val hblocks ⁻¹' U i) ∩
        ((fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹' V i)) ⊆
      rationalUniformPrefixCorridorReturnEvent X
        lower upper coreLower coreUpper hblocks (j.val + 1) := by
    intro ω hω
    obtain ⟨i, hprefix, hnext⟩ := Set.mem_iUnion.mp hω
    have hpast : ω ∈ rationalUniformPrefixCorridorEvent X lower upper hblocks j.val := by
      rw [rationalUniformPrefixCorridorEvent_eq_preimage]
      exact hprefix.1.1
    have hlimits := hbin i _ hprefix.2
    have hnew : ∀ q : ↑Skorokhod.RationalunitInterval,
        lower < X (rationalUniformBlockAbsoluteTime hblocks j q) ω - X 0 ω ∧
          X (rationalUniformBlockAbsoluteTime hblocks j q) ω - X 0 ω < upper := by
      apply rationalUniformBlockProcess_corridor_of_prefix_bin X hblocks j ω
        lower upper (binLower i) (binUpper i) hlimits.1 hlimits.2
      intro q
      have hq := Set.mem_iInter.mp hnext.1 q
      simpa [V, rationalCoordinateCorridor, rationalUniformBlockProcessFromTime,
        rationalTubeBlockIncrement, rationalUniformBlockAbsoluteTime] using hq
    have hreturn : rationalUniformPrefixPath X blocks (j.val + 1) hblocks ω ⊤ ∈
        Set.Ioo coreLower coreUpper := by
      have hend := hnext.2
      change coreLower - binLower i <
        rationalUniformBlockProcessFromTime X hblocks j ⊤ ω ∧
        rationalUniformBlockProcessFromTime X hblocks j ⊤ ω <
          coreUpper - binUpper i at hend
      rw [rationalUniformPrefixPath_top_succ X hblocks j ω]
      change coreLower < _ ∧ _ < coreUpper
      have hblockEq : rationalTubeBlockIncrement hblocks j
          (fun t => X (rationalUnitTime t) ω) ⊤ =
          rationalUniformBlockProcessFromTime X hblocks j ⊤ ω := rfl
      rw [hblockEq]
      constructor <;> linarith
    change ω ∈ rationalUniformPrefixCorridorEvent X lower upper hblocks (j.val + 1) ∩
      {ω | rationalUniformPrefixPath X blocks (j.val + 1) hblocks ω ⊤ ∈
        Set.Ioo coreLower coreUpper}
    rw [rationalUniformPrefixCorridorEvent_succ X lower upper hblocks j]
    exact ⟨⟨hpast, fun q => hnew q⟩, hreturn⟩
  exact hfactor.trans (measure_mono hglue)

/-- Iterating the core-return block estimate yields a positive-power lower
bound whenever the one-block probabilities have a uniform lower bound. -/
theorem IsStableLevyProcess.pow_le_measure_prefixCorridorReturn_of_steps
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (_h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks)
    (lower upper coreLower coreUpper : ℝ)
    (hcore : coreLower < 0 ∧ 0 < coreUpper) (c : ENNReal)
    (hstep : ∀ j : Fin blocks,
      c * P (rationalUniformPrefixCorridorReturnEvent X
          lower upper coreLower coreUpper hblocks j.val) ≤
        P (rationalUniformPrefixCorridorReturnEvent X
          lower upper coreLower coreUpper hblocks (j.val + 1))) :
    c ^ blocks ≤ P (rationalUniformPrefixCorridorReturnEvent X
      lower upper coreLower coreUpper hblocks blocks) := by
  have hiter : ∀ m : ℕ, m ≤ blocks →
      c ^ m ≤ P (rationalUniformPrefixCorridorReturnEvent X
        lower upper coreLower coreUpper hblocks m) := by
    intro m
    induction m with
    | zero =>
        intro _
        simp [rationalUniformPrefixCorridorReturnEvent_zero X
          lower upper coreLower coreUpper hblocks hcore]
    | succ m ih =>
        intro hm
        have hmlt : m < blocks := by omega
        calc
          c ^ (m + 1) = c * c ^ m := by rw [pow_succ]; ring
          _ ≤ c * P (rationalUniformPrefixCorridorReturnEvent X
              lower upper coreLower coreUpper hblocks m) := by
                simpa only [mul_comm c] using mul_le_mul_left (ih (by omega)) c
          _ ≤ P (rationalUniformPrefixCorridorReturnEvent X
              lower upper coreLower coreUpper hblocks (m + 1)) :=
            hstep ⟨m, hmlt⟩
  exact hiter blocks le_rfl

/-- The finite-bin version of the full core-return block lower bound. -/
theorem IsStableLevyProcess.pow_le_measure_prefixCorridorReturn_of_bins
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks)
    (lower upper coreLower coreUpper : ℝ)
    (hcore : coreLower < 0 ∧ 0 < coreUpper)
    (I : Fin blocks → ι → Set ℝ)
    (binLower binUpper : Fin blocks → ι → ℝ) (c : ENNReal)
    (hI : ∀ j i, MeasurableSet (I j i))
    (hdisj : ∀ j, Pairwise (fun i k => Disjoint (I j i) (I j k)))
    (hbin : ∀ j i b, b ∈ I j i → binLower j i ≤ b ∧ b ≤ binUpper j i)
    (hcover : ∀ j ω,
      ω ∈ rationalUniformPrefixCorridorReturnEvent X
        lower upper coreLower coreUpper hblocks j.val →
      ∃ i, rationalUniformPrefixPath X blocks j.val hblocks ω ⊤ ∈ I j i)
    (hc : ∀ j i, c ≤ P ((fun ω q =>
      rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹'
        rationalCoordinateCorridorReturn
          (lower - binLower j i) (upper - binUpper j i)
          (coreLower - binLower j i) (coreUpper - binUpper j i))) :
    c ^ blocks ≤ P (rationalUniformPrefixCorridorReturnEvent X
      lower upper coreLower coreUpper hblocks blocks) := by
  apply h.pow_le_measure_prefixCorridorReturn_of_steps blocks hblocks
    lower upper coreLower coreUpper hcore c
  intro j
  exact h.measure_prefixCorridorReturn_succ_ge_mul blocks hblocks j
    lower upper coreLower coreUpper (I j) (binLower j) (binUpper j) c
    (hI j) (hdisj j) (hbin j) (hcover j) (hc j)

end ProbabilityTheory
