module

public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.Binning
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Gluing

/-!
# One-block lower corridor recurrence

Finite endpoint bins, independence of the next translated block, and the
deterministic corridor-gluing inequality combine into a lower recurrence for
the probability that all visited blocks stay in a fixed spatial corridor.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

theorem IsStableLevyProcess.measure_prefixCorridor_succ_ge_mul
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks) (j : Fin blocks)
    (lower upper : ℝ) (I : ι → Set ℝ)
    (binLower binUpper : ι → ℝ) (c : ENNReal)
    (hI : ∀ i, MeasurableSet (I i))
    (hdisj : Pairwise (fun i k => Disjoint (I i) (I k)))
    (hbin : ∀ i b, b ∈ I i → binLower i ≤ b ∧ b ≤ binUpper i)
    (hcover : ∀ ω ∈ rationalUniformPrefixCorridorEvent X lower upper hblocks j.val,
      ∃ i, rationalUniformPrefixPath X blocks j.val hblocks ω ⊤ ∈ I i)
    (hc : ∀ i, c ≤ P ((fun ω q =>
      rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹'
        rationalCoordinateCorridor (lower - binLower i) (upper - binUpper i))) :
    c * P (rationalUniformPrefixCorridorEvent X lower upper hblocks j.val) ≤
      P (rationalUniformPrefixCorridorEvent X lower upper hblocks (j.val + 1)) := by
  let U : ι → Set (↑Skorokhod.RationalunitInterval → ℝ) :=
    fun i => rationalUniformPrefixCorridorSet lower upper hblocks j.val ∩
      {x | x ⊤ ∈ I i}
  let V : ι → Set (↑Skorokhod.RationalunitInterval → ℝ) :=
    fun i => rationalCoordinateCorridor (lower - binLower i) (upper - binUpper i)
  have hU : ∀ i, MeasurableSet (U i) := by
    intro i
    exact (measurableSet_rationalUniformPrefixCorridorSet lower upper hblocks j.val).inter
      ((hI i).preimage (measurable_pi_apply ⊤))
  have hV : ∀ i, MeasurableSet (V i) := by
    intro i
    exact measurableSet_rationalCoordinateCorridor _ _
  have hUdisj : Pairwise (fun i k => Disjoint (U i) (U k)) := by
    intro i k hik
    apply Set.disjoint_left.mpr
    intro x hxi hxk
    exact Set.disjoint_left.mp (hdisj hik) hxi.2 hxk.2
  have hunion :
      (⋃ i, rationalUniformPrefixPath X blocks j.val hblocks ⁻¹' U i) =
        rationalUniformPrefixCorridorEvent X lower upper hblocks j.val := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_preimage, U,
      rationalUniformPrefixCorridorEvent_eq_preimage]
    constructor
    · rintro ⟨i, hprefix, _⟩
      exact hprefix
    · intro hprefix
      have hprefixEvent :
          ω ∈ rationalUniformPrefixCorridorEvent X lower upper hblocks j.val := by
        rw [rationalUniformPrefixCorridorEvent_eq_preimage]
        exact hprefix
      obtain ⟨i, hi⟩ := hcover ω hprefixEvent
      exact ⟨i, hprefix, hi⟩
  have hfactor := h.measure_prefixBin_nextBlock_ge_mul blocks hblocks j U V c
    hU hV hUdisj hc
  rw [hunion] at hfactor
  have hglue :
      (⋃ i, (rationalUniformPrefixPath X blocks j.val hblocks ⁻¹' U i) ∩
        ((fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹' V i)) ⊆
      rationalUniformPrefixCorridorEvent X lower upper hblocks (j.val + 1) := by
    intro ω hω
    obtain ⟨i, hprefix, hnext⟩ := Set.mem_iUnion.mp hω
    have hpast : ω ∈ rationalUniformPrefixCorridorEvent X lower upper hblocks j.val := by
      rw [rationalUniformPrefixCorridorEvent_eq_preimage]
      exact hprefix.1
    have hlimits := hbin i _ hprefix.2
    have hnew : ∀ q : ↑Skorokhod.RationalunitInterval,
        lower < X (rationalUniformBlockAbsoluteTime hblocks j q) ω - X 0 ω ∧
          X (rationalUniformBlockAbsoluteTime hblocks j q) ω - X 0 ω < upper := by
      apply rationalUniformBlockProcess_corridor_of_prefix_bin X hblocks j ω
        lower upper (binLower i) (binUpper i) hlimits.1 hlimits.2
      intro q
      have hq := Set.mem_iInter.mp hnext q
      simpa [V, rationalCoordinateCorridor, rationalTubeBlockIncrement,
        rationalUniformBlockProcessFromTime, rationalUniformBlockAbsoluteTime]
        using hq
    rw [rationalUniformPrefixCorridorEvent_succ X lower upper hblocks j]
    exact ⟨hpast, fun q => hnew q⟩
  exact hfactor.trans (measure_mono hglue)

/-- Repeating the one-block corridor lower estimate gives a full finite-block
power lower bound. This isolates the original proof's remaining analytic task:
construct bins with a useful uniform next-block probability. -/
theorem IsStableLevyProcess.pow_le_measure_prefixCorridor_of_steps
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (_h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks)
    (lower upper : ℝ) (c : ENNReal)
    (hstep : ∀ j : Fin blocks,
      c * P (rationalUniformPrefixCorridorEvent X lower upper hblocks j.val) ≤
        P (rationalUniformPrefixCorridorEvent X lower upper hblocks (j.val + 1))) :
    c ^ blocks ≤
      P (rationalUniformPrefixCorridorEvent X lower upper hblocks blocks) := by
  have hiter : ∀ m : ℕ, m ≤ blocks →
      c ^ m ≤ P (rationalUniformPrefixCorridorEvent X lower upper hblocks m) := by
    intro m
    induction m with
    | zero =>
        intro _
        simp
    | succ m ih =>
        intro hm
        have hmlt : m < blocks := by omega
        calc
          c ^ (m + 1) = c * c ^ m := by rw [pow_succ]; ring
          _ ≤ c * P (rationalUniformPrefixCorridorEvent X lower upper hblocks m) :=
            by simpa only [mul_comm c] using mul_le_mul_left (ih (by omega)) c
          _ ≤ P (rationalUniformPrefixCorridorEvent X lower upper hblocks (m + 1)) :=
            hstep ⟨m, hmlt⟩
  exact hiter blocks le_rfl

/-- Uniformly usable finite endpoint bins yield a finite-block corridor lower
bound. The assumptions are local to each block and permit different bins at
different generations. -/
theorem IsStableLevyProcess.pow_le_measure_prefixCorridor_of_bins
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks) (lower upper : ℝ)
    (I : Fin blocks → ι → Set ℝ)
    (binLower binUpper : Fin blocks → ι → ℝ) (c : ENNReal)
    (hI : ∀ j i, MeasurableSet (I j i))
    (hdisj : ∀ j, Pairwise (fun i k => Disjoint (I j i) (I j k)))
    (hbin : ∀ j i b, b ∈ I j i → binLower j i ≤ b ∧ b ≤ binUpper j i)
    (hcover : ∀ j ω,
      ω ∈ rationalUniformPrefixCorridorEvent X lower upper hblocks j.val →
      ∃ i, rationalUniformPrefixPath X blocks j.val hblocks ω ⊤ ∈ I j i)
    (hc : ∀ j i, c ≤ P ((fun ω q =>
      rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹'
        rationalCoordinateCorridor
          (lower - binLower j i) (upper - binUpper j i))) :
    c ^ blocks ≤
      P (rationalUniformPrefixCorridorEvent X lower upper hblocks blocks) := by
  apply h.pow_le_measure_prefixCorridor_of_steps blocks hblocks lower upper c
  intro j
  exact h.measure_prefixCorridor_succ_ge_mul blocks hblocks j lower upper
    (I j) (binLower j) (binUpper j) c (hI j) (hdisj j) (hbin j)
    (hcover j) (hc j)

end ProbabilityTheory
