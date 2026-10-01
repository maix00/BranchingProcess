module

public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Prefix

/-!
# Adaptive conditions on a finite uniform path partition

The event is defined directly on a complete rational-coordinate path. Its
conditions on each block depend on the endpoint of the preceding prefix.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The pathwise condition for one sign-selected block. -/
def rationalFeedbackBlockSet {blocks : ℕ} (hblocks : 0 < blocks)
    (j : Fin blocks) (target : ℝ)
    (Vplus Vminus : Set (↑RationalGrid.RationalUnitInterval → ℝ)) :
    Set (↑RationalGrid.RationalUnitInterval → ℝ) :=
  {f | (0 ≤ f (rationalUniformBlockTime hblocks j ⊥) - target ∧
      rationalTubeBlockIncrement hblocks j f ∈ Vminus) ∨
    (f (rationalUniformBlockTime hblocks j ⊥) - target < 0 ∧
      rationalTubeBlockIncrement hblocks j f ∈ Vplus)}

theorem measurableSet_rationalFeedbackBlockSet {blocks : ℕ}
    (hblocks : 0 < blocks) (j : Fin blocks) (target : ℝ)
    {Vplus Vminus : Set (↑RationalGrid.RationalUnitInterval → ℝ)}
    (hplus : MeasurableSet Vplus) (hminus : MeasurableSet Vminus) :
    MeasurableSet (rationalFeedbackBlockSet hblocks j target Vplus Vminus) := by
  have heval : Measurable (fun f : ↑RationalGrid.RationalUnitInterval → ℝ =>
      f (rationalUniformBlockTime hblocks j ⊥) - target) :=
    (measurable_pi_apply _).sub measurable_const
  have hblock := measurable_rationalTubeBlockIncrement hblocks j
  exact (measurableSet_Ici.preimage heval).inter
      (hminus.preimage hblock) |>.union
        ((measurableSet_Iio.preimage heval).inter
          (hplus.preimage hblock))

/-- All sign-selected conditions on the first `m` blocks. -/
def rationalFeedbackPrefixSet {blocks : ℕ} (hblocks : 0 < blocks)
    (m : ℕ) (target : Fin blocks → ℝ)
    (Vplus Vminus : Set (↑RationalGrid.RationalUnitInterval → ℝ)) :
    Set (↑RationalGrid.RationalUnitInterval → ℝ) :=
  ⋂ j : Fin blocks,
    if j.val < m then
      rationalFeedbackBlockSet hblocks j (target j) Vplus Vminus
    else Set.univ

theorem measurableSet_rationalFeedbackPrefixSet {blocks : ℕ}
    (hblocks : 0 < blocks) (m : ℕ) (target : Fin blocks → ℝ)
    {Vplus Vminus : Set (↑RationalGrid.RationalUnitInterval → ℝ)}
    (hplus : MeasurableSet Vplus) (hminus : MeasurableSet Vminus) :
    MeasurableSet (rationalFeedbackPrefixSet hblocks m target Vplus Vminus) := by
  unfold rationalFeedbackPrefixSet
  apply MeasurableSet.iInter
  intro j
  split_ifs
  · exact measurableSet_rationalFeedbackBlockSet hblocks j (target j) hplus hminus
  · exact MeasurableSet.univ

@[simp] theorem rationalFeedbackPrefixSet_zero {blocks : ℕ}
    (hblocks : 0 < blocks) (target : Fin blocks → ℝ)
    (Vplus Vminus : Set (↑RationalGrid.RationalUnitInterval → ℝ)) :
    rationalFeedbackPrefixSet hblocks 0 target Vplus Vminus = Set.univ := by
  simp [rationalFeedbackPrefixSet]

theorem rationalFeedbackPrefixSet_succ {blocks : ℕ}
    (hblocks : 0 < blocks) (m : ℕ) (hm : m < blocks)
    (target : Fin blocks → ℝ)
    (Vplus Vminus : Set (↑RationalGrid.RationalUnitInterval → ℝ)) :
    rationalFeedbackPrefixSet hblocks (m + 1) target Vplus Vminus =
      rationalFeedbackPrefixSet hblocks m target Vplus Vminus ∩
        rationalFeedbackBlockSet hblocks ⟨m, hm⟩
          (target ⟨m, hm⟩) Vplus Vminus := by
  ext f
  simp only [rationalFeedbackPrefixSet, Set.mem_iInter, Set.mem_inter_iff]
  constructor
  · intro h
    constructor
    · intro j
      by_cases hj : j.val < m
      · have hj' : j.val < m + 1 := by omega
        simpa [hj, hj'] using h j
      · simp [hj]
    · have h' := h ⟨m, hm⟩
      simpa using h'
  · rintro ⟨hp, hblock⟩ j
    by_cases hj : j.val < m
    · simpa [hj, Nat.lt_succ_of_lt hj] using hp j
    · by_cases hjeq : j.val = m
      · have heq : j = ⟨m, hm⟩ := Fin.ext hjeq
        simpa [hjeq, heq] using hblock
      · have hnot : ¬ j.val < m + 1 := by omega
        simp [hnot]

/-- The stopped prefix retains the starting position of each earlier block. -/
theorem rationalUniformPrefixPath_blockStart_eq
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) (m : ℕ)
    (k : Fin blocks) (hk : k.val < m) (ω : Ω) :
    rationalUniformPrefixPath X blocks m hblocks ω
        (rationalUniformBlockTime hblocks k ⊥) =
      X (rationalUniformBlockAbsoluteTime hblocks k ⊥) ω - X 0 ω := by
  have htime := rationalUniformBlockAbsoluteTime_le_boundary
    hblocks k m hk ⊥
  change X (min (rationalUniformBlockAbsoluteTime hblocks k ⊥)
      (rationalUniformBlockBoundary blocks m hblocks)) ω - X 0 ω = _
  rw [min_eq_left htime]

/-- Whether an earlier block succeeds is unchanged by stopping the path at
the end of a later prefix. -/
theorem mem_rationalFeedbackBlockSet_prefix_iff
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) (m : ℕ)
    (k : Fin blocks) (hk : k.val < m) (ω : Ω)
    (target : ℝ)
    (Vplus Vminus : Set (↑RationalGrid.RationalUnitInterval → ℝ)) :
    rationalUniformPrefixPath X blocks m hblocks ω ∈
        rationalFeedbackBlockSet hblocks k target Vplus Vminus ↔
      (fun q => X (rationalUnitTime q) ω - X 0 ω) ∈
        rationalFeedbackBlockSet hblocks k target Vplus Vminus := by
  have hstart := rationalUniformPrefixPath_blockStart_eq X hblocks m k hk ω
  have hblock := rationalUniformPrefixPath_blockIncrement_eq
    X hblocks m k hk ω
  have hraw : rationalTubeBlockIncrement hblocks k
        (fun q => X (rationalUnitTime q) ω - X 0 ω) =
      fun q => rationalUniformBlockProcessFromTime X hblocks k q ω := by
    funext q
    simp only [rationalTubeBlockIncrement, rationalUniformBlockProcessFromTime,
      rationalUniformBlockAbsoluteTime]
    ring
  simp only [rationalFeedbackBlockSet, Set.mem_ofPred_eq]
  rw [hstart, hblock, hraw]
  rfl

/-- The prefix success event is completely determined by the stopped past
path; no future coordinate is inspected. -/
theorem mem_rationalFeedbackPrefixSet_prefix_iff
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) (m : ℕ)
    (ω : Ω) (target : Fin blocks → ℝ)
    (Vplus Vminus : Set (↑RationalGrid.RationalUnitInterval → ℝ)) :
    rationalUniformPrefixPath X blocks m hblocks ω ∈
        rationalFeedbackPrefixSet hblocks m target Vplus Vminus ↔
      (fun q => X (rationalUnitTime q) ω - X 0 ω) ∈
        rationalFeedbackPrefixSet hblocks m target Vplus Vminus := by
  simp only [rationalFeedbackPrefixSet, Set.mem_iInter]
  apply forall_congr'
  intro k
  by_cases hk : k.val < m
  · simpa [hk] using mem_rationalFeedbackBlockSet_prefix_iff
      X hblocks m k hk ω (target k) Vplus Vminus
  · simp [hk]

/-- Adding a sign-selected fresh block extends the success event by one
block. This is a deterministic statement about path restriction. -/
theorem rationalFeedbackPrefixSet_step
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) (j : Fin blocks)
    (ω : Ω) (target : Fin blocks → ℝ)
    (Vplus Vminus : Set (↑RationalGrid.RationalUnitInterval → ℝ))
    (hpast : rationalUniformPrefixPath X blocks j.val hblocks ω ∈
      rationalFeedbackPrefixSet hblocks j.val target Vplus Vminus)
    (hnext :
      (0 ≤ rationalUniformPrefixPath X blocks j.val hblocks ω ⊤ - target j ∧
        (fun q => rationalUniformBlockProcessFromTime X hblocks j q ω) ∈ Vminus) ∨
      (rationalUniformPrefixPath X blocks j.val hblocks ω ⊤ - target j < 0 ∧
        (fun q => rationalUniformBlockProcessFromTime X hblocks j q ω) ∈ Vplus)) :
    rationalUniformPrefixPath X blocks (j.val + 1) hblocks ω ∈
      rationalFeedbackPrefixSet hblocks (j.val + 1) target Vplus Vminus := by
  let Y : ↑RationalGrid.RationalUnitInterval → ℝ :=
    fun q => X (rationalUnitTime q) ω - X 0 ω
  have hYpast : Y ∈ rationalFeedbackPrefixSet hblocks j.val target
      Vplus Vminus :=
    (mem_rationalFeedbackPrefixSet_prefix_iff X hblocks j.val ω
      target Vplus Vminus).mp hpast
  have hstart : rationalUniformPrefixPath X blocks j.val hblocks ω ⊤ =
      Y (rationalUniformBlockTime hblocks j ⊥) := by
    rw [rationalUniformPrefixPath_top X hblocks j.val j.isLt.le ω,
      rationalUniformBlockBoundary_eq_start hblocks j]
    rfl
  have hblock : rationalTubeBlockIncrement hblocks j Y =
      fun q => rationalUniformBlockProcessFromTime X hblocks j q ω := by
    funext q
    simp only [Y, rationalTubeBlockIncrement,
      rationalUniformBlockProcessFromTime,
      rationalUniformBlockAbsoluteTime]
    ring
  have hYnext : Y ∈ rationalFeedbackBlockSet hblocks j
      (target j) Vplus Vminus := by
    simp only [rationalFeedbackBlockSet, Set.mem_ofPred_eq]
    rw [← hstart, hblock]
    exact hnext
  have hYsucc : Y ∈ rationalFeedbackPrefixSet hblocks (j.val + 1)
      target Vplus Vminus := by
    rw [rationalFeedbackPrefixSet_succ hblocks j.val j.isLt]
    exact ⟨hYpast, hYnext⟩
  exact (mem_rationalFeedbackPrefixSet_prefix_iff X hblocks
    (j.val + 1) ω target Vplus Vminus).mpr hYsucc

end ProbabilityTheory

end
