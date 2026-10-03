module

public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Prefix
public import Topology.Cadlag.Skorokhod.Corridor.Dense
public import Order.Bounds.Feedback
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Cover

/-!
# Adaptive conditions on a finite uniform path partition

The event is defined directly on a complete rational-coordinate path. Its
conditions on each block depend on the endpoint of the preceding prefix.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The sign of the endpoint error is read from the stopped past path. -/
def feedbackPrefixNonnegative (target : ℝ) :
    Set (↑RationalGrid.RationalUnitInterval → ℝ) :=
  {f | 0 ≤ f ⊤ - target}

theorem measurableSet_feedbackPrefixNonnegative (target : ℝ) :
    MeasurableSet (feedbackPrefixNonnegative target) := by
  exact measurableSet_Ici.preimage
    ((measurable_pi_apply ⊤).sub measurable_const)

/-- A complete-block corridor, expressed on rational coordinates, together
with an open window for its terminal correction relative to the drift. -/
def feedbackCorrectionSet (δ d lower upper : ℝ) :
    Set (↑RationalGrid.RationalUnitInterval → ℝ) :=
  Skorokhod.rationalCoordinateCorridorWithMargin (-δ) δ ∩
    {f | f ⊤ - d ∈ Set.Ioo lower upper}

theorem measurableSet_feedbackCorrectionSet (δ d lower upper : ℝ) :
    MeasurableSet (feedbackCorrectionSet δ d lower upper) := by
  exact (Skorokhod.measurableSet_rationalCoordinateCorridorWithMargin
    (-δ) δ).inter
      (measurableSet_Ioo.preimage
        ((measurable_pi_apply ⊤).sub measurable_const))

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

/-- A successful rational path keeps every uniform-block endpoint within
the prescribed error radius around the linear target. -/
theorem rationalFeedback_endpoint_bound
    {blocks : ℕ} (hblocks : 0 < blocks)
    (f : ↑RationalGrid.RationalUnitInterval → ℝ)
    (hf0 : f ⊥ = 0) (v δ r R : ℝ)
    (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hsuccess : f ∈ rationalFeedbackPrefixSet hblocks blocks
      (fun j => v * (j.val : ℝ) / (blocks : ℝ))
      (feedbackCorrectionSet δ (v / (blocks : ℝ)) r R)
      (feedbackCorrectionSet δ (v / (blocks : ℝ)) (-R) (-r))) :
    ∀ k ≤ blocks,
      |f (rationalUniformBlockBoundaryTime hblocks k) -
        v * (k : ℝ) / (blocks : ℝ)| ≤ R := by
  let e : ℕ → ℝ := fun k =>
    f (rationalUniformBlockBoundaryTime hblocks k) -
      v * (k : ℝ) / (blocks : ℝ)
  have he0 : e 0 = 0 := by simp [e, hf0]
  have hstep (k : ℕ) (hk : k < blocks) :
      (0 ≤ e k → -R ≤ e (k + 1) - e k ∧
          e (k + 1) - e k ≤ -r) ∧
      (e k < 0 → r ≤ e (k + 1) - e k ∧
          e (k + 1) - e k ≤ R) := by
    let j : Fin blocks := ⟨k, hk⟩
    have hj := Set.mem_iInter.mp hsuccess j
    have hblock : f ∈ rationalFeedbackBlockSet hblocks j
        (v * (j.val : ℝ) / (blocks : ℝ))
        (feedbackCorrectionSet δ (v / (blocks : ℝ)) r R)
        (feedbackCorrectionSet δ (v / (blocks : ℝ)) (-R) (-r)) := by
      simpa [rationalFeedbackPrefixSet, hk] using hj
    have hdiff : e (k + 1) - e k =
        rationalTubeBlockIncrement hblocks j f ⊤ -
          v / (blocks : ℝ) := by
      dsimp [e, rationalTubeBlockIncrement]
      rw [rationalUniformBlockBoundaryTime_eq_blockStart hblocks j,
        rationalUniformBlockBoundaryTime_succ_eq_blockEnd hblocks j]
      push_cast
      ring
    have hsign : e k = f (rationalUniformBlockTime hblocks j ⊥) -
        v * (j.val : ℝ) / (blocks : ℝ) := by
      change f (rationalUniformBlockBoundaryTime hblocks k) -
          v * (k : ℝ) / (blocks : ℝ) = _
      rw [rationalUniformBlockBoundaryTime_eq_blockStart hblocks j]
    simp only [rationalFeedbackBlockSet, Set.mem_ofPred_eq,
      feedbackCorrectionSet, Set.mem_inter_iff, Set.mem_ofPred_eq] at hblock
    constructor
    · intro he
      rcases hblock with hneg | hpos
      · rw [hdiff]
        exact ⟨hneg.2.2.1.le, hneg.2.2.2.le⟩
      · have : ¬ e k < 0 := not_lt.mpr he
        exact False.elim (this (by simpa [hsign] using hpos.1))
    · intro he
      rcases hblock with hneg | hpos
      · have : ¬ 0 ≤ e k := not_le.mpr he
        exact False.elim (this (by simpa [hsign] using hneg.1))
      · rw [hdiff]
        exact ⟨hpos.2.2.1.le, hpos.2.2.2.le⟩
  intro k hk
  exact Real.feedback_endpoint_error_bound e blocks r R hR hr he0 hstep k hk

/-- Every rational-time coordinate of a successful feedback path lies in a
fixed tube around the target line. -/
theorem rationalFeedback_coordinate_bound
    {blocks : ℕ} (hblocks : 0 < blocks)
    (f : ↑RationalGrid.RationalUnitInterval → ℝ)
    (hf0 : f ⊥ = 0) (v δ r R : ℝ)
    (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hsuccess : f ∈ rationalFeedbackPrefixSet hblocks blocks
      (fun j => v * (j.val : ℝ) / (blocks : ℝ))
      (feedbackCorrectionSet δ (v / (blocks : ℝ)) r R)
      (feedbackCorrectionSet δ (v / (blocks : ℝ)) (-R) (-r)))
    (q : ↑RationalGrid.RationalUnitInterval) :
    |f q - v * (q : ℝ)| ≤ R + δ + |v / (blocks : ℝ)| := by
  obtain ⟨j, s, hjs⟩ := exists_rationalUniformBlockTime hblocks q
  have hend := rationalFeedback_endpoint_bound hblocks f hf0 v δ r R
    hr hR hsuccess j.val j.isLt.le
  have hstart :
      |f (rationalUniformBlockTime hblocks j ⊥) -
        v * (j.val : ℝ) / (blocks : ℝ)| ≤ R := by
    simpa [rationalUniformBlockBoundaryTime_eq_blockStart hblocks j] using hend
  have hj := Set.mem_iInter.mp hsuccess j
  have hblock : f ∈ rationalFeedbackBlockSet hblocks j
      (v * (j.val : ℝ) / (blocks : ℝ))
      (feedbackCorrectionSet δ (v / (blocks : ℝ)) r R)
      (feedbackCorrectionSet δ (v / (blocks : ℝ)) (-R) (-r)) := by
    simpa [rationalFeedbackPrefixSet, j.isLt] using hj
  have hcorr : rationalTubeBlockIncrement hblocks j f ∈
      Skorokhod.rationalCoordinateCorridorWithMargin (-δ) δ := by
    rcases hblock with hneg | hpos
    · exact hneg.2.1
    · exact hpos.2.1
  obtain ⟨margin, hmargin, hpath⟩ := hcorr
  have hs := hpath s
  have hblockBound :
      |f (rationalUniformBlockTime hblocks j s) -
          f (rationalUniformBlockTime hblocks j ⊥)| ≤ δ := by
    change -δ + (margin : ℝ) ≤
        f (rationalUniformBlockTime hblocks j s) -
          f (rationalUniformBlockTime hblocks j ⊥) ∧
        f (rationalUniformBlockTime hblocks j s) -
          f (rationalUniformBlockTime hblocks j ⊥) ≤
          δ - (margin : ℝ) at hs
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hstime : |(s : ℝ)| ≤ 1 := by
    have hs0 : 0 ≤ (s : ℝ) := by exact_mod_cast s.property.1
    rw [abs_of_nonneg hs0]
    exact_mod_cast s.property.2
  have hdrift : |v / (blocks : ℝ) * (s : ℝ)| ≤
      |v / (blocks : ℝ)| := by
    rw [abs_mul]
    nlinarith [abs_nonneg (v / (blocks : ℝ))]
  have htime : v * (q : ℝ) =
      v * (j.val : ℝ) / (blocks : ℝ) +
        v / (blocks : ℝ) * (s : ℝ) := by
    have hjsQ : ((j.val : ℚ) + (s : ℚ)) / (blocks : ℚ) =
        (q : ℚ) := congrArg Subtype.val hjs
    have hjsR : ((j.val : ℝ) + (s : ℝ)) / (blocks : ℝ) =
        (q : ℝ) := by exact_mod_cast hjsQ
    rw [← hjsR]
    ring
  rw [htime, ← hjs]
  exact Real.feedback_within_block_bound
    (f (rationalUniformBlockTime hblocks j ⊥))
    (f (rationalUniformBlockTime hblocks j s))
    (v * (j.val : ℝ) / (blocks : ℝ))
    (v / (blocks : ℝ) * (s : ℝ)) R δ
    (v / (blocks : ℝ)) hstart hblockBound hdrift

end ProbabilityTheory

end
