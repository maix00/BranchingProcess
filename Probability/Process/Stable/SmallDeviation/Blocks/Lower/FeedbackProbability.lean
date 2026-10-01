module

public import Probability.Process.Stable.SmallDeviation.Blocks.Factorization
public import Probability.Independence.Feedback
public import Topology.Cadlag.Skorokhod.Corridor.Dense

/-!
# Feedback choice for the next stable-process block

A condition on the complete stopped prefix path may select either of two
conditions on the next complete block path. The resulting probability bound
does not assume that the selected event itself is independent of the past.
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

theorem IsStableLevyProcess.measure_feedbackNextBlock_ge_mul
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks) (j : Fin blocks)
    (U S Vplus Vminus : Set (↑RationalGrid.RationalUnitInterval → ℝ))
    (hU : MeasurableSet U) (hS : MeasurableSet S)
    (hVplus : MeasurableSet Vplus) (hVminus : MeasurableSet Vminus)
    (q : ENNReal)
    (hqplus : q ≤ P ((fun ω q =>
      rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹' Vplus))
    (hqminus : q ≤ P ((fun ω q =>
      rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹' Vminus)) :
    q * P (rationalUniformPrefixPath X blocks j.val hblocks ⁻¹' U) ≤
      P (((rationalUniformPrefixPath X blocks j.val hblocks ⁻¹' (U ∩ S)) ∩
        ((fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹'
          Vminus)) ∪
        ((rationalUniformPrefixPath X blocks j.val hblocks ⁻¹' (U ∩ Sᶜ)) ∩
        ((fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹'
          Vplus))) := by
  let past := rationalUniformPrefixPath X blocks j.val hblocks
  let next : Ω → ↑RationalGrid.RationalUnitInterval → ℝ :=
    fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω
  have hpast : AEMeasurable past P := by
    rw [aemeasurable_pi_iff]
    intro q
    change AEMeasurable (fun ω =>
      X (min (rationalUnitTime q)
        (rationalUniformBlockBoundary blocks j.val hblocks)) ω - X 0 ω) P
    exact (h.increments.aemeasurable_eval _).sub
      (h.increments.aemeasurable_eval 0)
  have hnext : AEMeasurable next P := by
    rw [aemeasurable_pi_iff]
    intro q
    change AEMeasurable (fun ω =>
      X (rationalUniformBlockAbsoluteTime hblocks j q) ω -
        X (rationalUniformBlockAbsoluteTime hblocks j ⊥) ω) P
    exact (h.increments.aemeasurable_eval _).sub
      (h.increments.aemeasurable_eval _)
  exact measure_adaptiveChoice_ge_mul P past next
    (h.indepFun_rationalPrefix_nextBlock blocks hblocks j)
    hpast hnext U S Vplus Vminus hU hS hVplus hVminus q hqplus hqminus

/-- The measurable sign rule chooses a negative correction when the endpoint
is nonnegative and a positive correction otherwise. This gives the exact
one-step lower bound used by the finite feedback induction. -/
theorem IsStableLevyProcess.measure_signedFeedbackNextBlock_ge_mul
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks) (j : Fin blocks)
    (U : Set (↑RationalGrid.RationalUnitInterval → ℝ))
    (hU : MeasurableSet U) (target δ d r R : ℝ)
    (q : ENNReal)
    (hqplus : q ≤ P ((fun ω q =>
      rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹'
        feedbackCorrectionSet δ d r R))
    (hqminus : q ≤ P ((fun ω q =>
      rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹'
        feedbackCorrectionSet δ d (-R) (-r))) :
    q * P (rationalUniformPrefixPath X blocks j.val hblocks ⁻¹' U) ≤
      P (((rationalUniformPrefixPath X blocks j.val hblocks ⁻¹'
        (U ∩ feedbackPrefixNonnegative target)) ∩
        ((fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹'
          feedbackCorrectionSet δ d (-R) (-r))) ∪
        ((rationalUniformPrefixPath X blocks j.val hblocks ⁻¹'
          (U ∩ (feedbackPrefixNonnegative target)ᶜ)) ∩
        ((fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹'
          feedbackCorrectionSet δ d r R))) := by
  exact h.measure_feedbackNextBlock_ge_mul blocks hblocks j U
    (feedbackPrefixNonnegative target)
    (feedbackCorrectionSet δ d r R)
    (feedbackCorrectionSet δ d (-R) (-r))
    hU (measurableSet_feedbackPrefixNonnegative target)
    (measurableSet_feedbackCorrectionSet δ d r R)
    (measurableSet_feedbackCorrectionSet δ d (-R) (-r))
    q hqplus hqminus

end ProbabilityTheory

end
