import Probability.BranchingRandomWalk.Walk.Law
import Probability.BranchingRandomWalk.Walk.Path.Window
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# Horizontal tube probabilities for random walks

The logarithm is `ENNReal.log : ENNReal → EReal`, so an impossible tube has
log-probability `-∞`, as required by small-deviation asymptotics.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

/-- The first `n` partial sums stay in the width-`width` interval whose lower
endpoint is `-a * width`. Time zero is omitted, matching the convention used
for horizontal-tube estimates. -/
def InHorizontalTube (a width : ℝ) (n : ℕ)
    (increment : ℕ → ℝ) : Prop :=
  ∀ k : Fin n,
    -a * width ≤ partialSum (k + 1) increment ∧
      partialSum (k + 1) increment ≤ (1 - a) * width

theorem measurableSet_inHorizontalTube (a width : ℝ) (n : ℕ) :
    MeasurableSet {increment : ℕ → ℝ |
      InHorizontalTube a width n increment} := by
  rw [show {increment : ℕ → ℝ | InHorizontalTube a width n increment} =
      ⋂ k : Fin n,
        {increment | -a * width ≤ partialSum (k + 1) increment} ∩
        {increment | partialSum (k + 1) increment ≤ (1 - a) * width} by
    ext increment
    simp [InHorizontalTube]]
  exact MeasurableSet.iInter fun k =>
    measurableSet_Ici.preimage (partialSum_measurable (k + 1)) |>.inter
      (measurableSet_Iic.preimage (partialSum_measurable (k + 1)))

/-- Probability of the horizontal-tube event under an increment-path law. -/
def horizontalTubeProbability (incrementLaw : Measure (ℕ → ℝ))
    (a width : ℝ) (n : ℕ) : ENNReal :=
  incrementLaw {increment | InHorizontalTube a width n increment}

/-- Extended-real log-probability of a horizontal tube. -/
noncomputable def horizontalTubeLogProbability
    (incrementLaw : Measure (ℕ → ℝ)) (a width : ℝ) (n : ℕ) : EReal :=
  ENNReal.log (horizontalTubeProbability incrementLaw a width n)

/-- Enlarging a horizontal tube increases its event. -/
theorem inHorizontalTube_mono_width
    {a width₁ width₂ : ℝ} {n : ℕ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hwidth : width₁ ≤ width₂) :
    {increment : ℕ → ℝ | InHorizontalTube a width₁ n increment} ⊆
      {increment | InHorizontalTube a width₂ n increment} := by
  intro increment hin k
  have hk := hin k
  constructor
  · nlinarith
  · nlinarith

/-- The horizontal-tube probability is monotone in its width. -/
theorem horizontalTubeProbability_mono_width
    (incrementLaw : Measure (ℕ → ℝ))
    {a width₁ width₂ : ℝ} {n : ℕ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hwidth : width₁ ≤ width₂) :
    horizontalTubeProbability incrementLaw a width₁ n ≤
      horizontalTubeProbability incrementLaw a width₂ n :=
  measure_mono (inHorizontalTube_mono_width ha0 ha1 hwidth)

/-- The thesis monotonicity lemma for `q(width,n)`, stated with the
extended-real logarithm so it remains valid when a tube has probability zero.
-/
theorem horizontalTubeLogProbability_mono_width
    (incrementLaw : Measure (ℕ → ℝ))
    {a width₁ width₂ : ℝ} {n : ℕ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hwidth : width₁ ≤ width₂) :
    horizontalTubeLogProbability incrementLaw a width₁ n ≤
      horizontalTubeLogProbability incrementLaw a width₂ n :=
  ENNReal.log_monotone
    (horizontalTubeProbability_mono_width incrementLaw ha0 ha1 hwidth)

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
