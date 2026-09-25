import ThesisSpeed.Probability.PointProcess.Enumeration.FirstAtom
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The normalized offspring spine law

The normalized law is defined on raw slot indices.  It is only introduced
when the total exponential weight is finite and nonzero; no survival or
ordered-support assumption is hidden in this definition.
-/

open MeasureTheory
open scoped ENNReal

namespace ThesisSpeed.Spine

noncomputable def tiltedOffspringPMF (ξ : OffspringMark)
    (hzero : totalChildWeight ξ ≠ 0)
    (hfinite : totalChildWeight ξ ≠ ∞) : PMF ℕ :=
  PMF.normalize (realizedChildWeight ξ) hzero hfinite

instance tiltedOffspringPMF_isProbability (ξ : OffspringMark)
    (hzero : totalChildWeight ξ ≠ 0)
    (hfinite : totalChildWeight ξ ≠ ∞) :
    IsProbabilityMeasure (tiltedOffspringPMF ξ hzero hfinite).toMeasure := by
  infer_instance

theorem tiltedOffspringPMF_apply (ξ : OffspringMark)
    (hzero : totalChildWeight ξ ≠ 0)
    (hfinite : totalChildWeight ξ ≠ ∞) (i : ℕ) :
    tiltedOffspringPMF ξ hzero hfinite i =
      realizedChildWeight ξ i * (totalChildWeight ξ)⁻¹ := by
  exact PMF.normalize_apply hzero hfinite i

theorem tiltedOffspringPMF_sum (ξ : OffspringMark)
    (hzero : totalChildWeight ξ ≠ 0)
    (hfinite : totalChildWeight ξ ≠ ∞) :
    ∑' i : ℕ, tiltedOffspringPMF ξ hzero hfinite i = 1 := by
  simpa using (tiltedOffspringPMF ξ hzero hfinite).tsum_coe

end ThesisSpeed.Spine
