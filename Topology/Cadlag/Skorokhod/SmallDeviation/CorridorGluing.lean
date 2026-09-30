module

public import Topology.Cadlag.Skorokhod.SmallDeviation.PathSets

/-!
# Gluing a shifted corridor after an endpoint window

The endpoint window of the first segment determines how far the second
segment's increment corridor must be shifted. This is a pathwise inclusion;
no independence or process law enters here.
-/

@[expose] public section

namespace Skorokhod

/-- If the first segment stays in a corridor and ends in a narrower window,
then a translated corridor for the remaining increments keeps the whole path
inside the original corridor. -/
theorem corridor_of_initial_and_translated_remainder
    (f : CadlagPath unitInterval ℝ) (cut : unitInterval)
    (lower upper endpointLower endpointUpper : ℝ)
    (hfirst : ∀ t, t ≤ cut → lower < f t ∧ f t < upper)
    (hend : endpointLower < f cut ∧ f cut < endpointUpper)
    (hsecond : ∀ t, cut ≤ t →
      lower - endpointLower < f t - f cut ∧
        f t - f cut < upper - endpointUpper) :
    ∀ t, lower < f t ∧ f t < upper := by
  intro t
  rcases le_total t cut with htc | hct
  · exact hfirst t htc
  · have hstep := hsecond t hct
    constructor <;> linarith

end Skorokhod

end
