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

/-- A strict corridor on the initial segment of a complete path. -/
def prefixCorridor (cut : unitInterval) (lower upper : ℝ) :
    Set (CadlagPath unitInterval ℝ) :=
  {f | ∃ margin > 0, ∀ t, t ≤ cut →
    lower + margin ≤ f t ∧ f t ≤ upper - margin}

/-- A strict corridor for increments measured from the cut time. -/
def translatedRemainderCorridor (cut : unitInterval) (lower upper : ℝ) :
    Set (CadlagPath unitInterval ℝ) :=
  {f | ∃ margin > 0, ∀ t, cut ≤ t →
    lower + margin ≤ f t - f cut ∧
      f t - f cut ≤ upper - margin}

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

/-- Complete-path form of the shifted-corridor inclusion used in a
two-segment gluing argument. All three input events constrain the original
càdlàg path, and the conclusion is the original full-path corridor event. -/
theorem prefix_endpoint_remainder_subset_corridor
    (cut : unitInterval) (lower upper endpointLower endpointUpper : ℝ) :
    prefixCorridor cut lower upper ∩
        {f : CadlagPath unitInterval ℝ |
          f cut ∈ Set.Ioo endpointLower endpointUpper} ∩
        translatedRemainderCorridor cut
          (lower - endpointLower) (upper - endpointUpper) ⊆
      rangeInOpenInterval lower upper := by
  intro f hf
  rcases hf with ⟨⟨hprefix, hend⟩, hrem⟩
  rcases hprefix with ⟨margin₁, hmargin₁, hfirst⟩
  rcases hrem with ⟨margin₂, hmargin₂, hsecond⟩
  let margin := min margin₁ (min margin₂
    (min (f cut - endpointLower) (endpointUpper - f cut)))
  have hmargin : 0 < margin := by
    dsimp [margin]
    exact lt_min hmargin₁ (lt_min hmargin₂
      (lt_min (sub_pos.mpr hend.1) (sub_pos.mpr hend.2)))
  refine ⟨margin, hmargin, ?_⟩
  intro t
  rcases le_total t cut with htc | hct
  · have ht := hfirst t htc
    have hm : margin ≤ margin₁ := by
      dsimp [margin]
      exact min_le_left _ _
    constructor <;> linarith
  · have ht := hsecond t hct
    have hmLow : margin ≤ f cut - endpointLower := by
      dsimp [margin]
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _))
    have hmUp : margin ≤ endpointUpper - f cut := by
      dsimp [margin]
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _))
    constructor <;> linarith

end Skorokhod

end
