module

public import Algebra.Order.BigOperators.WeightedSum
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

/-!
# Compatibility names for finite-state weighted mass bounds

The general finite-sum estimates live in `Algebra.Order.BigOperators`.
This module retains the matrix names used by the frozen Mogulskii spectral
applications.
-/

@[expose] public section

namespace Matrix

section FiniteState

variable {ι : Type*}

/-- Compatibility name for
`Finset.weightedSum_bounds_of_sum_eq`. -/
@[deprecated Finset.weightedSum_bounds_of_sum_eq (since := "2026-10-03")]
theorem totalMass_bounds_of_weightedMass
    (s : Finset ι) (mass weight : ι → ℝ) (lower upper spectralMass : ℝ)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hlower : ∀ i ∈ s, lower ≤ weight i)
    (hupper : ∀ i ∈ s, weight i ≤ upper)
    (hweighted : ∑ i ∈ s, mass i * weight i = spectralMass) :
    lower * ∑ i ∈ s, mass i ≤ spectralMass ∧
      spectralMass ≤ upper * ∑ i ∈ s, mass i :=
  Finset.weightedSum_bounds_of_sum_eq s mass weight lower upper spectralMass
    hmass hlower hupper hweighted

/-- Compatibility name for `Finset.div_le_sum_of_weightedSum_eq`. -/
@[deprecated Finset.div_le_sum_of_weightedSum_eq (since := "2026-10-03")]
theorem div_le_totalMass_of_weightedMass
    (s : Finset ι) (mass weight : ι → ℝ) (upper spectralMass : ℝ)
    (hupper_pos : 0 < upper)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hweight : ∀ i ∈ s, weight i ≤ upper)
    (hweighted : ∑ i ∈ s, mass i * weight i = spectralMass) :
    spectralMass / upper ≤ ∑ i ∈ s, mass i :=
  Finset.div_le_sum_of_weightedSum_eq s mass weight upper spectralMass
    hupper_pos hmass hweight hweighted

/-- Compatibility name for `Finset.sum_le_div_of_weightedSum_eq`. -/
@[deprecated Finset.sum_le_div_of_weightedSum_eq (since := "2026-10-03")]
theorem totalMass_le_div_of_weightedMass
    (s : Finset ι) (mass weight : ι → ℝ) (lower spectralMass : ℝ)
    (hlower_pos : 0 < lower)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hweight : ∀ i ∈ s, lower ≤ weight i)
    (hweighted : ∑ i ∈ s, mass i * weight i = spectralMass) :
    (∑ i ∈ s, mass i) ≤ spectralMass / lower :=
  Finset.sum_le_div_of_weightedSum_eq s mass weight lower spectralMass
    hlower_pos hmass hweight hweighted

end FiniteState

end Matrix

end
