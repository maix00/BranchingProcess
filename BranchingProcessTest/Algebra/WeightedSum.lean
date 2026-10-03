import Algebra.Order.BigOperators.WeightedSum
import LinearAlgebra.Spectrum.FiniteState.WeightedMass

open scoped BigOperators

#check Finset.weightedSum_bounds_of_sum_eq
#check Finset.div_le_sum_of_weightedSum_eq
#check Finset.sum_le_div_of_weightedSum_eq

example {ι : Type*} (s : Finset ι) (mass weight : ι → ℝ)
    (lower upper weighted : ℝ)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hlower : ∀ i ∈ s, lower ≤ weight i)
    (hupper : ∀ i ∈ s, weight i ≤ upper)
    (hweighted : ∑ i ∈ s, mass i * weight i = weighted) :
    lower * ∑ i ∈ s, mass i ≤ weighted ∧
      weighted ≤ upper * ∑ i ∈ s, mass i :=
  Finset.weightedSum_bounds_of_sum_eq s mass weight lower upper weighted
    hmass hlower hupper hweighted

example {ι : Type*} (s : Finset ι) (mass weight : ι → ℝ)
    (lower upper weighted : ℝ)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hlower : ∀ i ∈ s, lower ≤ weight i)
    (hupper : ∀ i ∈ s, weight i ≤ upper)
    (hweighted : ∑ i ∈ s, mass i * weight i = weighted) :
    lower * ∑ i ∈ s, mass i ≤ weighted ∧
      weighted ≤ upper * ∑ i ∈ s, mass i :=
  Matrix.totalMass_bounds_of_weightedMass s mass weight lower upper weighted
    hmass hlower hupper hweighted
