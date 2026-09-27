import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Order.Preorder.Finite
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Local finiteness from summable positive atom weights

The corresponding normalization makes the total exponential weight finite almost
surely.  Before sorting a countable point process, we need the deterministic
fact that only finitely many atoms can carry weight above any positive
threshold.  This file states that fact without choosing an enumeration or a
probability law.
-/

open Filter
open scoped Topology BigOperators ENNReal NNReal

namespace MeasureTheory

/-- A finite sum of nonnegative extended-real atom weights has only finitely
many atoms above a positive threshold. -/
theorem finite_large_atoms {ι : Type*} (weight : ι → ENNReal)
    (hsum : (∑' i, weight i) ≠ ∞) (c : ENNReal) (hc : 0 < c) :
    {i | c ≤ weight i}.Finite := by
  have hzero : Tendsto weight (cofinite : Filter ι) (𝓝 0) :=
    ENNReal.tendsto_cofinite_zero_of_tsum_ne_top hsum
  have hsmall : ∀ᶠ i in (cofinite : Filter ι), weight i < c :=
    hzero.eventually (Iio_mem_nhds hc)
  simpa only [eventually_cofinite, not_lt] using hsmall

/-- Any family of atoms whose weights are uniformly bounded below by a
positive amount is finite. -/
theorem finite_atoms_of_weight_lower_bound {ι : Type*}
    (weight : ι → ENNReal) (hsum : (∑' i, weight i) ≠ ∞)
    (s : Set ι) (c : ENNReal) (hc : 0 < c)
    (hbound : ∀ i ∈ s, c ≤ weight i) : s.Finite :=
  (finite_large_atoms weight hsum c hc).subset hbound

/-- Finite total exponential weight forces left-local finiteness of a
countably indexed branching-step point process, with multiplicities retained by
the labels. -/
theorem finite_displacements_below {ι : Type*} (displacement : ι → ℝ)
    (hsum : (∑' i, ENNReal.ofReal (Real.exp (-displacement i))) ≠ ∞)
    (R : ℝ) :
    {i | displacement i ≤ R}.Finite := by
  apply finite_atoms_of_weight_lower_bound
    (fun i => ENNReal.ofReal (Real.exp (-displacement i)))
    hsum _ (ENNReal.ofReal (Real.exp (-R)))
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  intro i hi
  apply ENNReal.ofReal_le_ofReal
  exact Real.exp_le_exp.mpr (neg_le_neg hi)

/-- Any nonempty labelled point family with finite sublevel sets has a
leftmost atom. This also covers infinite child sets with tied positions. -/
theorem exists_leftmost_of_finite_sublevels {ι : Type*} [Nonempty ι]
    (displacement : ι → ℝ)
    (hfinite : ∀ R : ℝ, {i | displacement i ≤ R}.Finite) :
    ∃ j : ι, ∀ i : ι, displacement j ≤ displacement i := by
  let i₀ : ι := Classical.choice inferInstance
  let s : Set ι := {i | displacement i ≤ displacement i₀}
  obtain ⟨j, hj⟩ :=
    (hfinite (displacement i₀)).exists_minimalFor displacement s
      ⟨i₀, by simp [s]⟩
  refine ⟨j, fun i => ?_⟩
  rcases le_total (displacement j) (displacement i) with h | h
  · exact h
  · have hi : i ∈ s := h.trans hj.1
    exact hj.2 hi h

/-- Finite exponential weight and at least one child imply that the
a leftmost atom is well defined. -/
theorem exists_leftmost_of_finite_exponential_weight
    {ι : Type*} [Nonempty ι] (displacement : ι → ℝ)
    (hsum : (∑' i, ENNReal.ofReal (Real.exp (-displacement i))) ≠ ∞) :
    ∃ j : ι, ∀ i : ι, displacement j ≤ displacement i :=
  exists_leftmost_of_finite_sublevels displacement
    (finite_displacements_below displacement hsum)

end MeasureTheory
