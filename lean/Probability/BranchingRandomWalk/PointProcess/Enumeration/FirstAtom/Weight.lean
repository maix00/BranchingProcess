import Probability.BranchingRandomWalk.PointProcess.Enumeration.FirstAtom.Selector
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Combinatorics.BranchingWalk.Step.Basic

/-!
# Finite exponential weight of the realized children

Total exponential child weight has a finite first moment, which turns
left-local finiteness into a genuine leftmost child almost surely. The
normalization `E[totalChildWeight] = 1` is one instance of the hypothesis.
-/

open MeasureTheory
open scoped Topology BigOperators ENNReal NNReal

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


/-- Exponential weight of a realized raw child, with absent slots assigned
zero weight. -/
noncomputable def realizedChildWeight (ξ : Step ℕ ℝ) (i : ℕ) :
    ENNReal := by
  classical
  exact if survive ξ i then
    ENNReal.ofReal (Real.exp (-value' ξ i)) else 0

theorem realizedChildWeight_measurable (i : ℕ) :
    Measurable (fun ξ : Step ℕ ℝ => realizedChildWeight ξ i) := by
  classical
  unfold realizedChildWeight
  exact (ENNReal.measurable_ofReal.comp
    ((value'_measurable i).neg.exp)).ite
    (survive_measurableSet i) measurable_const

/-- The total exponential weight of every realized child. -/
noncomputable def totalChildWeight (ξ : Step ℕ ℝ) : ENNReal :=
  ∑' i, realizedChildWeight ξ i

theorem totalChildWeight_measurable : Measurable totalChildWeight := by
  unfold totalChildWeight
  exact Measurable.tsum realizedChildWeight_measurable

theorem finite_realized_children_below (ξ : Step ℕ ℝ)
    (hsum : (∑' i, realizedChildWeight ξ i) ≠ ∞)
    (R : ℝ) :
    {i : ℕ | survive ξ i ∧
      value' ξ i ≤ R}.Finite := by
  classical
  apply finite_atoms_of_weight_lower_bound
    (realizedChildWeight ξ) hsum _
    (ENNReal.ofReal (Real.exp (-R)))
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  intro i hi
  have hle := ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr (neg_le_neg hi.2))
  simpa [realizedChildWeight, hi.1] using hle

/-- A nonempty raw child mark has a genuine leftmost child under the
finite exponential-weight condition. -/
theorem firstAtomIndex_spec_of_finite_weight (ξ : Step ℕ ℝ)
    (hsum : totalChildWeight ξ ≠ ∞)
    (hnonempty : ∃ i, survive ξ i) :
    firstAtomAt ξ (firstAtomIndex ξ) :=
  firstAtomIndex_spec ξ
    (firstAtomAt_exists_of_finite_sublevels ξ
      (finite_realized_children_below ξ hsum) hnonempty)

/-- A finite first moment of total exponential child weight makes the
first-atom selector correct almost surely. The normalization
`E[totalChildWeight] = 1` is one instance of this hypothesis. -/
theorem firstAtomIndex_ae_firstAtomAt
    (μ : Measure (Step ℕ ℝ))
    (hmoment : (∫⁻ ξ, totalChildWeight ξ ∂μ) ≠ ∞)
    (hnonempty : ∀ᵐ ξ ∂μ, ∃ i, survive ξ i) :
    ∀ᵐ ξ ∂μ, firstAtomAt ξ (firstAtomIndex ξ) := by
  filter_upwards [ae_lt_top totalChildWeight_measurable hmoment,
    hnonempty] with ξ hξ hne
  exact firstAtomIndex_spec_of_finite_weight ξ hξ.ne hne

end ProbabilityTheory.BranchingRandomWalk
