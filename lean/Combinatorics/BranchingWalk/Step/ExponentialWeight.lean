import Combinatorics.BranchingWalk.Step.Measurability
import MeasureTheory.Measure.AtomFiniteness
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Exponential weights of a deterministic branching step

Weights are functions of a step. Their measurability is proved here once and
is inherited by every random step by composition.
-/

open MeasureTheory
open scoped ENNReal

namespace Combinatorics.Branching

noncomputable def realizedChildWeight (ξ : Step ℕ ℝ) (i : ℕ) : ENNReal := by
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

noncomputable def totalChildWeight (ξ : Step ℕ ℝ) : ENNReal :=
  ∑' i, realizedChildWeight ξ i

theorem totalChildWeight_measurable : Measurable totalChildWeight := by
  unfold totalChildWeight
  exact Measurable.tsum realizedChildWeight_measurable

theorem finite_realized_children_below (ξ : Step ℕ ℝ)
    (hsum : totalChildWeight ξ ≠ ∞) (R : ℝ) :
    {i : ℕ | survive ξ i ∧ value' ξ i ≤ R}.Finite := by
  classical
  apply finite_atoms_of_weight_lower_bound
    (realizedChildWeight ξ) hsum _
    (ENNReal.ofReal (Real.exp (-R)))
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  intro i hi
  have hle := ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr (neg_le_neg hi.2))
  simpa [realizedChildWeight, hi.1] using hle

end Combinatorics.Branching
