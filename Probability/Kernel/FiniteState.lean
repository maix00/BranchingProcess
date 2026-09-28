import Probability.Kernel.SubMarkov
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Kernels on finite state spaces

This file connects nonnegative real matrices with mathlib's measure-valued
`Kernel`.  The matrix is a representation; the probability-layer object
remains `ProbabilityTheory.Kernel`.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Matrix

variable {ι : Type*} [Fintype ι]

/-- A real matrix is row-substochastic when its entries are nonnegative and
every row has mass at most one. -/
def IsRowSubstochastic (matrix : Matrix ι ι ℝ) : Prop :=
  (∀ i j, 0 ≤ matrix i j) ∧ ∀ i, (∑ j, matrix i j) ≤ 1

namespace IsRowSubstochastic

variable {matrix : Matrix ι ι ℝ}

theorem nonneg (h : matrix.IsRowSubstochastic) (i j : ι) :
    0 ≤ matrix i j := h.1 i j

theorem rowSum_le_one (h : matrix.IsRowSubstochastic) (i : ι) :
    (∑ j, matrix i j) ≤ 1 := h.2 i

end IsRowSubstochastic

end Matrix

namespace ProbabilityTheory

namespace Kernel

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

/-- The mathlib kernel represented by a finite nonnegative real matrix.
Negative entries are sent to zero by `ENNReal.ofReal`; applications normally
pair this definition with `Matrix.IsRowSubstochastic`. -/
noncomputable def ofRealMatrix (matrix : Matrix ι ι ℝ) : Kernel ι ι where
  toFun i := ∑ j, ENNReal.ofReal (matrix i j) • Measure.dirac j
  measurable' := measurable_of_countable _

@[simp]
theorem ofRealMatrix_apply_univ (matrix : Matrix ι ι ℝ) (i : ι) :
    ofRealMatrix matrix i univ = ∑ j, ENNReal.ofReal (matrix i j) := by
  simp [ofRealMatrix, Measure.finsetSum_apply]

/-- A row-substochastic matrix represents a sub-Markov kernel. -/
theorem isSubMarkovKernel_ofRealMatrix {matrix : Matrix ι ι ℝ}
    (hmatrix : matrix.IsRowSubstochastic) :
    IsSubMarkovKernel (ofRealMatrix matrix) where
  measure_univ_le_one i := by
    rw [ofRealMatrix_apply_univ, ← ENNReal.ofReal_sum_of_nonneg]
    · exact ENNReal.ofReal_le_one.2 (hmatrix.rowSum_le_one i)
    · exact fun j _ => hmatrix.nonneg i j

end Kernel

end ProbabilityTheory
