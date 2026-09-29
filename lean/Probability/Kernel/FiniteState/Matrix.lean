module

public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Data.Matrix.Mul
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Probability.Kernel.Composition.Comp
public import Probability.Kernel.SubMarkov

/-!
# Finite matrix kernels

This file connects nonnegative real matrices with mathlib's measure-valued
`Kernel`.  The matrix is a representation; the probability-layer object
remains `ProbabilityTheory.Kernel`.
-/

@[expose] public section

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

theorem ofRealMatrix_apply (matrix : Matrix ι ι ℝ) (i : ι) (s : Set ι) :
    ofRealMatrix matrix i s =
      ∑ j, ENNReal.ofReal (matrix i j) * s.indicator 1 j := by
  classical
  simp [ofRealMatrix, Measure.finsetSum_apply]

/-- Matrix multiplication agrees with Chapman--Kolmogorov composition.  The
order reversal is the usual one: the left matrix acts first, whereas
`right ∘ₖ left` reads composition from right to left. -/
theorem ofRealMatrix_mul {left right : Matrix ι ι ℝ}
    (hleft : ∀ i j, 0 ≤ left i j) (hright : ∀ i j, 0 ≤ right i j) :
    ofRealMatrix (left * right) = ofRealMatrix right ∘ₖ ofRealMatrix left := by
  classical
  ext i s hs
  rw [comp_apply' _ _ _ hs, ofRealMatrix_apply, show ofRealMatrix left i =
      ∑ j, ENNReal.ofReal (left i j) • Measure.dirac j by rfl]
  rw [lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, ofRealMatrix_apply,
    Matrix.mul_apply, smul_eq_mul]
  calc
    _ = ∑ k, (∑ j, ENNReal.ofReal (left i j) * ENNReal.ofReal (right j k)) *
          s.indicator 1 k := by
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      have hsum := ENNReal.ofReal_sum_of_nonneg
        (s := Finset.univ) (f := fun j => left i j * right j k)
        (fun j _ => mul_nonneg (hleft i j) (hright j k))
      rw [hsum]
      simp only [ENNReal.ofReal_mul (hleft i _)]
    _ = ∑ k, ∑ j, ENNReal.ofReal (left i j) *
          (ENNReal.ofReal (right j k) * s.indicator 1 k) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_assoc]
    _ = ∑ j, ∑ k, ENNReal.ofReal (left i j) *
          (ENNReal.ofReal (right j k) * s.indicator 1 k) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.mul_sum]

section Powers

variable [DecidableEq ι]

@[simp]
theorem ofRealMatrix_one :
    ofRealMatrix (1 : Matrix ι ι ℝ) = 1 := by
  ext i s hs
  rw [ofRealMatrix_apply]
  change (∑ j, ENNReal.ofReal (if i = j then 1 else 0) * s.indicator 1 j) =
    Measure.dirac i s
  rw [Finset.sum_eq_single i]
  · simp [Measure.dirac_apply' _ hs]
  · intro j _ hji
    simp [hji.symm]
  · simp

/-- Iterating a finite-state kernel agrees with taking powers of its
nonnegative transition matrix. -/
theorem ofRealMatrix_pow {matrix : Matrix ι ι ℝ}
    (hnonneg : ∀ i j, 0 ≤ matrix i j) (n : ℕ) :
    ofRealMatrix (matrix ^ n) = ofRealMatrix matrix ^ n := by
  induction n with
  | zero => exact ofRealMatrix_one
  | succ n ih =>
      rw [pow_succ, ofRealMatrix_mul]
      · rw [ih]
        change ofRealMatrix matrix * ofRealMatrix matrix ^ n =
          ofRealMatrix matrix ^ n * ofRealMatrix matrix
        exact (Commute.self_pow _ _).eq
      · exact Matrix.pow_apply_nonneg hnonneg n
      · exact hnonneg

theorem pow_apply_univ_ofRealMatrix {matrix : Matrix ι ι ℝ}
    (hnonneg : ∀ i j, 0 ≤ matrix i j) (n : ℕ) (i : ι) :
    (ofRealMatrix matrix ^ n) i univ =
      ENNReal.ofReal (∑ j, (matrix ^ n) i j) := by
  rw [← ofRealMatrix_pow hnonneg, ofRealMatrix_apply_univ,
    ← ENNReal.ofReal_sum_of_nonneg]
  exact fun j _ => Matrix.pow_apply_nonneg hnonneg n i j

/-- On a finite target set, a finite-state matrix kernel assigns the `ofReal`
of the corresponding matrix-power sum. -/
theorem ofRealMatrix_pow_apply_finset {matrix : Matrix ι ι ℝ}
    (hnonneg : ∀ i j, 0 ≤ matrix i j) (n : ℕ) (i : ι)
    (target : Finset ι) :
    (ofRealMatrix matrix ^ n) i (target : Set ι) =
      ENNReal.ofReal (∑ j ∈ target, (matrix ^ n) i j) := by
  classical
  rw [← ofRealMatrix_pow hnonneg n, ofRealMatrix_apply]
  have hsum :
      (∑ j, ENNReal.ofReal ((matrix ^ n) i j) *
          (target : Set ι).indicator 1 j) =
        ∑ j ∈ target, ENNReal.ofReal ((matrix ^ n) i j) := by
    simp [Set.indicator]
  rw [hsum, ← ENNReal.ofReal_sum_of_nonneg]
  intro j hj
  exact Matrix.pow_apply_nonneg hnonneg n i j

end Powers

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

end
