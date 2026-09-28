import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Basic
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.FiniteKernel
import Probability.Kernel.FiniteState
import Mathlib.Data.Finset.Max

/-!
# The killed symmetric-walk kernel on a finite interval

`Fin interiorCount` represents the interior sites `1, ..., interiorCount`.
A step that would reach either exterior Dirichlet boundary is omitted, so the
matrix is substochastic at the two edge sites.
-/

open scoped BigOperators Matrix

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk.Mogulskii

/-- The left neighboring interior site, when it exists. -/
def intervalLeftNeighbor {interiorCount : ℕ} (i : Fin interiorCount) :
    Option (Fin interiorCount) :=
  if _hi : 0 < i.val then
    some ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
  else none

/-- The right neighboring interior site, when it exists. -/
def intervalRightNeighbor {interiorCount : ℕ} (i : Fin interiorCount) :
    Option (Fin interiorCount) :=
  if hi : i.val + 1 < interiorCount then some ⟨i.val + 1, hi⟩ else none

/-- The killed simple symmetric transition matrix on the interior of a
finite lattice interval. -/
noncomputable def intervalKernel (interiorCount : ℕ) :
    Matrix (Fin interiorCount) (Fin interiorCount) ℝ :=
  fun i j =>
    (if intervalLeftNeighbor i = some j then 1 / 2 else 0) +
      (if intervalRightNeighbor i = some j then 1 / 2 else 0)

/-- Summing a point mass selected by an optional index evaluates the function
at that index, and gives zero when the index is absent. -/
theorem sum_ite_option_eq_elim {ι : Type*} [Fintype ι] [DecidableEq ι]
    (index : Option ι) (coefficient : ℝ) (f : ι → ℝ) :
    (∑ j, (if index = some j then coefficient else 0) * f j) =
      index.elim 0 (fun j => coefficient * f j) := by
  cases index with
  | none => simp
  | some i => simp

theorem option_elim_mul {ι : Type*} (index : Option ι)
    (coefficient : ℝ) (f : ι → ℝ) :
    index.elim 0 (fun i => coefficient * f i) =
      coefficient * index.elim 0 f := by
  cases index <;> simp

/-- Matrix multiplication by the interval kernel is averaging over the
available interior neighbors. -/
theorem intervalKernel_mulVec (interiorCount : ℕ)
    (f : Fin interiorCount → ℝ) (i : Fin interiorCount) :
    (intervalKernel interiorCount *ᵥ f) i =
      (intervalLeftNeighbor i).elim 0 (fun j => (1 / 2 : ℝ) * f j) +
        (intervalRightNeighbor i).elim 0 (fun j => (1 / 2 : ℝ) * f j) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [intervalKernel, add_mul, Finset.sum_add_distrib]
  rw [sum_ite_option_eq_elim, sum_ite_option_eq_elim]

/-- The positive Dirichlet sine profile on the interior lattice sites. -/
noncomputable def intervalSineWeight (interiorCount : ℕ) : Fin interiorCount → ℝ :=
  fun i => dirichletSine (interiorCount + 1 : ℕ) (i.val + 1 : ℕ)

theorem intervalLeftNeighbor_sine (interiorCount : ℕ) (i : Fin interiorCount) :
    (intervalLeftNeighbor i).elim 0 (intervalSineWeight interiorCount) =
      dirichletSine (interiorCount + 1 : ℕ) i.val := by
  unfold intervalLeftNeighbor
  split_ifs with hi
  · simp only [Option.elim_some, intervalSineWeight]
    congr 2
    omega
  · have hiz : i.val = 0 := Nat.eq_zero_of_not_pos hi
    simp [hiz]

theorem intervalRightNeighbor_sine (interiorCount : ℕ) (i : Fin interiorCount) :
    (intervalRightNeighbor i).elim 0 (intervalSineWeight interiorCount) =
      dirichletSine (interiorCount + 1 : ℕ) (i.val + 2 : ℕ) := by
  unfold intervalRightNeighbor
  split_ifs with hi
  · simp only [Option.elim_some, intervalSineWeight]
  · have hilast : i.val + 1 = interiorCount := by omega
    rw [show (i.val + 2 : ℕ) = interiorCount + 1 by omega]
    symm
    apply dirichletSine_right
    positivity

/-- The interval sine profile is the positive principal eigenfunction of the
killed symmetric kernel. -/
theorem intervalKernel_mulVec_sine (interiorCount : ℕ) :
    intervalKernel interiorCount *ᵥ intervalSineWeight interiorCount =
      Real.cos (Real.pi / (interiorCount + 1 : ℕ)) •
        intervalSineWeight interiorCount := by
  funext i
  rw [intervalKernel_mulVec]
  rw [option_elim_mul, option_elim_mul, intervalLeftNeighbor_sine,
    intervalRightNeighbor_sine]
  have hs := symmetricStep_dirichletSine
    (interiorCount + 1 : ℕ) (i.val + 1 : ℕ)
  simp only [symmetricStep] at hs
  have hs' :
      (dirichletSine (interiorCount + 1 : ℕ) i.val +
        dirichletSine (interiorCount + 1 : ℕ) (i.val + 2 : ℕ)) / 2 =
          Real.cos (Real.pi / (interiorCount + 1 : ℕ)) *
            intervalSineWeight interiorCount i := by
    norm_num [Nat.cast_add, Nat.cast_one] at hs
    rw [show (i.val : ℝ) + 1 + 1 = (i.val : ℝ) + 2 by ring] at hs
    simpa [intervalSineWeight, Nat.cast_add, Nat.cast_one] using hs
  calc
    _ = (dirichletSine (interiorCount + 1 : ℕ) i.val +
        dirichletSine (interiorCount + 1 : ℕ) (i.val + 2 : ℕ)) / 2 := by ring
    _ = _ := hs'

theorem intervalKernel_nonneg (interiorCount : ℕ) (i j : Fin interiorCount) :
    0 ≤ intervalKernel interiorCount i j := by
  simp only [intervalKernel]
  positivity

/-- The killed interval matrix is row-substochastic: probability mass is
lost precisely when a step exits the interval. -/
theorem intervalKernel_isRowSubstochastic (interiorCount : ℕ) :
    (intervalKernel interiorCount).IsRowSubstochastic := by
  constructor
  · exact intervalKernel_nonneg interiorCount
  · intro i
    rw [← show (intervalKernel interiorCount *ᵥ (fun _ => (1 : ℝ))) i =
      ∑ j, intervalKernel interiorCount i j by
        simp [Matrix.mulVec, dotProduct]]
    rw [intervalKernel_mulVec]
    cases intervalLeftNeighbor i <;> cases intervalRightNeighbor i <;> norm_num

/-- The measure-valued mathlib kernel represented by the killed interval
matrix is a sub-Markov kernel. -/
instance intervalKernel_isSubMarkovKernel (interiorCount : ℕ) :
    IsSubMarkovKernel (Kernel.ofRealMatrix (intervalKernel interiorCount)) :=
  Kernel.isSubMarkovKernel_ofRealMatrix
    (intervalKernel_isRowSubstochastic interiorCount)

/-- The surviving mass after `n` killed transitions is the row sum of the
`n`th matrix power.  This is the finite-state Chapman--Kolmogorov identity,
stated in mathlib's kernel language. -/
theorem intervalKernel_pow_apply_univ (interiorCount n : ℕ)
    (start : Fin interiorCount) :
    (Kernel.ofRealMatrix (intervalKernel interiorCount) ^ n) start Set.univ =
      ENNReal.ofReal
        (∑ finish, (intervalKernel interiorCount ^ n) start finish) :=
  Kernel.pow_apply_univ_ofRealMatrix
    (intervalKernel_nonneg interiorCount) n start

theorem intervalSineWeight_pos {interiorCount : ℕ} (hcount : 0 < interiorCount)
    (i : Fin interiorCount) :
    0 < intervalSineWeight interiorCount i := by
  apply dirichletSine_pos
  · positivity
  · constructor
    · positivity
    · exact_mod_cast Nat.add_lt_add_right i.isLt 1

theorem intervalSineWeight_le_one (interiorCount : ℕ) (i : Fin interiorCount) :
    intervalSineWeight interiorCount i ≤ 1 := by
  exact Real.sin_le_one _

/-- On every nonempty finite interval the positive sine ground state has a
strictly positive uniform lower bound. -/
theorem exists_pos_le_intervalSineWeight {interiorCount : ℕ}
    (hcount : 0 < interiorCount) :
    ∃ lower : ℝ, 0 < lower ∧ ∀ i, lower ≤ intervalSineWeight interiorCount i := by
  let i₀ : Fin interiorCount := ⟨0, hcount⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
    (intervalSineWeight interiorCount) ⟨i₀, Finset.mem_univ _⟩
  exact ⟨intervalSineWeight interiorCount i,
    intervalSineWeight_pos hcount i, fun j => hi j (Finset.mem_univ _)⟩

/-- Quantitative row-mass bounds for every power of the killed interval
kernel.  The row sum becomes the interval-survival probability once the
kernel is identified with the Rademacher path law. -/
theorem intervalKernel_pow_rowSum_bounds {interiorCount : ℕ}
    (hcount : 0 < interiorCount) (n : ℕ) (start : Fin interiorCount) :
    ∃ lower : ℝ, 0 < lower ∧
      Real.cos (Real.pi / (interiorCount + 1 : ℕ)) ^ n *
          intervalSineWeight interiorCount start ≤
        ∑ finish, (intervalKernel interiorCount ^ n) start finish ∧
      (∑ finish, (intervalKernel interiorCount ^ n) start finish) ≤
        (Real.cos (Real.pi / (interiorCount + 1 : ℕ)) ^ n *
          intervalSineWeight interiorCount start) / lower := by
  obtain ⟨lower, hlower_pos, hlower⟩ :=
    exists_pos_le_intervalSineWeight hcount
  refine ⟨lower, hlower_pos, ?_, ?_⟩
  · have hbounds := pow_rowSum_bounds_of_positive_eigenfunction
      (intervalKernel interiorCount) (intervalSineWeight interiorCount)
      (Real.cos (Real.pi / (interiorCount + 1 : ℕ))) lower 1
      (intervalKernel_nonneg interiorCount) (intervalKernel_mulVec_sine interiorCount)
      hlower (intervalSineWeight_le_one interiorCount) n start
    simpa using hbounds.2
  · apply totalMass_le_div_of_weightedMass Finset.univ
      (fun finish => (intervalKernel interiorCount ^ n) start finish)
      (intervalSineWeight interiorCount) lower
      (Real.cos (Real.pi / (interiorCount + 1 : ℕ)) ^ n *
        intervalSineWeight interiorCount start)
      hlower_pos
    · intro finish _
      exact Matrix.pow_apply_nonneg (intervalKernel_nonneg interiorCount)
        n start finish
    · exact fun finish _ => hlower finish
    · simpa using sum_pow_apply_mul_weight
        (intervalKernel interiorCount) (intervalSineWeight interiorCount)
        (Real.cos (Real.pi / (interiorCount + 1 : ℕ)))
        (intervalKernel_mulVec_sine interiorCount) n start

end ProbabilityTheory.BranchingRandomWalk.RandomWalk.Mogulskii
