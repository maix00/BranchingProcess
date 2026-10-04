/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.IndepIncrements.Disjoint

/-!
# Finite block paths from independent increments

On a fixed monotone time grid, the partial-sum paths formed from disjoint
finite sets of elementary increments are independent. This finite-coordinate
statement is used before passing to whole block paths.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- Partial sums of a finite increment vector, ordered by its natural-number
grid indices. The index set need not be an interval. -/
noncomputable def finiteBlockPartialSums (S : Finset ℕ) (v : S → ℝ) : S → ℝ :=
  fun i => ∑ j ∈ (Finset.univ : Finset S).filter (fun j => j.val ≤ i.val), v j

theorem measurable_finiteBlockPartialSums (S : Finset ℕ) :
    Measurable (finiteBlockPartialSums S) := by
  rw [measurable_pi_iff]
  intro i
  exact Finset.measurable_sum _ (fun j _ => measurable_pi_apply j)

/-- Telescoping elementary increments across a contiguous block. -/
theorem sum_Ico_consecutive_sub (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ i ∈ Finset.Ico a b, (f (i + 1) - f i) = f b - f a := by
  rw [Finset.sum_Ico_eq_sub _ hab]
  simp only [Finset.sum_range_sub]
  ring

/-- At a selected grid index, the finite block partial-sum vector recovers
the process displacement from the first block endpoint. -/
theorem finiteBlockPartialSums_Ico_eq_sub (f : ℕ → ℝ)
    (a b : ℕ) (i : Finset.Ico a b) :
    finiteBlockPartialSums (Finset.Ico a b)
      (fun j => f (j.val + 1) - f j.val) i = f (i.val + 1) - f a := by
  let s : Finset (Finset.Ico a b) :=
    (Finset.univ : Finset (Finset.Ico a b)).filter (fun j => j.val ≤ i.val)
  have hmap : s.map (Function.Embedding.subtype _) = Finset.Ico a (i.val + 1) := by
    ext j
    simp only [Finset.mem_map, Finset.mem_Ico, Finset.mem_filter,
      Finset.mem_univ, true_and, s]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(Finset.mem_Ico.mp k.property).1, Nat.lt_succ_of_le hk⟩
    · intro hj
      refine ⟨⟨j, Finset.mem_Ico.mpr ⟨hj.1, ?_⟩⟩,
        Nat.le_of_lt_succ hj.2, rfl⟩
      exact lt_of_le_of_lt (Nat.le_of_lt_succ hj.2) (Finset.mem_Ico.mp i.property).2
  have ha : a ≤ i.val + 1 := Nat.le_succ_of_le (Finset.mem_Ico.mp i.property).1
  calc
    finiteBlockPartialSums (Finset.Ico a b)
        (fun j => f (j.val + 1) - f j.val) i =
      ∑ j ∈ s, (f (j.val + 1) - f j.val) := rfl
    _ = ∑ j ∈ Finset.Ico a (i.val + 1), (f (j + 1) - f j) := by
      rw [← hmap, Finset.sum_map]
      rfl
    _ = f (i.val + 1) - f a := sum_Ico_consecutive_sub f a (i.val + 1) ha

/-- The partial-sum paths over two disjoint finite collections of elementary
grid intervals are independent as vectors, not merely coordinatewise. -/
theorem HasIndepIncrements.indepFun_finiteBlockPartialSums
    {Ω Time : Type*} [MeasurableSpace Ω] [Preorder Time]
    {X : Time → Ω → ℝ} {P : Measure Ω}
    (hX : HasIndepIncrements X P) (t : ℕ → Time) (ht : Monotone t)
    (hXt : ∀ i, AEMeasurable (X (t i)) P)
    (S T : Finset ℕ) (hST : Disjoint S T) :
    (fun ω => finiteBlockPartialSums S
      (fun i => X (t (i.val + 1)) ω - X (t i.val) ω)) ⟂ᵢ[P]
    (fun ω => finiteBlockPartialSums T
      (fun i => X (t (i.val + 1)) ω - X (t i.val) ω)) := by
  exact (hX.indepFun_increment_vectors t ht hXt S T hST).comp
    (measurable_finiteBlockPartialSums S)
    (measurable_finiteBlockPartialSums T)

/-- Consecutive finite time blocks have independent partial-sum paths. The
left endpoint of the second block may coincide with the right endpoint of
the first. -/
theorem HasIndepIncrements.indepFun_adjacentBlockPartialSums
    {Ω Time : Type*} [MeasurableSpace Ω] [Preorder Time]
    {X : Time → Ω → ℝ} {P : Measure Ω}
    (hX : HasIndepIncrements X P) (t : ℕ → Time) (ht : Monotone t)
    (hXt : ∀ i, AEMeasurable (X (t i)) P) (a b c : ℕ) :
    (fun ω => finiteBlockPartialSums (Finset.Ico a b)
      (fun i => X (t (i.val + 1)) ω - X (t i.val) ω)) ⟂ᵢ[P]
    (fun ω => finiteBlockPartialSums (Finset.Ico b c)
      (fun i => X (t (i.val + 1)) ω - X (t i.val) ω)) := by
  apply hX.indepFun_finiteBlockPartialSums t ht hXt
  apply Finset.disjoint_left.mpr
  intro i hi₁ hi₂
  simp only [Finset.mem_Ico] at hi₁ hi₂
  omega

/-- On consecutive finite blocks, the vectors of actual positions relative
to each block's initial position are independent. -/
theorem HasIndepIncrements.indepFun_adjacentBlockPositionVectors
    {Ω Time : Type*} [MeasurableSpace Ω] [Preorder Time]
    {X : Time → Ω → ℝ} {P : Measure Ω}
    (hX : HasIndepIncrements X P) (t : ℕ → Time) (ht : Monotone t)
    (hXt : ∀ i, AEMeasurable (X (t i)) P) (a b c : ℕ) :
    (fun ω (i : Finset.Ico a b) => X (t (i.val + 1)) ω - X (t a) ω) ⟂ᵢ[P]
    (fun ω (i : Finset.Ico b c) => X (t (i.val + 1)) ω - X (t b) ω) := by
  have h := hX.indepFun_adjacentBlockPartialSums t ht hXt a b c
  convert h using 1
  · funext ω i
    exact (finiteBlockPartialSums_Ico_eq_sub (fun k => X (t k) ω) a b i).symm
  · funext ω i
    exact (finiteBlockPartialSums_Ico_eq_sub (fun k => X (t k) ω) b c i).symm

end ProbabilityTheory
