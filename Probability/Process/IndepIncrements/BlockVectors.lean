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

/-- The partial-sum paths over two disjoint finite collections of elementary
grid intervals are independent as vectors, not merely coordinatewise. -/
theorem HasIndepIncrements.indepFun_finiteBlockPartialSums
    {Ω Time : Type*} [MeasurableSpace Ω] [Preorder Time]
    {X : Time → Ω → ℝ} {P : Measure Ω}
    (hX : HasIndepIncrements X P) (t : ℕ → Time) (ht : Monotone t)
    (hXt : ∀ i, Measurable (X (t i)))
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
    (hXt : ∀ i, Measurable (X (t i))) (a b c : ℕ) :
    (fun ω => finiteBlockPartialSums (Finset.Ico a b)
      (fun i => X (t (i.val + 1)) ω - X (t i.val) ω)) ⟂ᵢ[P]
    (fun ω => finiteBlockPartialSums (Finset.Ico b c)
      (fun i => X (t (i.val + 1)) ω - X (t i.val) ω)) := by
  apply hX.indepFun_finiteBlockPartialSums t ht hXt
  apply Finset.disjoint_left.mpr
  intro i hi₁ hi₂
  simp only [Finset.mem_Ico] at hi₁ hi₂
  omega

end ProbabilityTheory
