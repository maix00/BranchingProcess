/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/

module

public import Probability.Ergodic.Birkhoff
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Basic objects for Kingman's subadditive ergodic theorem

## Public declarations

* `ProbabilityTheory.IsSubadditiveCocycle`: a sequence `g : ℕ → X → ℝ` satisfying
  `g (m+n) x ≤ g m x + g n (T^[m] x)`.
* `ProbabilityTheory.IsSubadditiveCocycle.le_birkhoffSum_one`: for `n ≥ 0`,
  `g (n+1) x ≤ birkhoffSum T (g 1) (n+1) x`.
* `ProbabilityTheory.IsSubadditiveCocycle.le_sum_blocks`: for consecutive block lengths
  `ℓ 0, …, ℓ k`, `g (∑ i ≤ k, ℓ i) x` is at most the sum of the corresponding cocycle values
  at the successive orbit frontiers.
* `ProbabilityTheory.Kingman.cdiv`: the normalized cocycle `g (n+1) x / (n+1)`.
* `ProbabilityTheory.Kingman.cdiv_le_birkhoffAverage`: `cdiv g n x` is bounded above by
  `birkhoffAverage ℝ T (g 1) (n+1) x`.
* `ProbabilityTheory.Kingman.ecdiv`: the coercion of `cdiv g n x` to `EReal`.

For a subadditive cocycle, the defining inequality iterates over consecutive
blocks and over singleton blocks as follows:

\[\begin{aligned}
g_{m+n}(x)&\le g_m(x)+g_n(T^m x),\\
g_{n+1}(x)&\le\sum_{j=0}^{n}g_1(T^j x),\\
g_{\sum_{i=0}^{k}\ell_i}(x)
&\le\sum_{i=0}^{k}
  g_{\ell_i}\!\left(T^{\sum_{j=0}^{i-1}\ell_j}x\right).
\end{aligned}\]
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace ProbabilityTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

/-- A sequence `g : ℕ → X → ℝ` is a **subadditive cocycle** over `T` when
`g (m + n) x ≤ g m x + g n (T^[m] x)` for all `m, n, x`. (For `gₙ = log‖A⁽ⁿ⁾‖` this
follows from submultiplicativity of the operator norm and the cocycle identity.) -/
structure IsSubadditiveCocycle (T : X → X) (g : ℕ → X → ℝ) : Prop where
  apply_add_le : ∀ m n x, g (m + n) x ≤ g m x + g n (T^[m] x)

omit [MeasurableSpace X] in
/-- **Singleton partition subadditivity.** For `n ≥ 1`, a subadditive cocycle is dominated by
the Birkhoff sum of its first level: `g (n+1) x ≤ birkhoffSum T (g 1) (n+1) x`. -/
theorem IsSubadditiveCocycle.le_birkhoffSum_one {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (n : ℕ) (x : X) :
    g (n + 1) x ≤ birkhoffSum T (g 1) (n + 1) x := by
  induction n with
  | zero => simp only [Nat.zero_add, birkhoffSum_one]; exact le_refl _
  | succ n ih =>
      rw [birkhoffSum_succ]
      calc g (n + 1 + 1) x ≤ g (n + 1) x + g 1 (T^[n + 1] x) := hsub.apply_add_le (n + 1) 1 x
        _ ≤ birkhoffSum T (g 1) (n + 1) x + g 1 (T^[n + 1] x) := by linarith [ih]

omit [MeasurableSpace X] in
/-- **Block subadditivity.** For a subadditive cocycle and consecutive block lengths
`ℓ 0, …, ℓ k`, the cocycle over the total length is bounded by the sum of the block cocycle
values evaluated at their successive orbit frontiers. -/
theorem IsSubadditiveCocycle.le_sum_blocks {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (ℓ : ℕ → ℕ) (k : ℕ) (x : X) :
    g (∑ i ∈ Finset.range (k + 1), ℓ i) x
      ≤ ∑ i ∈ Finset.range (k + 1), g (ℓ i) (T^[∑ j ∈ Finset.range i, ℓ j] x) := by
  induction k with
  | zero =>
      rw [Finset.range_one, Finset.sum_singleton, Finset.sum_singleton, Finset.range_zero,
        Finset.sum_empty, Function.iterate_zero, id_eq]
  | succ k ih =>
      rw [Finset.sum_range_succ (n := k + 1), Finset.sum_range_succ (n := k + 1)]
      set s : ℕ := ∑ j ∈ Finset.range (k + 1), ℓ j with hs
      calc g (s + ℓ (k + 1)) x
          ≤ g s x + g (ℓ (k + 1)) (T^[s] x) := hsub.apply_add_le s (ℓ (k + 1)) x
        _ ≤ (∑ i ∈ Finset.range (k + 1), g (ℓ i) (T^[∑ j ∈ Finset.range i, ℓ j] x))
              + g (ℓ (k + 1)) (T^[s] x) := by linarith [ih]

end ProbabilityTheory

namespace ProbabilityTheory.Kingman

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

/-- The normalized cocycle `g (n+1) x / (n+1)`. -/
noncomputable def cdiv (g : ℕ → X → ℝ) (n : ℕ) (x : X) : ℝ := g (n + 1) x / (n + 1)

omit [MeasurableSpace X] in
/-- `cdiv g n x` is dominated by the Birkhoff average of `g 1`. -/
theorem cdiv_le_birkhoffAverage {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g)
    (n : ℕ) (x : X) : cdiv g n x ≤ birkhoffAverage ℝ T (g 1) (n + 1) x := by
  have h := hsub.le_birkhoffSum_one n x
  rw [cdiv, birkhoffAverage, smul_eq_mul]
  rw [div_eq_inv_mul]
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  apply mul_le_mul_of_nonneg_left h (le_of_lt (by positivity))

/-- The `EReal`-valued normalized cocycle. -/
noncomputable def ecdiv (g : ℕ → X → ℝ) (n : ℕ) (x : X) : EReal := (cdiv g n x : EReal)

end ProbabilityTheory.Kingman
