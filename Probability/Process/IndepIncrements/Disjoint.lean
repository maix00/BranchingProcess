/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic

/-!
# Independent increments on separated intervals

## Public declarations

* `HasIndepIncrements.indepFun_disjoint_sub_sub`: if `a ≤ b ≤ c ≤ d`, then
  `(ω ↦ X b ω - X a ω) ⟂ᵢ[P] (ω ↦ X d ω - X c ω)`.
* `HasIndepIncrements.indepFun_increment_vectors`: for a monotone time grid,
  a.e.-measurable process coordinates, measurable subtraction, and disjoint
  finite index sets `S,T`, the vectors
  `i ↦ X (t (i+1)) - X (t i)` on `S` and `T` are independent.

For ordered times `a≤b≤c≤d`, and more generally for disjoint finite sets of
indices in a monotone grid, the independent-increment conclusions are

\[\begin{aligned}
\operatorname{IndepFun}_P(X_b-X_a,X_d-X_c),\\
S\cap T=\varnothing&\Longrightarrow
  \operatorname{IndepFun}_P
    \left((X_{t(i+1)}-X_{t(i)})_{i\in S},
          (X_{t(i+1)}-X_{t(i)})_{i\in T}\right).
\end{aligned}\]
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

variable {Time Ω E : Type*} [Preorder Time] [MeasurableSpace Ω]
  [MeasurableSpace E] [Sub E] {P : Measure Ω} {X : Time → Ω → E}

/-- Increments on ordered, disjoint time intervals are independent. -/
theorem HasIndepIncrements.indepFun_disjoint_sub_sub
    (hX : HasIndepIncrements X P) {a b c d : Time}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    (fun ω => X b ω - X a ω) ⟂ᵢ[P]
      (fun ω => X d ω - X c ω) := by
  let τ : ℕ → Time
    | 0 => a
    | 1 => b
    | 2 => c
    | _ => d
  have hmono : Monotone τ := by
    have hac : a ≤ c := le_trans hab hbc
    have hbd : b ≤ d := le_trans hbc hcd
    have had : a ≤ d := le_trans hac hcd
    intro i j hij
    dsimp [τ]
    repeat' split
    all_goals try simp_all
    all_goals omega
  have h := (hX.nat hmono).indepFun (by decide : (0 : ℕ) ≠ 2)
  simpa [τ] using h

/-- Finite vectors of elementary increments on disjoint parts of a time grid
are independent. This is the finite-coordinate input for independence of
increment paths on disjoint time blocks. -/
theorem HasIndepIncrements.indepFun_increment_vectors
    [MeasurableSub₂ E]
    (hX : HasIndepIncrements X P) (t : ℕ → Time) (ht : Monotone t)
    (hXt : ∀ i, AEMeasurable (X (t i)) P)
    (S T : Finset ℕ) (hST : Disjoint S T) :
    (fun ω (i : S) => X (t (i.val + 1)) ω - X (t i.val) ω) ⟂ᵢ[P]
      (fun ω (i : T) => X (t (i.val + 1)) ω - X (t i.val) ω) := by
  have hmeas (i : ℕ) :
      AEMeasurable (fun ω => X (t (i + 1)) ω - X (t i) ω) P :=
    (hXt (i + 1)).sub (hXt i)
  exact (hX.nat ht).indepFun_finset₀ S T hST hmeas

end ProbabilityTheory
