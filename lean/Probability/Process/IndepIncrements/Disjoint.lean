module

public import Probability.Process.IndepIncrements

/-!
# Disjoint increments

Independent increments on a four-point time grid give independence of two
increments even when there is an unused interval between them.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

variable {Time Ω E : Type*} [Preorder Time] [MeasurableSpace Ω]
  [MeasurableSpace E] [Sub E] {P : Measure Ω} {X : Time → Ω → E}

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

/-- A monotone sequence of separated intervals yields a mutually independent
family of increments. The intervening intervals may have nonzero length; no
adjacency assumption is needed. -/
theorem HasIndepIncrements.iIndepFun_even_sub
    (hX : HasIndepIncrements X P) (t : ℕ → Time) (ht : Monotone t) :
    iIndepFun (fun i ω => X (t (2 * i + 1)) ω - X (t (2 * i)) ω) P := by
  let even : ℕ → ℕ := fun i => 2 * i
  have heven : Function.Injective even := by
    intro i j hij
    dsimp [even] at hij
    omega
  have h := (hX.nat ht).precomp heven
  simpa [even] using h

end ProbabilityTheory
