import Combinatorics.BranchingWalk.Walk.Path.Scaling
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Corridors for scaled walk paths

Corridor membership, grid restriction, and corridor energy are deterministic
properties of real-valued paths.
-/

open MeasureTheory Set

namespace Combinatorics.Branching.Walk

/-- A path stays strictly between two boundaries at every time in `times`. -/
def InOpenCorridorOn (times : Set ℝ) (lower upper path : ℝ → ℝ) : Prop :=
  ∀ t ∈ times, lower t < path t ∧ path t < upper t

/-- A path stays weakly between two boundaries at every time in `times`. -/
def InClosedCorridorOn (times : Set ℝ) (lower upper path : ℝ → ℝ) : Prop :=
  ∀ t ∈ times, lower t ≤ path t ∧ path t ≤ upper t

/-- The open corridor on the unit time interval used in the original
Mogulskii statement. -/
abbrev InOpenCorridor := InOpenCorridorOn (Icc (0 : ℝ) 1)

/-- Closed corridor membership on the unit time interval. -/
abbrev InClosedCorridor := InClosedCorridorOn (Icc (0 : ℝ) 1)

/-- Closed corridor membership checked at the positive points of the `n`-step
grid.  Unlike full path-space membership, this is a finite predicate. -/
def InClosedCorridorOnGrid (scale : ℕ → ℝ) (n : ℕ)
    (lower upper : ℝ → ℝ) (increment : ℕ → ℝ) : Prop :=
  ∀ k : Fin n,
    let t := ((k.val + 1 : ℕ) : ℝ) / n
    lower t ≤ normalizedStepPath scale n increment t ∧
      normalizedStepPath scale n increment t ≤ upper t

theorem InOpenCorridorOn.closed {times : Set ℝ} {lower upper path : ℝ → ℝ}
    (h : InOpenCorridorOn times lower upper path) :
    InClosedCorridorOn times lower upper path := by
  intro t ht
  exact ⟨(h t ht).1.le, (h t ht).2.le⟩

/-- For a step path and constant boundaries, checking the positive grid is
equivalent to checking the whole unit interval. Time zero contributes exactly
the requirement that the constant interval contain zero. -/
theorem inClosedCorridor_const_iff_grid
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    {lower upper : ℝ} (hlower : lower ≤ 0) (hupper : 0 ≤ upper)
    (increment : ℕ → ℝ) :
    InClosedCorridor (fun _ => lower) (fun _ => upper)
        (normalizedStepPath scale n increment) ↔
      InClosedCorridorOnGrid scale n (fun _ => lower) (fun _ => upper)
        increment := by
  constructor
  · intro h k
    apply h
    constructor
    · positivity
    · rw [div_le_one (by positivity)]
      exact_mod_cast Nat.succ_le_iff.2 k.isLt
  · intro h t ht
    have hnt : (n : ℝ) * t ≤ n := by
      calc
        (n : ℝ) * t ≤ (n : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg n)
        _ = n := by ring
    have hfloor : ⌊(n : ℝ) * t⌋₊ ≤ n := by
      exact Nat.floor_le_of_le hnt
    generalize hm : ⌊(n : ℝ) * t⌋₊ = m at hfloor ⊢
    cases m with
    | zero =>
        simpa [normalizedStepPath, hm] using And.intro hlower hupper
    | succ k =>
        have hk : k < n := Nat.succ_le_iff.1 hfloor
        have hg := h ⟨k, hk⟩
        dsimp only at hg
        rw [normalizedStepPath_grid scale hn] at hg
        rw [normalizedStepPath, hm]
        exact hg

/-- The width functional `H_α` from the original theorem, restricted to its
basic corridor representation. -/
noncomputable def corridorEnergy (α : ℝ) (lower upper : ℝ → ℝ) : ℝ :=
  ∫ t in Icc (0 : ℝ) 1, (upper t - lower t) ^ (-α)

/-- A horizontal corridor of width `width` has energy `width⁻ᵅ`. -/
theorem corridorEnergy_const (α lower upper : ℝ) :
    corridorEnergy α (fun _ => lower) (fun _ => upper) =
      (upper - lower) ^ (-α) := by
  simp [corridorEnergy]

/-- Translating both boundaries leaves the corridor energy unchanged. -/
theorem corridorEnergy_add_const (α shift : ℝ) (lower upper : ℝ → ℝ) :
    corridorEnergy α (fun t => shift + lower t)
        (fun t => shift + upper t) =
      corridorEnergy α lower upper := by
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  ring

end Combinatorics.Branching.Walk
