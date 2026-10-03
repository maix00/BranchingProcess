import Probability.BranchingRandomWalk.Selection.NSelection.Totalized
import Mathlib.Basic.Real.Basic
import Combinatorics.BranchingWalk.Step.Basic

/-!
# Regression tests for infinite first-N selection

The negative integer positions have no leftmost particle, while the usual
natural-number order is an infinite population with a valid first-N segment.
-/

open Combinatorics.Branching.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
open Combinatorics.Branching

def negNatOffspring : Combinatorics.Branching.Step ℕ ℝ :=
  fun j => some (-(j : ℝ))

theorem negNat_positions_do_not_admit_positive_firstN
    (N : ℕ) (hN : 0 < N) :
    ¬ AdmitsFirstNBy (ι := ℕ) (Value := ℝ) N
      (fun j : ℕ => -(j : ℝ)) (Set.univ : Set ℕ) := by
  rintro ⟨selected, hselected⟩
  have hcard : selected.card = N :=
    hselected.card_infinite Set.infinite_univ
  have hnonempty : selected.Nonempty :=
    Finset.card_pos.mp (by omega)
  let j := selected.max' hnonempty
  have hj : j ∈ selected := by
    exact Finset.max'_mem selected hnonempty
  have hvalue : (-(↑(j + 1) : ℝ)) < -(↑j : ℝ) := by
    exact neg_lt_neg (Nat.cast_lt.mpr (Nat.lt_succ_self j))
  have hkey : valueKey (ι := ℕ) (Value := ℝ)
      (fun k : ℕ => -(k : ℝ)) (j + 1) <
      valueKey (ι := ℕ) (Value := ℝ) (fun k : ℕ => -(k : ℝ)) j := by
    exact Prod.Lex.left _ _ hvalue
  have hnext : j + 1 ∈ selected :=
    hselected.lower j hj (j + 1) (Set.mem_univ _) hkey
  have hle := selected.le_max' (j + 1) hnext
  have hcontra : j + 1 ≤ j := by
    change j + 1 ≤ j at hle
    exact hle
  omega

theorem negNat_offspring_candidates_are_universal :
    {j : ℕ | survive negNatOffspring j} = Set.univ := by
  ext j
  simp [negNatOffspring, survive]

theorem negNat_offspring_does_not_admit_positive_firstN
    (N : ℕ) (hN : 0 < N) :
    ¬ AdmitsFirstNBy (ι := ℕ) (Value := ℝ) N
      (fun j : ℕ => -(j : ℝ))
      {j | survive negNatOffspring j} := by
  rw [negNat_offspring_candidates_are_universal]
  exact negNat_positions_do_not_admit_positive_firstN N hN

theorem natural_positions_are_lower_finite :
    IsLowerFiniteBy (ι := ℕ) (Value := ℕ)
      (fun j : ℕ => j) (Set.univ : Set ℕ) := by
  intro p _
  apply (Set.finite_Iic p).subset
  intro q hq
  have hqle : q ≤ p := by
    rcases (Prod.Lex.toLex_le_toLex.mp hq.2) with hlt | ⟨_, hle⟩
    · exact hlt.le
    · exact hle
  exact hqle

theorem natural_positions_admit_infinite_firstN (N : ℕ) :
    AdmitsFirstNBy (ι := ℕ) (Value := ℕ) N
      (fun j : ℕ => j) (Set.univ : Set ℕ) :=
  admitsFirstNBy_of_lowerFinite N _ natural_positions_are_lower_finite

theorem natural_positions_totalized_selector_is_firstN (N : ℕ) :
    IsFirstNBy N (fun j : ℕ => j) (Set.univ : Set ℕ)
      (selectFirstNFromSetTotalized (ι := ℕ) (Value := ℕ) N
        (fun _ : ℕ => fun j : ℕ => j)
        (fun _ => (Set.univ : Set ℕ)) 0) :=
  selectFirstNFromSetTotalized_spec N
    (fun _ : ℕ => fun j : ℕ => j)
    (fun _ => (Set.univ : Set ℕ)) 0 (by
      simpa using natural_positions_are_lower_finite)

theorem negNat_totalized_selection_is_empty
    (N : ℕ) (hN : 0 < N) :
    selectFirstNFromSetTotalized (ι := ℕ) (Value := ℝ) N
        (fun _ : ℕ => fun j : ℕ => -(j : ℝ))
        (fun _ => {j | survive negNatOffspring j}) 0 = ∅ := by
  apply selectFirstNFromSetTotalized_empty_of_not_lowerFinite
  intro hlower
  apply negNat_offspring_does_not_admit_positive_firstN N hN
  exact admitsFirstNBy_of_lowerFinite N _ hlower
