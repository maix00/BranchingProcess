import Probability.BranchingRandomWalk.Genealogy.Lineage.Lineages
import Combinatorics.BranchingWalk.Step.Measurability
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Filtration

/-!
# Reserve lineages for every initial root

The two indices are the initial-root label and the reserve-trial label. Each
lineage is again pre-sampled, its path is adapted to the root-indexed
step filtration of `FiniteRootStepField m ℝ`, and its visible split
generation is a stopping time.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



/-- Pre-sampled reserve lineages for every labelled initial root. The two
indices are the initial-root label and the reserve-trial label. -/
structure MultiRootReserveLineages (m : ℕ) where
  path : Fin m → ℕ → ℕ → FiniteRootStepField m ℝ → 𝕍
  step : Fin m → ℕ → 𝕍 × Step ℕ ℝ → 𝕍
  measurable_step : ∀ i k, Measurable (step i k)
  measurable_root : ∀ i k,
    Measurable[multiRootStepFiltration (m := m) (X := ℝ) 0] (path i k 0)
  depth : ∀ i k n ω, (path i k n ω).length = n
  recursion : ∀ i k n ω,
    path i k (n + 1) ω =
      step i k (path i k n ω, ω i (path i k n ω))

theorem MultiRootReserveLineages.path_adapted {m : ℕ}
    (r : MultiRootReserveLineages m) (i : Fin m) (k : ℕ) :
    ∀ n, Measurable[multiRootStepFiltration (m := m) (X := ℝ) n] (r.path i k n) := by
  intro n
  induction n with
  | zero => exact r.measurable_root i k
  | succ n ih =>
      have hold : Measurable[multiRootStepFiltration (m := m) (X := ℝ) (n + 1)]
          (r.path i k n) :=
        ih.mono (multiRootStepFiltration (m := m) (X := ℝ) |>.mono (Nat.le_succ n)) le_rfl
      have hmark : Measurable[multiRootStepFiltration (m := m) (X := ℝ) (n + 1)]
          (fun ω : FiniteRootStepField m ℝ => ω i (r.path i k n ω)) :=
        multiRootSelectedStep_measurable (X := ℝ) i (r.path i k n) hold
          (fun ω => by rw [r.depth i k n ω]; exact Nat.lt_succ_self n)
      have hpair : Measurable[multiRootStepFiltration (m := m) (X := ℝ) (n + 1)]
          (fun ω : FiniteRootStepField m ℝ =>
            (r.path i k n ω, ω i (r.path i k n ω))) :=
        hold.prodMk hmark
      convert (r.measurable_step i k).comp hpair using 1
      funext ω
      exact r.recursion i k n ω

def multiRootSplitDeclaration {m : ℕ}
    (i : Fin m) (path : ℕ → FiniteRootStepField m ℝ → 𝕍) :
    ℕ → Set (FiniteRootStepField m ℝ)
  | 0 => ∅
  | n + 1 => {ω | ω i (path n ω) ∈ nontrivialSupport}

noncomputable def MultiRootReserveLineages.sigma {m : ℕ}
    (r : MultiRootReserveLineages m) (i : Fin m) (k : ℕ) :
    FiniteRootStepField m ℝ → WithTop ℕ :=
  firstDeclaredSuccess (multiRootSplitDeclaration i (r.path i k))

theorem MultiRootReserveLineages.sigma_isStoppingTime {m : ℕ}
    (r : MultiRootReserveLineages m) (i : Fin m) (k : ℕ) :
    IsStoppingTime (multiRootStepFiltration (m := m) (X := ℝ)) (r.sigma i k) := by
  apply firstDeclaredSuccess_isStoppingTime
  intro n
  cases n with
  | zero =>
      exact (multiRootStepFiltration (m := m) (X := ℝ) 0).measurableSet_empty
  | succ n =>
      have hold : Measurable[multiRootStepFiltration (m := m) (X := ℝ) (n + 1)]
          (r.path i k n) :=
        (r.path_adapted i k n).mono
          (multiRootStepFiltration (m := m) (X := ℝ) |>.mono (Nat.le_succ n)) le_rfl
      exact (multiRootSelectedStep_measurable (X := ℝ) i (r.path i k n) hold
        (fun ω => by rw [r.depth i k n ω]; exact Nat.lt_succ_self n))
          nontrivialSupport_measurable

theorem MultiRootReserveLineages.all_sigma_isStoppingTime {m : ℕ}
    (r : MultiRootReserveLineages m) :
    ∀ i k, IsStoppingTime (multiRootStepFiltration (m := m) (X := ℝ)) (r.sigma i k) :=
  r.sigma_isStoppingTime

end ProbabilityTheory.BranchingRandomWalk
