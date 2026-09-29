import Combinatorics.BranchingWalk.Walk.Path.Basic
import Mathlib.Probability.Process.Adapted

/-!
# The filtration of an increment path

At time `n`, a walk position uses exactly the increments with indices below
`n`.  This file records that alignment explicitly.  In particular, it avoids
using the natural filtration of the coordinate process itself, whose value at
time `n` already exposes increment `n`.
-/

open MeasureTheory
open scoped BigOperators

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

variable {E : Type*} [MeasurableSpace E]

/-- The first `n` coordinates of an increment path. -/
def incrementPrefix (n : ℕ) : (ℕ → E) → (Fin n → E) :=
  fun increment k ↦ increment k

theorem measurable_incrementPrefix (n : ℕ) :
    Measurable (incrementPrefix (E := E) n) := by
  exact Measurable.of_eval fun k ↦ by
    change Measurable (fun increment : ℕ → E ↦ increment (k : ℕ))
    exact measurable_pi_apply (k : ℕ)

/-- The walk filtration: at time `n` it contains exactly the first `n`
increments.  It is implemented as the natural filtration of finite-prefix
observations so that it reuses mathlib's filtration API. -/
def incrementFiltration :
    Filtration ℕ (inferInstance : MeasurableSpace (ℕ → E)) where
  seq n := ⨆ k : Fin n,
    MeasurableSpace.comap (fun increment : ℕ → E ↦ increment (k : ℕ))
      inferInstance
  mono' n m hnm := by
    refine iSup_le fun k ↦ ?_
    let k' : Fin m := ⟨k, lt_of_lt_of_le k.isLt hnm⟩
    simpa [k'] using le_iSup
      (fun j : Fin m ↦ MeasurableSpace.comap
        (fun increment : ℕ → E ↦ increment (j : ℕ)) inferInstance) k'
  le' n := by
    refine iSup_le fun k ↦ ?_
    exact (measurable_pi_apply (k : ℕ)).comap_le

theorem incrementPrefix_measurable (n : ℕ) :
    Measurable[incrementFiltration (E := E) n]
      (incrementPrefix (E := E) n) := by
  rw [measurable_iff_comap_le]
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp]
  exact iSup_le fun k ↦ le_iSup
    (fun j : Fin n ↦ MeasurableSpace.comap
      (fun increment : ℕ → E ↦ increment (j : ℕ)) inferInstance) k

theorem incrementPrefix_adapted :
    Adapted (incrementFiltration (E := E)) (incrementPrefix (E := E)) :=
  incrementPrefix_measurable

theorem increment_measurable (n : ℕ) (k : Fin n) :
    Measurable[incrementFiltration (E := E) n]
      (fun increment : ℕ → E ↦ increment k) :=
  (measurable_pi_apply k).comp
    (incrementPrefix_measurable n)

section AddCommMonoid

variable [AddCommMonoid E] [MeasurableAdd₂ E]

/-- The position process is adapted to the filtration exposing precisely the
increments already used in the position. -/
theorem positionProcess_adapted (initial : E) :
    Adapted (incrementFiltration (E := E)) (positionProcess initial) := by
  intro n
  rw [show positionProcess initial n = fun increment : ℕ → E ↦
      initial + ∑ k : Fin n, increment k by
    funext increment
    simp only [positionProcess, partialSum]
    rw [Fin.sum_univ_eq_sum_range]]
  exact measurable_const.add
    (Finset.measurable_sum Finset.univ fun k _ ↦ increment_measurable n k)

end AddCommMonoid

end ProbabilityTheory.RandomWalk
