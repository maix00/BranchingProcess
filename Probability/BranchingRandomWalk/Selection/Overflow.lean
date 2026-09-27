import Probability.BranchingRandomWalk.Selection.Process
import Probability.BranchingRandomWalk.Timing.Overflow
import Combinatorics.UlamHarris.Basic

/-!
# Overflow time of a causal multi-root selected population

The particle labels are `Root × TreeNode α`; `Root` is arbitrary. A countable
label type is only a convenience assumption for deriving size measurability
from full labelled-population measurability. The primary stopping-time theorem
accepts observable population sizes directly and has no root-countability
assumption.
-/

open MeasureTheory Combinatorics.UlamHarris

namespace ProbabilityTheory.BranchingRandomWalk.Selection

variable {Ω Root α : Type*} {m : MeasurableSpace Ω}
    [MeasurableSpace (RootIndexed.TreeNode Root α)]

namespace CausalSelectMechanism

/-- First generation at which a causal selected population over all roots has
more than `N` particles. -/
noncomputable def overflowTime
    (F : Filtration ℕ m)
    (R : CausalSelectMechanism ℕ Ω (RootIndexed.TreeNode Root α)
      (fun n => F n))
    (candidates : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (N : ℕ) : Ω → WithTop ℕ :=
  finsetPopulationOverflowTime (R.population candidates) N

theorem overflowTime_le_iff
    (F : Filtration ℕ m)
    (R : CausalSelectMechanism ℕ Ω (RootIndexed.TreeNode Root α)
      (fun n => F n))
    (candidates : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (N n : ℕ) (ω : Ω) :
    R.overflowTime F candidates N ω ≤ n ↔
      ∃ j ≤ n, N < (R.population candidates j ω).card :=
  finsetPopulationOverflowTime_le_iff _ N n ω

theorem population_card_le_of_lt_overflowTime
    (F : Filtration ℕ m)
    (R : CausalSelectMechanism ℕ Ω (RootIndexed.TreeNode Root α)
      (fun n => F n))
    (candidates : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (N n : ℕ) (ω : Ω)
    (h : (n : WithTop ℕ) < R.overflowTime F candidates N ω) :
    (R.population candidates n ω).card ≤ N :=
  card_le_of_lt_finsetPopulationOverflowTime _ N n ω h

theorem population_card_gt_of_overflowTime_eq
    (F : Filtration ℕ m)
    (R : CausalSelectMechanism ℕ Ω (RootIndexed.TreeNode Root α)
      (fun n => F n))
    (candidates : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (N n : ℕ) (ω : Ω)
    (h : R.overflowTime F candidates N ω = n) :
    N < (R.population candidates n ω).card :=
  card_gt_of_finsetPopulationOverflowTime_eq _ N n ω h

/-- Multi-root overflow is a stopping time once its size process is observable.
This formulation does not require `Root` or `α` to be countable. -/
theorem overflowTime_isStoppingTime
    (F : Filtration ℕ m)
    (R : CausalSelectMechanism ℕ Ω (RootIndexed.TreeNode Root α)
      (fun n => F n))
    (candidates : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (hcard : ∀ n, Measurable[F n]
      (fun ω => (R.population candidates n ω).card))
    (N : ℕ) :
    IsStoppingTime F (R.overflowTime F candidates N) :=
  populationOverflowTime_isStoppingTime F
    (fun n ω => (↑(R.population candidates n ω) :
      Set (RootIndexed.TreeNode Root α)))
    (fun n => by
      let _ : MeasurableSpace Ω := F n
      have hcoe : Measurable (fun ω =>
          ((R.population candidates n ω).card : ℕ∞)) :=
        (measurable_of_countable (fun k : ℕ => (k : ℕ∞))).comp (hcard n)
      simpa only [encard_coe_finset] using hcoe)
    N

/-- When the multi-root label type is countable, causal selection of adapted
candidates automatically supplies the observable size hypothesis. -/
theorem overflowTime_isStoppingTime_of_countable
    [Countable (RootIndexed.TreeNode Root α)]
    (F : Filtration ℕ m)
    (R : CausalSelectMechanism ℕ Ω (RootIndexed.TreeNode Root α)
      (fun n => F n))
    (candidates : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (hcandidates : ∀ n, Measurable[F n] (candidates n))
    (N : ℕ) :
    IsStoppingTime F (R.overflowTime F candidates N) :=
  populationOverflowTime_isStoppingTime_of_countable F
    (fun n ω => (↑(R.population candidates n ω) :
      Set (RootIndexed.TreeNode Root α)))
    (fun n => by
      let _ : MeasurableSpace Ω := F n
      exact measurable_finset_iff_measurable_set.mp
        (R.measurable_population candidates hcandidates n)) N

end CausalSelectMechanism

end ProbabilityTheory.BranchingRandomWalk.Selection
