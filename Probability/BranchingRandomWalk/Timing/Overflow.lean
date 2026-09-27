import Probability.BranchingRandomWalk.Timing.Stopping
import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# First population overflow time

For a finite labelled population process, the first generation whose size is
strictly greater than `N` is a possibly infinite stopping time whenever the
population is adapted. Particle labels and their position space play no role.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

variable {Ω ι : Type*} {m : MeasurableSpace Ω}

/-- First generation at which the finite population contains more than `N`
particles. -/
noncomputable def populationOverflowTime
    (population : ℕ → Ω → Finset ι) (N : ℕ) : Ω → WithTop ℕ :=
  firstDeclaredSuccess fun n => {ω | N < (population n ω).card}

theorem populationOverflowTime_le_iff
    (population : ℕ → Ω → Finset ι) (N n : ℕ) (ω : Ω) :
    populationOverflowTime population N ω ≤ n ↔
      ∃ j ≤ n, N < (population j ω).card :=
  firstDeclaredSuccess_le_iff _ ω n

/-- Before the overflow time every observed population has size at most `N`. -/
theorem card_le_of_lt_populationOverflowTime
    (population : ℕ → Ω → Finset ι) (N n : ℕ) (ω : Ω)
    (h : (n : WithTop ℕ) < populationOverflowTime population N ω) :
    (population n ω).card ≤ N := by
  by_contra hn
  have hover : N < (population n ω).card := Nat.lt_of_not_ge hn
  have hle : populationOverflowTime population N ω ≤ n :=
    (populationOverflowTime_le_iff population N n ω).2 ⟨n, le_rfl, hover⟩
  exact (not_le_of_gt h) hle

/-- At a finite value of the first overflow time the population really exceeds
the capacity. -/
theorem card_gt_of_populationOverflowTime_eq
    (population : ℕ → Ω → Finset ι) (N n : ℕ) (ω : Ω)
    (h : populationOverflowTime population N ω = n) :
    N < (population n ω).card := by
  have hex : ∃ j ≤ n, N < (population j ω).card :=
    (populationOverflowTime_le_iff population N n ω).1 (by rw [h])
  obtain ⟨j, hjn, hj⟩ := hex
  have hnle : (n : WithTop ℕ) ≤ j := by
    rw [← h]
    exact (populationOverflowTime_le_iff population N j ω).2 ⟨j, le_rfl, hj⟩
  have hnj : n ≤ j := WithTop.coe_le_coe.mp hnle
  have : j = n := Nat.le_antisymm hjn hnj
  simpa [this] using hj

/-- The overflow time of an adapted finite population process is a stopping
time for the same generation filtration. -/
theorem populationOverflowTime_isStoppingTime
    (F : Filtration ℕ m) (population : ℕ → Ω → Finset ι)
    (hcard : ∀ n, Measurable[F n] (fun ω => (population n ω).card))
    (N : ℕ) :
    IsStoppingTime F (populationOverflowTime population N) := by
  apply firstDeclaredSuccess_isStoppingTime F
  intro n
  exact measurableSet_lt measurable_const (hcard n)

/-- For countable particle labels, adaptedness of the labelled finite
population implies adaptedness of its cardinality. This is a convenience
corollary; the stopping-time theorem itself only assumes observable sizes and
does not restrict the root or slot types. -/
theorem populationOverflowTime_isStoppingTime_of_countable [Countable ι]
    (F : Filtration ℕ m) (population : ℕ → Ω → Finset ι)
    (hpopulation : ∀ n, Measurable[F n] (population n)) (N : ℕ) :
    IsStoppingTime F (populationOverflowTime population N) := by
  apply populationOverflowTime_isStoppingTime F population _ N
  intro n
  let _ : MeasurableSpace Ω := F n
  have hpop : Measurable (population n) := hpopulation n
  have hset : Measurable (fun ω => (population n ω : Set ι)) :=
    measurable_finset_iff_measurable_set.mp hpop
  have hncard := measurable_ncard.comp hset
  convert hncard using 1
  funext ω
  exact (Set.ncard_coe_finset (population n ω)).symm

end ProbabilityTheory.BranchingRandomWalk
