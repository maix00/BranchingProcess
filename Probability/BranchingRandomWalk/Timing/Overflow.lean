import Probability.BranchingRandomWalk.Timing.Stopping
import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# First population overflow time

The population is an arbitrary set of labels. Overflow compares its extended
cardinality with the finite capacity `N`, so an infinite population overflows
automatically. No countability or finiteness assumption is built into the
definition.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

variable {Ω ι : Type*} {m : MeasurableSpace Ω}

/-- First generation at which a set-valued population has more than `N`
particles. -/
noncomputable def populationOverflowTime
    (population : ℕ → Ω → Set ι) (N : ℕ) : Ω → WithTop ℕ :=
  firstDeclaredSuccess fun n =>
    {ω | (N : ℕ∞) < (population n ω).encard}

theorem populationOverflowTime_le_iff
    (population : ℕ → Ω → Set ι) (N n : ℕ) (ω : Ω) :
    populationOverflowTime population N ω ≤ n ↔
      ∃ j ≤ n, (N : ℕ∞) < (population j ω).encard :=
  firstDeclaredSuccess_le_iff _ ω n

/-- Before overflow, the extended population cardinality is at most `N`. -/
theorem encard_le_of_lt_populationOverflowTime
    (population : ℕ → Ω → Set ι) (N n : ℕ) (ω : Ω)
    (h : (n : WithTop ℕ) < populationOverflowTime population N ω) :
    (population n ω).encard ≤ N := by
  by_contra hn
  have hover : (N : ℕ∞) < (population n ω).encard := lt_of_not_ge hn
  have hle : populationOverflowTime population N ω ≤ n :=
    (populationOverflowTime_le_iff population N n ω).2 ⟨n, le_rfl, hover⟩
  exact (not_le_of_gt h) hle

/-- At a finite overflow time the population's extended cardinality exceeds
the capacity. -/
theorem encard_gt_of_populationOverflowTime_eq
    (population : ℕ → Ω → Set ι) (N n : ℕ) (ω : Ω)
    (h : populationOverflowTime population N ω = n) :
    (N : ℕ∞) < (population n ω).encard := by
  have hex : ∃ j ≤ n, (N : ℕ∞) < (population j ω).encard :=
    (populationOverflowTime_le_iff population N n ω).1 (by rw [h])
  obtain ⟨j, hjn, hj⟩ := hex
  have hnle : (n : WithTop ℕ) ≤ j := by
    rw [← h]
    exact (populationOverflowTime_le_iff population N j ω).2 ⟨j, le_rfl, hj⟩
  have hnj : n ≤ j := WithTop.coe_le_coe.mp hnle
  have : j = n := Nat.le_antisymm hjn hnj
  simpa [this] using hj

/-- Observable extended population sizes make overflow a stopping time. -/
theorem populationOverflowTime_isStoppingTime
    (F : Filtration ℕ m) (population : ℕ → Ω → Set ι)
    (hencard : ∀ n, Measurable[F n]
      (fun ω => (population n ω).encard))
    (N : ℕ) :
    IsStoppingTime F (populationOverflowTime population N) := by
  apply firstDeclaredSuccess_isStoppingTime F
  intro n
  let _ : MeasurableSpace Ω := F n
  exact measurableSet_setOfPred.2
    ((measurable_of_countable fun k : ℕ∞ => (N : ℕ∞) < k).comp (hencard n))

/-- For countable labels, a measurable set-valued population has measurable
extended cardinality. -/
theorem populationOverflowTime_isStoppingTime_of_countable [Countable ι]
    (F : Filtration ℕ m) (population : ℕ → Ω → Set ι)
    (hpopulation : ∀ n, Measurable[F n] (population n)) (N : ℕ) :
    IsStoppingTime F (populationOverflowTime population N) := by
  apply populationOverflowTime_isStoppingTime F population _ N
  intro n
  let _ : MeasurableSpace Ω := F n
  exact measurable_encard.comp (hpopulation n)

/-- Finset-valued processes embed into the general set-valued overflow
definition. -/
noncomputable def finsetPopulationOverflowTime
    (population : ℕ → Ω → Finset ι) (N : ℕ) : Ω → WithTop ℕ :=
  populationOverflowTime (fun n ω => (↑(population n ω) : Set ι)) N

theorem encard_coe_finset (s : Finset ι) :
    (↑s : Set ι).encard = s.card := by
  rw [Set.encard_eq_coe_toFinset_card]
  simp

theorem finsetPopulationOverflowTime_le_iff
    (population : ℕ → Ω → Finset ι) (N n : ℕ) (ω : Ω) :
    finsetPopulationOverflowTime population N ω ≤ n ↔
      ∃ j ≤ n, N < (population j ω).card := by
  rw [finsetPopulationOverflowTime, populationOverflowTime_le_iff]
  simp only [encard_coe_finset, ENat.natCast_lt_natCast]

theorem card_le_of_lt_finsetPopulationOverflowTime
    (population : ℕ → Ω → Finset ι) (N n : ℕ) (ω : Ω)
    (h : (n : WithTop ℕ) < finsetPopulationOverflowTime population N ω) :
    (population n ω).card ≤ N := by
  rw [finsetPopulationOverflowTime] at h
  have hle := encard_le_of_lt_populationOverflowTime
    (fun n ω => (↑(population n ω) : Set ι)) N n ω h
  simpa only [encard_coe_finset, ENat.natCast_le_natCast] using hle

theorem card_gt_of_finsetPopulationOverflowTime_eq
    (population : ℕ → Ω → Finset ι) (N n : ℕ) (ω : Ω)
    (h : finsetPopulationOverflowTime population N ω = n) :
    N < (population n ω).card := by
  rw [finsetPopulationOverflowTime] at h
  have hgt := encard_gt_of_populationOverflowTime_eq
    (fun n ω => (↑(population n ω) : Set ι)) N n ω h
  simpa only [encard_coe_finset, ENat.natCast_lt_natCast] using hgt

end ProbabilityTheory.BranchingRandomWalk
