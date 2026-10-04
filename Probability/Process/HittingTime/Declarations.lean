/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Probability.Process.HittingTime

/-!
# First declared success times

A sequence of success events determines a possibly infinite first time. If
each event is observable at its generation, this time is a stopping time.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The first index at which a sequence of declarations holds, or `⊤` if
there is no such index. -/
noncomputable def firstDeclaredSuccess (success : ℕ → Set Ω) : Ω → WithTop ℕ := by
  classical
  exact hittingAfter (fun n ω => if ω ∈ success n then (1 : ℝ) else 0)
    (Set.Ici 1) 0

/-- The finite-time event is exactly the union of declarations seen so far. -/
theorem firstDeclaredSuccess_le_iff (success : ℕ → Set Ω) (ω : Ω) (n : ℕ) :
    firstDeclaredSuccess success ω ≤ n ↔
      ∃ j : ℕ, j ≤ n ∧ ω ∈ success j := by
  classical
  unfold firstDeclaredSuccess
  convert (hittingAfter_le_iff
    (u := fun k x => if x ∈ success k then (1 : ℝ) else 0)
    (s := Set.Ici 1) (n := 0) (i := n) (ω := ω)) using 1
  simp only [Set.mem_Icc, zero_le, true_and, Set.mem_Ici]
  constructor
  · rintro ⟨j, hj, hs⟩
    exact ⟨j, hj, by simp [hs]⟩
  · rintro ⟨j, hj, h⟩
    have hs : ω ∈ success j := by
      by_contra hn
      simp [hn] at h
      norm_num at h
    exact ⟨j, hj, hs⟩

/-- A finite first-success value records success at that index and failure at
every earlier index. -/
theorem firstDeclaredSuccess_eq_iff (success : ℕ → Set Ω) (ω : Ω) (k : ℕ) :
    firstDeclaredSuccess success ω = k ↔
      ω ∈ success k ∧ ∀ j < k, ω ∉ success j := by
  constructor
  · intro heq
    have hle : firstDeclaredSuccess success ω ≤ k := by simp [heq]
    obtain ⟨j, hjk, hj⟩ :=
      (firstDeclaredSuccess_le_iff success ω k).mp hle
    have hnotEarlier : ∀ i < k, ω ∉ success i := by
      intro i hik hi
      have hτi : firstDeclaredSuccess success ω ≤ i :=
        (firstDeclaredSuccess_le_iff success ω i).mpr ⟨i, le_rfl, hi⟩
      rw [heq] at hτi
      exact (Nat.not_le_of_lt hik) (WithTop.coe_le_coe.mp hτi)
    have hjk' : j = k := by
      by_contra hne
      have hjlt : j < k := by omega
      exact hnotEarlier j hjlt hj
    exact ⟨hjk' ▸ hj, hnotEarlier⟩
  · rintro ⟨hk, hnotEarlier⟩
    apply le_antisymm
    · exact (firstDeclaredSuccess_le_iff success ω k).mpr ⟨k, le_rfl, hk⟩
    · by_contra hnot
      have hlt : firstDeclaredSuccess success ω < k := lt_of_not_ge hnot
      have hfinite : firstDeclaredSuccess success ω ≠ ⊤ := by
        intro htop
        rw [htop] at hlt
        exact (not_lt_of_ge le_top) hlt
      obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp hfinite
      have hjlt : j < k := by
        apply WithTop.coe_lt_coe.mp
        rw [hj]
        exact hlt
      have hτj : firstDeclaredSuccess success ω ≤ j := by
        calc
          firstDeclaredSuccess success ω = (j : WithTop ℕ) := hj.symm
          _ ≤ (j : WithTop ℕ) := le_rfl
      obtain ⟨i, hij, hi⟩ :=
        (firstDeclaredSuccess_le_iff success ω j).mp hτj
      exact hnotEarlier i (hij.trans_lt hjlt) hi

/-- If each declaration is measurable at its generation, the first
declaration time is a stopping time. -/
theorem firstDeclaredSuccess_isStoppingTime (F : Filtration ℕ m)
    (success : ℕ → Set Ω)
    (hmeasure : ∀ n, MeasurableSet[F n] (success n)) :
    IsStoppingTime F (firstDeclaredSuccess success) := by
  classical
  unfold firstDeclaredSuccess
  have hadapted : Adapted F
      (fun n ω => if ω ∈ success n then (1 : ℝ) else 0) := by
    intro n
    exact measurable_const.ite (hmeasure n) measurable_const
  exact hadapted.isStoppingTime_hittingAfter measurableSet_Ici

/-- A declaration made after a random stopping time remains a stopping time
when the observable at each generation is adapted. -/
theorem firstSuccessAfterStopping_isStoppingTime (F : Filtration ℕ m)
    (start : Ω → WithTop ℕ) (hstart : IsStoppingTime F start)
    (observable : ℕ → Ω → ℝ) (hadapted : Adapted F observable)
    (threshold : ℝ) :
    IsStoppingTime F
      (firstDeclaredSuccess (fun n =>
        {ω | start ω ≤ n ∧ threshold ≤ observable n ω})) := by
  apply firstDeclaredSuccess_isStoppingTime F
  intro n
  exact (hstart n).inter ((hadapted n) measurableSet_Ici)

end ProbabilityTheory

end
