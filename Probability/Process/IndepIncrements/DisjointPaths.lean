/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.IndepIncrements.FiniteBlockPaths
public import Mathlib.Probability.Independence.Process.Basic

/-!
# Finite-dimensional independence of disjoint increment paths

Independent increments imply independence of all finitely many sampled
positions, relative to the left endpoint, on two adjacent time intervals.
The finite observation grid is assembled from the two query families and the
three interval endpoints.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- Finite-dimensional paths on consecutive time intervals are independent.
The query families need not be ordered or injective, and may contain the
common endpoint. -/
theorem HasIndepIncrements.indepFun_adjacentPaths_finiteDimensional
    {Time Ω J K : Type*} [LinearOrder Time] [MeasurableSpace Ω]
    [Fintype J] [Fintype K]
    {X : Time → Ω → ℝ} {P : Measure Ω}
    (hX : HasIndepIncrements X P)
    (hXmeas : ∀ t, AEMeasurable (X t) P)
    (a b c : Time) (left : J → Time) (right : K → Time)
    (hleft : ∀ j, a ≤ left j ∧ left j ≤ b)
    (hright : ∀ k, b ≤ right k ∧ right k ≤ c) :
    (fun ω j => X (left j) ω - X a ω) ⟂ᵢ[P]
    (fun ω k => X (right k) ω - X b ω) := by
  classical
  let s : Finset Time :=
    insert a (insert b (insert c
      ((Finset.univ.image left) ∪ (Finset.univ.image right))))
  have ha : a ∈ s := by simp [s]
  have hb : b ∈ s := by simp [s]
  have hc : c ∈ s := by simp [s]
  have hL (j : J) : left j ∈ s := by
    simp [s, Finset.mem_image]
  have hR (k : K) : right k ∈ s := by
    simp [s, Finset.mem_image]
  let a' : s := ⟨a, ha⟩
  let b' : s := ⟨b, hb⟩
  let c' : s := ⟨c, hc⟩
  let left' (j : J) : s := ⟨left j, hL j⟩
  let right' (k : K) : s := ⟨right k, hR k⟩
  have h : (fun ω j => X (left' j) ω - X a' ω) ⟂ᵢ[P]
      (fun ω k => X (right' k) ω - X b' ω) := by
    apply hX.indepFun_finiteObservationQueries hXmeas s
      ⟨a, ha⟩ a' b' c' left' right'
    · intro j
      exact hleft j
    · intro k
      exact hright k
  simpa [a', b', left', right'] using h

/-- The complete increment paths on two consecutive intervals are
independent as function-valued random variables. This follows from the
finite-dimensional result via Mathlib's process independence theorem. -/
theorem HasIndepIncrements.indepFun_adjacentPaths
    {Time Ω S T : Type*} [LinearOrder Time] [MeasurableSpace Ω]
    {X : Time → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (hX : HasIndepIncrements X P)
    (hXmeas : ∀ t, AEMeasurable (X t) P)
    (a b c : Time) (left : S → Time) (right : T → Time)
    (hleft : ∀ i, a ≤ left i ∧ left i ≤ b)
    (hright : ∀ j, b ≤ right j ∧ right j ≤ c) :
    (fun ω i => X (left i) ω - X a ω) ⟂ᵢ[P]
    (fun ω j => X (right j) ω - X b ω) := by
  apply IndepFun.process_indepFun_process₀
    (X := fun i ω => X (left i) ω - X a ω)
    (Y := fun j ω => X (right j) ω - X b ω)
  · intro i
    exact (hXmeas (left i)).sub (hXmeas a)
  · intro j
    exact (hXmeas (right j)).sub (hXmeas b)
  · intro I J
    exact hX.indepFun_adjacentPaths_finiteDimensional hXmeas a b c
      (fun i : I => left i) (fun j : J => right j)
      (fun i => hleft i) (fun j => hright j)

end ProbabilityTheory
