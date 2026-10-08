/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.IndepIncrements.FiniteBlockPaths
public import Mathlib.Probability.Independence.Process.Basic
public import Probability.Independence.Finite

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

/-- The translated paths on finitely many consecutive time intervals are
mutually independent. The path coordinates may be any countable family of
observation times inside each interval, provided the distinguished coordinate
`q₀` is the left endpoint. The proof iterates the adjacent-process
independence theorem, retaining the whole preceding path family at each step. -/
theorem HasIndepIncrements.iIndepFun_finiteAdjacentPaths
    {Time Ω J : Type*} [LinearOrder Time] [MeasurableSpace Ω] [Countable J]
    {X : Time → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (hX : HasIndepIncrements X P)
    (hXmeas : ∀ t, AEMeasurable (X t) P)
    (n : ℕ) (t : ℕ → Time) (ht : Monotone t) (q₀ : J)
    (τ : ℕ → J → Time)
    (hleft : ∀ i < n, ∀ q, t i ≤ τ i q)
    (hright : ∀ i < n, ∀ q, τ i q ≤ t (i + 1))
    (hstart : ∀ i < n, τ i q₀ = t i) :
    iIndepFun
      (fun (i : Fin n) (ω : Ω) (q : J) =>
        X (τ i.val q) ω - X (t i.val) ω) P := by
  induction n with
  | zero => exact iIndepFun.of_subsingleton
  | succ n ih =>
      let Y : Fin (n + 1) → Ω → (J → ℝ) := fun i ω q =>
        X (τ i.val q) ω - X (t i.val) ω
      have hprev : iIndepFun (fun (i : Fin n) => Y i.castSucc) P := by
        simpa [Y] using ih
          (fun i hi q => hleft i (lt_trans hi (Nat.lt_succ_self n)) q)
          (fun i hi q => hright i (lt_trans hi (Nat.lt_succ_self n)) q)
          (fun i hi => hstart i (lt_trans hi (Nat.lt_succ_self n)))
      let past : Ω → (Fin n × J → ℝ) := fun ω ij =>
        X (τ ij.1.val ij.2) ω - X (t 0) ω
      let last : Ω → (J → ℝ) := fun ω q =>
        X (τ n q) ω - X (t n) ω
      have htimePast : ∀ ij : Fin n × J,
          t 0 ≤ τ ij.1.val ij.2 ∧ τ ij.1.val ij.2 ≤ t n := by
        rintro ⟨i, q⟩
        have hi : i.val < n + 1 := lt_trans i.isLt (Nat.lt_succ_self n)
        constructor
        · exact (ht (Nat.zero_le i.val)).trans (hleft i.val hi q)
        · exact (hright i.val hi q).trans (ht (Nat.succ_le_of_lt i.isLt))
      have htimeLast : ∀ q : J,
          t n ≤ τ n q ∧ τ n q ≤ t (n + 1) := by
        intro q
        exact ⟨hleft n (Nat.lt_succ_self n) q,
          hright n (Nat.lt_succ_self n) q⟩
      have hadj := hX.indepFun_adjacentPaths hXmeas (t 0) (t n) (t (n + 1))
        (fun ij : Fin n × J => τ ij.1.val ij.2) (τ n) htimePast htimeLast
      let rebase : (Fin n × J → ℝ) → (Fin n → J → ℝ) := fun z i q =>
        z (i, q) - z (i, q₀)
      have hrebase : Measurable rebase := by
        rw [measurable_pi_iff]
        intro i
        rw [measurable_pi_iff]
        intro q
        exact (measurable_pi_apply (i, q)).sub
          (measurable_pi_apply (i, q₀))
      have hlast :
          (fun ω (i : Fin n) => Y i.castSucc ω) ⟂ᵢ[P] Y (Fin.last n) := by
        have h := hadj.comp hrebase measurable_id
        convert h using 1
        · funext ω i q
          have hsi : τ i.val q₀ = t i.val :=
            hstart i.val (lt_trans i.isLt (Nat.lt_succ_self n))
          simp [rebase, Y, hsi]
        · rfl
      have hYmeas : ∀ i, AEMeasurable (Y i) P := by
        intro i
        apply AEMeasurable.of_eval
        intro q
        exact (hXmeas (τ i.val q)).sub (hXmeas (t i.val))
      exact iIndepFun.finSucc hYmeas hprev hlast

end ProbabilityTheory
