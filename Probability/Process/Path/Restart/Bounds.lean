/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Order.Interval.Set.Basic
public import Probability.Process.Path.Restart.Basic

/-!
# Endpoint bounds from restarted windows

## Public declarations

- `ProbabilityTheory.Process.Path.endpoint_sub_start_le_of_inRestartedWindows`:
  for an additively ordered commutative group `E`, if
  `path k - path (restartAnchor cutoff k) ≤ upper k` for each `k`, then
  `path n - path 0 ≤ upper n` through the cutoff and
  `path n - path 0 ≤ upper cutoff + upper n` afterwards.

In one formula, the endpoint estimate is
`\(x_n-x_0\le u_n\)` when `\(n\le c\), and
`\(x_n-x_0\le u_c+u_n\)` when `\(c<n\), assuming
`\(x_k-x_{r_c(k)}\le u_k\)` for each `k`.
-/

@[expose] public section

namespace ProbabilityTheory.Process.Path

/-- In an additively ordered commutative group, upper bounds on each restarted
displacement give an upper bound on the displacement from the initial point to
the endpoint. -/
theorem endpoint_sub_start_le_of_inRestartedWindows
    {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
    {n : ℕ} (cutoff : ℕ) (window : ℕ → Set E) (upper : ℕ → E)
    (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (path : Fin (n + 1) → E)
    (hpath : InRestartedWindows cutoff window path) :
    path ⟨n, Nat.lt_succ_self n⟩ - path ⟨0, by omega⟩ ≤
      if n ≤ cutoff then upper n else upper cutoff + upper n := by
  let i0 : Fin (n + 1) := ⟨0, by omega⟩
  let iEnd : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
  change path iEnd - path i0 ≤ _
  by_cases hn : n ≤ cutoff
  · have hbound : path iEnd - path i0 ≤ upper n := by
      have h := hupper n (hpath iEnd)
      have hanchor :
          (⟨restartAnchor cutoff n,
            by have h := restartAnchor_le cutoff n; omega⟩ : Fin (n + 1)) = i0 := by
        apply Fin.ext
        simp [i0, restartAnchor_eq_zero hn]
      simpa [iEnd, hanchor] using h
    simpa [hn] using hbound
  · have hstrict : cutoff < n := Nat.lt_of_not_ge hn
    let iCutoff : Fin (n + 1) := ⟨cutoff, by omega⟩
    have hEndBound : path iEnd - path iCutoff ≤ upper n := by
      have h := hupper n (hpath iEnd)
      have hanchor :
          (⟨restartAnchor cutoff n,
            by have h := restartAnchor_le cutoff n; omega⟩ : Fin (n + 1)) =
            iCutoff := by
        apply Fin.ext
        simp [iCutoff, restartAnchor_eq_cutoff hstrict]
      simpa [iEnd, hanchor] using h
    have hCutoffBound : path iCutoff - path i0 ≤ upper cutoff := by
      have h := hupper cutoff (hpath iCutoff)
      have hanchor :
          (⟨restartAnchor cutoff cutoff,
            by have h := restartAnchor_le cutoff cutoff; omega⟩ :
              Fin (n + 1)) = i0 := by
        apply Fin.ext
        simp [i0, restartAnchor]
      rw [hanchor] at h
      simpa [iCutoff, i0] using h
    have hdecomp : path iEnd - path i0 =
        (path iEnd - path iCutoff) + (path iCutoff - path i0) := by
      exact (sub_add_sub_cancel (path iEnd) (path iCutoff) (path i0)).symm
    rw [ite_eq_right hn]
    calc
      path iEnd - path i0 =
          (path iEnd - path iCutoff) + (path iCutoff - path i0) := hdecomp
      _ = (path iCutoff - path i0) + (path iEnd - path iCutoff) := by ac_rfl
      _ ≤ upper cutoff + upper n := add_le_add hCutoffBound hEndBound

end ProbabilityTheory.Process.Path
