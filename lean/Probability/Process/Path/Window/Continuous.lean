/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Continuous
public import Mathlib.Topology.Order.Monotone

/-!
# Windows above their starting level on a continuous path

The public definition and theorems in this file are:

- `ProbabilityTheory.IsNonnegativeWindowStart`: for a continuous path $f$,
  $f(t+u)\ge f(t)$ for every $u\in[0,1]$.
- `ProbabilityTheory.isClosed_nonnegativeWindowStarts`: the set of such
  starting times is closed.
- `ProbabilityTheory.exists_earliestNonnegativeWindowStart`: if this set
  is nonempty, it has a least element.
- `ProbabilityTheory.firstNonnegativeWindowStart`: the earliest eligible
  time, with value $\infty$ when there is no eligible time.
- `ProbabilityTheory.firstNonnegativeWindowStart_eq_coe_iff`:
  $T(f)=t<\infty$ precisely when $t$ is an eligible start and no
  earlier start is eligible.

These are deterministic ingredients of the first-window time $T^s$ in
Erwin Bolthausen, *On a functional central limit theorem for random walks
conditioned to stay positive*, Section 2, Lemmas 2.1 and 2.4,
Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open scoped NNReal

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

/-- A length-one window of a continuous path lies above its initial value. -/
def IsNonnegativeWindowStart (f : C(ℝ≥0, ℝ)) (t : ℝ≥0) : Prop :=
  ∀ u : Set.Icc (0 : ℝ≥0) 1, f t ≤ f (t + u)

/-- For a fixed continuous path, eligible window starting times form a
closed set. This supplies the attainment of the first eligible time. -/
theorem isClosed_nonnegativeWindowStarts (f : C(ℝ≥0, ℝ)) :
    IsClosed {t : ℝ≥0 | IsNonnegativeWindowStart f t} := by
  have hset : {t : ℝ≥0 | IsNonnegativeWindowStart f t} =
      ⋂ u : Set.Icc (0 : ℝ≥0) 1,
        {t | f t ≤ f (t + u)} := by
    ext t
    simp [IsNonnegativeWindowStart]
  rw [hset]
  apply isClosed_iInter
  intro u
  exact isClosed_le f.continuous
    (f.continuous.comp (continuous_id.add continuous_const))

/-- A nonempty closed family of eligible starts has a first member. -/
theorem exists_earliestNonnegativeWindowStart
    (f : C(ℝ≥0, ℝ))
    (h : ∃ t : ℝ≥0, IsNonnegativeWindowStart f t) :
    ∃ t : ℝ≥0, IsNonnegativeWindowStart f t ∧
      ∀ s : ℝ≥0, IsNonnegativeWindowStart f s → t ≤ s := by
  let starts : Set ℝ≥0 := {t | IsNonnegativeWindowStart f t}
  have hnonempty : starts.Nonempty := h
  have hclosed : IsClosed starts := isClosed_nonnegativeWindowStarts f
  have hbelow : BddBelow starts := ⟨0, fun _ _ => bot_le⟩
  exact ⟨sInf starts, hclosed.csInf_mem hnonempty hbelow,
    fun s hs => csInf_le hbelow hs⟩

/-- First length-one window above its starting level; the value is
infinite if the path has no such window. This is $T=T^\infty$ in
Bolthausen, Section 2, equation (2.1). -/
noncomputable def firstNonnegativeWindowStart
    (f : C(ℝ≥0, ℝ)) : WithTop ℝ≥0 :=
  if _h : ∃ t : ℝ≥0, IsNonnegativeWindowStart f t then
    (sInf {t | IsNonnegativeWindowStart f t} : ℝ≥0)
  else ⊤

/-- The finite value of the first-window time is characterized by
eligibility and minimality. -/
theorem firstNonnegativeWindowStart_eq_coe_iff
    (f : C(ℝ≥0, ℝ)) (t : ℝ≥0) :
    firstNonnegativeWindowStart f = t ↔
      IsNonnegativeWindowStart f t ∧
        ∀ s : ℝ≥0, IsNonnegativeWindowStart f s → t ≤ s := by
  classical
  unfold firstNonnegativeWindowStart
  split_ifs with h
  · let starts : Set ℝ≥0 := {x | IsNonnegativeWindowStart f x}
    have hnonempty : starts.Nonempty := h
    have hclosed : IsClosed starts := isClosed_nonnegativeWindowStarts f
    have hbelow : BddBelow starts := ⟨0, fun _ _ => bot_le⟩
    constructor
    · intro heq
      have ht : sInf starts = t := WithTop.coe_injective heq
      constructor
      · exact ht ▸ hclosed.csInf_mem hnonempty hbelow
      · intro s hs
        rw [← ht]
        exact csInf_le hbelow hs
    · rintro ⟨ht, hmin⟩
      congr 1
      apply le_antisymm
      · exact csInf_le hbelow ht
      · exact le_csInf hnonempty fun s hs => hmin s hs
  · constructor
    · intro heq
      exact False.elim (WithTop.coe_ne_top heq.symm)
    · rintro ⟨ht, _⟩
      exact False.elim (h ⟨t, ht⟩)

end ProbabilityTheory

end
