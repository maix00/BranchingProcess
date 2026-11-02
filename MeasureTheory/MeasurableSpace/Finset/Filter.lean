/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurable filters of finite-set-valued maps

If `F : Ω → Finset α` is measurable and `keep ω a` is measurable in `ω` for
each fixed `a`, then the filtered finite-set-valued map
`ω ↦ {a ∈ F ω | keep ω a}` is measurable. No countability assumption on `α`
is needed.

## Public declarations

* `Measurable.finset_filter` states that if \(F:\Omega\to\operatorname{Finset}(\alpha)\)
  is measurable and each section \(\omega\mapsto keep(\omega,a)\) is
  measurable, then \(\omega\mapsto\{a\in F(\omega):keep(\omega,a)\}\)
  is measurable.
-/

@[expose] public section

namespace MeasureTheory

attribute [local instance] Classical.propDecidable

theorem Measurable.finset_filter
    {Ω α : Type*} [MeasurableSpace Ω] {F : Ω → Finset α}
    (hF : Measurable F) (keep : Ω → α → Prop)
    (hkeep : ∀ a, Measurable (fun ω => keep ω a)) :
    Measurable (fun ω => (F ω).filter (keep ω)) := by
  classical
  rw [measurable_finset_iff]
  intro a
  simp only [Finset.mem_filter]
  exact ((measurable_finset_mem a).comp hF).and (hkeep a)

end MeasureTheory
