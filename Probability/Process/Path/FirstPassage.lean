/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Continuous

/-!
# First passage of a continuous path below a level

The public definition and theorems in this file are:

- `ProbabilityTheory.firstPassageBelow`: the first $t\ge0$ with $f(t)\le a$,
  with value $\top$ when the path stays above $a$.
- `ProbabilityTheory.firstPassageBelow_eq_top_iff`: the first passage is
  infinite exactly when every path value exceeds $a$.
- `ProbabilityTheory.firstPassageBelow_attained`: a finite first passage
  time belongs to the closed hitting set.
- `ProbabilityTheory.firstPassageBelow_no_earlier`: every path value strictly
  before the first passage exceeds $a$.
- `ProbabilityTheory.firstPassageBelow_value_eq`: if $f(0)>a$ and the
  first passage is finite, then the path equals $a$ at that time.

The first-passage time $\tau_x=\inf\{t:W(t)=-x\}$ appears in the proof of
Lemma 2.3 of Erwin Bolthausen, *On a functional central limit theorem for
random walks conditioned to stay positive*, Ann. Probab. 4(3) (1976),
480--485, DOI 10.1214/aop/1176996098. These deterministic lemmas use the
closed sublevel set of a continuous path.
-/

@[expose] public section

open scoped NNReal Classical

namespace ProbabilityTheory

/-- The first time a continuous real path falls at or below `a`, with
`⊤` when the path never does so. This is the pathwise first-passage time
used in Bolthausen's Lemma 2.3, *On a functional central limit theorem
for random walks conditioned to stay positive*, DOI 10.1214/aop/1176996098. -/
noncomputable def firstPassageBelow (f : C(ℝ≥0, ℝ)) (a : ℝ) : WithTop ℝ≥0 :=
  if ∃ t : ℝ≥0, f t ≤ a then (sInf {t : ℝ≥0 | f t ≤ a} : ℝ≥0) else ⊤

/-- The first passage is infinite precisely when the path stays above
the level at every time. -/
theorem firstPassageBelow_eq_top_iff (f : C(ℝ≥0, ℝ)) (a : ℝ) :
    firstPassageBelow f a = ⊤ ↔ ∀ t : ℝ≥0, a < f t := by
  by_cases h : ∃ t : ℝ≥0, f t ≤ a
  · have hall : ¬ ∀ t : ℝ≥0, a < f t := by
      intro hstrict
      obtain ⟨t, ht⟩ := h
      exact (not_le.mpr (hstrict t)) ht
    constructor
    · intro htop
      have hne : (↑(sInf {t : ℝ≥0 | f t ≤ a}) : WithTop ℝ≥0) ≠ ⊤ :=
        WithTop.coe_ne_top
      exact False.elim (hne (by simpa [firstPassageBelow, h] using htop))
    · intro hstrict
      exact False.elim (hall hstrict)
  · have hall : ∀ t : ℝ≥0, a < f t := by
      intro t
      exact lt_of_not_ge (fun ht => h ⟨t, ht⟩)
    simp [firstPassageBelow, h, hall]

/-- The first passage belongs to the closed sublevel set when that set
is nonempty. -/
theorem firstPassageBelow_attained (f : C(ℝ≥0, ℝ)) (a : ℝ)
    (h : ∃ t : ℝ≥0, f t ≤ a) :
    f (sInf {t : ℝ≥0 | f t ≤ a}) ≤ a := by
  have hclosed : IsClosed {t : ℝ≥0 | f t ≤ a} :=
    isClosed_Iic.preimage f.continuous
  exact hclosed.csInf_mem h ⟨0, fun _ _ => bot_le⟩

/-- Before the first passage every path value is strictly above the
level. -/
theorem firstPassageBelow_no_earlier (f : C(ℝ≥0, ℝ)) (a : ℝ)
    (_h : ∃ t : ℝ≥0, f t ≤ a) {u : ℝ≥0}
    (hu : u < sInf {t : ℝ≥0 | f t ≤ a}) : a < f u := by
  by_contra hle
  exact (not_le.mpr hu) (csInf_le ⟨0, fun _ _ => bot_le⟩
    (show u ∈ {t : ℝ≥0 | f t ≤ a} from le_of_not_gt hle))

/-- A continuous path starting above `a` meets `a` exactly at its first
passage below `a`. Thus the sublevel-set definition agrees with the
level-hitting time in Bolthausen's Lemma 2.3, *On a functional central
limit theorem for random walks conditioned to stay positive*,
DOI 10.1214/aop/1176996098. -/
theorem firstPassageBelow_value_eq (f : C(ℝ≥0, ℝ)) (a : ℝ)
    (h0 : a < f 0) (h : ∃ t : ℝ≥0, f t ≤ a) :
    f (sInf {t : ℝ≥0 | f t ≤ a}) = a := by
  let τ : ℝ≥0 := sInf {t : ℝ≥0 | f t ≤ a}
  have hτ : f τ ≤ a := firstPassageBelow_attained f a h
  rcases lt_or_eq_of_le hτ with hstrict | heq
  · have hbetween : a ∈ Set.Icc (f τ) (f 0) := ⟨hτ, h0.le⟩
    obtain ⟨u, hu, huval⟩ :=
      (intermediate_value_Icc' (show (0 : ℝ≥0) ≤ τ from bot_le)
        f.continuous.continuousOn) hbetween
    have hu_ne : u ≠ τ := by
      intro hueq
      rw [hueq] at huval
      exact (ne_of_lt hstrict) huval
    have hu_lt : u < τ := lt_of_le_of_ne hu.2 hu_ne
    have hbefore := firstPassageBelow_no_earlier f a h hu_lt
    simp only [huval, lt_self_iff_false] at hbefore
  · exact heq

end ProbabilityTheory

end
