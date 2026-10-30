/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Representation.Continuous
public import Mathlib.Probability.Process.HittingTime

/-!
# First passage of a continuous path below a level

## Public declarations

- `ProbabilityTheory.firstPassageLE`: the first time a continuous path
  enters the lower set $(-\infty,a]$ in an ordered value space.
- `ProbabilityTheory.firstPassageLE_eq_sInf`: identifies this path
  specialization of Mathlib's `MeasureTheory.hittingAfter` with its infimum
  over all times at which the path lies in $(-\infty,a]$.
- `ProbabilityTheory.firstPassageBelow`: the first $t\ge0$ with $f(t)\le a$,
  with value $\top$ when the path stays above $a$.
- `ProbabilityTheory.firstPassageAbove`: the corresponding upper-level
  passage, obtained from `firstPassageLE` on `OrderDual ℝ`.
- `ProbabilityTheory.firstPassageAbove_eq_top_iff`: upper passage is infinite
  exactly when every path value remains below $a$.
- `ProbabilityTheory.firstPassageAbove_le_iff`: upper passage occurs by $t$
  exactly when the path reaches $[a,\infty)$ by $t$.
- `ProbabilityTheory.firstPassageBelow_eq_top_iff`: the first passage is
  infinite exactly when every path value exceeds $a$.
- `ProbabilityTheory.firstPassageBelow_attained`: a finite first passage
  time belongs to the closed hitting set.
- `ProbabilityTheory.firstPassageBelow_no_earlier`: every path value strictly
  before the first passage exceeds $a$.
- `ProbabilityTheory.firstPassageBelow_value_eq`: if $f(0)>a$ and the
  first passage is finite, then the path equals $a$ at that time.
- `ProbabilityTheory.firstPassageBelow_le_iff`: the first passage is at
  most $t$ exactly when the path reaches the sublevel by time $t$.

The first-passage time $\tau_x=\inf\{t:W(t)=-x\}$ appears in the proof of
Lemma 2.3 of Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976),
480--485, DOI 10.1214/aop/1176996098. These deterministic lemmas use the
closed sublevel set of a continuous path.
-/

@[expose] public section

open scoped NNReal Classical

namespace ProbabilityTheory

/-- The first time a continuous path enters the order interval
$(-\infty,a]$, with `⊤` when it never enters. -/
noncomputable def firstPassageLE {α : Type*} [TopologicalSpace α] [Preorder α]
    (f : C(ℝ≥0, α)) (a : α) : WithTop ℝ≥0 :=
  MeasureTheory.hittingAfter (fun t (g : C(ℝ≥0, α)) => g t) (Set.Iic a) ⊥ f

/-- The continuous-path specialization of `MeasureTheory.hittingAfter` is
the infimum of the times when the path lies in the lower set. -/
@[simp] theorem firstPassageLE_eq_sInf {α : Type*} [TopologicalSpace α] [Preorder α]
    (f : C(ℝ≥0, α)) (a : α) :
    firstPassageLE f a =
      if ∃ t : ℝ≥0, f t ≤ a then
        ((sInf {t : ℝ≥0 | f t ≤ a} : ℝ≥0) : WithTop ℝ≥0)
      else (⊤ : WithTop ℝ≥0) := by
  simp [firstPassageLE, MeasureTheory.hittingAfter_def]

/-- The first time a continuous real path falls at or below `a`, with
`⊤` when the path never does so. This is the pathwise first-passage time
used in Bolthausen's Lemma 2.3, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, DOI 10.1214/aop/1176996098. -/
noncomputable def firstPassageBelow (f : C(ℝ≥0, ℝ)) (a : ℝ) : WithTop ℝ≥0 :=
  firstPassageLE f a

/-- The first time a continuous real path rises to or above `a`, defined
as a lower-level passage in the order dual of the real line. -/
noncomputable def firstPassageAbove (f : C(ℝ≥0, ℝ)) (a : ℝ) : WithTop ℝ≥0 :=
  firstPassageLE
    (⟨fun t => OrderDual.toDual (f t), f.continuous⟩ : C(ℝ≥0, OrderDual ℝ))
    (OrderDual.toDual a)

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
level-hitting time in Bolthausen's Lemma 2.3, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*,
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

/-- A first passage occurs by `t` exactly when the path reaches the
sublevel set on $[0,t]$. -/
theorem firstPassageBelow_le_iff (f : C(ℝ≥0, ℝ)) (a : ℝ) (t : ℝ≥0) :
    firstPassageBelow f a ≤ t ↔ ∃ u : ℝ≥0, u ≤ t ∧ f u ≤ a := by
  constructor
  · intro hf
    have h : ∃ u : ℝ≥0, f u ≤ a := by
      by_contra hnone
      have htop := (firstPassageBelow_eq_top_iff f a).2 (by
        intro u
        exact lt_of_not_ge (fun hu => hnone ⟨u, hu⟩))
      rw [htop] at hf
      exact (not_le_of_gt (WithTop.coe_lt_top t)) hf
    let τ : ℝ≥0 := sInf {u : ℝ≥0 | f u ≤ a}
    have hτ : f τ ≤ a := firstPassageBelow_attained f a h
    have hτt : τ ≤ t := by
      have hfirst : firstPassageBelow f a = τ := by
        simp only [firstPassageBelow, firstPassageLE_eq_sInf, ite_eq_left h]
        rfl
      rw [hfirst] at hf
      exact WithTop.coe_le_coe.mp hf
    exact ⟨τ, hτt, hτ⟩
  · rintro ⟨u, hut, hua⟩
    have h : ∃ v : ℝ≥0, f v ≤ a := ⟨u, hua⟩
    have hτu : sInf {v : ℝ≥0 | f v ≤ a} ≤ u :=
      csInf_le ⟨0, fun _ _ => bot_le⟩ hua
    rw [firstPassageBelow, firstPassageLE_eq_sInf, ite_eq_left h]
    exact WithTop.coe_le_coe.mpr (hτu.trans hut)

/-- The first upper passage is infinite precisely when the path stays
strictly below the level. The statement is the order-dual form of
`firstPassageBelow_eq_top_iff`. -/
theorem firstPassageAbove_eq_top_iff (f : C(ℝ≥0, ℝ)) (a : ℝ) :
    firstPassageAbove f a = ⊤ ↔ ∀ t : ℝ≥0, f t < a := by
  let g : C(ℝ≥0, OrderDual ℝ) := ⟨fun t => OrderDual.toDual (f t), f.continuous⟩
  have hdef : firstPassageAbove f a = firstPassageLE g (OrderDual.toDual a) := rfl
  rw [hdef]
  by_cases h : ∃ t : ℝ≥0, g t ≤ OrderDual.toDual a
  · have hall : ¬ ∀ t : ℝ≥0, f t < a := by
      intro hstrict
      obtain ⟨t, ht⟩ := h
      exact (not_le.mpr (hstrict t)) ht
    constructor
    · intro htop
      have hne : (↑(sInf {t : ℝ≥0 | g t ≤ OrderDual.toDual a}) : WithTop ℝ≥0) ≠ ⊤ :=
        WithTop.coe_ne_top
      exact False.elim (hne (by simpa [h] using htop))
    · intro hstrict
      exact False.elim (hall hstrict)
  · have hall : ∀ t : ℝ≥0, f t < a := by
      intro t
      exact lt_of_not_ge (fun ht => h ⟨t, ht⟩)
    simp [h, hall]

/-- The first upper passage occurs by `t` exactly when the path enters
`[a,∞)` during $[0,t]$. This uses the lower-passage construction on
`OrderDual ℝ`. -/
theorem firstPassageAbove_le_iff (f : C(ℝ≥0, ℝ)) (a : ℝ) (t : ℝ≥0) :
    firstPassageAbove f a ≤ t ↔ ∃ u : ℝ≥0, u ≤ t ∧ a ≤ f u := by
  let g : C(ℝ≥0, OrderDual ℝ) := ⟨fun u => OrderDual.toDual (f u), f.continuous⟩
  have hclosed : IsClosed {u : ℝ≥0 | g u ≤ OrderDual.toDual a} :=
    isClosed_Iic.preimage g.continuous
  constructor
  · intro hf
    have h : ∃ u : ℝ≥0, g u ≤ OrderDual.toDual a := by
      by_contra hnone
      have htop : firstPassageAbove f a = ⊤ :=
        (firstPassageAbove_eq_top_iff f a).2 (by
          intro u
          exact lt_of_not_ge (fun hu => hnone ⟨u, hu⟩))
      rw [htop] at hf
      exact (not_le_of_gt (WithTop.coe_lt_top t)) hf
    let τ : ℝ≥0 := sInf {u : ℝ≥0 | g u ≤ OrderDual.toDual a}
    have hτ : g τ ≤ OrderDual.toDual a :=
      hclosed.csInf_mem h ⟨0, fun _ _ => bot_le⟩
    have hτt : τ ≤ t := by
      have hfirst : firstPassageAbove f a = τ := by
        change firstPassageLE g (OrderDual.toDual a) = τ
        simp only [firstPassageLE_eq_sInf, ite_eq_left h]
        rfl
      rw [hfirst] at hf
      exact WithTop.coe_le_coe.mp hf
    exact ⟨τ, hτt, hτ⟩
  · rintro ⟨u, hut, hua⟩
    have h : ∃ v : ℝ≥0, g v ≤ OrderDual.toDual a := ⟨u, hua⟩
    have hτu : sInf {v : ℝ≥0 | g v ≤ OrderDual.toDual a} ≤ u :=
      csInf_le ⟨0, fun _ _ => bot_le⟩ hua
    rw [firstPassageAbove, firstPassageLE_eq_sInf, ite_eq_left h]
    exact WithTop.coe_le_coe.mpr (hτu.trans hut)

end ProbabilityTheory

end
