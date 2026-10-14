/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Continuous
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

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
- `ProbabilityTheory.isClosed_hasPassageBefore`: the set of paths reaching
  the sublevel $(-\infty,a]$ by a fixed time is closed.
- `ProbabilityTheory.firstPassageBelow_le_iff`: the first passage is at
  most $t$ exactly when the path reaches the sublevel by time $t$.
- `ProbabilityTheory.measurable_firstPassageBelow`: the first-passage map
  to $[0,\infty]$ is Borel measurable.

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

/-- The paths that reach the closed sublevel set by a fixed time form a
closed subset of continuous-path space. The time interval is compact,
so projection of the closed path-time hitting set is closed. -/
theorem isClosed_hasPassageBefore (t : ℝ≥0) (a : ℝ) :
    IsClosed {f : C(ℝ≥0, ℝ) | ∃ u : ℝ≥0, u ≤ t ∧ f u ≤ a} := by
  let K := Set.Icc (0 : ℝ≥0) t
  let E : Set (C(ℝ≥0, ℝ) × K) := {p | p.1 (p.2 : ℝ≥0) ≤ a}
  have hE : IsClosed E := by
    have hcont : Continuous (fun p : C(ℝ≥0, ℝ) × K => p.1 (p.2 : ℝ≥0)) := by
      fun_prop
    exact isClosed_Iic.preimage hcont
  have hclosed : IsClosed ((Prod.fst : C(ℝ≥0, ℝ) × K → C(ℝ≥0, ℝ)) '' E) :=
    isClosedMap_fst_of_compactSpace E hE
  convert hclosed using 1
  ext f
  constructor
  · rintro ⟨u, hut, hfa⟩
    exact ⟨(f, ⟨u, ⟨bot_le, hut⟩⟩), hfa, rfl⟩
  · rintro ⟨⟨g, u⟩, hga, hgf⟩
    change g = f at hgf
    subst g
    exact ⟨u, u.2.2, hga⟩

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
        simp only [firstPassageBelow, ite_eq_left h]
        rfl
      rw [hfirst] at hf
      exact WithTop.coe_le_coe.mp hf
    exact ⟨τ, hτt, hτ⟩
  · rintro ⟨u, hut, hua⟩
    have h : ∃ v : ℝ≥0, f v ≤ a := ⟨u, hua⟩
    have hτu : sInf {v : ℝ≥0 | f v ≤ a} ≤ u :=
      csInf_le ⟨0, fun _ _ => bot_le⟩ hua
    rw [firstPassageBelow, ite_eq_left h]
    exact WithTop.coe_le_coe.mpr (hτu.trans hut)

/-- The first-passage time of a continuous path is Borel measurable.
The sublevel event at time $t$ is the closed hitting-by-$t$ event. -/
theorem measurable_firstPassageBelow (a : ℝ) :
    Measurable (fun f : C(ℝ≥0, ℝ) => firstPassageBelow f a) := by
  apply measurable_of_Iic
  intro x
  cases x with
  | top => simp
  | coe t =>
      have hset : {f : C(ℝ≥0, ℝ) | firstPassageBelow f a ≤ t} =
          {f | ∃ u : ℝ≥0, u ≤ t ∧ f u ≤ a} := by
        ext f
        exact firstPassageBelow_le_iff f a t
      simpa only [Set.preimage, Set.mem_Iic, Set.mem_ofPred_eq] using
        (hset ▸ (isClosed_hasPassageBefore t a).measurableSet)

end ProbabilityTheory

end
