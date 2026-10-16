/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.AboveStart.FirstWindow.Shift

/-!
# Centered first-window paths

The public definitions and theorems in this file are:

- `ProbabilityTheory.centeredFirstWindowShift`:
  $f\mapsto(t\mapsto f(T(f)+t)-f(T(f)))$ when $T(f)<\infty$,
  and the constant path $-1$ otherwise.
- `ProbabilityTheory.centeredFirstWindowShiftUpTo`:
  the same map with $T^s(f)$.
- `ProbabilityTheory.measurable_centeredFirstWindowShift` and
  `ProbabilityTheory.measurable_centeredFirstWindowShiftUpTo`:
  both path maps are Borel measurable.
- `ProbabilityTheory.centeredFirstWindowShiftUpTo_eq_of_finite`:
  when $T^s(f)<\infty$, the finite and unrestricted centered shifts agree.
- `ProbabilityTheory.eventually_centeredFirstWindowShiftUpTo_eq`:
  when $T(f)<\infty$, these centered shifts agree for all sufficiently
  large integer cutoffs.
- `ProbabilityTheory.continuousAt_centeredFirstWindowShift_of_finite` and
  `ProbabilityTheory.continuousAt_centeredFirstWindowShiftUpTo_of_finite`:
  continuity at paths with finite first-window times and continuous
  first-window-time functionals.

The displayed map $\Phi_s(f)(t)=f(T^s(f)+t)$ in Erwin Bolthausen,
*On a functional central limit theorem for random walks conditioned to
stay positive*, p. 482, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098, is implemented separately as
`shiftAtFirstNonnegativeWindowStartUpTo`. The centered map here is the
path transform required by the centered random-walk block $Z_k$
in Lemma 3.1, equation (3.2), and by the limit
$W(T+t)-W(T)$ stated on p. 484.
-/

@[expose] public section

namespace ProbabilityTheory

open Filter
open scoped NNReal Topology

/-- Rebase the first eligible unit window at its starting height. -/
noncomputable def centeredFirstWindowShift
    (f : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) :=
  if firstNonnegativeWindowStart f = ⊤ then
    (⟨fun _ => -1, continuous_const⟩ : C(ℝ≥0, ℝ))
  else shiftToZero f (firstNonnegativeWindowStart f).untopA

/-- Rebase the first eligible unit window before a fixed horizon. -/
noncomputable def centeredFirstWindowShiftUpTo
    (f : C(ℝ≥0, ℝ)) (s : ℝ≥0) : C(ℝ≥0, ℝ) :=
  if firstNonnegativeWindowStartUpTo f s = ⊤ then
    (⟨fun _ => -1, continuous_const⟩ : C(ℝ≥0, ℝ))
  else shiftToZero f (firstNonnegativeWindowStartUpTo f s).untopA

/-- The centered unrestricted first-window path is measurable. -/
theorem measurable_centeredFirstWindowShift :
    Measurable centeredFirstWindowShift := by
  have hT : Measurable firstNonnegativeWindowStart :=
    measurable_firstNonnegativeWindowStart
  have hshift : Measurable (fun f : C(ℝ≥0, ℝ) =>
      shiftToZero f (firstNonnegativeWindowStart f).untopA) :=
    measurable_shiftToZero.comp (measurable_id.prodMk hT.untopA)
  unfold centeredFirstWindowShift
  exact Measurable.ite (hT (measurableSet_singleton ⊤))
    measurable_const hshift

/-- The centered first-window path before a fixed horizon is measurable. -/
theorem measurable_centeredFirstWindowShiftUpTo (s : ℝ≥0) :
    Measurable (fun f => centeredFirstWindowShiftUpTo f s) := by
  have hT : Measurable (fun f : C(ℝ≥0, ℝ) =>
      firstNonnegativeWindowStartUpTo f s) :=
    measurable_firstNonnegativeWindowStartUpTo s
  have hshift : Measurable (fun f : C(ℝ≥0, ℝ) =>
      shiftToZero f (firstNonnegativeWindowStartUpTo f s).untopA) :=
    measurable_shiftToZero.comp (measurable_id.prodMk hT.untopA)
  unfold centeredFirstWindowShiftUpTo
  exact Measurable.ite (hT (measurableSet_singleton ⊤))
    measurable_const hshift

/-- A finite first eligible window before the cutoff gives the same
centered path as the unrestricted first eligible window. -/
theorem centeredFirstWindowShiftUpTo_eq_of_finite
    (f : C(ℝ≥0, ℝ)) (s : ℝ≥0)
    (hfinite : firstNonnegativeWindowStartUpTo f s ≠ ⊤) :
    centeredFirstWindowShiftUpTo f s = centeredFirstWindowShift f := by
  have htime := firstNonnegativeWindowStartUpTo_eq_first_of_ne_top
    f s hfinite
  have hfirstfinite : firstNonnegativeWindowStart f ≠ ⊤ := by
    rw [← htime]
    exact hfinite
  simp [centeredFirstWindowShiftUpTo, centeredFirstWindowShift,
    hfirstfinite, htime]

/-- On a path with a finite first eligible window, every sufficiently
large finite-horizon centered shift agrees with the unrestricted shift. -/
theorem eventually_centeredFirstWindowShiftUpTo_eq
    (f : C(ℝ≥0, ℝ))
    (hfinite : firstNonnegativeWindowStart f ≠ ⊤) :
    ∀ᶠ n : ℕ in atTop,
      centeredFirstWindowShiftUpTo f ((n : ℝ≥0) + 1) =
        centeredFirstWindowShift f := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hfinite
  obtain ⟨N, hN⟩ := exists_nat_ge t
  filter_upwards [eventually_ge_atTop N] with n hn
  have hbound : t + 1 ≤ (n : ℝ≥0) + 1 := by
    gcongr
    exact hN.trans (by exact_mod_cast hn)
  have heq := firstNonnegativeWindowStartUpTo_eq_first_of_le
    f ht.symm hbound
  apply centeredFirstWindowShiftUpTo_eq_of_finite
  rw [heq]
  exact WithTop.coe_ne_top

/-- Continuity of the first-window time at a path with a finite first
window implies continuity of its centered first-window path. -/
theorem continuousAt_centeredFirstWindowShift_of_finite
    (f : C(ℝ≥0, ℝ))
    (hfinite : firstNonnegativeWindowStart f ≠ ⊤)
    (hcont : ContinuousAt firstNonnegativeWindowStart f) :
    ContinuousAt centeredFirstWindowShift f := by
  have htime : ContinuousAt
      (fun g : C(ℝ≥0, ℝ) => (firstNonnegativeWindowStart g).untopA) f :=
    (WithTop.tendsto_untopA hfinite).comp hcont
  have hshift : ContinuousAt
      (fun g : C(ℝ≥0, ℝ) =>
        shiftToZero g (firstNonnegativeWindowStart g).untopA) f :=
    continuous_shiftToZero.continuousAt.comp
      (continuousAt_id.prodMk htime)
  have hnear : ∀ᶠ g in 𝓝 f,
      firstNonnegativeWindowStart g ≠ ⊤ := by
    have hopen : IsOpen {v : WithTop ℝ≥0 | v ≠ ⊤} :=
      (isClosed_singleton : IsClosed ({⊤} : Set (WithTop ℝ≥0))).isOpen_compl
    exact hcont.eventually (hopen.mem_nhds hfinite)
  apply hshift.congr_of_eventuallyEq
  filter_upwards [hnear] with g hg
  simp [centeredFirstWindowShift, hg]

/-- The centered finite-horizon shift is continuous when its first-window
time is finite and continuous at the path. -/
theorem continuousAt_centeredFirstWindowShiftUpTo_of_finite
    (f : C(ℝ≥0, ℝ)) (s : ℝ≥0)
    (hfinite : firstNonnegativeWindowStartUpTo f s ≠ ⊤)
    (hcont : ContinuousAt
      (fun g => firstNonnegativeWindowStartUpTo g s) f) :
    ContinuousAt (fun g => centeredFirstWindowShiftUpTo g s) f := by
  have htime : ContinuousAt
      (fun g : C(ℝ≥0, ℝ) =>
        (firstNonnegativeWindowStartUpTo g s).untopA) f :=
    (WithTop.tendsto_untopA hfinite).comp hcont
  have hshift : ContinuousAt
      (fun g : C(ℝ≥0, ℝ) =>
        shiftToZero g (firstNonnegativeWindowStartUpTo g s).untopA) f :=
    continuous_shiftToZero.continuousAt.comp
      (continuousAt_id.prodMk htime)
  have hnear : ∀ᶠ g in 𝓝 f,
      firstNonnegativeWindowStartUpTo g s ≠ ⊤ := by
    have hopen : IsOpen {v : WithTop ℝ≥0 | v ≠ ⊤} :=
      (isClosed_singleton : IsClosed ({⊤} : Set (WithTop ℝ≥0))).isOpen_compl
    exact hcont.eventually (hopen.mem_nhds hfinite)
  apply hshift.congr_of_eventuallyEq
  filter_upwards [hnear] with g hg
  simp [centeredFirstWindowShiftUpTo, hg]

/-- Beyond the horizon cutoff, the centered shift is locally the
constant sentinel path. -/
theorem continuousAt_centeredFirstWindowShiftUpTo_of_cutoff_lt
    (f : C(ℝ≥0, ℝ)) {s : ℝ≥0} (hs : 1 ≤ s)
    (hcut : (s - 1 : WithTop ℝ≥0) < firstNonnegativeWindowStart f)
    (hcont : ContinuousAt firstNonnegativeWindowStart f) :
    ContinuousAt (fun g => centeredFirstWindowShiftUpTo g s) f := by
  have hnear : ∀ᶠ g in 𝓝 f,
      (s - 1 : WithTop ℝ≥0) < firstNonnegativeWindowStart g :=
    hcont.eventually (isOpen_Ioi.mem_nhds hcut)
  have hconst : ContinuousAt
      (fun _ : C(ℝ≥0, ℝ) =>
        (⟨fun _ => -1, continuous_const⟩ : C(ℝ≥0, ℝ))) f :=
    continuousAt_const
  apply hconst.congr_of_eventuallyEq
  filter_upwards [hnear] with g hg
  have htop := firstNonnegativeWindowStartUpTo_eq_top_of_cutoff_lt g hs hg
  simp [centeredFirstWindowShiftUpTo, htop]

end ProbabilityTheory

end
