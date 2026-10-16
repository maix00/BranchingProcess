/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.AboveStart.FirstWindow.Continuity

/-!
# Shifting a path to its first nonnegative unit window

The public definitions and theorems in this file are:

- `ProbabilityTheory.shiftAtFirstNonnegativeWindowStart`:
  $\Phi(f)(u)=f(T(f)+u)$ when $T(f)<\infty$ and the constant
  path $-1$ otherwise.
- `ProbabilityTheory.shiftAtFirstNonnegativeWindowStartUpTo`:
  the same construction with $T^s(f)$.
- `ProbabilityTheory.measurable_shiftAtFirstNonnegativeWindowStart`:
  the unrestricted shift is Borel measurable.
- `ProbabilityTheory.measurable_shiftAtFirstNonnegativeWindowStartUpTo`:
  the finite-horizon shift is Borel measurable.
- `ProbabilityTheory.continuousAt_shiftAtFirstNonnegativeWindowStart_of_finite`:
  continuity of $T$ at $f$ and $T(f)<\infty$ imply continuity
  of $\Phi$ at $f$.
- `ProbabilityTheory.continuousAt_shiftAtFirstNonnegativeWindowStartUpTo_of_finite`:
  continuity of $T^s$ at $f$ and $T^s(f)<\infty$ imply
  continuity of $\Phi_s$ at $f$.

These are the path maps in Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Lemma 2.5,
Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace ProbabilityTheory

open Filter
open scoped NNReal Topology

/-- Shift to the first unrestricted eligible unit window; use the
constant path $-1$ when the first-window time is infinite. -/
noncomputable def shiftAtFirstNonnegativeWindowStart
    (f : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) :=
  if firstNonnegativeWindowStart f = ⊤ then
    (⟨fun _ => -1, continuous_const⟩ : C(ℝ≥0, ℝ))
  else shiftPath f (firstNonnegativeWindowStart f).untopA

/-- Shift to the first eligible unit window before horizon $s$;
use the constant path $-1$ when that window does not exist. -/
noncomputable def shiftAtFirstNonnegativeWindowStartUpTo
    (f : C(ℝ≥0, ℝ)) (s : ℝ≥0) : C(ℝ≥0, ℝ) :=
  if firstNonnegativeWindowStartUpTo f s = ⊤ then
    (⟨fun _ => -1, continuous_const⟩ : C(ℝ≥0, ℝ))
  else shiftPath f (firstNonnegativeWindowStartUpTo f s).untopA

/-- The unrestricted first-window shift is measurable. -/
theorem measurable_shiftAtFirstNonnegativeWindowStart :
    Measurable shiftAtFirstNonnegativeWindowStart := by
  have hT : Measurable firstNonnegativeWindowStart :=
    measurable_firstNonnegativeWindowStart
  have hshift : Measurable (fun f : C(ℝ≥0, ℝ) =>
      shiftPath f (firstNonnegativeWindowStart f).untopA) :=
    measurable_shiftPath.comp (measurable_id.prodMk hT.untopA)
  unfold shiftAtFirstNonnegativeWindowStart
  exact Measurable.ite (hT (measurableSet_singleton ⊤))
    measurable_const hshift

/-- The first-window shift before a fixed horizon is measurable. -/
theorem measurable_shiftAtFirstNonnegativeWindowStartUpTo (s : ℝ≥0) :
    Measurable (fun f => shiftAtFirstNonnegativeWindowStartUpTo f s) := by
  have hT : Measurable (fun f : C(ℝ≥0, ℝ) =>
      firstNonnegativeWindowStartUpTo f s) :=
    measurable_firstNonnegativeWindowStartUpTo s
  have hshift : Measurable (fun f : C(ℝ≥0, ℝ) =>
      shiftPath f (firstNonnegativeWindowStartUpTo f s).untopA) :=
    measurable_shiftPath.comp (measurable_id.prodMk hT.untopA)
  unfold shiftAtFirstNonnegativeWindowStartUpTo
  exact Measurable.ite (hT (measurableSet_singleton ⊤))
    measurable_const hshift

/-- At a finite first-window time, Bolthausen's shifted path is the
composition of the continuous time-shift map and the first-window
functional. This is the $s=\infty$ step of Lemma 2.5. -/
theorem continuousAt_shiftAtFirstNonnegativeWindowStart_of_finite
    (f : C(ℝ≥0, ℝ))
    (hfinite : firstNonnegativeWindowStart f ≠ ⊤)
    (hcont : ContinuousAt firstNonnegativeWindowStart f) :
    ContinuousAt shiftAtFirstNonnegativeWindowStart f := by
  have htime : ContinuousAt
      (fun g : C(ℝ≥0, ℝ) => (firstNonnegativeWindowStart g).untopA) f :=
    (WithTop.tendsto_untopA hfinite).comp hcont
  have hshift : ContinuousAt
      (fun g : C(ℝ≥0, ℝ) =>
        shiftPath g (firstNonnegativeWindowStart g).untopA) f :=
    continuous_shiftPath.continuousAt.comp
      (continuousAt_id.prodMk htime)
  have hnear : ∀ᶠ g in 𝓝 f,
      firstNonnegativeWindowStart g ≠ ⊤ := by
    have hopen : IsOpen {v : WithTop ℝ≥0 | v ≠ ⊤} :=
      (isClosed_singleton : IsClosed ({⊤} : Set (WithTop ℝ≥0))).isOpen_compl
    exact hcont.eventually (hopen.mem_nhds hfinite)
  apply hshift.congr_of_eventuallyEq
  filter_upwards [hnear] with g hg
  simp [shiftAtFirstNonnegativeWindowStart, hg]

/-- The finite-horizon shifted path is continuous wherever its
first-window time is finite and continuous. -/
theorem continuousAt_shiftAtFirstNonnegativeWindowStartUpTo_of_finite
    (f : C(ℝ≥0, ℝ)) (s : ℝ≥0)
    (hfinite : firstNonnegativeWindowStartUpTo f s ≠ ⊤)
    (hcont : ContinuousAt
      (fun g => firstNonnegativeWindowStartUpTo g s) f) :
    ContinuousAt (fun g => shiftAtFirstNonnegativeWindowStartUpTo g s) f := by
  have htime : ContinuousAt
      (fun g : C(ℝ≥0, ℝ) =>
        (firstNonnegativeWindowStartUpTo g s).untopA) f :=
    (WithTop.tendsto_untopA hfinite).comp hcont
  have hshift : ContinuousAt
      (fun g : C(ℝ≥0, ℝ) =>
        shiftPath g (firstNonnegativeWindowStartUpTo g s).untopA) f :=
    continuous_shiftPath.continuousAt.comp
      (continuousAt_id.prodMk htime)
  have hnear : ∀ᶠ g in 𝓝 f,
      firstNonnegativeWindowStartUpTo g s ≠ ⊤ := by
    have hopen : IsOpen {v : WithTop ℝ≥0 | v ≠ ⊤} :=
      (isClosed_singleton : IsClosed ({⊤} : Set (WithTop ℝ≥0))).isOpen_compl
    exact hcont.eventually (hopen.mem_nhds hfinite)
  apply hshift.congr_of_eventuallyEq
  filter_upwards [hnear] with g hg
  simp [shiftAtFirstNonnegativeWindowStartUpTo, hg]

/-- If the first window lies strictly beyond the horizon cutoff,
the shifted path is locally the constant path $-1$. -/
theorem continuousAt_shiftAtFirstNonnegativeWindowStartUpTo_of_cutoff_lt
    (f : C(ℝ≥0, ℝ)) {s : ℝ≥0} (hs : 1 ≤ s)
    (hcut : (s - 1 : WithTop ℝ≥0) < firstNonnegativeWindowStart f)
    (hcont : ContinuousAt firstNonnegativeWindowStart f) :
    ContinuousAt (fun g => shiftAtFirstNonnegativeWindowStartUpTo g s) f := by
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
  simp [shiftAtFirstNonnegativeWindowStartUpTo, htop]

end ProbabilityTheory

end
