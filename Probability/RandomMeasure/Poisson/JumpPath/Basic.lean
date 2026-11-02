/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Probability.RandomMeasure.Poisson.RandomMeasure.Basic
import Probability.RandomMeasure.Poisson.RandomMeasure.SourceSlots

/-!
# The path of a single selected jump

The large-jump path is a time-indexed integral against the part of a Poisson
random measure in a prescribed mark region. On the event that the region
contains exactly one point, the entire path is a single step function.

For $\mu_\omega=\operatorname{poissonRandomMeasure}(K,X,\omega)$, the path
and its single-point reduction are
$$
J_A(\omega,t)=\int_A \mathbf 1_{\{s\le t\}}x\,\mu_\omega(d(s,x)),
\qquad
J_{J\cup B}(\omega,t)=\mathbf 1_{\{s_p\le t\}}x_p\quad(t\in\mathrm{Time}),
$$
where the second identity holds when $\mu_\omega(J)=1$ and
$\mu_\omega(B)=0$, with $p$ the unique source slot in $J$ and
$(s_p,x_p)=X_p(\omega)$.

## Public declarations

`poissonJumpPath K X A ω t` is the integral over marks in `A` whose time is at
most `t`, for a preordered time type with a measurable space and measurable
singletons. If the realized Poisson random measure assigns mass `1` to a
measurable set `J` and mass `0` to a measurable set `B`,
`poissonJumpPath_eq_singleJump_of_one_zero` produces an observed point in `J`
and identifies the path integrated over `J ∪ B`, simultaneously for every
`t`; the theorem assumes that the time type is nonempty.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The (possibly killed) large-jump contribution from a mark region. -/
noncomputable def poissonJumpPath {Ω Time : Type} [MeasurableSpace Ω]
    [Preorder Time] [MeasurableSpace Time] [MeasurableSingletonClass Time]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → Time × ℝ)
    (A : Set (Time × ℝ)) (ω : Ω) (t : Time) : ℝ :=
  ∫ z in A, if z.1 ≤ t then z.2 else 0 ∂(poissonRandomMeasure K X ω)

/-- A unique point in `J`, with no other point in `B`, gives a single-jump
path simultaneously at every time, without choosing a measurable jump slot. -/
theorem poissonJumpPath_eq_singleJump_of_one_zero
    {Ω Time : Type} [MeasurableSpace Ω] [Preorder Time] [MeasurableSpace Time]
    [MeasurableSingletonClass Time]
    [Nonempty Time]
    {K : ℕ → Ω → ℕ}
    {X : ℕ → ℕ → Ω → Time × ℝ}
    {m : Measure (Time × ℝ)} [SigmaFinite m]
    {J B : Set (Time × ℝ)}
    (hJ : MeasurableSet J) (hB : MeasurableSet B) (ω : Ω)
    (hOne : (poissonRandomMeasure K X ω : Measure (Time × ℝ)) J = 1)
    (hZero : (poissonRandomMeasure K X ω : Measure (Time × ℝ)) B = 0) :
    ∃ p : ℕ × ℕ,
      p.2 < K p.1 ω ∧ X p.1 p.2 ω ∈ J ∧
      ∀ t : Time,
        poissonJumpPath K X (J ∪ B) ω t =
          if (X p.1 p.2 ω).1 ≤ t then (X p.1 p.2 ω).2 else 0 := by
  obtain ⟨p, hpK, hpJ, hmeasure⟩ :=
    poissonRandomMeasure_restrict_union_eq_dirac_of_one_zero
      (m := m) hJ hB ω hOne hZero
  refine ⟨p, hpK, hpJ, ?_⟩
  intro t
  unfold poissonJumpPath
  rw [hmeasure, integral_dirac]

end ProbabilityTheory
