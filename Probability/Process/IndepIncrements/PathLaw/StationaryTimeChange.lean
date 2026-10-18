/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Probability.Process.StationaryIncrements.Basic
import Probability.Process.IndepIncrements.FiniteDimensional

/-!
# Path laws under stationary time changes

For a process with independent stationary increments, two monotone
parameterizations with the same elapsed time on every ordered pair induce the
same law on centered paths. In particular, for $s \le t$,
$\tau(t)-\tau(s)=\tau'(t)-\tau'(s)$ implies
$(X_{\tau(q)}-X_{\tau(\bot)})_{q\in I}
\stackrel{d}{=}(X_{\tau'(q)}-X_{\tau'(\bot)})_{q\in I}$.
The index type $I$ is any linearly ordered type with a least element, and the
two centered path maps are assumed almost-everywhere measurable. The time type
is an ordered additive commutative monoid with ordered subtraction.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

/-- Independent-increment processes have the same centered path law under
two monotone time changes whose elapsed times agree on every ordered pair.
No path regularity or process-start assumption is needed. -/
theorem HasIndepIncrements.process_identDistrib_of_sameDuration_timeChanges
    {Time : Type*} [AddCommMonoid Time] [PartialOrder Time] [AddLeftMono Time]
    [ExistsAddOfLE Time] [Sub Time] [OrderedSub Time]
    {Index : Type*} [LinearOrder Index] [OrderBot Index]
    {E : Type*} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd₂ E]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : Time → Ω → E} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : HasIndepIncrements X P)
    (hstationary : HasStationaryIncrements X P)
    (τ τ' : Index → Time) (hτ : Monotone τ) (hτ' : Monotone τ')
    (hduration : ∀ s t : Index, s ≤ t → τ t - τ s = τ' t - τ' s)
    (hYmeas : AEMeasurable
      (fun ω i => X (τ i) ω - X (τ ⊥) ω) P)
    (hY'meas : AEMeasurable
      (fun ω i => X (τ' i) ω - X (τ' ⊥) ω) P) :
    IdentDistrib
      (fun ω i => X (τ i) ω - X (τ ⊥) ω)
      (fun ω i => X (τ' i) ω - X (τ' ⊥) ω) P P := by
  let Y : Index → Ω → E := fun i ω => X (τ i) ω - X (τ ⊥) ω
  let Y' : Index → Ω → E := fun i ω => X (τ' i) ω - X (τ' ⊥) ω
  have hY : HasIndepIncrements Y P := by
    intro n grid hgrid
    let grid' := τ ∘ grid
    have hgrid' : Monotone grid' := hτ.comp hgrid
    simpa [Y, grid', Function.comp_def, sub_sub_sub_cancel_right] using
      h n grid' hgrid'
  have hY' : HasIndepIncrements Y' P := by
    intro n grid hgrid
    let grid' := τ' ∘ grid
    have hgrid' : Monotone grid' := hτ'.comp hgrid
    simpa [Y', grid', Function.comp_def, sub_sub_sub_cancel_right] using
      h n grid' hgrid'
  have hYstart : ∀ᵐ ω ∂P, Y ⊥ ω = 0 := by
    filter_upwards [] with ω
    simp [Y]
  have hY'start : ∀ᵐ ω ∂P, Y' ⊥ ω = 0 := by
    filter_upwards [] with ω
    simp [Y']
  have hYinc (s t : Index) (hst : s ≤ t) :
      IdentDistrib (fun ω => Y t ω - Y s ω)
        (fun ω => Y' t ω - Y' s ω) P P := by
    let d := τ t - τ s
    let d' := τ' t - τ' s
    have hd : d = d' := hduration s t hst
    have hsum : τ s + d = τ t := add_tsub_cancel_of_le (hτ hst)
    have hsum' : τ' s + d' = τ' t := add_tsub_cancel_of_le (hτ' hst)
    have hleft := hstationary (τ s) d
    have hright := hstationary (τ' s) d'
    have hleft' : IdentDistrib (fun ω => Y t ω - Y s ω)
        (fun ω => X d ω - X 0 ω) P P := by
      simpa [Y, hsum, sub_sub_sub_cancel_right] using hleft
    have hright' : IdentDistrib (fun ω => Y' t ω - Y' s ω)
        (fun ω => X d ω - X 0 ω) P P := by
      simpa [Y', hd, hsum', sub_sub_sub_cancel_right] using hright
    exact hleft'.trans hright'.symm
  exact hY.process_identDistrib_of_aemeasurable hY'
    hYstart hY'start hYinc hYmeas hY'meas

end ProbabilityTheory

end
