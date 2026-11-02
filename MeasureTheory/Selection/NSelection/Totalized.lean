/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Selection.NSelection.Admissible
public import Combinatorics.Selection.NSelection.Mechanism.Infinite.Totalized
public import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# Measurability of totalized first-N selection

## Public declarations

For countable labels, measurable candidate fibres, and measurable pairwise
key comparisons, the totalized first-\(N\) selector is a measurable map into
finite sets:

\[
\operatorname{Measurable}\!\left(
\omega\mapsto
\operatorname{selectFirstNFromSetTotalized}(N,v,A,\omega)\right).
\]

- `Combinatorics.Selection.NSelection.measurable_selectFirstNFromSetTotalized`:
  when labels are countable, the candidate set is measurable, and all
  pairwise key comparisons are measurable, the totalized first-`N` selector
  is a measurable finite-set-valued map.
-/

open MeasureTheory

@[expose] public section

namespace Combinatorics.Selection.NSelection

variable {Ω ι Value : Type*}

theorem measurable_selectFirstNFromSetTotalized
    [MeasurableSpace Ω]
    [Countable ι] [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : Ω → ι → Value) (candidates : Ω → Set ι)
    (hcandidates : Measurable candidates)
    (hkey : ∀ p q : ι, Measurable fun ω =>
      valueKey (value ω) q < valueKey (value ω) p) :
    Measurable fun ω => selectFirstNFromSetTotalized N value candidates ω := by
  classical
  rw [measurable_finset_iff]
  intro p
  simp_rw [mem_selectFirstNFromSetTotalized_iff]
  have hgood : Measurable fun ω => IsLowerFiniteBy (value ω) (candidates ω) :=
    measurableSet_setOfPred.mp
      (measurableSet_lowerFiniteDomain value candidates hcandidates hkey)
  have hmem : Measurable fun ω => p ∈ candidates ω :=
    (measurable_set_mem p).comp hcandidates
  let lower : Ω → Set ι := fun ω =>
    {q | q ∈ candidates ω ∧ valueKey (value ω) q < valueKey (value ω) p}
  have hlower : Measurable lower := by
    rw [measurable_set_iff]
    intro q
    exact ((measurable_set_mem q).comp hcandidates).and (hkey p q)
  have hfinite : Measurable fun ω => (lower ω).Finite := by
    apply measurableSet_setOfPred.mp
    exact MeasurableSet.setOfPred_finite.preimage hlower
  have hncard : Measurable fun ω => (lower ω).ncard := measurable_ncard.comp hlower
  exact hgood.and (hmem.and
    (hfinite.and ((measurable_of_countable (fun k : ℕ => k < N)).comp hncard)))


end Combinatorics.Selection.NSelection
