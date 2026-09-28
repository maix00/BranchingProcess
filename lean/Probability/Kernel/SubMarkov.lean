import Mathlib.Probability.Kernel.Defs

/-!
# Sub-Markov kernels

A sub-Markov kernel has total mass at most one at every source point.  The
missing mass is interpreted as killing.  Markov kernels are the mass-one
special case.
-/

open MeasureTheory Set

namespace ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A kernel is sub-Markov when every measure in its image has mass at most
one. -/
class IsSubMarkovKernel (κ : Kernel α β) : Prop where
  measure_univ_le_one : ∀ a, κ a univ ≤ 1

namespace IsSubMarkovKernel

variable {κ : Kernel α β}

theorem measure_le_one [hκ : IsSubMarkovKernel κ] (a : α) (s : Set β) :
    κ a s ≤ 1 :=
  (measure_mono (subset_univ s)).trans (hκ.measure_univ_le_one a)

instance (priority := 90) isFiniteKernel [hκ : IsSubMarkovKernel κ] :
    IsFiniteKernel κ :=
  ⟨1, ENNReal.one_lt_top, hκ.measure_univ_le_one⟩

end IsSubMarkovKernel

instance isSubMarkovKernel_zero : IsSubMarkovKernel (0 : Kernel α β) where
  measure_univ_le_one a := by simp

/-- Every Markov kernel is sub-Markov. -/
instance (priority := 100) IsMarkovKernel.isSubMarkovKernel
    {κ : Kernel α β} [hκ : IsMarkovKernel κ] : IsSubMarkovKernel κ where
  measure_univ_le_one a := by
    let _ := hκ.isProbabilityMeasure a
    simp

/-- A sub-Markov kernel is Markov exactly when no mass is killed. -/
theorem isMarkovKernel_iff_measure_univ_eq_one
    (κ : Kernel α β) [IsSubMarkovKernel κ] :
    IsMarkovKernel κ ↔ ∀ a, κ a univ = 1 := by
  constructor
  · intro hκ a
    let _ := hκ.isProbabilityMeasure a
    simp
  · intro hmass
    exact ⟨fun a => ⟨hmass a⟩⟩

end ProbabilityTheory
