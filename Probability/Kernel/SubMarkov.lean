import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap

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

/-- Restricting the possible target states of a sub-Markov kernel is a
measurable state selection and remains sub-Markov.  For a Markov kernel, the
mass removed by this restriction is exactly the killing probability. -/
instance IsSubMarkovKernel.restrict {s : Set β} (κ : Kernel α β)
    [IsSubMarkovKernel κ] (hs : MeasurableSet s) :
    IsSubMarkovKernel (κ.restrict hs) where
  measure_univ_le_one a := by
    rw [Kernel.restrict_apply' κ hs a MeasurableSet.univ, Set.univ_inter]
    exact IsSubMarkovKernel.measure_le_one a s

/-- Reindexing the source of a sub-Markov kernel preserves its mass bound. -/
instance IsSubMarkovKernel.comap {γ : Type*} [MeasurableSpace γ]
    (κ : Kernel α β) [IsSubMarkovKernel κ]
    (g : γ → α) (hg : Measurable g) :
    IsSubMarkovKernel (κ.comap g hg) where
  measure_univ_le_one c :=
    IsSubMarkovKernel.measure_univ_le_one (κ := κ) (g c)

/-- Restricting the target of a sub-Markov kernel along a measurable
embedding preserves its mass bound. -/
instance IsSubMarkovKernel.comapRight {γ : Type*} [MeasurableSpace γ]
    {f : γ → β} (κ : Kernel α β) [IsSubMarkovKernel κ]
    (hf : MeasurableEmbedding f) :
    IsSubMarkovKernel (κ.comapRight hf) where
  measure_univ_le_one a := by
    rw [Kernel.comapRight_apply' κ hf a MeasurableSet.univ]
    simpa only [Set.image_univ] using
      IsSubMarkovKernel.measure_le_one (κ := κ) a (Set.range f)

/-- Composition preserves sub-Markov kernels. -/
instance IsSubMarkovKernel.comp {γ : Type*} [MeasurableSpace γ]
    (η : Kernel β γ) (κ : Kernel α β)
    [IsSubMarkovKernel η] [IsSubMarkovKernel κ] :
    IsSubMarkovKernel (η ∘ₖ κ) where
  measure_univ_le_one a := by
    rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ]
    calc
      (∫⁻ b, η b univ ∂κ a) ≤ ∫⁻ _b, 1 ∂κ a :=
        lintegral_mono fun b => IsSubMarkovKernel.measure_le_one b univ
      _ = κ a univ := by simp
      _ ≤ 1 := IsSubMarkovKernel.measure_univ_le_one a

/-- Every iterate of a sub-Markov transition kernel remains sub-Markov. -/
instance IsSubMarkovKernel.pow (κ : Kernel α α) [IsSubMarkovKernel κ]
    (n : ℕ) : IsSubMarkovKernel (κ ^ n) := by
  induction n with
  | zero =>
      simp only [pow_zero]
      refine ⟨fun a => ?_⟩
      change Kernel.id a univ ≤ 1
      rw [Kernel.id_apply]
      simp
  | succ n ih =>
      rw [pow_succ]
      change IsSubMarkovKernel ((κ ^ n) ∘ₖ κ)
      exact IsSubMarkovKernel.comp (κ ^ n) κ

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
