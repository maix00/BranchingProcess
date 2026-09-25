import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.DomainFlow.Space

/-!
# Subtree step fields rooted at finitely many addresses

Selected descendants may belong to different initial roots while still sharing
one pre-sampled product probability space. Equal-length, injectively labelled
roots give a vector of independent subtree step fields.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory


def multiRootSubtreeStepFieldVector
    {m k : ℕ} {X : Type*}
    (roots : Fin k → Fin m × 𝕍) (step : FiniteRootBranchingStepField m X) :
    Fin k → 𝕍 → BranchingStep ℕ X :=
  fun j v => step (roots j).1 ((roots j).2 ++ v)

theorem multiRootBranchingAddresses_injective {m k n : ℕ}
    (roots : Fin k → Fin m × 𝕍)
    (hlen : ∀ j, (roots j).2.length = n)
    (hinj : Function.Injective roots) :
    Function.Injective (fun p : Fin k × 𝕍 =>
      ((roots p.1).1, (roots p.1).2 ++ p.2)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hrootIndex : (roots i).1 = (roots j).1 := (Prod.mk.inj h).1
  have hpath : (roots i).2 ++ a = (roots j).2 ++ b := (Prod.mk.inj h).2
  have hp := congrArg (List.take n) hpath
  have hrootPath : (roots i).2 = (roots j).2 := by
    simpa [hlen i, hlen j] using hp
  have hij : i = j := hinj (Prod.ext hrootIndex hrootPath)
  subst j
  exact Prod.ext rfl (List.append_cancel_left hpath)

theorem fixed_multiRootSubtreeStepFieldVector_law
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ} (roots : Fin k → Fin m × 𝕍)
    (hlen : ∀ j, (roots j).2.length = n)
    (hinj : Function.Injective roots) :
    (finiteRootBranchingStepFieldLaw μ m).map
        (multiRootSubtreeStepFieldVector roots) =
      Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ) := by
  have hflat := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Fin m × 𝕍 => μ)
    (f := fun p : Fin k × 𝕍 =>
      ((roots p.1).1, (roots p.1).2 ++ p.2))
    (multiRootBranchingAddresses_injective roots hlen hinj)
  have hcurrySource := Measure.infinitePi_map_curry
    (μ := fun (_ : Fin m) (_ : 𝕍) => μ)
  have hcurryTarget := Measure.infinitePi_map_curry
    (μ := fun (_ : Fin k) (_ : 𝕍) => μ)
  change (Measure.infinitePi
    (fun _ : Fin m => Measure.infinitePi (fun _ : 𝕍 => μ))).map
    (fun ω j v => ω (roots j).1 ((roots j).2 ++ v)) =
      Measure.infinitePi
        (fun _ : Fin k => Measure.infinitePi (fun _ : 𝕍 => μ))
  rw [← hcurrySource, ← hcurryTarget, ← hflat]
  rw [Measure.map_map, Measure.map_map]
  · rfl
  · exact (MeasurableEquiv.curry (Fin k) 𝕍
      (BranchingStep ℕ X)).measurable
  · apply measurable_pi_iff.mpr
    intro p
    exact measurable_pi_apply ((roots p.1).1, (roots p.1).2 ++ p.2)
  · apply measurable_pi_iff.mpr
    intro j
    apply measurable_pi_iff.mpr
    intro v
    exact (measurable_pi_apply ((roots j).2 ++ v)).comp
      (measurable_pi_apply (roots j).1)
  · exact (MeasurableEquiv.curry (Fin m) 𝕍
      (BranchingStep ℕ X)).measurable

theorem multiRootSubtreeStepFieldVector_measurable
    {m k : ℕ} {X : Type*} [MeasurableSpace X]
    (roots : Fin k → Fin m × 𝕍) :
    Measurable (multiRootSubtreeStepFieldVector (X := X) roots) := by
  apply measurable_pi_iff.mpr
  intro j
  apply measurable_pi_iff.mpr
  intro v
  exact (measurable_pi_apply ((roots j).2 ++ v)).comp
    (measurable_pi_apply (roots j).1)

end ProbabilityTheory.BranchingRandomWalk
