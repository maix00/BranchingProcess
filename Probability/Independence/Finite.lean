import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.Probability.Independence.Basic

/-!
# Extending finite independent families

This file supplies a successor step for mutual independence indexed by
`Fin`. It complements the binary and finite-product interfaces in mathlib.
-/

open MeasureTheory

namespace ProbabilityTheory

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A finite independent family remains mutually independent after appending
one random variable that is independent of the entire preceding vector. -/
theorem iIndepFun.finSucc {n : ℕ} {X : Fin (n + 1) → Ω → E}
    (hX : ∀ i, AEMeasurable (X i) μ)
    (hprev : iIndepFun (fun i : Fin n => X i.castSucc) μ)
    (hlast : IndepFun (fun (ω : Ω) (i : Fin n) => X i.castSucc ω)
      (X (Fin.last n)) μ) :
    iIndepFun X μ := by
  rw [iIndepFun_iff_map_fun_eq_pi_map hX]
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => E) (Fin.last n)
  apply e.map_measurableEquiv_injective
  rw [AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable
    (AEMeasurable.of_eval hX)]
  change μ.map (fun ω => (X (Fin.last n) ω,
    fun j : Fin n => X ((Fin.last n).succAbove j) ω)) = _
  rw [Fin.succAbove_last]
  have hjoint := hlast.symm.map_prod_eq_prod_map_map
    (hX (Fin.last n))
    (AEMeasurable.of_eval fun (i : Fin n) => hX i.castSucc)
  change μ.map (fun ω => (X (Fin.last n) ω,
      fun j : Fin n => X j.castSucc ω)) =
    (μ.map (X (Fin.last n))).prod
      (μ.map (fun (ω : Ω) (j : Fin n) => X j.castSucc ω)) at hjoint
  rw [hjoint]
  have hprevLaw :=
    (iIndepFun_iff_map_fun_eq_pi_map
      (fun (i : Fin n) => hX i.castSucc)).1 hprev
  change μ.map (fun (ω : Ω) (j : Fin n) => X j.castSucc ω) =
    Measure.pi (fun j : Fin n => μ.map (X j.castSucc)) at hprevLaw
  rw [hprevLaw]
  simpa only [e, Fin.succAbove_last] using
    (measurePreserving_piFinSuccAbove
      (fun i : Fin (n + 1) => μ.map (X i)) (Fin.last n)).map_eq.symm

end ProbabilityTheory
