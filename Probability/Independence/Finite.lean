module

public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.Probability.Independence.Basic

/-!
# Extending finite independent families

This file supplies a successor step for mutual independence indexed by
`Fin`. It complements the binary and finite-product interfaces in mathlib.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A finite product lower bound for events whose next event factors from
the preceding prefix. This is the probability-theoretic induction behind
finite independent-block estimates. -/
theorem pow_le_measure_prefix_inter_of_factorization
    (pref nextEvent : ℕ → Set Ω) (q : ENNReal) (n : ℕ)
    (hzero : pref 0 = Set.univ)
    (hrec : ∀ m < n, pref (m + 1) = pref m ∩ nextEvent m)
    (hfactor : ∀ m < n,
      μ (pref m ∩ nextEvent m) = μ (pref m) * μ (nextEvent m))
    (hprob : ∀ m < n, q ≤ μ (nextEvent m)) :
    q ^ n ≤ μ (pref n) := by
  have hbound : ∀ m : ℕ, m ≤ n → q ^ m ≤ μ (pref m) := by
    intro m
    induction m with
    | zero =>
        intro _
        simp [hzero]
    | succ m ih =>
        intro hm
        have hmn : m < n := by omega
        rw [hrec m hmn]
        calc
          q ^ (m + 1) = q * q ^ m := pow_succ' q m
          _ ≤ q * μ (pref m) := by
            simpa [mul_comm] using mul_le_mul_left (ih (by omega)) q
          _ ≤ μ (pref m) * μ (nextEvent m) := by
            have hm' := mul_le_mul_left (hprob m hmn) (μ (pref m))
            simpa [mul_comm] using hm'
          _ = μ (pref m ∩ nextEvent m) := (hfactor m hmn).symm
  exact hbound n le_rfl

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
