import Probability.RandomMeasure.Poisson.Integral

open MeasureTheory
open scoped ENNReal

-- The measure-valued map and its nonnegative integrals require no point in `E`.
example {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hK : ∀ k, Measurable (K k)) (hX : ∀ k n, Measurable (X k n)) :
    Measurable (ProbabilityTheory.poissonRandomMeasure K X) :=
  ProbabilityTheory.measurable_poissonRandomMeasure hK hX

example {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hK : ∀ k, Measurable (K k)) (hX : ∀ k n, Measurable (X k n)) :
    Measurable (fun ω =>
      ∫⁻ _, (⊤ : ℝ≥0∞) ∂(ProbabilityTheory.poissonRandomMeasure K X ω)) :=
  ProbabilityTheory.measurable_lintegral_poissonRandomMeasure hK hX measurable_const

-- A configuration with no realized points contributes zero.
example {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (X : ℕ → ℕ → Ω → E) (ω : Ω) {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂(ProbabilityTheory.poissonRandomMeasure (fun _ _ => 0) X ω) = 0 := by
  rw [ProbabilityTheory.lintegral_poissonRandomMeasure hg ω]
  simp

-- A deterministic one-point configuration integrates `g` to its value at that point.
example {E : Type} [MeasurableSpace E] (x : E) {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g y ∂(ProbabilityTheory.poissonRandomMeasure
      (fun k (_ : Unit) => if k = 0 then 1 else 0)
      (fun _ _ _ => x) ()) = g x := by
  rw [ProbabilityTheory.lintegral_poissonRandomMeasure hg ()]
  simp

-- Campbell's formula needs neither finite intensity nor finite integral assumptions.
example {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : ProbabilityTheory.IsPoissonPointFamily K X m P)
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, ∫⁻ x, g x ∂(ProbabilityTheory.poissonRandomMeasure K X ω) ∂P
      = ∫⁻ x, g x ∂m :=
  ProbabilityTheory.lintegral_lintegral_poissonRandomMeasure hd hg

-- The real-valued integral API retains the original almost-sure integrability assumption.
example {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : ProbabilityTheory.IsPoissonPointFamily K X m P)
    {f : E → ℝ} (hf : Measurable f)
    (hrealized : ∀ᵐ ω ∂P,
      Integrable f (ProbabilityTheory.poissonRandomMeasure K X ω)) :
    AEMeasurable (fun ω =>
      ∫ x, f x ∂(ProbabilityTheory.poissonRandomMeasure K X ω)) P :=
  hd.aemeasurable_integral_poissonRandomMeasure hf hrealized

#check ProbabilityTheory.bind_poissonRandomMeasure_eq_intensity
#check ProbabilityTheory.hasSum_pieceSum_poissonRandomMeasure
#check ProbabilityTheory.integral_poissonRandomMeasure_eq_tsum_pieceSum
