module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

public section

/-!
# Basic operations on convergence in distribution

Cofinal reindexing and eventual almost-everywhere replacement for random
variables converging in distribution.
-/

open Filter ProbabilityTheory
open scoped Topology

namespace MeasureTheory

variable {I E Ω' : Type*} {Ω : I → Type*}
  {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : I) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {mE : MeasurableSpace E} [TopologicalSpace E] [OpensMeasurableSpace E]
  {X : (i : I) → Ω i → E} {Z : Ω' → E} {l : Filter I}

/-- Convergence in distribution is preserved by a cofinal reindexing. -/
theorem TendstoInDistribution.comp_tendsto
    (h : TendstoInDistribution X l Z μ μ')
    {J : Type*} {g : J → I} {l' : Filter J} (hg : Tendsto g l' l) :
    TendstoInDistribution (fun j => X (g j)) l' Z
      (fun j => μ (g j)) μ' where
  forall_aemeasurable j := h.forall_aemeasurable (g j)
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.comp hg

/-- Changing the approximating random variables almost everywhere at only an
eventually cofinal set of indices preserves convergence in distribution. -/
theorem TendstoInDistribution.congr_eventually
    {Y : (i : I) → Ω i → E}
    (h : TendstoInDistribution X l Z μ μ')
    (hXY : ∀ᶠ i in l, X i =ᵐ[μ i] Y i)
    (hY : ∀ i, AEMeasurable (Y i) (μ i)) :
    TendstoInDistribution Y l Z μ μ' where
  forall_aemeasurable := hY
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.congr' <| hXY.mono fun i hi => by
    apply Subtype.ext
    exact Measure.map_congr hi

/-- Convergence in distribution is unchanged when the approximating random
variables eventually have exactly the same laws.  Unlike
`TendstoInDistribution.congr_eventually`, this does not require the variables
to live on the same coupling almost everywhere. -/
theorem TendstoInDistribution.congr_map_eventually
    {Y : (i : I) → Ω i → E}
    (h : TendstoInDistribution X l Z μ μ')
    (hXY : ∀ᶠ i in l, (μ i).map (X i) = (μ i).map (Y i))
    (hY : ∀ i, AEMeasurable (Y i) (μ i)) :
    TendstoInDistribution Y l Z μ μ' where
  forall_aemeasurable := hY
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.congr' <| hXY.mono fun i hi => by
    apply Subtype.ext
    exact hi

/-- Replace the realization of the limiting law by any random variable with
the same distribution. -/
theorem TendstoInDistribution.congr_limit
    {Omega'' : Type*} [MeasurableSpace Omega'']
    {μ'' : Measure Omega''} [IsProbabilityMeasure μ'']
    {Z' : Omega'' → E}
    (h : TendstoInDistribution X l Z μ μ')
    (hZ' : AEMeasurable Z' μ'')
    (hlaw : μ'.map Z = μ''.map Z') :
    TendstoInDistribution X l Z' μ μ'' where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := hZ'
  tendsto := by
    convert h.tendsto using 1
    exact congrArg nhds (Subtype.ext hlaw.symm)

/-- Replace the limiting random variable by a supplied realization of its
law. -/
theorem TendstoInDistribution.congr_limit_hasLaw
    {Omega'' : Type*} [MeasurableSpace Omega'']
    {μ'' : Measure Omega''} [IsProbabilityMeasure μ'']
    {Z' : Omega'' → E}
    (h : TendstoInDistribution X l Z μ μ')
    (hZ' : HasLaw Z' (μ'.map Z) μ'') :
    TendstoInDistribution X l Z' μ μ'' :=
  h.congr_limit hZ'.aemeasurable hZ'.map_eq.symm

end MeasureTheory
