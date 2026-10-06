/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.DiracProba
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Weak convergence with a deterministic parameter

This module records the product-measure form of the continuous mapping
theorem when one coordinate is deterministic and converges. It does not
require an additive structure on the other coordinate.
-/

public section

open Filter TopologicalSpace
open scoped Topology

namespace MeasureTheory
namespace ProbabilityMeasure

variable {ι E E' F : Type*} {l : Filter ι}
  [TopologicalSpace E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [PseudoMetrizableSpace E] [SecondCountableTopology E]
  [TopologicalSpace E'] [MeasurableSpace E']
  [OpensMeasurableSpace E'] [PseudoMetrizableSpace E'] [SecondCountableTopology E']
  [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]

/-- If probability measures converge and a deterministic parameter converges,
then the push-forward of their product with the corresponding Dirac measures
converges under every continuous map. This is a Slutsky-type rule that applies
when the first coordinate has no additive structure. -/
theorem tendsto_map_prod_dirac_of_tendsto
    (μs : ι → ProbabilityMeasure E) (μ : ProbabilityMeasure E)
    (hμ : Tendsto μs l (nhds μ))
    (ys : ι → E') (y : E') (hy : Tendsto ys l (nhds y))
    (g : E × E' → F) (hg : Continuous g) :
    Tendsto (fun i => ((μs i).prod (MeasureTheory.diracProba (ys i))).map g)
      l (nhds ((μ.prod (MeasureTheory.diracProba y)).map g)) := by
  have hdirac : Tendsto (fun i => MeasureTheory.diracProba (ys i)) l
      (nhds (MeasureTheory.diracProba y)) := by
    exact MeasureTheory.continuous_diracProba.continuousAt.tendsto.comp hy
  have hprod : Tendsto
      (fun i => (μs i).prod (MeasureTheory.diracProba (ys i))) l
      (nhds (μ.prod (MeasureTheory.diracProba y))) := by
    have hpair : Tendsto (fun i => (μs i, MeasureTheory.diracProba (ys i))) l
        (nhds (μ, MeasureTheory.diracProba y)) := by
      rw [nhds_prod_eq]
      exact hμ.prodMk hdirac
    exact ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp hpair
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hprod hg

end ProbabilityMeasure
end MeasureTheory

end
