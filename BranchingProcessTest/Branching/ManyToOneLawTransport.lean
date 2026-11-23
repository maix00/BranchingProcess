import Probability.BranchingRandomWalk.Spine.Additive.PathLaw
import Probability.BranchingProcess.Spine.Tree.Density.PathPayoff
import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.PointMeasure
import Probability.BranchingRandomWalk.Spine.ManyToOne.GenerationManyToOne
import Probability.BranchingRandomWalk.Spine.StoppingLine.FirstEntrance

open MeasureTheory ProbabilityTheory Combinatorics.Branching
open scoped ENNReal

-- The complete IID trajectory law requires neither measurable singletons
-- nor a standard-Borel state space.
example {E : Type*} [MeasurableSpace E] [AddCommMonoid E] [MeasurableAdd₂ E]
    (ν : Measure E) [IsProbabilityMeasure ν] (x : E) :
    (iidSequenceLaw ν).map (fun ξ n => RandomWalk.positionProcess x n ξ) =
      Kernel.trajMeasure (Measure.dirac x)
        (Kernel.historyKernel (RandomWalk.incrementKernel ν)) :=
  RandomWalk.map_positionProcess_eq_trajMeasure ν x

-- Raw marks need no distinguished zero, ordering, or nonextinction hypothesis.
example {ι E : Type*} [MeasurableSpace E] (φ : Potential E)
    (μ : Measure (Step ι E)) [IsProbabilityMeasure μ] (x : ℝ) :
    (BranchingProcess.offspringFieldLaw μ).map (stateTree (fun x e => x + φ e) x) =
      BranchingProcess.State.treeKernel
        (BranchingRandomWalk.Spine.Additive.offspringKernel φ μ) (some x) :=
  BranchingRandomWalk.Spine.Additive.map_stateTree_law φ μ x

-- The mean-measure formula retains its strictly weaker hypotheses:
-- the outer law need not be a probability and the inner measure can be diffuse.
example {E : Type*} [MeasurableSpace E] {φ : E → ℝ} (hφ : Measurable φ)
    (law : Measure (Measure E)) (hn : RandomMeasure.HasNormalization φ (-1) law)
    (n : ℕ) {F : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) (x : ℝ) :
    BranchingRandomWalk.Spine.pointMeasureWeightedPathIterate φ (-1) law n F x =
      ∫⁻ ξ, F (RandomWalk.history n x ξ)
        ∂iidSequenceLaw (RandomMeasure.tiltedLaw φ (-1) law) :=
  BranchingRandomWalk.Spine.pointMeasureWeightedPathManyToOne hφ law hn n hF x

#print axioms ProbabilityTheory.RandomWalk.map_positionProcess_eq_trajMeasure
#print axioms ProbabilityTheory.BranchingProcess.Spine.lintegral_pathPayoff_eq
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.Additive.map_stateTree_law
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.Additive.harmonic_weight
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.Additive.spineChildKernel_eq_incrementKernel
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.Additive.map_spinePath_law
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.weightedPathManyToOneCore
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.generationManyToOne
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_firstEntranceWeight_eq
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.pointMeasureWeightedPathManyToOne
