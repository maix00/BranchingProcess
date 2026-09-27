import Probability.BranchingRandomWalk.Spine.FiniteKernel
import Probability.BranchingRandomWalk.Spine.TiltedSlot
import Probability.BranchingRandomWalk.Spine.TiltedLaw
import Probability.BranchingRandomWalk.Spine.IncrementProcess
import Probability.BranchingRandomWalk.Spine.EndpointManyToOne
import Probability.BranchingRandomWalk.Spine.EndpointRealization
import Probability.BranchingRandomWalk.Spine.Generation
import Probability.BranchingRandomWalk.Spine.GenerationBranching
import Probability.BranchingRandomWalk.Spine.GenerationManyToOne
import Probability.BranchingRandomWalk.Spine.Path
import Probability.BranchingRandomWalk.Spine.RandomWalk
import Probability.BranchingRandomWalk.Spine.TruncatedWeights

/-!
# Spine and tilted-kernel algebra

Finite-kernel algebra, truncated child weights, conditional tilted slot laws,
the integrated tilted potential law, and its iterated endpoint identities.
The tilted product law is packaged as a single-root `RandomWalk`, canonically
realized as a `PUnit`-slot branching random walk.
-/
