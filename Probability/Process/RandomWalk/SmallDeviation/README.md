# Random-walk small deviations

The folders here are organized by the event being estimated.

| Folder | Event and principal entry point |
| --- | --- |
| `Mogulskii` | A walk stays in a fixed or time-dependent corridor. The stable-domain framework also contains the finite-variance case. For finite-variance horizontal tubes, start with `Mogulskii/Stable/RandomWalkBounds/FromIncrementLaw/HorizontalTube/Basic.lean`; sampled and inverse-scale forms are in `Scales.lean`, and endpoint windows are in `EndpointWindow.lean`. Reusable irregular-time scale interpolation is in `Analysis/Asymptotics/Scale/Sampling.lean`; the theorem-specific source-corridor definitions and comparisons are grouped under `HorizontalTube/Lemmas/`. |
| `Drawdown` | The running maximum minus the current walk stays bounded. This is a small-deviation question for the drawdown process. The finite-variance upper estimate is in `Drawdown/FiniteVarianceUpper/Basic.lean`. |
| `DriftedTube` | A walk stays between linearly moving boundaries. The two finite-variance endpoint lower bounds formalizing Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.5, are in `DriftedTube/FiniteVarianceLower/EndpointBounds.lean`. The theorem-specific staircase proof is in `FiniteVarianceLower/Lemmas/Staircase/`, including its binning and block-assembly steps. Reusable real-width and block estimates are in `HorizontalTube/RealWidthLower.lean` and `HorizontalTube/Blocks/`; moving-tube inclusion is in `DriftedTube/BlockInclusion.lean`. `EndpointEvent.lean`, `Reflection.lean`, and `FiniteVarianceLower/BlockSchedule.lean` own the reusable event, symmetry, and block schedule. |
| `Entrance` | Transition estimates into a corridor, shared by several small-deviation arguments. `Robust/PowerAssembly.lean` exposes the general power-bound assembly, while `Robust/Lemmas/` holds its fixed-window geometric steps. The drifted-tube theorem-specific entrance budget is under `DriftedTube/FiniteVarianceLower/Lemmas/Staircase/Concrete/EntranceBudget.lean`. |
| `HorizontalTube` | Upper bounds for a fixed horizontal corridor and the reusable finite-variance lower bound with an interior endpoint window. |

The conditioned Brownian-meander input to the entrance estimate is in
`Probability/Process/RandomWalk/FunctionalLimit/Conditioned/Meander/` and
`.../Transition/`. Its finite-variance survival factor uses the finite IID
cyclic-rotation inequality in
`Probability/Process/RandomWalk/Fluctuation/SparreAndersen/Rotation/Probability.lean`.
The separate coefficient recurrence in that directory gives a stronger general
survival-power estimate and is not an input to the Lemma 3.5 entrance bound.
`Entrance/Rotation` groups a separate reusable cyclic-rotation method used by
`Entrance/NormalDomain.lean`.
