# Random-walk small deviations

The folders here are organized by the event being estimated.

| Folder | Event and principal entry point |
| --- | --- |
| `Mogulskii` | A walk stays in a fixed or time-dependent corridor. The stable-domain framework also contains the finite-variance case. For finite-variance horizontal tubes, start with `Mogulskii/Stable/RandomWalkBounds/FromIncrementLaw/HorizontalTube.lean`. |
| `Drawdown` | The running maximum minus the current walk stays bounded. This is a small-deviation question for the drawdown process. The finite-variance upper estimate is in `Drawdown/FiniteVarianceUpper.lean`. |
| `DriftedTube` | A walk stays between linearly moving boundaries. The two finite-variance endpoint lower bounds of Wang Yiyang's Lemma 3.5 are in `DriftedTube/FiniteVarianceLower/EndpointBounds.lean`. Its `Lemmas/Staircase/` directory holds the lemma-specific staircase assembly. `Binning/` and `Blocks/` retain the reusable real-width, conditional-block, and moving-tube inclusion estimates; `EndpointEvent.lean`, `Reflection.lean`, and `BlockSchedule.lean` own the reusable events, symmetry, and finite block schedule. |
| `Entrance` | Transition estimates into a corridor, shared by several small-deviation arguments. `Robust/ExponentialBudget.lean` contains the private fixed-window estimate and supplies the entrance factor used by the tilted-tube endpoint bounds; `Robust/PowerAssembly.lean` exposes the general power-bound assembly, while `Robust/Lemmas/` holds its fixed-window geometric steps. |
| `HorizontalTube` | Upper bounds for a fixed horizontal corridor and the reusable finite-variance lower bound with an interior endpoint window. |

The conditioned Brownian-meander input to the entrance estimate is in
`Probability/Process/RandomWalk/FunctionalLimit/Conditioned`. Its finite-variance
survival factor uses the finite IID cyclic-rotation inequality in
`Probability/Process/RandomWalk/Fluctuation/SparreAndersen/RotationProbability.lean`.
The separate coefficient recurrence in that directory gives a stronger general
survival-power estimate and is not an input to the Lemma 3.5 entrance bound.
`Entrance/Rotation` groups a separate reusable cyclic-rotation method used by
`Entrance/NormalDomain.lean`.
