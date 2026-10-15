# Random-walk small deviations

The folders here are organized by the event being estimated.

| Folder | Event and principal entry point |
| --- | --- |
| `Mogulskii` | A walk stays in a fixed or time-dependent corridor. The stable-domain framework also contains the finite-variance case. For finite-variance horizontal tubes, start with `Mogulskii/Stable/RandomWalkBounds/FromIncrementLaw/HorizontalTube.lean`. |
| `Drawdown` | The running maximum minus the current walk stays bounded. This is a small-deviation question for the drawdown process. The finite-variance upper estimate is in `Drawdown/FiniteVarianceUpper.lean`. |
| `DriftedTube` | A walk stays between linearly moving boundaries. The two finite-variance endpoint lower bounds of Wang Yiyang's Lemma 3.5 are in `DriftedTube/FiniteVarianceLower/EndpointBounds.lean`. The `Staircase`, `Binning`, and `Blocks` directories contain its proof components. |
| `Entrance` | Transition estimates into a corridor, shared by several small-deviation arguments. `RobustExponentialBudget.lean` supplies the entrance factor used by the tilted-tube endpoint bounds. |
| `HorizontalTube` | Upper bounds for a fixed horizontal corridor. |

The conditioned Brownian-meander input to the entrance estimate is in
`Probability/Process/RandomWalk/FunctionalLimit/Conditioned`. Its finite-variance
survival factor uses the coefficient recurrence in
`Probability/Process/RandomWalk/Fluctuation/SparreAndersen`.
`Entrance/Rotation` groups a separate reusable cyclic-rotation method used by
`Entrance/NormalDomain.lean`.
