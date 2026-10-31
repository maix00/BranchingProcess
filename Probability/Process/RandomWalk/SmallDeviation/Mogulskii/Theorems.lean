/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Gaussian.FiniteVariance
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Rate.Energy
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.FromIncrementLaw.Normal.ContinuousBoundary
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.FromIncrementLaw.Normal.Domain
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.FromIncrementLaw.Normal.FiniteVariance
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.FromIncrementLaw.Stable.Domain
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.PathClass.Rate
public import Probability.Process.Stable.SmallDeviation.PathClass.StepCorridor.Rate

/-!
# Main theorem entry points for Mogul'skii small deviations

This is the Lean import entry point for the main results in A. A. Mogul'skii,
“Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755–765; English translation, “Small Deviations in
a Space of Trajectories,” *Theory of Probability and Its Applications* 19(4)
(1975), 726–736, DOI 10.1137/1119081. The theorem numbers below refer to the
1974 Russian original.

## Public declarations

**Formalization status.** This is the Lean import entry for A. A. Mogul'skii's
four theorems. Its imports make the formalized interfaces for Theorems 1–3
available to clients, and the entries below give their source formulas, Lean
declarations, and hypotheses. Theorem 4 is not a proved Lean declaration yet;
its source statement and missing proof interfaces are recorded in
`docs/MOGULSKII_PROCESS_THEOREM_4_PROOF_ROUTE.md`.

* **Theorem 1, equation (15):** the discrete random-walk small-deviation rate
  in the stable domain of attraction. For $0<\alpha\le2$,
  $0<F_\alpha(0)<1$, $x_n\to\infty$, $x_n/B(n)\to0$, and $G\in\mathfrak M$,
  its source formula is
  $\log\mathbb P(s_n(\cdot)\in G)\sim C H_\alpha(G)n x_n^{-\alpha}L^*(x_n)$.
  Here $C<0$ depends only on the stable law $F_\alpha$.
  The Lean path-class APIs state this under their explicit relative
  approximation and measurability hypotheses. The stable-index range `0 < α < 2` is
  exposed from raw increment-law assumptions by
  `Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.FromIncrementLaw.Stable.Domain`;
  the normal-domain index-two branch is in
  `Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.FromIncrementLaw.Normal.Domain`.
  The path-class theorem and its explicit approximation and measurability
  hypotheses are stated by
  `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_discreteStepCorridorRates`, with raw-source wrappers in
  `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.exists_source_relative_pathClass_rates_of_rawSource`.
  The declaration-level interface is also available in
  `Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.PathClass.Rate`.
* **Theorem 2, equation (16):** the corresponding rate for a strictly stable
  process. For $0<F_\alpha(0)<1$ and $G\in\mathfrak M$, its source formula
  (with the same negative $C$ as Theorem 1) is
  $\log\mathbb P(\varepsilon^{-1}\xi(\cdot)\in G)\sim
  C H_\alpha(G)\varepsilon^{-\alpha}$ as $\varepsilon\downarrow0$.
  Its `M₂`, `M₃`, and approximation-class declarations are
  `ProbabilityTheory.HasStableProcessEscapeRate.stepCorridor_rate`,
  `ProbabilityTheory.HasStableProcessEscapeRate.finiteCorridorUnion_rate`, and
  `ProbabilityTheory.HasStableProcessEscapeRate.approximableSet_measurableRate`,
  in `Probability.Process.Stable.SmallDeviation.PathClass.StepCorridor.Rate`.
* **Theorem 3, Section 4:** in the original statement, the increments have
  mean $0$ and variance $1$, and $x_n\to\infty$ with $x_n/\sqrt n\to0$;
  for $G\in\mathfrak M$, the source path-class formula is
  $\log\mathbb P(s_n\in G)\sim-\frac{\pi^2}{2}H_2(G)n x_n^{-2}$.
  The Lean finite-variance declaration extends this by normalization to
  centered increments with variance $\sigma^2>0$, giving coefficient
  $-\frac{\pi^2}{2}\sigma^2 H_2(G)$. Its declaration is
  `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.tendsto_scaledLog_sourceProbability_of_finiteVariance`
  in `Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Gaussian.FiniteVariance`.
  The unit-variance normal-domain specialization is
  `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredUnitVariance_sourceRelativePathClassRate`
  in `Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.FromIncrementLaw.Normal.FiniteVariance`;
  the continuous-boundary specialization is imported from its semantic module.
* **Theorem 4, Section 5:** for a homogeneous process with stationary
  independent increments and right-continuous paths, whose one-time law is in
  the strictly stable domain of attraction with $0 < \alpha<2$ and
  $0<F_\alpha(0)<1$, subject to the source centering conditions
  $\mathbb E[\xi(t)]=0$ whenever the expectation exists and, for $\alpha=1$,
  $\int_{\mathbb R}\sin(z/B(n))\,\operatorname{Law}(\xi(1))(dz)\to0$,
  the rescaled path
  $t\mapsto\xi(nt)/x(n)$ has the rate for $G\in\mathfrak M$
  $\log\mathbb P(\xi(n\cdot)/x(n)\in G)\sim
  C H_\alpha(G)n x(n)^{-\alpha}L^*(x(n))$
  with the same $C<0$ as Theorem 1,
  when $x(n)\to\infty$ and $x(n)/B(n)\to0$. This theorem does not yet have a Lean
  declaration in the repository. The stable-process results imported above
  concern the limiting stable process, while the random-walk results concern
  the discrete skeleton; neither formalizes this full source-process
  statement. Its missing interfaces are audited in
  `docs/MOGULSKII_PROCESS_THEOREM_4_PROOF_ROUTE.md`.

The other directories below `Mogulskii/` organize supporting mathematical
interfaces rather than additional main theorems of the 1974 article:
`Path/` owns corridor approximations and realization of finite-corridor
events; `Scale/` owns normalization; and `Rate/` owns energy and
probability-rate results, grouped by bounds, endpoints, and finite partitions.
The generic finite-partition endpoint-core propagation, path-to-corridor
gluing, and IID product lower bound are owned by
`Probability.Process.RandomWalk.Path.Block.Partition.CoreReturn`.
The generic terminal-left partition indices and selected-cell probability
bound live with the path convention in
`Probability.Process.RandomWalk.Path.Skorokhod.TerminalLeft.Partition/`.
The theorem-specific lower-bound geometry and product assembly are private
proof support in `Lemmas/TerminalLeft/Partition/`. `Stable/` and `Gaussian/` organize
the stable and finite-variance regimes. The Gaussian block open-box,
finite-product, and return-kernel proof steps used by the finite-partition rate
assembly are collected under `Gaussian/Blocks/Lemmas/`. The Gaussian
terminal-left path-class adapters
are grouped under `Gaussian/Path/TerminalLeft/`; they support Theorem 3 and
are not separate article-theorem entries.
The one-step Rademacher averaging operator and its sine eigenfunction are
general random-walk interfaces in
`Probability.Process.RandomWalk.Rademacher.Transition.Basic`; the killed finite
interval matrix and its spectral estimates remain specific to this subject.
The terminal-left normalized random-walk path, its path law and range
identities, and its continuous-boundary measurability API are owned by
`Probability.Process.RandomWalk.Path.Skorokhod.TerminalLeft`. Within this
subtree, `Discrete/TerminalLeft/Partition/` owns the terminal-left source-grid
indices and selected-cell bounds used by the partition arguments, while
`Stable/Discrete/TerminalLeft/Partition/` owns their stable rate consequences.
The reusable endpoint-band and endpoint-window
probability interfaces live under
`Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointBand`
and `.EndpointWindow`; their Donsker transfers are in the corresponding
`Donsker/` subdirectories. `Lemmas/EndpointBands/` contains the
Mogul'skii-specific seven-window spectral construction and its one-use transfer
to the generic endpoint-band interface. These probability constructions
support Theorem 3 and are not additional numbered theorem entries.

The IID finite-block inequalities for horizontal tubes are in
`Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.Blocks.UpperBound`,
the strict whole-path range inequality is in
`Probability.Process.RandomWalk.Path.Block.Partition.Range`, and
the common-core return-block iteration is in
`Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.Kernel.BlockIteration`.
The finite-state spectral model is owned by
`Probability.Process.RandomWalk.Rademacher.FiniteInterval.Spectral`, and the
Brownian range bounds by `Probability.Process.Brownian.SmallDeviation.Range`.
`Lemmas/` is reserved for derivation steps that have no standalone reusable
interface.
The theorem-specific Gaussian block and return-kernel proof steps are
collected under `Gaussian/Blocks/Lemmas/` and feed the finite-partition rate
assembly in `Rate/Partition/Finite.lean`. The generic return-block iteration
estimate is in
`Probability/Process/RandomWalk/Kernel/Killed/Return/Uniform.lean`. General
killed-kernel and return-kernel interfaces remain in
`Probability/Process/RandomWalk/Kernel/Killed/`.

In Mogul'skii's notation, $F$ is the law of one increment and
$L^*(u)=u^{\alpha-2}\int_{-u}^{u}x^2\,F(dx)$; the norming is chosen so that
$B^*(B(n))\sim n$, where $B^*(u)=u^\alpha/L^*(u)$. For a finite step
corridor with upper and lower boundaries $L_1$ and $L_2$,
$H_\alpha(G)=\int_0^1(L_1(t)-L_2(t))^{-\alpha}\,dt$; for Mogul'skii's full
path class $\mathfrak M$, the same energy is defined through finite-corridor
approximations. For real-valued finite corridor boundaries `lower` and `upper`,
the formula is provided by
`ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Rate.corridorEnergy`.
The original publication is A. A. Mogul'skii, “Small
deviations in the sample function space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755–765; English translation, “Small Deviations
in a Space of Trajectories,” *Theory of Probability and Its Applications*
19(4) (1975), 726–736, DOI 10.1137/1119081.

This file reexports the existing theorem modules; it does not duplicate their
proofs or change their declaration names. Definitions and complete supporting
results remain with the mathematical subjects listed above; theorem-specific
derivation steps stay in nested `Lemmas` modules beside the results that use
them. In this subtree, `source` in a declaration name refers to the original
random walk or process before scaling or passage to a limiting stable process;
it does not refer to a bibliographic source. `FromIncrementLaw` names the
specialization that starts from the one-step increment law.
-/
