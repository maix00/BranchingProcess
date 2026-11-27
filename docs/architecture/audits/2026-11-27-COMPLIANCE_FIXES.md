# Repairs from the post-consolidation compliance audit

The audit used source commit `6bed8050a`; its Lean subtree equals that at
`79b36fe9`. Repairs preserve the mathematical assumptions of all retained
production statements. LaTeX and dependency revisions are outside this change.

## Verification defects

The axiom parser now recognizes both `depends on axioms: [...]` and the native
`does not depend on any axioms` output. Every required test is audited against
its registered inventory, including empty inventories. Regression cases cover
valid zero-axiom proofs, unexpected zero-axiom reports, duplicate reports and
mixed reports containing `sorryAx`. A native `True.intro` test exercises the
actual Lean output through the normal required runner.

The source comparison for check selection now includes same-line and multiline
attributes on declarations. An added assumption on `finitePrefix_zero` previously
compiled from stdin while failing to request the full scope. The new cases
exercise changed binders, attributed definitions and adjacent proof-only edits.
This remains a heuristic source comparison; the normative explicit escalation
for meaning-changing interfaces that it cannot recognize is unchanged.

## Mathematical owners and reuse decisions

The first-split descendant factorization concerns an arbitrary measurable finite
selection rule, its finite split completion, and the selected sibling roots.
It has no capacity-N or speed hypotheses. Its statement and proof move unchanged
to `Population/Processes/StepSelection/SplitTime/BranchingProperty.lean` and
`ProbabilityTheory.BranchingRandomWalk.Selection.Stepwise.SplitTime`. The existing
stopped selected-subtree-vector factorization proves it; no new process,
conditioning convention or independent law implementation is introduced.

Seven candidate-failure wrappers formerly under speed `Lemmas/Failure/` are
removed. Their content is the existing arbitrary-event identity
`RootIndexed.integral_selectedSubtree_observable_abs_on_event` or its disjoint-root
counterpart, followed by candidate-event measurability and multiplication of
nonnegative bounds. The actual growth-trial client now performs that composition
directly, with the same filtration, chosen family, countable-range assumptions,
integrability, moment bound and failure-probability bound. Tests audit the owner
and the retained application, rather than the removed convenience API.

The geometric split-reward specializations have no production callers. Their
instantiations of `iidGeometricFailurePositiveReward_integral` and the bounded-split
cutoff theorem are retained in the existing required regression module, within a
test namespace. There is no separately exported speed-helper API. This is an API
specialization regression, not a claim to preserve a separate external reference
argument. No compatibility paths or names remain.

These are interface-level owner/reuse repairs: the relevant general statements
already exist in the pinned local library. The exact native measure-independence
and IID reward APIs are used by those owners; no foundational mathematical object
or new external theorem is added. The original first-split hypotheses are retained,
and no necessity claim or source-strategy replacement is made.

## Documentation

The status index correctly names `Probability/BranchingProcess/State/` as the
owner of the general state-update and optional-line branching results. The
threshold-count module inventories both public theorems and their quantitative
statements. Current ownership/ledger records follow the moves; historical audit
snapshots keep their original scope and wording.

## Directory-count review

Exceeding eight direct files triggers semantic review, not forced moves.
`Analysis/Asymptotics/Sequence/` retains nine peer sequence-limit interfaces.
`Probability/Process/Tree/Line/` retains nine peer line/information operations,
with detailed information constructions already grouped below `Information/`.
The nine `Selection/NSelection/Law/Causal/` entries identify distinct causal-law,
selection, nested-root and endpoint comparison interfaces; stopped restart laws
have their own subgroup. These complete interfaces are not moved into `Lemmas/`.
The thirteen direct `SelectedPath/Completion/Lemmas/` files support the same
model's completion/entrance estimate, covering clock, trial count, position and
stopped endpoint comparisons; all remain nonpublic. Existing deeper proof groups
remain separate. No new public API is inferred from cross-file use or file count.
