# Advisory literature-proof tests

Each citation-key directory preserves a reference-specific argument replaced
in production by a general theorem. These modules are not production APIs or
required regressions. The default Lake target and `run-all-lean-tests.py`
exclude them. Required import checks prohibit production and blocking tests
from importing this root.

Run the independent checks with:

```sh
python3 scripts/run-literature-proof-tests.py --output-dir .lake/literature-proof-reports
```

Each manifest records the full reference, exact results, recovery revisions,
entry modules, named axiom audits, and source correspondence. Reports retain
compiler logs and environment revisions. A failure produces a diagnostic report
and a nonzero runner exit, while the separately named GitHub Actions workflow
uses job-level `continue-on-error: true`; it is not a merge requirement.
The subtree publication script explicitly watches `build.yml`, not this
advisory workflow. Do not add the advisory job to branch protection or a
required aggregate. Mechanical success does not replace a source review or
justify calling an alternative argument the reference's original proof.
