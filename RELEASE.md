# Standalone Lean library pull requests

The Lean library is maintained in the canonical repository's `lean/` subtree
and reviewed in `https://github.com/maix00/BranchingProcess`. Keep the subtree
on a persistent remote PR branch while the work is in progress. The standalone
`main` branch is the PR base and is updated only by merging that pull request.

## Preflight branch workflow

From the canonical repository root, compile the Lean project, commit the
verified changes, then run:

```sh
cd lean
lake build
cd ..
git diff --check
git status --short --untracked-files=all
./scripts/update-branchingprocess-subtree.sh --preflight
```

The script splits `lean/`, updates a persistent branch on the standalone
repository (by default, the current local branch name), and waits for the
GitHub Actions build for that exact commit. It never pushes to `main` and does
not delete the preflight branch. Use the branch as the head of the pull
request; later verified commits update the same branch. Merge only through the
pull request after review and all required checks pass.

To select a different persistent head branch, pass its name or set
`BRANCHINGPROCESS_PREFLIGHT_BRANCH`:

```sh
./scripts/update-branchingprocess-subtree.sh --preflight codex/branch-name
```

The remote and PR base branch can be selected with
`BRANCHINGPROCESS_REMOTE` and `BRANCHINGPROCESS_BRANCH`. If the local subtree
does not contain the base branch's changes, publication is refused rather
than rewriting or dropping them. Publishing requires an authenticated GitHub
CLI (`gh`) session with permission to push branches and read workflow results.

Do not publish uncommitted files. The Lake package version and exact
dependency revisions are recorded in `lakefile.toml`, `lake-manifest.json`,
and `lean-toolchain`; a preflight update requires a successful build with
those pinned dependencies.
