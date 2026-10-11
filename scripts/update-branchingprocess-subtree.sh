#!/bin/sh
set -eu

# Split the canonical lean/ subtree. --preflight updates a persistent PR branch,
# runs CI for that exact commit, and never pushes to the standalone main branch.
root=$(git rev-parse --show-toplevel)
cd "$root"
branch=$(git symbolic-ref --quiet --short HEAD || true)
mode=${1:-}
case "$mode" in
  "") ;;
  --preflight) ;;
  *)
    printf 'Usage: %s [--preflight [branch]]\n' "$0" >&2
    exit 2
    ;;
esac

if [ "$mode" = "--preflight" ]; then
  if [ "${3:-}" != "" ]; then
    printf 'Usage: %s [--preflight [branch]]\n' "$0" >&2
    exit 2
  fi
  preflight_branch=${BRANCHINGPROCESS_PREFLIGHT_BRANCH:-${2:-$branch}}
  if [ -z "$preflight_branch" ]; then
    printf 'A named branch is required for preflight publication.\n' >&2
    exit 2
  fi
  if [ "${2:-}" != "" ] && [ -n "${BRANCHINGPROCESS_PREFLIGHT_BRANCH:-}" ]; then
    printf 'Set either the preflight branch argument or BRANCHINGPROCESS_PREFLIGHT_BRANCH, not both.\n' >&2
    exit 2
  fi
  if [ -n "$(git status --porcelain --untracked-files=all)" ]; then
    printf 'Refusing to publish with uncommitted changes; commit or remove them first.\n' >&2
    exit 1
  fi
else
  if [ "${2:-}" != "" ]; then
    printf 'Usage: %s [--preflight [branch]]\n' "$0" >&2
    exit 2
  fi
fi

remote=${BRANCHINGPROCESS_REMOTE:-branchingprocess}
target=${BRANCHINGPROCESS_BRANCH:-main}
if [ "$mode" = "--preflight" ] && [ "$preflight_branch" = "$target" ]; then
  printf 'The preflight branch must differ from the PR base branch %s.\n' "$target" >&2
  exit 2
fi

if [ "$mode" = "--preflight" ]; then
  command -v gh >/dev/null 2>&1 || {
    printf 'Preflight publication requires GitHub CLI (gh) to verify the required CI check.\n' >&2
    exit 1
  }
  git fetch "$remote" "$target"
  onto=$(git rev-parse FETCH_HEAD)
  preflight_line=$(git ls-remote --heads "$remote" "refs/heads/$preflight_branch")
  preflight_head=
  if [ -n "$preflight_line" ]; then
    git fetch "$remote" "refs/heads/$preflight_branch"
    preflight_head=$(git rev-parse FETCH_HEAD)
  fi
fi

commit=$(git subtree split --prefix=lean)
if [ "$mode" = "--preflight" ] && ! git merge-base --is-ancestor "$onto" "$commit"; then
  if git diff --quiet "$onto" "$commit"; then
    commit=$onto
  else
    remote_tree=$(git rev-parse "$onto^{tree}")
    matching_base=
    for candidate in $(git log --first-parent --format=%H "$branch" -- lean); do
      if [ "$(git rev-parse "$candidate:lean")" = "$remote_tree" ]; then
        matching_base=$candidate
        break
      fi
    done
    if [ -z "$matching_base" ]; then
      printf 'Refusing to publish: standalone %s/%s contains changes missing from the lean/ subtree.\n' "$remote" "$target" >&2
      printf 'Merge those changes into lean/ and retry.\n' >&2
      exit 1
    fi
    printf 'The lean/ tree at %s matches standalone %s/%s; joining the subtree and standalone histories.\n' \
      "$matching_base" "$remote" "$target"
    split_tree=$(git rev-parse "$commit^{tree}")
    commit=$(printf 'Merge canonical lean subtree into standalone history\n' |
      git commit-tree "$split_tree" -p "$onto" -p "$commit")
  fi
  if ! git merge-base --is-ancestor "$onto" "$commit"; then
    printf 'Could not join the subtree split to standalone %s/%s history.\n' "$remote" "$target" >&2
    exit 1
  fi
fi

if [ "$mode" = "--preflight" ] && [ -n "$preflight_head" ] &&
    ! git merge-base --is-ancestor "$preflight_head" "$commit"; then
  if git diff --quiet "$preflight_head" "$commit"; then
    commit=$preflight_head
  else
    split_tree=$(git rev-parse "$commit^{tree}")
    commit=$(printf 'Update persistent subtree PR preflight branch\n' |
      git commit-tree "$split_tree" -p "$preflight_head" -p "$commit")
  fi
fi

printf 'Prepared standalone subtree commit %s\n' "$commit"
if [ "$mode" = "--preflight" ]; then
  remote_url=$(git remote get-url "$remote")
  repository=$(gh repo view "$remote_url" --json nameWithOwner --jq .nameWithOwner)
  git push "$remote" "$commit:refs/heads/$preflight_branch"
  run_id=
  attempt=0
  while [ -z "$run_id" ] && [ "$attempt" -lt 30 ]; do
    run_id=$(gh run list --repo "$repository" --workflow build.yml \
      --commit "$commit" --limit 10 --json databaseId --jq '.[0].databaseId // empty')
    if [ -z "$run_id" ]; then
      sleep 2
    fi
    attempt=$((attempt + 1))
  done
  if [ -z "$run_id" ]; then
    printf 'No GitHub Actions build was created for preflight commit %s. The persistent PR branch remains updated.\n' "$commit" >&2
    exit 1
  fi
  gh run watch "$run_id" --repo "$repository" --exit-status --compact
  printf 'Preflight branch %s is synced and its build passed. No base-branch update was made.\n' \
    "$preflight_branch"
fi
