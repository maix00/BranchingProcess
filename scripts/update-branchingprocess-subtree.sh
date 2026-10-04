#!/bin/sh
set -eu

# Split the canonical lean/ subtree and optionally publish it after CI passes.
root=$(git rev-parse --show-toplevel)
cd "$root"
branch=$(git symbolic-ref --quiet --short HEAD || true)
if [ "$branch" != master ]; then
  printf 'Skipping subtree refresh on %s\n' "${branch:-detached HEAD}"
  exit 0
fi
push=0
if [ "${1:-}" = "--push" ]; then
  push=1
elif [ "${1:-}" != "" ]; then
  printf 'Usage: %s [--push]\n' "$0" >&2
  exit 2
fi
if [ "$push" -eq 1 ] && [ -n "$(git status --porcelain --untracked-files=all)" ]; then
  printf 'Refusing to publish with uncommitted changes; commit or remove them first.\n' >&2
  exit 1
fi
commit=$(git subtree split --prefix=lean)
printf 'Prepared standalone subtree commit %s\n' "$commit"
if [ "$push" -eq 1 ]; then
  remote=${BRANCHINGPROCESS_REMOTE:-branchingprocess}
  target=${BRANCHINGPROCESS_BRANCH:-main}
  command -v gh >/dev/null 2>&1 || {
    printf 'Publishing requires GitHub CLI (gh) to verify the required CI check.\n' >&2
    exit 1
  }
  remote_url=$(git remote get-url "$remote")
  repository=$(gh repo view "$remote_url" --json nameWithOwner --jq .nameWithOwner)
  preflight_branch="branchingprocess-preflight-$commit"
  preflight_pushed=0
  cleanup_preflight() {
    cleanup_status=$?
    trap - EXIT HUP INT TERM
    if [ "$preflight_pushed" -eq 1 ]; then
      git push "$remote" --delete "$preflight_branch" >/dev/null 2>&1 || true
    fi
    exit "$cleanup_status"
  }
  trap cleanup_preflight EXIT
  trap 'exit 129' HUP
  trap 'exit 130' INT
  trap 'exit 143' TERM

  git push "$remote" "$commit:refs/heads/$preflight_branch"
  preflight_pushed=1
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
    printf 'No GitHub Actions build was created for preflight commit %s.\n' "$commit" >&2
    exit 1
  fi
  gh run watch "$run_id" --repo "$repository" --exit-status --compact
  git push "$remote" "$commit:refs/heads/$target"
fi
