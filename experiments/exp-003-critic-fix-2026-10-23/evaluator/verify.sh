#!/usr/bin/env bash
set -euo pipefail

repo_dir=${1:-.}
cd $repo_dir

lake build

if grep -RInE '\b(sorry|admit)\b' Research --include='*.lean'; then
  echo 'Verification failed: unresolved proof placeholder found.' >&2
  exit 1
fi

if grep -RInE '^[[:space:]]*axiom[[:space:]]' Research --include='*.lean'; then
  echo 'Verification failed: project-defined axiom found.' >&2
  exit 1
fi

echo 'Verification passed: build succeeds with no proof placeholders or custom axioms.'
