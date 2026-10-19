#!/usr/bin/env bash
set -euo pipefail

repo_dir=${1:-.}
cd "$repo_dir"

lake build

if [[ -d lean/Research ]]; then
  source_dir=lean/Research
elif [[ -d Research ]]; then
  source_dir=Research
else
  echo 'Verification failed: Lean source directory is missing.' >&2
  exit 1
fi

scan() {
  local pattern=$1 reason=$2 scan_status
  if grep -RInE "$pattern" "$source_dir" --include='*.lean'; then
    echo "Verification failed: $reason." >&2
    exit 1
  else
    scan_status=$?
    if [[ $scan_status -ne 1 ]]; then
      echo 'Verification failed: source scan could not complete.' >&2
      exit "$scan_status"
    fi
  fi
}

scan '\b(sorry|admit)\b' 'unresolved proof placeholder found'
scan '^[[:space:]]*axiom[[:space:]]' 'project-defined axiom found'

echo 'Verification passed: build succeeds with no proof placeholders or custom axioms.'
