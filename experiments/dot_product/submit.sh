#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

set -a
source .env
set +a

: "${aristotle_key:?Set aristotle_key in .env before submitting}"

export ARISTOTLE_API_KEY="$aristotle_key"
export PATH="/home/abouvel/.local/bin:$PATH"

prompt="$(cat experiments/dot_product/prompt.txt)"
exec aristotle submit "$prompt" \
  --project-dir experiments/dot_product/submission \
  "$@"
