#!/usr/bin/env bash
set -euo pipefail

repo_dir=${1:-.}
cd $repo_dir

lake build
