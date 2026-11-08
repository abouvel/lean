#!/usr/bin/env bash
set -euo pipefail
cd /home/abouvel/fall26/research
printf '%s\n' 'Waiting for the previous study to release the shared machine.'
exec flock -x experiments/exp-032-roundtrip-study-2026-11-06/coordinator.lock bash -c 'printf "%s\n" "Starting the Block Jacobi batch."; exec python3 -u pipeline/batch.py run --experiment experiments/exp-034-block-jacobi-roundtrip-2026-11-06'
