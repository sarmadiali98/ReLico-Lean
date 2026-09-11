#!/usr/bin/env bash

set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: run-general-focused-test.sh TEST_ID" >&2
  exit 2
fi

repository_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repository_root"

exec lake env lean --run frontend/lean-bridge/GeneralFocusedTestMain.lean "$1"
