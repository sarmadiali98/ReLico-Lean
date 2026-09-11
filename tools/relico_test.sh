#!/bin/bash

set -euo pipefail

REPOSITORY_ROOT="$(
  cd "${BASH_SOURCE[0]%/*}/.." &&
  /bin/pwd
)"

PYTHON_BIN=""

python_is_compatible() {
  local candidate="$1"

  if [[ "$candidate" != */* ]]
  then
    candidate="$(command -v "$candidate" || true)"
  fi

  test -n "$candidate" && test -x "$candidate" || return 1

  "$candidate" -c '
import sys
raise SystemExit(0 if sys.version_info >= (3, 10) else 1)
' >/dev/null 2>&1
}

if test -n "${RELICO_PYTHON:-}"
then
  if python_is_compatible "$RELICO_PYTHON"
  then
    PYTHON_BIN="$RELICO_PYTHON"
  else
    echo "relico-test: RELICO_PYTHON is not Python 3.10+" >&2
    exit 127
  fi
fi

if test -z "$PYTHON_BIN"
then
  for candidate in \
    "${VIRTUAL_ENV:+$VIRTUAL_ENV/bin/python3}" \
    /opt/homebrew/bin/python3 \
    /usr/local/bin/python3 \
    /usr/bin/python3 \
    python3
  do
    test -n "$candidate" || continue
    if python_is_compatible "$candidate"
    then
      PYTHON_BIN="$(command -v "$candidate" 2>/dev/null || printf '%s' "$candidate")"
      break
    fi
  done
fi

if test -z "$PYTHON_BIN"
then
  echo "relico-test: no compatible Python 3.10+ was found" >&2
  exit 127
fi

export PYTHONDONTWRITEBYTECODE=1

exec \
  "$PYTHON_BIN" \
  "$REPOSITORY_ROOT/tools/relico_test.py" \
  "$@"
