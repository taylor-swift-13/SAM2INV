#!/usr/bin/env bash

if ! command -v opam >/dev/null 2>&1; then
  echo "opam not found in PATH. Please install opam first." >&2
  return 1 2>/dev/null || exit 1
fi

if [ -n "${1:-}" ]; then
  eval "$(opam env --switch="$1" --set-switch)"
else
  eval "$(opam env)"
fi
