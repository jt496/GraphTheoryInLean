#!/bin/bash
# Sets up a codespace for the guide: fetches Mathlib's compiled files, then builds
# the chapters (they import one another, so opening a late chapter would
# otherwise first build every chapter before it). The codespace starts it by
# itself once it has been created, out of sight; run it in a terminal to follow
# its progress. If it is already running, this shows its log until it finishes,
# rather than unpack Mathlib alongside it; once it has succeeded, it only says so.
set -o pipefail
cd "$(dirname "$0")/.." || exit 1
mkdir -p .lake
exec 9> .lake/setup.lock
if ! flock -n 9; then
  echo "The setup is already running; showing its progress."
  tail -n +1 -F .lake/setup.log 2> /dev/null &
  tail=$!
  flock 9
  sleep 1
  kill "$tail"
  wait "$tail" 2> /dev/null
fi
if [ ! -f .lake/setup-done ]; then
  { echo "Fetching Mathlib and building the chapters: this takes ten to fifteen minutes."
    lake exe cache get && lake build
  } 2>&1 | tee .lake/setup.log || {
    echo "The setup failed: run 'bash .devcontainer/setup.sh' to try again."
    exit 1
  }
  touch .lake/setup-done
fi
echo "Done: open a chapter from the Explorer."
