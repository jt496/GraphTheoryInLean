#!/bin/bash
# Sets up a codespace for the guide: fetches Mathlib's compiled files, then builds
# the chapters (they import one another, so opening a late chapter would
# otherwise first build every chapter before it). VS Code runs it in a terminal
# whenever the codespace opens (the task in .devcontainer/tasks.json); once it
# has succeeded it only says so. A second copy waits for the first rather than
# unpack Mathlib alongside it.
cd "$(dirname "$0")/.." || exit 1
mkdir -p .lake
exec 9> .lake/setup.lock
if ! flock -n 9; then
  echo "The setup is already running in another terminal; waiting for it to finish…"
  flock 9
fi
if [ ! -f .lake/setup-done ]; then
  echo "Fetching Mathlib and building the chapters: this takes ten to fifteen minutes."
  lake exe cache get && lake build || {
    echo "The setup failed: run 'bash .devcontainer/setup.sh' in a terminal to try again."
    exit 1
  }
  touch .lake/setup-done
fi
echo "Done: open a chapter from the Explorer."
