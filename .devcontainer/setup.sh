#!/bin/bash
# Sets up a codespace for the guide, and readies it again whenever it restarts.
# The first time, it fetches Mathlib's compiled files and builds the chapters
# (they import one another, so opening a late chapter would otherwise first build
# every chapter before it). Every time, it then reads the compiled files that
# Lean imports into memory: the codespace's disk is slow, and Lean, which reads
# them piece by piece, would otherwise take minutes to open a chapter.
# The codespace runs it by itself whenever it starts, out of sight; run it in a
# terminal to follow its progress. If it is already running, this shows its log
# until it finishes rather than run alongside it.
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
{ if [ ! -f .lake/setup-done ]; then
    echo "Fetching Mathlib and building the chapters: this takes ten to fifteen minutes."
    lake exe cache get && lake build && touch .lake/setup-done || exit 1
  fi
  # Once per boot of the machine: a restart empties memory.
  boot=$(cat /proc/sys/kernel/random/boot_id)
  if [ "$boot" != "$(cat .lake/setup-read 2> /dev/null)" ]; then
    echo "Reading Lean and Mathlib into memory, so that chapters open quickly" \
         "(a minute or two)…"
    find "$(lean --print-prefix)/lib/lean" .lake/packages/*/.lake/build/lib/lean \
      -name '*.olean*' -print0 2> /dev/null | xargs -0 -r cat > /dev/null 2>&1
    echo "$boot" > .lake/setup-read
  fi
} 2>&1 | tee .lake/setup.log || {
  echo "The setup failed: run 'bash .devcontainer/setup.sh' to try again."
  exit 1
}
echo "Done: open a chapter from the Explorer."
