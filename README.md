# Graph Theory in Lean

*First edition · Release v4.36.0 · November 2026*

The Lean sources of *Graph Theory in Lean*: one directory per chapter under
`GraphTheoryInLean/`, each holding the chapter (`CNN_Name.lean`) and, for most chapters, its
exercises with solutions (`Exercises.lean`).

Read the guide online at <https://jt496.github.io/GraphTheoryInLean/>.
The HTML is in `docs/`, served by GitHub Pages.

## Building

    lake exe cache get   # download prebuilt Mathlib (do this first)
    lake build

`lakefile.toml` pins the Mathlib commit the guide was written against.

## Running in the browser

To use the guide's Lean files without installing anything, open this repository
in GitHub Codespaces (you need a GitHub account):

<https://codespaces.new/jt496/GraphTheoryInLean?quickstart=1>

This runs VS Code and Lean in your browser. The codespace then sets itself up,
downloading Mathlib and building the chapters, which takes ten to fifteen minutes
the first time. To follow its progress, open a terminal (Terminal > New Terminal)
and run

    bash .devcontainer/setup.sh

and wait for it to print "Done: open a chapter from the Explorer." before opening
a chapter. The same command starts the setup again if it has failed, and only
prints "Done" once it has succeeded.

Later, the same link offers to resume the codespace you already have.
Codespaces usage counts against your monthly GitHub allowance, so stop the
codespace when you have finished (by default it stops by itself after 30 idle
minutes). A stopped codespace still takes up storage (about 20 GB), so delete it
at <https://github.com/codespaces> once you no longer need it.

## Chapters

1. [Introduction](https://jt496.github.io/GraphTheoryInLean/Introduction/)
2. [SimpleGraph](https://jt496.github.io/GraphTheoryInLean/SimpleGraph/)
3. [Constructions](https://jt496.github.io/GraphTheoryInLean/Constructions/)
4. [Decidability, Finiteness and Degrees](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/)
5. [Maps](https://jt496.github.io/GraphTheoryInLean/Maps/)
6. [Cliques](https://jt496.github.io/GraphTheoryInLean/Cliques/)
7. [Colorings](https://jt496.github.io/GraphTheoryInLean/Colorings/)
8. [Walks](https://jt496.github.io/GraphTheoryInLean/Walks/)
9. [Subgraphs](https://jt496.github.io/GraphTheoryInLean/Subgraphs/)
10. [Connectivity](https://jt496.github.io/GraphTheoryInLean/Connectivity/)
11. [Distance](https://jt496.github.io/GraphTheoryInLean/Distance/)
12. [Algebraic Graph Theory](https://jt496.github.io/GraphTheoryInLean/Algebraic-Graph-Theory/)
13. [Theorems](https://jt496.github.io/GraphTheoryInLean/Theorems/)

- [Appendix](https://jt496.github.io/GraphTheoryInLean/Appendix/)
- [Bibliography](https://jt496.github.io/GraphTheoryInLean/Bibliography/)

This repository is generated from the guide's sources; edit those rather than
these files.

## License

Copyright (c) 2026 Richard M. Hill and John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
