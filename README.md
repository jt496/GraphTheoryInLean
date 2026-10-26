# Graph Theory in Lean

The Lean sources of *Graph Theory in Lean*: one directory per chapter under
`GraphTheoryInLean/`, each holding the chapter (`CNN_Name.lean`) and, for most chapters, its
exercises with solutions (`Exercises.lean`).

Read the guide online at <https://jt496.github.io/GraphTheoryInLean/>,
or as a PDF: [`docs/GraphTheoryInLean.pdf`](docs/GraphTheoryInLean.pdf).
The HTML is in `docs/`, served by GitHub Pages.

## Building

    lake exe cache get   # download prebuilt Mathlib (do this first)
    lake build

`lakefile.toml` pins the Mathlib commit the guide was written against.

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
14. [Bibliography](https://jt496.github.io/GraphTheoryInLean/Bibliography/)
15. [Appendix](https://jt496.github.io/GraphTheoryInLean/Appendix/)

This repository is generated from the guide's sources; edit those rather than
these files.

## License

Copyright (c) 2026 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
