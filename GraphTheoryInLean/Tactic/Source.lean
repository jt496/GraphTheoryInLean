import Lean

/-- Drop leading `@[...]` attribute lines from a list of lines. -/
private def dropLeadingAttributes (lines : List String) : List String :=
  match lines with
  | [] => []
  | first :: rest =>
    if first.trimAsciiStart.startsWith "@[" then
      dropLeadingAttributes rest
    else
      lines

/-- Drop a leading `/-- ... -/` doc-string block from a list of lines, if present. -/
private def dropLeadingDocComment (lines : List String) : List String :=
  match lines with
  | [] => []
  | first :: rest =>
    if first.trimAsciiStart.startsWith "/--" then
      -- Single-line doc-string: /-- foo -/
      if first.trimAsciiEnd.endsWith "-/" then
        rest
      else
        -- Multi-line: skip until the line that closes with -/
        let rec skipUntilClose : List String → List String
          | []        => []
          | l :: rest => if l.trimAsciiEnd.endsWith "-/" then rest else skipUntilClose rest
        skipUntilClose rest
    else
      lines

/--
Build a source search path usable even when `LEAN_SRC_PATH` is not set
(e.g., inside a `lake build` subprocess, which only receives `LEAN_PATH`).

Lake stores each package's oleans at `<pkg>/.lake/build/lib/lean`, so the
source root is four parent directories above each olean-path entry. We
collect those candidate roots and add them alongside whatever
`getSrcSearchPath` already returns.
-/
private def getFullSrcSearchPath : IO Lean.SearchPath := do
  -- Primary: LEAN_SRC_PATH (set by `lake env` and the language server)
  let primary ← Lean.getSrcSearchPath
  -- Fallback: derive source roots from the olean search path (LEAN_PATH)
  -- by walking 4 levels up from each entry (stripping .lake/build/lib/lean)
  let oleanPaths ← Lean.searchPathRef.get
  let fallback : Lean.SearchPath := oleanPaths.filterMap fun p =>
    p.parent >>= (·.parent) >>= (·.parent) >>= (·.parent)
  return primary ++ fallback

private def extractSource (name : Lean.Name) : Lean.Elab.Command.CommandElabM (List String) := do
  let some ranges ← Lean.findDeclarationRanges? name
    | throwError "#source: no source range found for '{name}'"
  let modName ← match ← Lean.findModuleOf? name with
    | some m => pure m
    | none   =>
      throwError "#source: '{name}' is defined in the current file — use your editor instead"
  let srcPath ← getFullSrcSearchPath
  let some path ← srcPath.findModuleWithExt "lean" modName
    | throwError "#source: could not find source file for module '{modName}'"
  let content ← IO.FS.readFile path
  let lines     := content.splitOn "\n"
  let startLine := ranges.range.pos.line - 1
  let endLine   := ranges.range.endPos.line - 1
  return (lines.toArray.extract startLine (endLine + 1)).toList

open Lean Elab Command in
/-- Shared implementation of the `#source` commands: log the source of `id` at `tk`,
after applying `clean` to its lines. -/
private def elabSource (tk : Syntax) (id : Ident)
    (clean : List String → List String) : CommandElabM Unit := do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let excerpt ← extractSource name
  withRef tk <| logInfo (String.intercalate "\n" (clean excerpt))

-- The commands below have plain comments, not doc-strings: the HTML would show a
-- doc-string in the hover of every `#source`, next to the printed source.

-- Print the source of a declaration, without its doc-string.
elab tk:"#source " id:ident : command =>
  elabSource tk id dropLeadingDocComment

-- Print the source of a declaration, without its doc-string and attributes.
elab tk:"#source' " id:ident : command =>
  elabSource tk id (dropLeadingAttributes ∘ dropLeadingDocComment)

-- Print the source of a declaration, with its doc-string but without attributes.
elab tk:"#source_doc " id:ident : command =>
  elabSource tk id dropLeadingAttributes
