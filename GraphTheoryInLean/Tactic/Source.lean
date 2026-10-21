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

/-- Whether `c` can occur in a (possibly dotted) name. -/
private def isNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' || c == '.' ||
    (c.toNat ≥ 0x80 && !c.isWhitespace)

/--
Whether the declaration ranges `r` of `name` fit `lines`, the current text of its
source file. The ranges are those recorded when the module was compiled, as loaded by
the current file; they stop fitting when the source is edited afterwards (say, an
earlier chapter is edited while a later one is open), and the excerpt would then be
shifted. The check: the recorded name position holds a whole token that names the
declaration (part of `name`, the keyword `instance` of an anonymous instance, or the
attribute or class that generated it, as in `@[simps]` or `deriving`), and the
declaration ends at the end of a token; unless it was generated, nothing but a
comment may follow its last line.
-/
private def rangesFit (name : Lean.Name) (r : Lean.DeclarationRanges)
    (lines : Array String) : Bool := Id.run do
  let s := r.selectionRange
  let e := r.range.endPos
  let some selLine := lines[s.pos.line - 1]? | return false
  let some endLine := lines[e.line - 1]? | return false
  let endChars := endLine.toList
  unless 0 < e.column && e.column ≤ endChars.length
      && !endChars[e.column - 1]!.isWhitespace do
    return false
  let chars := selLine.toList
  let len := if s.pos.line == s.endPos.line then s.endPos.column - s.pos.column
    else chars.length - s.pos.column
  let sel := String.ofList ((chars.drop s.pos.column).take len)
  let before := String.ofList (chars.take s.pos.column)
  -- A whole token (a `.` may follow it, as in `Multiset.{u}`).
  let after := (chars.drop (s.pos.column + len)).head?
  if sel.isEmpty || before.back?.any isNameChar
      || after.any (fun c => c != '.' && isNameChar c) then
    return false
  let comps := "_root_" ::
    name.components.filterMap fun | .str _ c => some c | _ => none
  let unescape (c : String) := (c.replace "«" "").replace "»" ""
  let named := sel == "instance"
    || (sel.splitOn ".").all (comps.contains <| unescape ·)
  let b := before.trimAsciiEnd
  let generated := sel.all isNameChar
    && (b.endsWith "[" || b.endsWith "," || b.endsWith "deriving")
  let rest := (String.ofList (endChars.drop e.column)).trimAsciiStart
  return generated
    || (named && (e.line == s.pos.line || rest.isEmpty || rest.startsWith "--"))

/-- The source lines of `name`, or `none` (with a warning) if its source file has
changed since its module was loaded (see `rangesFit`). -/
private def extractSource (name : Lean.Name) :
    Lean.Elab.Command.CommandElabM (Option (List String)) := do
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
  let lines     := content.splitOn "\n" |>.toArray
  unless rangesFit name ranges lines do
    Lean.logWarning m!"#source: '{modName}' has been edited since this file \
      loaded it, so the source of '{name}' cannot be located. Use the \
      \"Restart File\" command in your editor."
    return none
  let startLine := ranges.range.pos.line - 1
  let endLine   := ranges.range.endPos.line - 1
  return some (lines.extract startLine (endLine + 1)).toList

open Lean Elab Command in
/-- Shared implementation of the `#source` commands: log the source of `id` at `tk`,
after applying `clean` to its lines. -/
private def elabSource (tk : Syntax) (id : Ident)
    (clean : List String → List String) : CommandElabM Unit := do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let some excerpt ← withRef tk <| extractSource name | return
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
