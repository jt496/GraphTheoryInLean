import Lean

/-!
# Hovers for the names in doc comments

A linter that makes the names in the code spans of doc comments (`/-- … -/` and
`/-! … -/`) hoverable in the editor, as they would be in code: hovering one shows its
signature and docstring, and Ctrl-click goes to its declaration. It reports nothing.

Each identifier in a code span is resolved on its own, in the scope of the command
the comment belongs to (its namespace and `open`s, including those of `open … in`),
so in `completeGraph (Fin n)` both `completeGraph` and `Fin` become hoverable while
`n` does not. Identifiers that do not name a unique constant are left alone, and so
are the names of tactics in tactic code (so that `decide` in `decide +revert` or `by
decide` does not show `Decidable.decide`, while the `decide` of `decide p` does),
identifiers right after a `.` (as in `.inl`) and fenced code blocks.

It also covers each web link in a doc comment with an info node that names no
declaration, so that Ctrl-click on the link just opens it. Without one,
go-to-definition falls back to the elaborator of the command around the link, and
Ctrl-click first opens `elabModuleDoc` (say) in Lean's sources.

In a chapter of a guide (a file `C01_Introduction/X.lean`, say), each cross-reference
`<REF>tag</REF>` or `<REF tag>text</REF>`, or `[text](#tag)` as the plain export
writes one, goes to the heading of the guide with that tag on Ctrl-click, and shows
the heading's title on hover, even when the heading is in a chapter the file does not
import. A tag that names no heading gets a warning.

Turn it off with `set_option linter.docHover false`. The guide's generated Verso
files do, since Verso highlights their code from the info trees the linter adds to.
-/

open Lean Elab Command
open System (FilePath)

namespace STIL.DocHover

register_option linter.docHover : Bool := {
  defValue := true
  descr := "make the names in the code spans of doc comments hoverable, and their \
    links open on Ctrl-click without going to the comment's elaborator"
}

/-- The length of the run of backticks starting at `i`. -/
def runLength (cs : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  while j < cs.size && cs[j]! == '`' do
    j := j + 1
  return j - i

/-- The start of the first run of exactly `n` backticks at or after `i`. -/
def findRun (cs : Array Char) (i n : Nat) : Option Nat := Id.run do
  let mut j := i
  while j < cs.size do
    if cs[j]! == '`' then
      let r := runLength cs j
      if r == n then
        return some j
      j := j + r
    else
      j := j + 1
  return none

/-- The code spans of a doc comment's text `s` outside fenced code blocks, as pairs
of the byte offset of a span's contents in `s` and those contents. Like the guide's
prose, a span does not run across lines. -/
def codeSpans (s : String) : Array (Nat × String) := Id.run do
  let mut out := #[]
  let mut lineStart := 0
  let mut inFence := false
  for line in s.splitOn "\n" do
    let trimmed := line.trimAsciiStart
    if trimmed.startsWith "```" || trimmed.startsWith "~~~" then
      inFence := !inFence
    else if !inFence then
      let cs := line.toList.toArray
      -- The byte offset of each character in `line`.
      let offs := cs.foldl (fun acc c => acc.push (acc.back! + c.utf8Size)) #[0]
      let mut i := 0
      while i < cs.size do
        if cs[i]! != '`' then
          i := i + 1
          continue
        let run := runLength cs i
        match findRun cs (i + run) run with
        | some j =>
          let b := offs[i + run]!
          out := out.push (lineStart + b, String.Pos.Raw.extract line ⟨b⟩ ⟨offs[j]!⟩)
          i := j + run
        | none => i := i + run
    lineStart := lineStart + line.utf8ByteSize + 1
  return out

/-- The identifiers in the code `s`, as pairs of byte offset and identifier: the
maximal runs of identifier characters and dots that start with an identifier-start
character not preceded by a dot or by another identifier character, less any trailing
dots. -/
def identifiers (s : String) : Array (Nat × String) := Id.run do
  let mut out := #[]
  let mut start : Option Nat := none
  let mut prev := ' '
  let mut pos := 0
  for c in s.toList ++ [' '] do
    if let some b := start then
      unless isIdRest c || c == '.' do
        let id := String.Pos.Raw.extract s ⟨b⟩ ⟨pos⟩
        out := out.push (b, id.dropEndWhile (· == '.') |>.copy)
        start := none
    else if isIdFirst c && prev != '.' && !isIdRest prev then
      start := some pos
    prev := c
    pos := pos + c.utf8Size
  return out

/-- The web links in the text `s`, as pairs of byte offset and byte length: the runs
that start with `http://` or `https://` and end before whitespace, `<`, `>`, a
backtick, a quote or an unmatched `)`, less any trailing `.,;:`. -/
def links (s : String) : Array (Nat × Nat) := Id.run do
  let cs := s.toList.toArray
  -- The byte offset of each character in `s`.
  let offs := cs.foldl (fun acc c => acc.push (acc.back! + c.utf8Size)) #[0]
  let mut out := #[]
  let mut i := 0
  while i < cs.size do
    let next := String.Pos.Raw.extract s ⟨offs[i]!⟩ ⟨offs[min (i + 8) cs.size]!⟩
    unless next.startsWith "https://" || next.startsWith "http://" do
      i := i + 1
      continue
    let mut j := i
    let mut depth := 0
    while j < cs.size do
      let c := cs[j]!
      if c.isWhitespace || "<>`\"".contains c then
        break
      if c == '(' then
        depth := depth + 1
      else if c == ')' then
        if depth == 0 then
          break
        depth := depth - 1
      j := j + 1
    while j > i && ".,;:".contains cs[j - 1]! do
      j := j - 1
    out := out.push (offs[i]!, offs[j]! - offs[i]!)
    i := j
  return out

/-- `s` less leading and trailing whitespace. -/
def trim (s : String) : String :=
  String.ofList ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile
    Char.isWhitespace).reverse

/-- Whether `s` begins with `t` at the character index `i` of its characters `cs`. -/
def startsAt (cs : Array Char) (i : Nat) (t : String) : Bool :=
  (List.range t.length).all fun k => cs[i + k]? == t.toList[k]?

/-- The cross-references in the text `s`, as triples of the byte offsets of the start
and the end of each `<REF>tag</REF>` or `<REF tag>text</REF>`, and its tag. The text
may run across lines, as may the space after `<REF`; the placeholder `<REF />` is
skipped. A Markdown link to a fragment, `[text](#tag)`, which is how the plain export
of a guide writes a `<REF>`, is a cross-reference too. -/
def refs (s : String) : Array (Nat × Nat × String) := Id.run do
  let cs := s.toList.toArray
  -- The byte offset of each character in `s`.
  let offs := cs.foldl (fun acc c => acc.push (acc.back! + c.utf8Size)) #[0]
  let find (i : Nat) (p : Nat → Bool) : Option Nat :=
    (List.range (cs.size - i)).find? (p <| i + ·) |>.map (i + ·)
  let mut out := #[]
  let mut i := 0
  while i < cs.size do
    -- A link `[text](#tag)`: the `]` that ends the text comes before any other `[`.
    if cs[i]! == '[' then
      if let some j := find (i + 1) (cs[·]? ∈ [some '[', some ']']) then
        if cs[j]! == ']' && startsAt cs (j + 1) "(#" then
          if let some k := find (j + 3) (cs[·]? == some ')') then
            let tag := String.ofList (cs.extract (j + 3) k).toList
            if !tag.isEmpty && !tag.any Char.isWhitespace then
              out := out.push (offs[i]!, offs[k + 1]!, tag)
              i := k + 1
              continue
    unless startsAt cs i "<REF" do
      i := i + 1
      continue
    let j := i + 4
    -- The tag, and the index after it of the `>` that ends `<REF>` or `<REF tag>`.
    let (tag, g) ←
      if cs[j]? == some '>' then
        match find (j + 1) (startsAt cs · "</REF>") with
        | some k => pure (String.ofList (cs.extract (j + 1) k).toList, j)
        | none => break
      else if cs[j]?.any Char.isWhitespace then
        match find j (cs[·]? == some '>') with
        | some g => pure (String.ofList (cs.extract j g).toList, g)
        | none => break
      else
        i := j
        continue
    let tag := trim tag
    if tag == "/" then
      i := g + 1
      continue
    let some k := find (g + 1) (startsAt cs · "</REF>")
      | break
    out := out.push (offs[i]!, offs[k + 6]!, tag)
    i := k + 6
  return out

/-- The tag the guide's converter (`_slug` in `tools/convert_lean_to_verso.py`)
derives from a title: the title in lower case, with each run of characters other than
ASCII letters and digits replaced by `-`, and no `-` at either end. -/
def slug (title : String) : String := Id.run do
  let mut out := ""
  let mut gap := false
  for c in title.toList do
    let c := c.toLower
    if c.isLower || c.isDigit then
      if gap && !out.isEmpty then
        out := out.push '-'
      gap := false
      out := out.push c
    else
      gap := true
  return out

/-- The title `s` (already trimmed) less a final `marker` that whitespace separates
from the rest, as the converter drops ` {-}` (an unnumbered heading) and then ` *`
(an advanced section) before it derives a tag. -/
def dropMarker (s marker : String) : String :=
  match s.toList.reverse.drop marker.length with
  | rest@(c :: _) =>
    if s.endsWith marker && c.isWhitespace then trim (String.ofList rest.reverse)
    else s
  | [] => s

/-- The level and title of a heading line `# title`, `## title` or `### title`. -/
def heading? (line : String) : Option (Nat × String) :=
  let cs := line.toList
  let level := (cs.takeWhile (· == '#')).length
  let rest := cs.drop level
  if 1 ≤ level && level ≤ 3 && rest.head?.any Char.isWhitespace then
    let title := dropMarker (dropMarker (trim (String.ofList rest)) "{-}") "*"
    if title.isEmpty then none else some (level, title)
  else
    none

/-- Whether `name` is the name of a chapter directory of a guide, such as
`C01_Introduction`. -/
def isChapterDir (name : String) : Bool :=
  match name.toList with
  | 'C' :: d₁ :: d₂ :: '_' :: _ => d₁.isDigit && d₂.isDigit
  | _ => false

/-- Where a cross-reference goes: a heading of the guide. -/
structure Target where
  /-- The module of the heading's file. -/
  module : Name
  /-- The heading's line. -/
  range : DeclarationRange
  /-- What hovering over the cross-reference shows. -/
  hover : String

/-- The range of the whole of line `n` (counting from 1), whose text is `line`. -/
def lineRange (n : Nat) (line : String) : DeclarationRange where
  pos := ⟨n, 0⟩
  charUtf16 := 0
  endPos := ⟨n, line.length⟩
  endCharUtf16 := line.toList.foldl (· + ·.utf16Size.toNat) 0

/-- The title of the chapter in the directory `dir`: its entry in the
`chapter_titles` of `guide.json`, if any, and otherwise the name after the `C01_`
prefix with spaces for underscores, as the converter's `chapter_title` has it. -/
def chapterTitle (titles : Json) (dir : String) : String :=
  match titles.getObjValAs? String dir with
  | .ok title => title
  | .error _ => " ".intercalate ((dir.splitOn "_").drop 1)

/-- The tags of the headings of the guide whose chapter directories are in `root`,
with their targets, given the module name `pre` of `root` and the guide's
`chapter_titles`. As in the converter, a heading is a `#`, `##` or `###` line of a
module doc; its tag is `section-` and its `slug`, except that an `Exercises` heading
gets `section-exercises-` (or `subsection-…`, `subsubsection-…` by its level) and the
slug of the heading above it, or of its chapter. Each chapter also has the tag
`chapter-` and the slug of its title, for its main file's first module doc. Where two
headings have the same tag, the first wins. -/
def headingIndex (root : FilePath) (pre : Name) (titles : Json) :
    IO (Std.HashMap String Target) := do
  let mut index : Std.HashMap String Target := {}
  let dirs := (← root.readDir).filter (isChapterDir ·.fileName)
    |>.qsort (·.fileName < ·.fileName)
  for dir in dirs do
    let title := chapterTitle titles dir.fileName
    let files := (← dir.path.readDir).filter (·.path.extension == some "lean")
      |>.qsort (·.fileName < ·.fileName)
    for file in files do
      let stem := file.fileName.dropEnd 5 |>.copy
      let module := pre.str dir.fileName |>.str stem
      let target (n : Nat) (line : String) (hover : String) : Target :=
        { module, range := lineRange n line, hover }
      let lines := ((← IO.FS.readFile file.path).splitOn "\n").toArray
      let mut inProse := false
      -- The titles of the latest headings of each level, as `recent_titles`.
      let mut recent : Array String := #["", "", "", ""]
      let mut chapterLine? : Option (Nat × String) := none
      for h : n in [0:lines.size] do
        let line := lines[n]
        if line.trimAsciiStart.startsWith "/-!" then
          inProse := true
          if stem == dir.fileName && chapterLine?.isNone then
            chapterLine? := some (n + 1, line)
        if inProse then
          if let some (level, t) := heading? line then
            recent := (recent.set! level t).mapIdx fun i r =>
              if i > level then "" else r
            let mut tag := s!"section-{slug t}"
            if slug t == "exercises" then
              let parent := (List.range level).reverse.findSome? fun i =>
                let r := recent[i]!
                if i > 0 && !r.isEmpty then some r else none
              let kind := if level == 1 then "section"
                else if level == 2 then "subsection" else "subsubsection"
              tag := s!"{kind}-exercises-{slug (parent.getD title)}"
            unless index.contains tag do
              index := index.insert tag <| target (n + 1) line
                s!"Section *{t}* (`{dir.fileName}/{file.fileName}`, line {n + 1})"
        if (line.splitOn "-/").length > 1 then
          inProse := false
      if let some (n, line) := chapterLine? then
        let tag := s!"chapter-{slug title}"
        unless index.contains tag do
          index := index.insert tag <|
            target n line s!"Chapter *{title}* (`{dir.fileName}`)"
  return index

/-- The `chapter_titles` of the `guide.json` in `dir` or the nearest directory above
it that has one, or `null`. -/
partial def guideChapterTitles (dir : FilePath) : IO Json := do
  let file := dir / "guide.json"
  if ← file.pathExists then
    match Json.parse (← IO.FS.readFile file) with
    | .ok j => return j.getObjValD "chapter_titles"
    | .error _ => return .null
  match dir.parent with
  | some parent => if parent == dir then return .null else guideChapterTitles parent
  | none => return .null

/-- The modification times of the files of the chapter directories in `root`, from
which `headingIndex` was last computed, with its result. -/
initialize headingIndexCache :
    IO.Ref (Array (FilePath × IO.FS.SystemTime) × Std.HashMap String Target) ←
  IO.mkRef (#[], {})

/-- `headingIndex` for the guide that the current file is a chapter of, if it is one,
computed again only when a file of a chapter directory has changed. -/
def currentHeadingIndex? : CommandElabM (Option (Std.HashMap String Target)) := do
  let file ← try IO.FS.realPath (← getFileName) catch _ => pure (← getFileName)
  let some dir := file.parent | return none
  unless dir.fileName.any isChapterDir do
    return none
  let some root := dir.parent | return none
  let .str (.str pre _) _ ← getMainModule | return none
  let stamps ← (← root.readDir).filter (isChapterDir ·.fileName)
    |>.foldlM (init := #[]) fun acc d => do
      let files ← d.path.readDir
      files.foldlM (init := acc) fun acc f => do
        return acc.push (f.path, (← f.path.metadata).modified)
  let stamps := stamps.qsort (·.1.toString < ·.1.toString)
  let (cached, index) ← headingIndexCache.get
  if cached.size == stamps.size
      && (cached.zip stamps).all fun (a, b) => a.1 == b.1 && a.2 == b.2 then
    return some index
  let index ← headingIndex root pre (← guideChapterTitles root)
  headingIndexCache.set (stamps, index)
  return some index

/-- The atom holding the text of the doc comment `doc`: in a `commentBody` node, if
there is one. -/
def commentBody (doc : Syntax) : Syntax :=
  let body := doc[1]
  if body.isOfKind ``Parser.Command.commentBody then body[0] else body

/-- The doc comments in `stx`. -/
partial def docComments (stx : Syntax) : Array Syntax :=
  if stx.isOfKind ``Parser.Command.docComment
      || stx.isOfKind ``Parser.Command.moduleDoc then
    #[stx]
  else
    stx.getArgs.foldl (· ++ docComments ·) #[]

/-- The first words of the tactics, with the number of tactic syntaxes they were
computed for. -/
initialize tacticWordsCache : IO.Ref (Nat × Std.HashSet String) ← IO.mkRef (0, {})

/-- The first words of the tactics: `decide`, `simp`, … -/
def tacticWords : CommandElabM (Std.HashSet String) := do
  let count := (Parser.parserExtension.getState (← getEnv)).categories.find? `tactic
    |>.map (·.kinds.foldl (fun n _ _ => n + 1) 0) |>.getD 0
  let (cached, words) ← tacticWordsCache.get
  if cached == count then
    return words
  let words := (← Tactic.Doc.firstTacticTokens).foldl (fun s _ w => s.insert w) {}
  tacticWordsCache.set (count, words)
  return words

/-- Whether the code `s` is tactic code: a tactic, or `by` followed by tactics. -/
def isTacticCode (env : Environment) (s : String) : Bool :=
  s.trimAsciiStart.startsWith "by " || (Parser.runParserCategory env `tactic s).isOk

/-- Runs `k` on the command inside the `set_option … in` and `open … in` prefixes of
`stx`, in the scope they set up. -/
partial def withInPrefixes (k : Syntax → CommandElabM Unit) (stx : Syntax) :
    CommandElabM Unit := do
  if stx.isOfKind ``Parser.Command.in then
    if stx[0].isOfKind ``Parser.Command.open then
      let openDecls ← try withEnableInfoTree false <| elabOpenDecl ⟨stx[0][1]⟩
        catch _ => getOpenDecls
      return ← withScope ({ · with openDecls }) <| withInPrefixes k stx[2]
    if stx[0].isOfKind ``Parser.Command.set_option then
      return ← withSetOptionIn (withInPrefixes k) stx
  k stx

/-- See the module docstring. -/
def docHoverLinter : Linter where
  name := `docHover
  run := withInPrefixes fun stx => do
    unless linter.docHover.get (← getOptions) && (← getInfoState).enabled do
      return
    let docs := docComments stx
    if docs.isEmpty then
      return
    let tactics ← tacticWords
    let env ← getEnv
    -- The headings of the guide, read only for a comment with a cross-reference.
    let index? ← if docs.any fun doc => !(refs (commentBody doc).getAtomVal).isEmpty
      then currentHeadingIndex? else pure none
    -- `liftTermElabM` records the info nodes with the context the server needs.
    liftTermElabM do
      for doc in docs do
        let body := commentBody doc
        let some start := body.getPos?
          | continue
        for (spanOff, code) in codeSpans body.getAtomVal do
          let ids := identifiers code
          let tacticCode := ids.any (tactics.contains ·.2) && isTacticCode env code
          for (off, name) in ids do
            if tacticCode && tactics.contains name then
              continue
            let b : String.Pos.Raw := ⟨start.byteIdx + spanOff + off⟩
            let e : String.Pos.Raw := ⟨b.byteIdx + name.utf8ByteSize⟩
            let ref := Syntax.atom (.synthetic b e (canonical := true)) name
            try
              discard <| realizeGlobalConstNoOverloadWithInfo
                (mkIdentFrom ref name.toName (canonical := true))
            catch _ => pure ()
        -- An info node whose elaborator is no declaration, which go-to-definition
        -- picks over the command's own node as the innermost one.
        for (off, len) in links body.getAtomVal do
          let b : String.Pos.Raw := ⟨start.byteIdx + off⟩
          let e : String.Pos.Raw := ⟨b.byteIdx + len⟩
          let ref := Syntax.atom (.synthetic b e (canonical := true))
            (String.Pos.Raw.extract body.getAtomVal ⟨off⟩ ⟨off + len⟩)
          pushInfoLeaf <| .ofCommandInfo { elaborator := .anonymous, stx := ref }
        -- An info node with the heading's position for go-to-definition and its
        -- title for hover, which the server reads without the heading's module
        -- imported.
        let some index := index?
          | continue
        for (b, e, tag) in refs body.getAtomVal do
          let b : String.Pos.Raw := ⟨start.byteIdx + b⟩
          let e : String.Pos.Raw := ⟨start.byteIdx + e⟩
          let ref := Syntax.atom (.synthetic b e (canonical := true)) tag
          let some target := index[tag]?
            | Linter.logLint linter.docHover ref
                m!"no heading of the guide has the tag `{tag}`"
          pushInfoLeaf <| .ofDelabTermInfo {
            elaborator := .anonymous, stx := ref, lctx := ← getLCtx
            expectedType? := none, expr := mkStrLit tag
            location? := some ⟨target.module, target.range⟩
            mkDocString? := some fun _ => pure target.hover }

initialize addLinter docHoverLinter

end STIL.DocHover
