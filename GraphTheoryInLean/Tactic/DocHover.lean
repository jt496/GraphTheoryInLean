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

Turn it off with `set_option linter.docHover false`. The guide's generated Verso
files do, since Verso highlights their code from the info trees the linter adds to.
-/

open Lean Elab Command

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
    -- `liftTermElabM` records the info nodes with the context the server needs.
    liftTermElabM do
      for doc in docs do
        -- The comment's text is an atom, in a `commentBody` node.
        let body := doc[1]
        let body := if body.isOfKind ``Parser.Command.commentBody then body[0]
          else body
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

initialize addLinter docHoverLinter

end STIL.DocHover
