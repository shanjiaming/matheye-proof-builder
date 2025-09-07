import Lean
import Lean.Meta.Basic
import Lean.Elab.Tactic
import Lean.Server.Rpc.Basic
import Lean.PrettyPrinter

open Lean Elab Meta Server RequestM Parser

namespace MathEye

def VERSION := 1

/-- Input parameters for RPC method -/
structure InputParams where
  pos : Lsp.Position
  deriving FromJson, ToJson

/-- Proof goal information -/
structure ProofGoal where
  type : String
  name : Option String := none
  deriving FromJson, ToJson

/-- Output parameters for RPC method -/
structure OutputParams where
  goals : Array ProofGoal
  version : Nat
  deriving Inhabited, FromJson, ToJson

/-- Insertion point result for proof edits -/
structure InsertionPoint where
  pos : Lsp.Position
  deriving FromJson, ToJson

/-- File content parameters -/
structure FileContentParams where
  content : String
  deriving FromJson, ToJson

/-- AST data parameters -/
structure ASTDataParams where
  astJson : String
  deriving FromJson, ToJson

/-- File AST conversion result -/
structure FileConversionResult where
  ast : String  -- JSON representation of AST
  success : Bool
  errorMsg : Option String := none
  deriving FromJson, ToJson

/-- Text conversion result -/
structure TextConversionResult where
  text : String
  success : Bool
  errorMsg : Option String := none
  deriving FromJson, ToJson

/-- Main RPC method to get current proof goals -/
@[server_rpc_method]
def getProofGoals (params : InputParams) : RequestM (RequestTask OutputParams) := do
  withWaitFindSnapAtPos params.pos fun snap => do
    let doc ← readDoc
    let text : FileMap := doc.meta.text
    let hoverPos : String.Pos := text.lspPosToUtf8Pos params.pos

    -- Use infoTree.goalsAt? to find tactic info at position
    let results0 := snap.infoTree.goalsAt? text hoverPos
    -- Seam-probe near the position if empty
    let results :=
      if results0.isEmpty then
        let baseLsp := params.pos
        let probeRight : List Lsp.Position := (List.range 41).map (fun i => { line := baseLsp.line, character := baseLsp.character + i })
        let probeLeft  : List Lsp.Position := (List.range 4).map (fun i => { line := baseLsp.line, character := baseLsp.character - i })
        let probes := probeLeft ++ probeRight
        let rec firstSome (ps : List Lsp.Position) : List GoalsAtResult :=
          match ps with
          | [] => results0
          | p :: ps' =>
            let pos := text.lspPosToUtf8Pos p
            let rs := snap.infoTree.goalsAt? text pos
            if rs.isEmpty then firstSome ps' else rs
        firstSome probes
      else results0
    match results.head? with
    | some result =>
      let names := result.tacticInfo.goalsBefore.map (fun g => toString g.name)
      let realGoals : Array ProofGoal := (names.toArray.map (fun s => { type := s : ProofGoal }))
      return { goals := realGoals, version := VERSION }
    | none =>
      return { goals := #[], version := VERSION }

/-- Compute canonical insertion point inside current proof block.
Find the tactic at `params.pos` and return its start position + 1 line (first line inside the `by` block).
If not inside a tactic, return the original position. -/
@[server_rpc_method]
def getInsertionPoint (params : InputParams) : RequestM (RequestTask InsertionPoint) := do
  withWaitFindSnapAtPos params.pos fun snap => do
    let doc ← readDoc
    let text : FileMap := doc.meta.text
    let hoverPos : String.Pos := text.lspPosToUtf8Pos params.pos
    -- Robust: probe a small window around the hover position to avoid seam positions
    let results0 := snap.infoTree.goalsAt? text hoverPos
    let results :=
      if results0.isEmpty then
        let baseLsp := params.pos
        let probeRight : List Lsp.Position := (List.range 41).map (fun i => { line := baseLsp.line, character := baseLsp.character + i })
        let probeLeft  : List Lsp.Position := (List.range 4).map (fun i => { line := baseLsp.line, character := baseLsp.character - i })
        let probes := probeLeft ++ probeRight
        let rec firstSome (ps : List Lsp.Position) : List GoalsAtResult :=
          match ps with
          | [] => results0
          | p :: ps' =>
            let pos := text.lspPosToUtf8Pos p
            let rs := snap.infoTree.goalsAt? text pos
            if rs.isEmpty then firstSome ps' else rs
        firstSome probes
      else results0
    match results.head? with
    | some r =>
      -- Choose a stable position inside the tactic node (not after it),
      -- to ensure goalsAt? continues to work and seams are avoided.
      let stx := r.tacticInfo.stx
      let posInside? :=
        match stx.getTailPos?, stx.getPos? with
        | some tail, _ =>
          if tail.byteIdx > 0 then some (String.Pos.mk (tail.byteIdx - 1)) else stx.getPos?
        | none, some start => some (String.Pos.mk (start.byteIdx + 1))
        | none, none => none
      let inside := posInside?.getD hoverPos
      let insideLsp := text.utf8PosToLspPos inside
      return { pos := insideLsp }
    | none =>
      return { pos := params.pos }

/--
  Structured context RPC for analysis.
  Returns tactic range, goal (pretty + free vars), and locals with types and dependencies.
-/
structure BinderInfoDto where
  kind : String
  deriving FromJson, ToJson

structure LocalVarDto where
  name       : String
  binderInfo : String
  isLet      : Bool
  typePretty : String
  dependsOn  : Array String
  deriving FromJson, ToJson

structure GoalDto where
  pretty   : String
  freeVars : Array String
  deriving FromJson, ToJson

structure RangeDto where
  start : Lsp.Position
  stop  : Lsp.Position
  deriving FromJson, ToJson

structure StructuredContext where
  tacticRange? : Option RangeDto := none
  goal?        : Option GoalDto := none
  locals       : Array LocalVarDto := #[]
  deriving FromJson, ToJson

@[server_rpc_method]
def getStructuredContext (params : InputParams) : RequestM (RequestTask StructuredContext) := do
  withWaitFindSnapAtPos params.pos fun snap => do
    let doc ← readDoc
    let text : FileMap := doc.meta.text
    let hoverPos : String.Pos := text.lspPosToUtf8Pos params.pos
    -- Robust probe around hover to avoid seam positions
    let results :=
      let rs0 := snap.infoTree.goalsAt? text hoverPos
      if rs0.isEmpty then
        let baseLsp := params.pos
        let probeRight : List Lsp.Position := (List.range 41).map (fun i => { line := baseLsp.line, character := baseLsp.character + i })
        let probeLeft  : List Lsp.Position := (List.range 4).map (fun i => { line := baseLsp.line, character := baseLsp.character - i })
        let probes := probeLeft ++ probeRight
        let rec firstSome (ps : List Lsp.Position) : List GoalsAtResult :=
          match ps with
          | [] => rs0
          | p :: ps' =>
            let pos := text.lspPosToUtf8Pos p
            let rs := snap.infoTree.goalsAt? text pos
            if rs.isEmpty then firstSome ps' else rs
        firstSome probes
      else rs0
    match results.head? with
    | some r =>
      let stx := r.tacticInfo.stx
      let range? := stx.getRange?
      let tacticRange? : Option RangeDto := range?.map (fun rg =>
        { start := text.utf8PosToLspPos rg.start, stop := text.utf8PosToLspPos rg.stop })
      -- Run Meta in the context of this tactic
      let ctxInfo := r.ctxInfo
      -- goal pretty and free vars
      let goal? ← ctxInfo.runMetaM {} do
        -- Prefer the first goal after, fallback to before
        let some g := r.tacticInfo.goalsAfter.head? <|> r.tacticInfo.goalsBefore.head?
          | return none
        let ty ← instantiateMVars (← g.getType)
        let pretty ← ppExpr ty
        let fvars := (← ty.collectFVars.run {}).2.fvarIds.map (·.name.toString)
        return some { pretty := pretty.pretty, freeVars := fvars }
      -- locals
      let locals ← ctxInfo.runMetaM {} do
        let lctx ← getLCtx
        let arr := lctx.decls.toList.filterMap id |>.toArray
        arr.mapM fun d => do
          let t ← instantiateMVars d.type
          let tPretty ← ppExpr t
          let fvs := (← t.collectFVars.run {}).2.fvarIds.map (·.name.toString)
          let binder := match d.binderInfo with
            | BinderInfo.default      => "default"
            | BinderInfo.implicit     => "implicit"
            | BinderInfo.strictImplicit=> "strictImplicit"
            | BinderInfo.instImplicit => "instImplicit"
          return { name := d.userName.toString,
                   binderInfo := binder,
                   isLet := d.isLet,
                   typePretty := tPretty.pretty,
                   dependsOn := fvs }
      return { tacticRange?, goal? := goal?, locals := locals }
    | none =>
      return {}

-- AST structure based on jixia's approach
/-
-- DEV-ONLY DTOs and helpers re-enabled for round-trip tooling (non-RPC)
structure SyntaxNodeDto where
  kind : String
  range? : Option RangeDto := none
  children : Array SyntaxNodeDto := #[]
  value? : Option String := none
  leading? : Option String := none
  trailing? : Option String := none
  pos? : Option Nat := none
  endPos? : Option Nat := none
  deriving FromJson, ToJson, Inhabited

-- (duplicate removed) see definition above at line ~207

def syntaxToDto (text : FileMap) : Syntax → SyntaxNodeDto
  | .missing => { kind := "missing" }
  | .node info kind args =>
    let range? := info.getRange?.map (RangeDto.fromStringRange text)
    { kind := kind.toString, range?, children := args.map (syntaxToDto text) }
  | .atom info val =>
    let range? := info.getRange?.map (RangeDto.fromStringRange text)
    { kind := "atom", range?, value? := some val }
  | .ident info _ val _ =>
    let range? := info.getRange?.map (RangeDto.fromStringRange text)
    { kind := "ident", range?, value? := some val.toString }

-- Minimal, deterministic formatter over Syntax (no string heuristics)
def formatSyntaxCustom (stx : Syntax) : String :=
  let rec go : Syntax → String
    | .missing => ""
    | .atom _ v => v
    | .ident _ _ v _ => v.toString
    | .node _ _ args =>
      let parts := args.map go
      parts.foldl (· ++ ·) ""
  go stx

-- DTO → Syntax (structural, spacing fields are ignored by construction)
def dtoToSyntax_export : SyntaxNodeDto → Syntax
  | { kind := "missing", .. } => .missing
  | { kind := "atom", value? := some v, .. } =>
    let info := SourceInfo.synthetic (pos := ⟨0⟩) (endPos := ⟨0⟩) (canonical := true)
    .atom info v
  | { kind := "ident", value? := some v, .. } =>
    let name : Name := v.split (· == '.') |>.foldl Name.mkStr Name.anonymous
    let info := SourceInfo.synthetic (pos := ⟨0⟩) (endPos := ⟨0⟩) (canonical := false)
    .ident info v.toSubstring name []
  | { kind, children, .. } =>
    let k := kind.split (· == '.') |>.foldl Name.mkStr Name.anonymous
    let args := children.map dtoToSyntax_export
    let info := SourceInfo.synthetic (pos := ⟨0⟩) (endPos := ⟨0⟩) (canonical := false)
    .node info k args

--
-- DEPRECATED/DEV-ONLY: AST 快照调试，不用于生产；不导出为 RPC
def getASTAtPosition (params : InputParams) : RequestM (RequestTask SyntaxNodeDto) := do
  withWaitFindSnapAtPos params.pos fun snap => do
    let doc ← readDoc
    let text : FileMap := doc.meta.text
    let hoverPos : String.Pos := text.lspPosToUtf8Pos params.pos

    -- First try tactic info (most reliable for our use case)
    -- Probe around hover to capture inline tactics like `rfl` in `:= by rfl`
    let results :=
      let rs0 := snap.infoTree.goalsAt? text hoverPos
      if rs0.isEmpty then
        let baseLsp := params.pos
        let probeRight : List Lsp.Position := (List.range 41).map (fun i => { line := baseLsp.line, character := baseLsp.character + i })
        let probeLeft  : List Lsp.Position := (List.range 4).map (fun i => { line := baseLsp.line, character := baseLsp.character - i })
        let probes := probeLeft ++ probeRight
        let rec firstSome (ps : List Lsp.Position) : List GoalsAtResult :=
          match ps with
          | [] => rs0
          | p :: ps' =>
            let pos := text.lspPosToUtf8Pos p
            let rs := snap.infoTree.goalsAt? text pos
            if rs.isEmpty then firstSome ps' else rs
        firstSome probes
      else rs0
    match results.head? with
    | some r =>
      let stx := r.tacticInfo.stx
      return syntaxToDto text stx
    | none =>
      -- If no tactic info, fall back to basic approach
      return { kind := "no_tactic_found" }

-- No longer needed since we fixed the root cause in AST construction
def fixLineSpacing (line : String) : String := line

-- Post-processing function (currently unused as we fixed the AST issue)
def fixPrettyPrinterSpacing (text : String) : String :=
  -- No longer needed since we fixed the root cause in AST construction
  text

-- REMOVED: Old manual formatting functions replaced by Lean native PrettyPrinter

/- DEPRECATED/DEV-ONLY: AST 修复占位，不用于生产 -/
def fixAstStructure (kindName : Name) (args : Array Syntax) : Array Syntax :=
  -- 暂时只返回原始参数，将来扩展修复逻辑
  args

/- DEPRECATED/DEV-ONLY: DTO→Syntax 仅用于回环测试 -/
def dtoToSyntax_dev1 : SyntaxNodeDto → Syntax
  | { kind := "missing", .. } => .missing
  | { kind := "atom", value? := some val, leading?, trailing?, pos?, endPos?, .. } =>
    -- 特殊处理：人工插入的换行符
    if val == "\n" then
      let syntheticInfo := SourceInfo.synthetic (pos := ⟨0⟩) (endPos := ⟨1⟩) (canonical := true)
      .atom syntheticInfo val
    else if val.startsWith "«" && val.endsWith "»" then
      -- 通用规则：被引号包裹的标识符按ident处理，避免无意义的引号
      let core := (val.drop 1).dropRight 1
      let substr := core.toSubstring
      let name : Name := core.split (· == '.') |>.foldl Name.mkStr Name.anonymous
      match leading?, trailing? with
      | some leading, some trailing =>
        if leading.trim.isEmpty && trailing.trim.isEmpty then
          let leadingSubstr := leading.toSubstring
          let trailingSubstr := trailing.toSubstring
          let startPos : String.Pos := ⟨0⟩
          let endPos : String.Pos := ⟨0⟩
          let originalInfo := SourceInfo.original leadingSubstr startPos trailingSubstr endPos
          .ident originalInfo substr name []
        else
          let syntheticInfo := SourceInfo.synthetic (pos := ⟨0⟩) (endPos := ⟨0⟩) (canonical := false)
          .ident syntheticInfo substr name []
      | _, _ =>
        let syntheticInfo := SourceInfo.synthetic (pos := ⟨0⟩) (endPos := ⟨0⟩) (canonical := false)
        .ident syntheticInfo substr name []
    else
      -- 正常的atom处理
      match leading?, trailing? with
      | some leading, some trailing =>
        let leadingSubstr := leading.toSubstring
        let trailingSubstr := trailing.toSubstring
        let originalInfo := SourceInfo.original leadingSubstr ⟨0⟩ trailingSubstr ⟨0⟩
        .atom originalInfo val
      | _, _ =>
        let syntheticInfo := SourceInfo.synthetic (pos := ⟨0⟩) (endPos := ⟨0⟩) (canonical := true)
        .atom syntheticInfo val
  | { kind := "ident", value? := some val, leading?, trailing?, pos?, endPos?, .. } =>
    -- 对ident：忽略pos/endPos；仅在leading/trailing是纯空白时用original承载空白，否则synthetic
    let substr := val.toSubstring
    let name : Name := val.split (· == '.') |>.foldl Name.mkStr Name.anonymous
    match leading?, trailing? with
    | some leading, some trailing =>
      if leading.trim.isEmpty && trailing.trim.isEmpty then
        let leadingSubstr := leading.toSubstring
        let trailingSubstr := trailing.toSubstring
        let originalInfo := SourceInfo.original leadingSubstr ⟨0⟩ trailingSubstr ⟨0⟩
        .ident originalInfo substr name []
      else
        let syntheticInfo := SourceInfo.synthetic (pos := ⟨0⟩) (endPos := ⟨0⟩) (canonical := false)
        .ident syntheticInfo substr name []
    | _, _ =>
      let syntheticInfo := SourceInfo.synthetic (pos := ⟨0⟩) (endPos := ⟨0⟩) (canonical := false)
      .ident syntheticInfo substr name []
  | { kind, children, leading?, trailing?, pos?, endPos?, .. } =>
    -- Parse the kind string back to Name
    let kindName := kind.split (· == '.') |>.foldl Name.mkStr Name.anonymous
    let args := children.map dtoToSyntax_dev1

    -- AST层面修复：处理特殊情况
    let fixedArgs := fixAstStructure kindName args

    -- 对node也使用原始SourceInfo
    match leading?, trailing? with
    | some leading, some trailing =>
      let leadingSubstr := leading.toSubstring
      let trailingSubstr := trailing.toSubstring
      let originalInfo := SourceInfo.original leadingSubstr ⟨0⟩ trailingSubstr ⟨0⟩
      .node originalInfo kindName fixedArgs
    | _, _ =>
      let syntheticInfo := SourceInfo.synthetic (pos := ⟨0⟩) (endPos := ⟨0⟩) (canonical := false)
      .node syntheticInfo kindName fixedArgs

/- DEPRECATED/DEV-ONLY -/
structure TextConversionParams where
  syntaxData : SyntaxNodeDto
  deriving FromJson, ToJson

/- DEPRECATED/DEV-ONLY: 不导出为 RPC -/
def formatASTToText (params : TextConversionParams) : RequestM (RequestTask TextConversionResult) := do
  RequestM.asTask do
    let stx := dtoToSyntax_dev1 params.syntaxData
    let text ← formatSyntax stx
    return { text := text, success := true }

-- Test round-trip conversion: position -> AST -> text -> verify
/- DEPRECATED/DEV-ONLY -/
structure RoundTripTestParams where
  pos : Lsp.Position
  deriving FromJson, ToJson

/- DEPRECATED/DEV-ONLY -/
structure RoundTripTestResult where
  originalSyntax : String
  convertedText : String
  success : Bool
  errorMsg : Option String := none
  deriving FromJson, ToJson

/- DEPRECATED/DEV-ONLY: 不导出为 RPC -/
def testRoundTripConversion (params : RoundTripTestParams) : RequestM (RequestTask RoundTripTestResult) := do
  withWaitFindSnapAtPos params.pos fun snap => do
    let doc ← readDoc
    let text : FileMap := doc.meta.text
    let hoverPos : String.Pos := text.lspPosToUtf8Pos params.pos

    -- Step 1: Get AST at position (use same logic as getASTAtPosition)
    -- Robust probe around hover to avoid seam positions
    let results :=
      let rs0 := snap.infoTree.goalsAt? text hoverPos
      if rs0.isEmpty then
        let baseLsp := params.pos
        let probeRight : List Lsp.Position := (List.range 41).map (fun i => { line := baseLsp.line, character := baseLsp.character + i })
        let probeLeft  : List Lsp.Position := (List.range 4).map (fun i => { line := baseLsp.line, character := baseLsp.character - i })
        let probes := probeLeft ++ probeRight
        let rec firstSome (ps : List Lsp.Position) : List GoalsAtResult :=
          match ps with
          | [] => rs0
          | p :: ps' =>
            let pos := text.lspPosToUtf8Pos p
            let rs := snap.infoTree.goalsAt? text pos
            if rs.isEmpty then firstSome ps' else rs
        firstSome probes
      else rs0
    match results.head? with
    | some r =>
      let originalStx := r.tacticInfo.stx
      -- Step 2: Convert to DTO
      let dto := syntaxToDto text originalStx

      -- Step 3: Convert DTO back to Syntax (without original positions)
      let reconstructedStx := dtoToSyntax_dev1 dto

      -- Step 4: Format both for comparison
      let originalText ← formatSyntax originalStx
      let convertedText ← formatSyntax reconstructedStx

      return {
        originalSyntax := originalText,
        convertedText := convertedText,
        success := true
      }
    | none =>
      return {
        originalSyntax := "",
        convertedText := "",
        success := false,
        errorMsg := some "No syntax found at position"
      }

-/

/-- Insert a have statement at the end of the tactic sequence -/
def RangeDto.fromStringRange (text : FileMap) (range : String.Range) : RangeDto :=
  { start := text.utf8PosToLspPos range.start, stop := text.utf8PosToLspPos range.stop }

/- DEPRECATED/LEGACY: 旧的序列末尾插入原型，不用于生产 -/
def insertHaveStatement (originalStx : Syntax) (haveStmt : Syntax) : Syntax :=
  match originalStx with
  | .node info kind args =>
    -- For a tactic sequence, we want to add the have statement to the end
    let newArgs := args.push haveStmt
    .node info kind newArgs
  | _ => originalStx  -- If it's not a node, just return the original

/- DEPRECATED/LEGACY: 旧接口，不用于生产 -/
structure InsertHaveParams where
  pos : Lsp.Position
  haveStatement : String  -- The have statement as a string
  deriving FromJson, ToJson

/- DEPRECATED/LEGACY -/
structure InsertHaveResult where
  newText : String
  range   : RangeDto
  success : Bool
  errorMsg : Option String := none
  deriving FromJson, ToJson

def parseTacticSnippet (env : Environment) (s : String) : Except String Syntax :=
  -- Parse a single tactic snippet using Lean's parser category
  Parser.runParserCategory env `tactic s

def splitTacticSegments (s : String) : List String :=
  -- Split by newlines and semicolons, trimming blanks
  let parts := s.split (fun c => c = '\n' || c = ';')
  parts.map (·.trim) |>.filter (fun t => ¬ t.isEmpty)

def parseTacticSegments (env : Environment) (s : String) : List Syntax :=
  (splitTacticSegments s).foldl (fun acc seg =>
    match parseTacticSnippet env seg with
    | .ok stx  => acc ++ [stx]
    | .error _ => acc) []

/- DEPRECATED/DEV-ONLY: 未在生产路径使用 -/
def parseTacticSeq (env : Environment) (s : String) : Except String Syntax :=
  Parser.runParserCategory env `tacticSeq1Indented s

def formatTacticSeq (stx : Syntax) : MetaM String := do
  -- Use Lean's native PrettyPrinter instead of manual formatting
  let isSeqKind (k : Name) : Bool :=
    k == `Lean.Parser.Tactic.tacticSeq ||
    k == `Lean.Parser.Tactic.tacticSeq1Indented ||
    k == `Lean.Parser.Tactic.tacticSeqBracketed

  match stx with
  | .node _ kind _ =>
    -- Determine the correct category based on the syntax kind
    let category := if isSeqKind kind then `tacticSeq else `tactic
    -- Use Lean's native formatting
    let fmt ← PrettyPrinter.ppCategory category stx
    return fmt.pretty
  | _ =>
    -- For non-node syntax, use tactic category
    let fmt ← PrettyPrinter.ppCategory `tactic stx
    return fmt.pretty

/-- Keep only tactics whose range ends at or before the given position. Best-effort without relying on specific kinds. -/
/- DEPRECATED/LEGACY: 旧裁剪策略，不用于生产 -/
def trimTacticSequenceAt (stx : Syntax) (pos : String.Pos) : Syntax :=
  let isSeqKind (k : Name) : Bool :=
    k == `Lean.Parser.Tactic.tacticSeq ||
    k == `Lean.Parser.Tactic.tacticSeq1Indented ||
    k == `Lean.Parser.Tactic.tacticSeqBracketed
  let mkEmptySeq : Syntax :=
    let info := SourceInfo.synthetic (pos := ⟨0⟩) (endPos := ⟨0⟩) (canonical := true)
    Syntax.node info `Lean.Parser.Tactic.tacticSeq1Indented #[]
  match stx with
  | .node info kind args =>
    if isSeqKind kind then
      -- Keep only tactics that end at or before the cursor
      let kept := args.filter (fun a =>
        match a.getRange? with
        | some r => r.stop ≤ pos
        | none   => true)
      .node info kind kept
    else
      -- Not a sequence: wrap-or-drop the single tactic based on its end position
      match stx.getRange? with
      | some r =>
        if r.stop ≤ pos then
          -- Tactic ends before cursor: keep it by wrapping into a single-item sequence
          Syntax.node info `Lean.Parser.Tactic.tacticSeq1Indented #[stx]
        else
          -- Tactic extends beyond cursor: drop it by returning an empty sequence
          mkEmptySeq
      | none => mkEmptySeq
  | s =>
    -- Atom/ident/missing: treat as a single tactic and apply the same keep/drop rule
    match s.getRange? with
    | some r => if r.stop ≤ pos then
                  Syntax.node (SourceInfo.synthetic (pos := ⟨0⟩) (endPos := ⟨0⟩) (canonical := true)) `Lean.Parser.Tactic.tacticSeq1Indented #[s]
                else mkEmptySeq
    | none => mkEmptySeq

/-!- Unified sequence editing helpers -/
def isTacticSeqKind (k : Name) : Bool :=
  k == `Lean.Parser.Tactic.tacticSeq ||
  k == `Lean.Parser.Tactic.tacticSeq1Indented ||
  k == `Lean.Parser.Tactic.tacticSeqBracketed

def flattenTacticSeqArgs (stx : Syntax) : Array Syntax :=
  match stx with
  | .node _ kind args => if isTacticSeqKind kind then args else #[stx]
  | s => #[s]

def buildIndentedSeq (args : Array Syntax) : Syntax :=
  let info := SourceInfo.synthetic (pos := ⟨0⟩) (endPos := ⟨0⟩) (canonical := true)
  Syntax.node info `Lean.Parser.Tactic.tacticSeq1Indented args

/-!
  Shared helpers: choose the smallest enclosing tactic sequence container
  from a syntax path, falling back to the provided leaf if none is present.
-/
private def chooseSmallestTacticSeq (stxs : List Syntax) (fallback : Syntax) : Syntax :=
  let candidates := stxs.filter (fun s => isTacticSeqKind s.getKind)
  match candidates with
  | []      => fallback
  | c :: cs =>
    let pick (a b : Syntax) : Syntax :=
      match a.getRange?, b.getRange? with
      | some ra, some rb => if ra.stop.byteIdx - ra.start.byteIdx ≤ rb.stop.byteIdx - rb.start.byteIdx then a else b
      | _, _ => a
    cs.foldl pick c

@[server_rpc_method]
def insertHaveAtPosition (params : InsertHaveParams) : RequestM (RequestTask InsertHaveResult) := do
  withWaitFindSnapAtPos params.pos fun snap => do
    let doc ← readDoc
    let text : FileMap := doc.meta.text
    let hoverPos : String.Pos := text.lspPosToUtf8Pos params.pos

    -- Get the AST at the position
    -- Robust probe around hover to avoid seam positions
    let results :=
      let rs0 := snap.infoTree.goalsAt? text hoverPos
      if rs0.isEmpty then
        let baseLsp := params.pos
        let probeRight : List Lsp.Position := (List.range 41).map (fun i => { line := baseLsp.line, character := baseLsp.character + i })
        let probeLeft  : List Lsp.Position := (List.range 4).map (fun i => { line := baseLsp.line, character := baseLsp.character - i })
        let probes := probeLeft ++ probeRight
        let rec firstSome (ps : List Lsp.Position) : List GoalsAtResult :=
          match ps with
          | [] => rs0
          | p :: ps' =>
            let pos := text.lspPosToUtf8Pos p
            let rs := snap.infoTree.goalsAt? text pos
            if rs.isEmpty then firstSome ps' else rs
        firstSome probes
      else rs0
    match results.head? with
    | some r0 =>
      -- Prefer enclosing tactic-sequence container as edit target
      let path := results
      let stxs := path.map (fun rr => rr.tacticInfo.stx)
      let isSeqKind (k : Name) : Bool :=
        k == `Lean.Parser.Tactic.tacticSeq ||
        k == `Lean.Parser.Tactic.tacticSeq1Indented ||
        k == `Lean.Parser.Tactic.tacticSeqBracketed
      let chooseContainer (xs : List Syntax) : Syntax :=
        let candidates := xs.filter (fun s => isSeqKind s.getKind)
        match candidates with
        | []      => r0.tacticInfo.stx
        | c :: cs =>
          let pick (a b : Syntax) : Syntax :=
            match a.getRange?, b.getRange? with
            | some ra, some rb => if ra.stop.byteIdx - ra.start.byteIdx ≤ rb.stop.byteIdx - rb.start.byteIdx then a else b
            | _, _ => a
          cs.foldl pick c
      let originalStx := chooseContainer stxs
      let env := r0.ctxInfo.env
      -- Flatten → filter by end ≤ pos → append parsed haveStatement tactics → rebuild sequence
      let baseArgs := flattenTacticSeqArgs originalStx
      let kept := baseArgs.filter (fun a => match a.getRange? with | some r => r.stop ≤ hoverPos | none => true)
      let haveTactics := parseTacticSegments env params.haveStatement
      let newArgs := kept ++ haveTactics.toArray
      let newStx := buildIndentedSeq newArgs
      let body ← r0.ctxInfo.runMetaM {} do
        formatTacticSeq newStx
      let range := (originalStx.getRange?).map (RangeDto.fromStringRange text)
      let some r := range | return { newText := body, range := { start := params.pos, stop := params.pos }, success := true }
      -- Compute indentation based on start column; if original was not a sequence, prefix 'by' and indent children by two spaces
      -- Derive base indentation from client-anchored position (right after '=>')
      let baseIndent := String.mk (List.replicate params.pos.character ' ')
      let isSeq := isTacticSeqKind originalStx.getKind
      let mkIndented (indent : String) (s : String) : String :=
        let parts := s.splitOn "\n"
        parts.foldl (fun acc ln => if acc.isEmpty then indent ++ ln else acc ++ "\n" ++ indent ++ ln) ""
      let finalText := s!"\n{mkIndented (baseIndent ++ "  ") body}"
      return { newText := finalText, range := r, success := true }
    | none =>
      return {
        newText := "",
        range := { start := params.pos, stop := params.pos },
        success := false,
        errorMsg := some "No syntax found at position"
      }

structure InsertHaveByActionParams where
  pos    : Lsp.Position
  action : String   -- "admit" | "deny"
  blockRange? : Option RangeDto := none
  includeByOnSeq? : Option Bool := none
  returnWholeFile? : Option Bool := none
  deriving FromJson, ToJson

structure InsertHaveByActionResult where
  newText : String
  range   : RangeDto
  success : Bool
  errorMsg : Option String := none
  deriving FromJson, ToJson

@[server_rpc_method]
def insertHaveByAction (params : InsertHaveByActionParams) : RequestM (RequestTask InsertHaveByActionResult) := do
  let _ ← IO.FS.writeFile (System.mkFilePath ["tmp", "matheye_rpc_called.log"]) s!"insertHaveByAction called at {params.pos}
"
  let _ ← IO.FS.writeFile (System.mkFilePath ["tmp", "debug_params.log"]) s!"params.pos = {params.pos}
params.action = {params.action}
params.blockRange.isSome = {params.blockRange?.isSome}
"
  withWaitFindSnapAtPos params.pos fun snap => do
    let doc ← readDoc
    let text : FileMap := doc.meta.text
    let hoverPos : String.Pos := text.lspPosToUtf8Pos params.pos
    -- Robust probe around hover to avoid seam positions
    let results :=
      let rs0 := snap.infoTree.goalsAt? text hoverPos
      if rs0.isEmpty then
        let baseLsp := params.pos
        let probeRight : List Lsp.Position := (List.range 41).map (fun i => { line := baseLsp.line, character := baseLsp.character + i })
        let probeLeft  : List Lsp.Position := (List.range 4).map (fun i => { line := baseLsp.line, character := baseLsp.character - i })
        let probes := probeLeft ++ probeRight
        let rec firstSome (ps : List Lsp.Position) : List GoalsAtResult :=
          match ps with
          | [] => rs0
          | p :: ps' =>
            let pos := text.lspPosToUtf8Pos p
            let rs := snap.infoTree.goalsAt? text pos
            if rs.isEmpty then firstSome ps' else rs
        firstSome probes
      else rs0
    let _ ← IO.FS.writeFile (System.mkFilePath ["tmp", "debug_positions.log"]) s!"hoverPos = {hoverPos}
text.lspPosToUtf8Pos = {text.lspPosToUtf8Pos params.pos}
results.length = {results.length}
"
    match results.head? with
    | none =>
      -- 1) Broad tactic-only scan on the same line vicinity to find a reliable tactic container
      let base := params.pos
      let probeRight : List Lsp.Position := (List.range 81).map (fun i => { line := base.line, character := base.character + i })
      let probeLeft  : List Lsp.Position := (List.range 41).map (fun i => { line := base.line, character := base.character - i })
      let probes := probeLeft.reverse ++ probeRight
      let rec firstTactic (ps : List Lsp.Position) : Option (Syntax × RangeDto × GoalsAtResult) :=
        match ps with
        | [] => none
        | p :: ps' =>
          let pos := text.lspPosToUtf8Pos p
          let path := snap.infoTree.goalsAt? text pos
          match path.head? with
          | none => firstTactic ps'
          | some r1 =>
            let stxs := path.map (fun rr => rr.tacticInfo.stx)
            let container := chooseSmallestTacticSeq stxs r1.tacticInfo.stx
            match container.getRange? with
            | some rg => some (container, RangeDto.fromStringRange text rg, r1)
            | none => firstTactic ps'
      let picked? := firstTactic probes
      -- 2) Fallback: probe inside provided blockRange start (if any)
      let rr0 := params.blockRange?.getD { start := params.pos, stop := params.pos }
      let resAt := (snap.infoTree.goalsAt? text (String.Pos.mk ((text.lspPosToUtf8Pos rr0.start).byteIdx + 1)))
      let picked? := match picked? with
        | some x => some x
        | none =>
          match resAt.head? with
          | some r0 =>
            let stx0 := r0.tacticInfo.stx
            match stx0.getRange? with
            | some rg => some (stx0, RangeDto.fromStringRange text rg, r0)
            | none => none
          | none => none
      -- 3) If still none, give up explicitly
      match picked? with
      | none => return { newText := "", range := rr0, success := false, errorMsg := some "No tactic at pos" }
      | some (container, rr, rCtx) =>
        -- Read goal type near the container
        let tyStr? ← rCtx.ctxInfo.runMetaM {} do
          try
            let g? := rCtx.tacticInfo.goalsBefore.head? <|> rCtx.tacticInfo.goalsAfter.head?
            match g? with
            | some g =>
              let ty ← instantiateMVars (← g.getType)
              let fmt ← ppExpr ty
              return some fmt.pretty
            | none => return none
          catch _ => pure none
        let some tyStr := tyStr? | return { newText := "", range := rr, success := false, errorMsg := some "No goal type" }
        let name := s!"h_{params.pos.line}_{params.pos.character}"
        let action := params.action.trim
        let snippet := if action == "deny"
          then s!"have {name} : ¬ ({tyStr}) := by human_oracle"
          else s!"have {name} : {tyStr} := by human_oracle\nexact {name}"
        let body := snippet
        let baseIndent := String.mk (List.replicate rr.start.character ' ')
        let mkIndented (indent : String) (s : String) : String :=
          let parts := s.splitOn "\n"
          parts.foldl (fun acc ln => if acc.isEmpty then indent ++ ln else acc ++ "\n" ++ indent ++ ln) ""
        let includeBy := params.includeByOnSeq?.getD false
        let replacementSeg := if includeBy then s!"by\n{mkIndented baseIndent body}" else s!"\n{mkIndented baseIndent body}"
        let retWhole := params.returnWholeFile?.getD true
        if retWhole then
          let replaceStartUtf8 := text.lspPosToUtf8Pos rr.start
          let replaceStopUtf8  := text.lspPosToUtf8Pos rr.stop
          let src := text.source
          let pre := src.extract ⟨0⟩ replaceStartUtf8
          let suf := src.extract replaceStopUtf8 src.endPos
          let newFull := pre ++ replacementSeg ++ suf
          let fullRange : RangeDto := { start := { line := 0, character := 0 }, stop := text.utf8PosToLspPos src.endPos }
          return { newText := newFull, range := fullRange, success := true }
        else
          return { newText := replacementSeg, range := rr, success := true }
    | some r =>
      -- Unify container selection here: always choose smallest enclosing tactic sequence.
      let path := results
      let stxs := path.map (fun rr => rr.tacticInfo.stx)
      let originalStx := chooseSmallestTacticSeq stxs r.tacticInfo.stx
      let rr : RangeDto := match originalStx.getRange? with
        | some rg => RangeDto.fromStringRange text rg
        | none    => { start := params.pos, stop := params.pos }
      -- Stable position: clamp the actual hover position into the provided/found block range,
      -- to keep leaf context (e.g., inline `rfl`) instead of outer containers.
      let blockStartUtf8 := text.lspPosToUtf8Pos rr.start
      let blockStopUtf8  := text.lspPosToUtf8Pos rr.stop
      let lo := if blockStartUtf8.byteIdx + 1 < blockStopUtf8.byteIdx then ⟨blockStartUtf8.byteIdx + 1⟩ else blockStartUtf8
      let hi := if blockStopUtf8.byteIdx > blockStartUtf8.byteIdx + 1 then ⟨blockStopUtf8.byteIdx - 1⟩ else blockStopUtf8
      let stablePos :=
        if hoverPos.byteIdx < lo.byteIdx then lo else if hoverPos.byteIdx > hi.byteIdx then hi else hoverPos
      -- Fetch a reliable ctx for goal type; on failure, return explicit error (no fallback)
      let resultsStable := snap.infoTree.goalsAt? text stablePos
      let name := s!"h_{params.pos.line}_{params.pos.character}"
      let action := params.action.trim
      let _ ← IO.FS.writeFile (System.mkFilePath ["tmp", "debug_names.log"]) s!"name = {name}
action = {action}
params.pos.line = {params.pos.line}
params.pos.character = {params.pos.character}
"
      -- 如果容器不是 tacticSeq，尝试在其子树中找到一个具体的 tactic 节点（如 rfl）作为目标
      let isTacticNode (s : Syntax) : Bool := true  -- 简化：接受所有节点
      let rec findInnerTactic (s : Syntax) : Option Syntax :=
        if isTacticNode s then some s else
        match s with
        | .node _ _ args =>
          let rec loop (i : Nat) : Option Syntax :=
            if h : i < args.size then
              match findInnerTactic (args[i]'h) with
              | some t => some t
              | none => loop (i+1)
            else none
          loop 0
        | _ => none
      -- If the chosen container is not a tactic sequence (e.g., inline `rfl` tail), force the edit to happen
      -- at the container level by treating the container itself as the target. This ensures the inline tactic
      -- is fully replaced by a block body.
      let targetStx :=
        if isTacticSeqKind originalStx.getKind then
          originalStx
        else
          originalStx
      -- Try to get goal type strictly（容器内复刻 Lean 的最优选择）：
      -- 1) 收集容器内的候选（沿稳定路径），优先选择容器内最内层的节点
      -- 候选来自路径（稳定优先，然后原始），不再限制于某个容器 range，直接选“最内层”（最短范围）
      let isTacticNode (s : Syntax) : Bool := true  -- 简化：接受所有节点
      let pathCands : List (GoalsAtResult × String.Range) := resultsStable.filterMap (fun (gr : GoalsAtResult) =>
        let stx := gr.tacticInfo.stx
        match stx.getRange? with
        | some rg => if isTacticNode stx then some (gr, rg) else none
        | none => none)
      -- Debug: 记录候选数量
      let _ := IO.FS.writeFile "/tmp/matheye_debug.log" s!"pathCands.length={pathCands.length}; resultsStable.length={resultsStable.length}; results.length={results.length}
"
      let chosen? :=
        if let some last := pathCands.reverse.head? then some last else
        -- 退一步用原始 hover 路径
        (results.filterMap (fun (gr : GoalsAtResult) =>
          let stx := gr.tacticInfo.stx
          match stx.getRange? with
          | some rg => if isTacticNode stx then some (gr, rg) else none
          | none => none)).reverse.head?
      -- 若上面仍空，退回到 hover 的 head（仍是精确节点）
      let chosen? := match chosen? with | some c => some c | none => (do
        let r0? := results.head?
        match r0? with
        | some r0 =>
          let stx0 := r0.tacticInfo.stx
          if isTacticNode stx0 then
            match stx0.getRange? with
            | some rg0 => some (r0, rg0)
            | none => none
          else none
        | none => none)
      -- 最终在候选序列中选“最内层”（范围最短）
      let chosen? :=
        match chosen? with
        | some c =>
          let best := (pathCands ++ (results.filterMap (fun (gr : GoalsAtResult) =>
            match gr.tacticInfo.stx.getRange? with | some rg => some (gr, rg) | none => none))).foldl
              (fun (acc : Option (GoalsAtResult × String.Range)) (cur : (GoalsAtResult × String.Range)) =>
                match acc with
                | none => some cur
                | some prA =>
                  let rgA := prA.snd
                  let rgB := cur.snd
                  let lenA := rgA.stop.byteIdx - rgA.start.byteIdx
                  let lenB := rgB.stop.byteIdx - rgB.start.byteIdx
                  if lenB < lenA then some cur else acc)
              (some c)
          best
        | none => none
      -- 2) 依据 Lean 的 useAfter 定义（无嵌套即最内层），读取 before/after 目标；若路径上无战术节点，做一次“结构化探针”（用子战术range.start+1）
      let tyStr? ← do
        match chosen? with
        | none =>
          -- 结构化探针：选 lastKept 或第一个战术，进入其体内的两个严格结构位置（pos+1 / tail-1）查询
          let baseArgs := flattenTacticSeqArgs targetStx
          let lastKept? := baseArgs.foldl (init := none) (fun acc a =>
            match a.getRange? with | some rg => if decide (rg.start.byteIdx < stablePos.byteIdx) then some a else acc | none => acc)
          let probe? := lastKept? <|> baseArgs.get? 0
          match probe? with
          | some t =>
            let posOpt := t.getPos?
            let tailOpt := t.getTailPos?
            let pts : List String.Pos :=
              let mk (n : Nat) : String.Pos := ⟨n⟩
              let tailInside? := tailOpt.bind (fun tp => if tp.byteIdx > 0 then some (mk (tp.byteIdx - 1)) else none)
              let posInside?  := posOpt.map (fun p => mk (p.byteIdx + 1))
              match tailInside?, posInside? with
              | some a, some b => [a, b]
              | some a, none   => [a]
              | none, some b   => [b]
              | none, none     => []
            let rec tryPts (ps : List String.Pos) : RequestM (Option String) := do
                match ps with
                | [] => pure none
                | p :: ps' =>
                  let resAt := snap.infoTree.goalsAt? text p
                  match resAt.head? with
                  | none => tryPts ps'
                  | some gr =>
                    let r? ← gr.ctxInfo.runMetaM {} do
                      try
                        let g? := gr.tacticInfo.goalsBefore.head? <|> gr.tacticInfo.goalsAfter.head?
                        match g? with
                        | some g => let ty ← instantiateMVars (← g.getType); let fmt ← ppExpr ty; return some fmt.pretty
                        | none => return none
                      catch _ => return none
                    match r? with
                    | some s => pure (some s)
                    | none => tryPts ps'
            tryPts pts
          | none => pure none
        | some (gr, rg) =>
          let pos := rg.start
          let useAfter := decide (pos < stablePos)
          gr.ctxInfo.runMetaM {} do
            try
              let pick (afterFirst : Bool) : MetaM (Option String) := do
                let g1? := if afterFirst then gr.tacticInfo.goalsAfter.head? else gr.tacticInfo.goalsBefore.head?
                match g1? with
                | some g1 =>
                  let ty ← instantiateMVars (← g1.getType); let fmt ← ppExpr ty; return some fmt.pretty
                | none =>
                  let g2? := if afterFirst then gr.tacticInfo.goalsBefore.head? else gr.tacticInfo.goalsAfter.head?
                  match g2? with
                  | some g2 =>
                    let ty ← instantiateMVars (← g2.getType); let fmt ← ppExpr ty; return some fmt.pretty
                  | none => return none
              let afterFirst := useAfter
              pick afterFirst
            catch _ => pure none
      -- 2.1) 仍无则在稳定路径与原始路径上线性扫描，优先稳定路径；每个节点按 useAfter 选择 before/after
      let tyStr? ← do
        match tyStr? with
        | some s => pure (some s)
        | none   =>
          let pickFrom (gr : GoalsAtResult) (afterFirst : Bool) : MetaM (Option String) := do
            try
              let g1? := if afterFirst then gr.tacticInfo.goalsAfter.head? else gr.tacticInfo.goalsBefore.head?
              match g1? with
              | some g1 =>
                let ty ← instantiateMVars (← g1.getType); let fmt ← ppExpr ty; return some fmt.pretty
              | none =>
                let g2? := if afterFirst then gr.tacticInfo.goalsBefore.head? else gr.tacticInfo.goalsAfter.head?
                match g2? with
                | some g2 => let ty ← instantiateMVars (← g2.getType); let fmt ← ppExpr ty; return some fmt.pretty
                | none => return none
            catch _ => pure none
          let rec scan (xs : List GoalsAtResult) : RequestM (Option String) := do
            match xs with
            | [] => pure none
            | gr :: rest =>
              let useAfter :=
                match gr.tacticInfo.stx.getRange? with
                | some rg => decide (rg.start < stablePos)
                | none    => true
              let s? ← gr.ctxInfo.runMetaM {} (pickFrom gr useAfter)
              match s? with
              | some s => pure (some s)
              | none   => scan rest
          -- try stable path then fallback to original path
          let s1? ← scan resultsStable
          match s1? with
          | some s => pure (some s)
          | none   => scan results
      -- 2.2) 仍无则在容器起点内侧再探测一次（by 块体内第一个字节）
      let tyStr? ← do
        match tyStr? with
        | some s => pure (some s)
        | none   =>
          let probeUtf8 := text.lspPosToUtf8Pos rr.start
          let probeInside : String.Pos := ⟨probeUtf8.byteIdx + 1⟩
          let resAt := snap.infoTree.goalsAt? text probeInside
          match resAt.head? with
          | none => pure none
          | some gr => gr.ctxInfo.runMetaM {} do
              try
                let g? := gr.tacticInfo.goalsBefore.head? <|> gr.tacticInfo.goalsAfter.head?
                match g? with
                | some g =>
                  let ty ← instantiateMVars (← g.getType)
                  let fmt ← ppExpr ty
                  return some fmt.pretty
                | none => return none
              catch _ => pure none
      -- 若仍未获得类型，最后尝试直接从稳定路径的首节点读取 before/after（不引入占位符）
      let tyStr? ← do
        match tyStr? with
        | some s => pure (some s)
        | none =>
          match resultsStable.head? with
          | none => pure none
          | some gr => (gr.ctxInfo).runMetaM {} do
              try
                let g0? := gr.tacticInfo.goalsBefore.head? <|> gr.tacticInfo.goalsAfter.head?
                match g0? with
                | some g0 =>
                  let ty ← instantiateMVars (← g0.getType)
                  let fmt ← ppExpr ty
                  return some fmt.pretty
                | none => return none
              catch _ =>
                pure none
      -- 最终若仍无，明确报错（不做 `_` 回退）
      let some tyStr := tyStr? |
        let dbg :=
          let chosenStr := match chosen? with
            | some (gr, rg) => s!"{gr.tacticInfo.stx.getKind.toString}@{rg.start.byteIdx}-{rg.stop.byteIdx}"
            | none => "none"
          s!"failed to read goal type at stable position; chosen={chosenStr}; pathStable={resultsStable.length}; results={results.length}; stablePos={stablePos.byteIdx}"
        let _ := IO.FS.writeFile "/tmp/matheye_debug.log" s!"DEBUG FAILURE: {dbg}\n"
        return { newText := "", range := rr, success := false, errorMsg := some dbg }
      let snippet := if action == "deny"
        then s!"have {name} : ¬ ({tyStr}) := by human_oracle"
        else s!"have {name} : {tyStr} := by human_oracle\nexact {name}"
      -- Reconstruct: keep prefix tactics up to stablePos, then append snippet
      -- Choose actual container from stable path
      let env := (resultsStable.head?.getD r).ctxInfo.env
      let baseArgs := flattenTacticSeqArgs targetStx
      -- If the target is not a tactic sequence (e.g., inline `rfl`), drop it entirely to avoid keeping it.
      -- Otherwise, keep only tactics whose end position is strictly before the stable insertion point.
      let kept := match targetStx with
        | .node _ kind _ =>
          if isTacticSeqKind kind then
            baseArgs.filter (fun a => match a.getRange? with
              | some rg => decide (rg.stop.byteIdx < stablePos.byteIdx)
              | none => true)
          else
            #[]
        | _ => #[]
      let _ := IO.FS.writeFile "/tmp/matheye_debug.log" s!"SUCCESS: stablePos={stablePos.byteIdx}, baseArgs={baseArgs.size}, kept={kept.size}\n"
      let extra := parseTacticSegments env snippet
      let newArgs := kept ++ extra.toArray
      let newStx := buildIndentedSeq newArgs
      let body ← (resultsStable.head?.getD r).ctxInfo.runMetaM {} do
        formatTacticSeq newStx
      -- Indent and compute the replacement segment for the chosen container
      let some contRg := targetStx.getRange? | return { newText := body, range := rr, success := true }
      -- 优先使用客户端提供的 by 块范围进行落地；否则退回到当前目标节点的范围
      let contRange := match params.blockRange? with
        | some br => br
        | none    => RangeDto.fromStringRange text contRg
      let baseIndent := String.mk (List.replicate contRange.start.character ' ')
      let mkIndented (indent : String) (s : String) : String :=
        let parts := s.splitOn "\n"
        parts.foldl (fun acc ln => if acc.isEmpty then indent ++ ln else acc ++ "\n" ++ indent ++ ln) ""
      -- includeBy 由客户端的上下文判定控制（term 环境需要包 `by`），不在服务端做启发式推断
      let includeBy := params.includeByOnSeq?.getD false
      let replacementSeg := if includeBy
        then s!"by\n{mkIndented baseIndent body}"
        else s!"\n{mkIndented baseIndent body}"
      let retWhole := params.returnWholeFile?.getD true
      if retWhole then
        -- Splice into whole file deterministically and return whole-file replacement
        let replaceStartUtf8 := text.lspPosToUtf8Pos contRange.start
        let replaceStopUtf8  := text.lspPosToUtf8Pos contRange.stop
        let src := text.source
        let pre := src.extract ⟨0⟩ replaceStartUtf8
        let suf := src.extract replaceStopUtf8 src.endPos
        let newFull := pre ++ replacementSeg ++ suf
        let fullRange : RangeDto :=
          { start := { line := 0, character := 0 }
          , stop  := text.utf8PosToLspPos src.endPos }
        return { newText := newFull, range := fullRange, success := true }
      else
        return { newText := replacementSeg, range := contRange, success := true }

/-- Get current by-block (tactic) range at position -/
structure ByBlockRangeParams where
  pos : Lsp.Position
  deriving FromJson, ToJson

structure ByBlockRangeResult where
  range : RangeDto
  success : Bool
  errorMsg : Option String := none
  syntaxKind : Option String := none
  isMatchAlt : Bool := false
  parentKinds : Array String := #[]
  isTacticContext : Bool := false
  isTermContext : Bool := false
  deriving FromJson, ToJson

@[server_rpc_method]
def getByBlockRange (params : ByBlockRangeParams) : RequestM (RequestTask ByBlockRangeResult) := do
  withWaitFindSnapAtPos params.pos fun snap => do
    let doc ← readDoc
    let text : FileMap := doc.meta.text
    let hoverPos : String.Pos := text.lspPosToUtf8Pos params.pos

    -- Check both tactic and term contexts
    -- Robust probe around hover to avoid seam positions
    let tacticResults :=
      let rs0 := snap.infoTree.goalsAt? text hoverPos
      if rs0.isEmpty then
        let baseLsp := params.pos
        let probeRight : List Lsp.Position := (List.range 41).map (fun i => { line := baseLsp.line, character := baseLsp.character + i })
        let probeLeft  : List Lsp.Position := (List.range 4).map (fun i => { line := baseLsp.line, character := baseLsp.character - i })
        let probes := probeLeft ++ probeRight
        let rec firstSome (ps : List Lsp.Position) : List GoalsAtResult :=
          match ps with
          | [] => rs0
          | p :: ps' =>
            let pos := text.lspPosToUtf8Pos p
            let rs := snap.infoTree.goalsAt? text pos
            if rs.isEmpty then firstSome ps' else rs
        firstSome probes
      else rs0
    let termResults := snap.infoTree.termGoalAt? hoverPos
    let isTacticContext := tacticResults.length > 0
    let isTermContext := termResults.isSome

    match tacticResults.head? with
    | some r0 =>
      let path := tacticResults
      let stxs := path.map (fun rr => rr.tacticInfo.stx)
      -- Collect syntax context information
      let parentKinds : Array String := stxs.toArray.map (fun s => s.getKind.toString)
      let hasMatchAlt := parentKinds.any (fun k => k.startsWith "Lean.Parser.Term.matchAlt" || k.startsWith "Lean.Parser.Tactic.matchRhs")
      -- Prefer the smallest enclosing tactic sequence container as the by-block range
      let container0 := chooseSmallestTacticSeq stxs r0.tacticInfo.stx
      -- If the chosen node is a term `by` container, descend to its tacticSeq child when available
      let rec findTacticSeqChild (s : Syntax) : Option Syntax :=
        if isTacticSeqKind s.getKind then some s else
        match s with
        | .node _ _ args =>
          let rec loop (i : Nat) : Option Syntax :=
            if h : i < args.size then
              match findTacticSeqChild (args[i]'h) with
              | some t => some t
              | none => loop (i+1)
            else none
          loop 0
        | _ => none
      -- Enforce tactic-only: if no tacticSeq child found, report failure rather than mixing term context
      let container? := (findTacticSeqChild container0)
      let some container := container? | return {
        range := { start := params.pos, stop := params.pos },
        success := false,
        errorMsg := some "no tactic container",
        isTacticContext := false,
        isTermContext := false
      }
      let some rg := container.getRange? | return {
        range := { start := params.pos, stop := params.pos },
        success := false,
        errorMsg := some "no range"
      }
      return {
        range := RangeDto.fromStringRange text rg,
        success := true,
        syntaxKind := some container.getKind.toString,
        isMatchAlt := hasMatchAlt,
        parentKinds := parentKinds,
        isTacticContext := isTacticContext,
        isTermContext := isTermContext
      }
    | none =>
      -- No tactic context found, check if we're in term context
      let termResults := snap.infoTree.termGoalAt? hoverPos
      let isTermContext := termResults.isSome
      return {
        range := { start := params.pos, stop := params.pos },
        success := false,
        errorMsg := some "no tactic at pos",
        isTacticContext := false,
        isTermContext := isTermContext
      }

/-- Convert AST data to formatted text using Lean native formatter -/
/- DEPRECATED/DEV-ONLY: 不导出为 RPC -/
def convertASTToText (params : ASTDataParams) : RequestM (RequestTask TextConversionResult) := do
  RequestM.asTask do
    -- Real implementation: Parse JSON → DTO → Syntax → Format
    -- Note: This requires proper JSON parsing for SyntaxNodeDto
    -- For now, use the external Python tool: final_roundtrip_tool.py
    return {
      text := "Use final_roundtrip_tool.py for real AST conversion",
      success := false,
      errorMsg := some "Use external tool: ./final_roundtrip_tool.py <file>"
    }

/-- Complete file round-trip conversion test -/
structure FileRoundTripTestParams where
  content : String
  deriving FromJson, ToJson

structure FileRoundTripTestResult where
  originalContent : String
  convertedContent : String
  success : Bool
  errorMsg : Option String := none
  deriving FromJson, ToJson

/- DEPRECATED/DEV-ONLY: 不导出为 RPC -/
def testFileRoundTripConversion (params : FileRoundTripTestParams) : RequestM (RequestTask FileRoundTripTestResult) := do
  RequestM.asTask do
    -- Real round-trip conversion is implemented in final_roundtrip_tool.py
    -- This tool provides complete Lean → jixia AST → MathEye DTO → Lean formatter
    -- with proper semicolon insertion for tactic sequences
  return {
      originalContent := params.content,
      convertedContent := "Use ./final_roundtrip_tool.py for real round-trip conversion",
      success := false,
      errorMsg := some "Real implementation available: ./final_roundtrip_tool.py <file> --verbose --verify"
    }

-- Re-export minimal DTO + helpers for external round-trip tooling (non-RPC, safe)
structure SyntaxNodeDto where
  kind : String
  range? : Option RangeDto := none
  children : Array SyntaxNodeDto := #[]
  value? : Option String := none
  leading? : Option String := none
  trailing? : Option String := none
  pos? : Option Nat := none
  endPos? : Option Nat := none
  deriving FromJson, ToJson, Inhabited

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '«' || c == '»' || c == '"'

def firstChar? (s : String) : Option Char := s.toList.head?
def lastChar? (s : String) : Option Char := s.toList.reverse.head?

def needsSpace (prev : Option Char) (next : Option Char) : Bool :=
  match prev, next with
  | some p, some n => isWordChar p && isWordChar n
  | _, _ => False

-- REMOVED: Manual formatting functions replaced by Lean native PrettyPrinter

def dtoToSyntax : SyntaxNodeDto → Syntax
  | { kind := "missing", .. } => .missing
  | { kind := "atom", value? := some v, .. } =>
    .atom (SourceInfo.synthetic (pos := ⟨0⟩) (endPos := ⟨0⟩) (canonical := true)) v
  | { kind := "ident", value? := some v, .. } =>
    let nm : Name := v.split (· == '.') |>.foldl Name.mkStr Name.anonymous
    .ident (SourceInfo.synthetic (pos := ⟨0⟩) (endPos := ⟨0⟩) (canonical := false)) v.toSubstring nm []
  | { kind, children, .. } =>
    let k := kind.split (· == '.') |>.foldl Name.mkStr Name.anonymous
    let args := children.map dtoToSyntax
    .node (SourceInfo.synthetic (pos := ⟨0⟩) (endPos := ⟨0⟩) (canonical := false)) k args

end MathEye
namespace MathEye
/- Anchor path item for identifying a container deterministically (MVP keeps it empty) -/
structure AnchorPathItem where
  kind : String
  idx  : Nat
  deriving FromJson, ToJson

structure CaptureAnchorParams where
  pos : Lsp.Position
  deriving FromJson, ToJson

structure CaptureAnchorResult where
  declName : String
  path : Array AnchorPathItem := #[]
  originalBody : String
  anchorPos : Lsp.Position
  success : Bool
  errorMsg : Option String := none
  deriving FromJson, ToJson

@[server_rpc_method]
def captureAnchor (params : CaptureAnchorParams) : RequestM (RequestTask CaptureAnchorResult) := do
  withWaitFindSnapAtPos params.pos fun snap => do
    let doc ← readDoc
    let text : FileMap := doc.meta.text
    let hoverPos : String.Pos := text.lspPosToUtf8Pos params.pos
    -- Robust probe to avoid seam: try around hover position
    let results :=
      let rs0 := snap.infoTree.goalsAt? text hoverPos
      if rs0.isEmpty then
        let baseLsp := params.pos
        let probeRight : List Lsp.Position := (List.range 41).map (fun i => { line := baseLsp.line, character := baseLsp.character + i })
        let probeLeft  : List Lsp.Position := (List.range 4).map (fun i => { line := baseLsp.line, character := baseLsp.character - i })
        let probes := probeLeft ++ probeRight
        let rec firstSome (ps : List Lsp.Position) : List GoalsAtResult :=
          match ps with
          | [] => rs0
          | p :: ps' =>
            let pos := text.lspPosToUtf8Pos p
            let rs := snap.infoTree.goalsAt? text pos
            if rs.isEmpty then firstSome ps' else rs
        firstSome probes
      else rs0
    match results.head? with
    | some r =>
      let path := results
      let stxs := path.map (fun rr => rr.tacticInfo.stx)
      let container := chooseSmallestTacticSeq stxs r.tacticInfo.stx
      -- Build a simple parent-child index path from outermost to the chosen container
      let getArgs : Syntax → Array Syntax := fun s => match s with | .node _ _ args => args | _ => #[]
      let sameRange (a b : Syntax) : Bool :=
        match a.getRange?, b.getRange? with
        | some ra, some rb => ra.start == rb.start && ra.stop == rb.stop
        | _, _ => false
      let chainOuterToInner : List Syntax := (stxs.reverse)
      -- find container index and build path without recursion (Id.run loops)
      let tgtIdx := Id.run do
        let mut i := 0
        let mut found := chainOuterToInner.length - 1
        for s in chainOuterToInner do
          if sameRange s container then found := i
          i := i + 1
        return found
      let anchorPath := Id.run do
        let mut acc : Array AnchorPathItem := #[]
        let mut j := 0
        while j+1 ≤ tgtIdx do
          let parent := (chainOuterToInner.get? j).getD Syntax.missing
          let child  := (chainOuterToInner.get? (j+1)).getD container
          let args := getArgs parent
          let mut idx := 0
          let mut k := 0
          for a in args do
            if sameRange a child then idx := k
            k := k + 1
          acc := acc.push { kind := parent.getKind.toString, idx := idx }
          j := j + 1
        return acc
      let body ← (r.ctxInfo).runMetaM {} do
        formatTacticSeq container
      let some contRg := container.getRange? | return { declName := "", path := anchorPath, originalBody := body, anchorPos := params.pos, success := true }
      let anchorPos := text.utf8PosToLspPos contRg.start
      return { declName := "", path := anchorPath, originalBody := body, anchorPos := anchorPos, success := true }
    | none =>
      return { declName := "", path := #[], originalBody := "", anchorPos := params.pos, success := false, errorMsg := some "No tactic at pos" }

structure RestoreByAnchorParams where
  declName : String
  path : Array AnchorPathItem := #[]
  originalBody : String
  anchorPos : Lsp.Position
  deriving FromJson, ToJson

structure RestoreByAnchorResult where
  newText : String := ""
  range   : RangeDto := { start := { line := 0, character := 0 }, stop := { line := 0, character := 0 } }
  success : Bool
  errorMsg : Option String := none
  deriving FromJson, ToJson

@[server_rpc_method]
def restoreByAnchor (params : RestoreByAnchorParams) : RequestM (RequestTask RestoreByAnchorResult) := do
  -- MVP placeholder: strict Missing to avoid unsafe fallbacks. Full path walk will be implemented next.
  withWaitFindSnapAtPos params.anchorPos fun snap => do
    let doc ← readDoc
    let text : FileMap := doc.meta.text
    let pos : String.Pos := text.lspPosToUtf8Pos params.anchorPos
    let results := snap.infoTree.goalsAt? text pos
    match results.head? with
    | none => return { success := false, errorMsg := some "Missing" }
    | some r =>
      let stxs := results.map (fun rr => rr.tacticInfo.stx)
      let chainOuterToInner : List Syntax := (stxs.reverse)
      let getArgs : Syntax → Array Syntax := fun s => match s with | .node _ _ args => args | _ => #[]
      -- Walk by path
      let rec walk (cur : Syntax) (i : Nat) : Option Syntax :=
        if h : i < params.path.size then
          match params.path.get? i with
          | none => some cur
          | some step =>
            if cur.getKind.toString ≠ step.kind then none else
            let args := getArgs cur
            if h2 : step.idx < args.size then
              let child := args.get? step.idx |>.getD Syntax.missing
              walk child (i+1)
            else none
        else some cur
      let some top := chainOuterToInner.head? | return { success := false, errorMsg := some "Missing" }
      let some container := walk top 0 | return { success := false, errorMsg := some "Missing" }
      -- Parse original body into a tactic sequence
      let env := r.ctxInfo.env
      let parsed := Parser.runParserCategory env `tacticSeq1Indented params.originalBody
      match parsed with
      | Except.error _ => return { success := false, errorMsg := some "ParseError" }
      | Except.ok seqNew =>
        -- Format new body and splice back into whole file
        let body ← (r.ctxInfo).runMetaM {} do
          formatTacticSeq seqNew
        let some contRg := container.getRange? | return { success := false, errorMsg := some "Missing" }
        let contRange := RangeDto.fromStringRange text contRg
        let baseIndent := String.mk (List.replicate contRange.start.character ' ')
        let mkIndented (indent : String) (s : String) : String :=
          let parts := s.splitOn "\n"
          parts.foldl (fun acc ln => if acc.isEmpty then indent ++ ln else acc ++ "\n" ++ indent ++ ln) ""
        let replacementSeg := s!"\n{mkIndented baseIndent body}"
        let replaceStartUtf8 := text.lspPosToUtf8Pos contRange.start
        let replaceStopUtf8  := text.lspPosToUtf8Pos contRange.stop
        let src := text.source
        let pre := src.extract ⟨0⟩ replaceStartUtf8
        let suf := src.extract replaceStopUtf8 src.endPos
        let newFull := pre ++ replacementSeg ++ suf
        let fullRange : RangeDto := { start := { line := 0, character := 0 }, stop := text.utf8PosToLspPos src.endPos }
        return { success := true, newText := newFull, range := fullRange }

end MathEye
