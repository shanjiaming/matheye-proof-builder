import Lean
import Lean.Meta.Basic
import Lean.Elab.Tactic
import Lean.Elab.Tactic.Basic
import Lean.Parser.Tactic
import Lean.Server.Rpc.Basic
import Lean.PrettyPrinter
import Init.Tactics

open Lean Elab Meta Server RequestM Parser
open Lean.Elab

namespace MathEye

/-- Build tag for integration verification (no-probe, AST-only). -/
def buildTag : String := "NO_PROBE_VER_1"

def VERSION := 1

/-- 附加写日志（避免覆盖） -/
private def appendLog (p : System.FilePath) (msg : String) : IO Unit := do
  let dbg ← IO.getEnv "MATHEYE_DEBUG_AST"
  if dbg.isSome then
    IO.FS.withFile p .append fun h => h.putStr msg
  else
    pure ()

private def writeFileIfDebug (p : System.FilePath) (msg : String) : IO Unit := do
  let dbg ← IO.getEnv "MATHEYE_DEBUG_AST"
  if dbg.isSome then IO.FS.writeFile p msg else pure ()

-- 受环境变量控制的调试输出（默认不输出）
def dbgIf (msg : String) : RequestM Unit := do
  let dbg ← IO.getEnv "MATHEYE_DEBUG_AST"
  if dbg.isSome then dbg_trace msg else pure ()

/-- InfoTree 辅助：在给定位置收集语法路径（从外到内） -/
private def stxContains (stx : Syntax) (pos : String.Pos) : Bool :=
  match stx.getRange? with
  | some rg => decide (rg.start ≤ pos ∧ pos ≤ rg.stop)
  | none    => false

private partial def collectSyntaxPathAt (tree : InfoTree) (pos : String.Pos) (acc : List Syntax := []) : List Syntax :=
  match tree with
  | InfoTree.context _ t => collectSyntaxPathAt t pos acc
  | InfoTree.node i cs   =>
    let acc' := match i.toElabInfo? with
      | some ei => if stxContains ei.stx pos then acc ++ [ei.stx] else acc
      | none    => acc
    cs.toList.foldl (fun a t' => collectSyntaxPathAt t' pos a) acc'
  | InfoTree.hole _      => acc

private def isRelevantNode (s : Syntax) : Bool :=
  let k := s.getKind
  let ks := k.toString
  ks.startsWith "Lean.Parser.Tactic" || k == `Lean.Parser.Term.byTactic ||
  ks.startsWith "Lean.Parser.Term.calc" || ks.startsWith "Lean.Parser.Term.matchAlt"

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
    -- 无探针：直接使用当前点的结果
    let results := results0
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
    let results0 := snap.infoTree.goalsAt? text hoverPos
    let results := results0
    match results.head? with
    | some r =>
      -- 以“当前战术节点”为锚，尽量保留用户实际光标的相对位置，仅在边界时做最小偏移，避免落在 seam。
      let stx := r.tacticInfo.stx
      let inside := Id.run do
        match stx.getRange? with
        | some rg =>
          let start := rg.start.byteIdx
          let stop  := rg.stop.byteIdx
          let cur   := hoverPos.byteIdx
          if cur ≤ start then
            String.Pos.mk (start + 1)
          else if cur ≥ stop then
            String.Pos.mk (if stop > start then stop - 1 else start + 1)
          else
            hoverPos
        | none => hoverPos
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

/-! Helper: convert String.Range → RangeDto using a FileMap. -/
private def toRangeDto (text : FileMap) (rg : String.Range) : RangeDto :=
  { start := text.utf8PosToLspPos rg.start, stop := text.utf8PosToLspPos rg.stop }

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
    -- 不做探针：仅取 hoverPos 的结果（结构上下文不做额外回退）
    let results := snap.infoTree.goalsAt? text hoverPos
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

        -- 用 g.withContext 确保上下文里有 fvar 的命名信息
        let pretty ← g.withContext do
          Meta.ppExpr ty

        -- 收集自由变量，并映射到 userName
        let (_, fvars) ← ty.collectFVars.run {}
        let freeVars ← fvars.fvarIds.mapM fun fvarId => do
          let decl ← fvarId.getDecl
          pure decl.userName.toString

        return some { pretty := pretty.pretty, freeVars := freeVars }
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

--


/-- Insert a have statement at the end of the tactic sequence -/
-- Kept for backward-compat in this file; prefer `toRangeDto` above
def RangeDto.fromStringRange (text : FileMap) (range : String.Range) : RangeDto :=
  toRangeDto text range

-- （已移除）旧的序列末尾插入/参数结构；生产路径统一走 insertHaveByAction

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
    | .ok stx => acc ++ [stx]
    | .error _ =>
      let fallbackStx := Syntax.atom SourceInfo.none seg
      acc ++ [fallbackStx]) []

-- （已移除）旧的 parseTacticSeq 原型；使用 parseTacticSegments + buildIndentedSeq

/--
formatTacticSeq 设计说明：

我们需要把“保留的前缀战术 + 新插入的 have/exact”组装为一个战术序列并整段 pretty print。
直接用程序拼出来的 `tacticSeq1Indented` 语法树去走 `PrettyPrinter.ppCategory` 的 `tacticSeq` 路径，
在某些版本/环境下会触发“unknown constant 'exact'”类异常。这不是 `exact` 缺失，而是 pretty printer 在
`tacticSeq` 路径上对由代码组装的序列节点（SourceInfo、分隔/布局等）存在内部不变式要求；未满足时会异常。

为保持 AST 驱动又满足 pretty printer 的契约，我们采用：
- 首选尝试整段 `tacticSeq` pretty print；
- 若失败，则对子战术逐个以 `tactic` 类别 pretty print 得文本，再交由 parser 解析为标准的
  `tacticSeq1Indented` 语法树，最后再次整段 pretty print。该过程是“正形化”序列结构，不是字符串级编辑落地。
- 任一步失败，明确返回失败并落盘详细调试信息，保证可复现、可诊断。
-/

-- 统一判断 tactic 序列种类
def isTacticSeqKind (k : Name) : Bool :=
  k == `Lean.Parser.Tactic.tacticSeq ||
  k == `Lean.Parser.Tactic.tacticSeq1Indented ||
  k == `Lean.Parser.Tactic.tacticSeqBracketed

def formatTacticSeq (stx : Syntax) : MetaM String := do
  -- 首选整段 pretty；失败时逐子战术 pretty 后再拼接（仍无字符串编辑逻辑）。
  match stx with
  | .node _ kind args =>
    if isTacticSeqKind kind then
      try
        let fmt ← PrettyPrinter.ppCategory `tacticSeq stx
        return fmt.pretty
      catch _ =>
        let parts ← (args.toList.mapM (fun a => do
          let fmt ← PrettyPrinter.ppCategory `tactic a
          pure fmt.pretty))
        return String.intercalate "\n" parts
    else
      let fmt ← PrettyPrinter.ppCategory `tactic stx
      return fmt.pretty
  | _ =>
    let fmt ← PrettyPrinter.ppCategory `tactic stx
    return fmt.pretty

def flattenTacticSeqArgs (stx : Syntax) : Array Syntax :=
  match stx with
  | .node _ kind args => if isTacticSeqKind kind then args else #[stx]
  | s => #[s]

/-! 从语法路径中选择最近的 tacticSeq（范围最小者）。 -/
private def pickNearestTacticSeqInPath (xs : List Syntax) : Option Syntax :=
  let cands := xs.filter (fun s => isTacticSeqKind s.getKind)
  match cands with
  | [] => none
  | c :: cs =>
    let pick (a b : Syntax) : Syntax :=
      match a.getRange?, b.getRange? with
      | some ra, some rb =>
        let la := ra.stop.byteIdx - ra.start.byteIdx
        let lb := rb.stop.byteIdx - rb.start.byteIdx
        if lb < la then b else a
      | _, _ => a
    some (cs.foldl pick c)

def buildIndentedSeq (args : Array Syntax) : Syntax :=
  let info := SourceInfo.synthetic (pos := ⟨0⟩) (endPos := ⟨0⟩) (canonical := true)
  Syntax.node info `Lean.Parser.Tactic.tacticSeq1Indented args

-- 统一的按行缩进工具：对 s 的每一行前加上 indent，并用 \n 连接
def indentLines (indent : String) (s : String) : String :=
  let parts := s.splitOn "\n"
  parts.foldl (fun acc ln => if acc.isEmpty then indent ++ ln else acc ++ "\n" ++ indent ++ ln) ""

-- 将 UTF-8 位置 clamp 到给定 LSP 范围内部（首尾各偏移 1，以避免落在 token seam 上）
def clampUtf8Into (text : FileMap) (rr : RangeDto) (pos : String.Pos) : String.Pos :=
  let lo0 := text.lspPosToUtf8Pos rr.start
  let hi0 := text.lspPosToUtf8Pos rr.stop
  let lo := if lo0.byteIdx + 1 < hi0.byteIdx then ⟨lo0.byteIdx + 1⟩ else lo0
  let hi := if hi0.byteIdx > lo0.byteIdx + 1 then ⟨hi0.byteIdx - 1⟩ else hi0
  if pos.byteIdx < lo.byteIdx then lo else if pos.byteIdx > hi.byteIdx then hi else pos

-- 构造常用范围
def mkRangeDtoLsp (st : Lsp.Position) (en : Lsp.Position) : RangeDto :=
  { start := st, stop := en }

def mkWholeFileRange (text : FileMap) : RangeDto :=
  { start := { line := 0, character := 0 }, stop := text.utf8PosToLspPos text.source.endPos }

def validLspRange (text : FileMap) (st en : Lsp.Position) : Bool :=
  let s := text.lspPosToUtf8Pos st
  let e := text.lspPosToUtf8Pos en
  decide (e.byteIdx > s.byteIdx)

-- includeBy 判定：命中 by 容器则必为 true；若容器是 tacticSeq，则由 includeByOnSeq? 决定；否则 false
-- 生成替换片段：根据 includeBy 决定是否带 by 头
def makeReplacementSeg (includeBy : Bool) (baseIndent : String) (body : String) : String :=
  if includeBy then s!"by\n{indentLines baseIndent body}" else s!"\n{indentLines baseIndent body}"

-- 将 replacementSeg 替换到 contRange 上，并返回整篇新文本与整篇范围
def spliceWholeFile (text : FileMap) (contRange : RangeDto) (replacementSeg : String)
  : (String × RangeDto) :=
  let replaceStartUtf8 := text.lspPosToUtf8Pos contRange.start
  let replaceStopUtf8  := text.lspPosToUtf8Pos contRange.stop
  let src := text.source
  let pre := src.extract ⟨0⟩ replaceStartUtf8
  let suf := src.extract replaceStopUtf8 src.endPos
  let newFull := pre ++ replacementSeg ++ suf
  let fullRange := mkWholeFileRange text
  (newFull, fullRange)

-- 计算 by 容器的范围/选择容器：下文依赖 findTacticSeqChild/lastStopInSubtree，因此放在其后定义

/-! 统一的子树工具：寻找 tacticSeq 子节点 与 求子树最右 stop -/
private partial def findTacticSeqChild (s : Syntax) : Option Syntax :=
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

private partial def lastStopInSubtree (s : Syntax) : Option String.Pos :=
  let cur := s.getRange? |>.map (·.stop)
  match s with
  | .node _ _ args =>
    let rec loop (i : Nat) (best : Option String.Pos) : Option String.Pos :=
      if h : i < args.size then
        let child := args[i]'h
        let best1 :=
          match best, lastStopInSubtree child with
          | some a, some b => if b.byteIdx > a.byteIdx then some b else some a
          | none,   some b => some b
          | some a, none   => some a
          | none,   none   => none
        loop (i+1) best1
      else best
    match loop 0 cur with
    | some p => some p
    | none   => cur
  | _ => cur

-- 计算 by 容器的范围：起点为 by.start，终点优先为其子 tacticSeq 的最右 stop，否则退回 by.tail 或 by.stop
def byContainerStartStop (text : FileMap) (byC : Syntax) : Option (Lsp.Position × Lsp.Position) :=
  let st? := byC.getRange? |>.map (fun rg => text.utf8PosToLspPos rg.start)
  let child? := findTacticSeqChild byC
  let en? : Option Lsp.Position :=
    match child? with
    | some seq =>
      match lastStopInSubtree seq with
      | some p => some (text.utf8PosToLspPos p)
      | none   =>
        match byC.getTailPos? with
        | some q => some (text.utf8PosToLspPos q)
        | none   =>
          match byC.getRange? with
          | some rg => some (text.utf8PosToLspPos rg.stop)
          | none    => none
    | none =>
      match lastStopInSubtree byC with
      | some p => some (text.utf8PosToLspPos p)
      | none   =>
        match byC.getTailPos? with
        | some q => some (text.utf8PosToLspPos q)
        | none   =>
          match byC.getRange? with
          | some rg => some (text.utf8PosToLspPos rg.stop)
          | none    => none
  match st?, en? with
  | some st, some en => some (st, en)
  | _, _ => none

-- 根据 container 与 term 路径，优先选择覆盖 container 的最小 by 容器范围；否则退回 container 自身范围
/-! 收集整棵 InfoTree 中的 `byTactic` 语法节点（AST-only） -/
private partial def collectByNodes (tree : InfoTree) (acc : List Syntax := []) : List Syntax :=
  match tree with
  | InfoTree.context _ t => collectByNodes t acc
  | InfoTree.node i cs   =>
    let acc' := match i.toElabInfo? with
      | some ei => if ei.stx.getKind == `Lean.Parser.Term.byTactic then acc ++ [ei.stx] else acc
      | none    => acc
    cs.toList.foldl (fun a t' => collectByNodes t' a) acc'
  | InfoTree.hole _      => acc

/-! 在一组 by 节点中，选择“最靠近 pos”的一个：
    优先 start ≥ pos 的最小者；否则选 start < pos 的最大者。-/
private def chooseNearestBy (bys : List Syntax) (pos : String.Pos) : Option Syntax :=
  let withStart := bys.filterMap (fun s => s.getRange? |>.map (fun rg => (s, rg.start)))
  let (afters, befores) := withStart.partition (fun (_, st) => decide (st.byteIdx ≥ pos.byteIdx))
  let pickMin (xs : List (Syntax × String.Pos)) : Option Syntax :=
    match xs with
    | [] => none
    | x :: xs =>
      let rec goMin (best : Syntax × String.Pos) (ys : List (Syntax × String.Pos)) : Syntax × String.Pos :=
        match ys with
        | [] => best
        | y :: ys' =>
          if y.snd.byteIdx < best.snd.byteIdx then goMin y ys' else goMin best ys'
      some (goMin x xs).fst
  let pickMax (xs : List (Syntax × String.Pos)) : Option Syntax :=
    match xs with
    | [] => none
    | x :: xs =>
      let rec goMax (best : Syntax × String.Pos) (ys : List (Syntax × String.Pos)) : Syntax × String.Pos :=
        match ys with
        | [] => best
        | y :: ys' =>
          if y.snd.byteIdx > best.snd.byteIdx then goMax y ys' else goMax best ys'
      some (goMax x xs).fst
  match pickMin afters with
  | some s => some s
  | none   => pickMax befores

/-! 在一组 term 路径节点中，选取“覆盖 target 的最小 byTactic 容器”。 -/
private def pickEnclosingBy (termNodes : List Syntax) (target : Syntax) : Option Syntax :=
  -- 优先：term 路径中所有包含光标位置的 by 容器（已由 collectSyntaxPathAt 保证包含 pos），选最小者
  let byNodes := termNodes.filter (fun s => s.getKind == `Lean.Parser.Term.byTactic)
  let chooseSmallest (xs : List Syntax) : Option Syntax :=
    match xs with
    | [] => none
    | c :: cs =>
      let pick (a b : Syntax) : Syntax :=
        match a.getRange?, b.getRange? with
        | some ra, some rb =>
          let la := ra.stop.byteIdx - ra.start.byteIdx
          let lb := rb.stop.byteIdx - rb.start.byteIdx
          if la ≤ lb then a else b
          | _, _ => a
      some (cs.foldl pick c)
  match chooseSmallest byNodes with
  | some y => some y
  | none   =>
    -- 次选：by 容器完整覆盖 target 范围（最小者）
    match target.getRange? with
    | none => none
    | some tr =>
      let byCoverTarget := byNodes.filter (fun byC =>
        match byC.getRange? with
        | some br => decide (br.start.byteIdx ≤ tr.start.byteIdx ∧ tr.stop.byteIdx ≤ br.stop.byteIdx)
        | none    => false)
      chooseSmallest byCoverTarget

-- includeBy 判定：命中 by 容器则必为 true；若容器是 tacticSeq，则由 includeByOnSeq? 决定；否则 false
def includeByFor (stxsTerm : List Syntax) (targetStx : Syntax) (usedByContainer : Bool)
  (includeByOnSeq? : Option Bool) : Bool :=
  let hasByCont := (pickEnclosingBy stxsTerm targetStx).isSome || usedByContainer
  if hasByCont then true else
  match targetStx with
  | .node _ kind _ => if isTacticSeqKind kind then includeByOnSeq?.getD false else false
  | _               => false

-- 根据 container 与 term 路径，优先选择覆盖 container 的最小 by 容器范围；否则退回 container 自身范围
def containerEffectiveStartStop (text : FileMap) (stxsTerm : List Syntax) (container : Syntax)
  : Option (Lsp.Position × Lsp.Position) :=
  match pickEnclosingBy stxsTerm container with
  | some byC => byContainerStartStop text byC
  | none     =>
    match container.getRange? with
    | some rg => some (text.utf8PosToLspPos rg.start, text.utf8PosToLspPos rg.stop)
    | none    => none

-- 容器视图：范围 + 语法种类 + 是否 by 容器
structure ContainerView where
  start : Lsp.Position
  stop  : Lsp.Position
  kind  : Name
  isBy  : Bool

-- 生成 ContainerView：若 term 路径命中 by，则返回 by 的范围与种类；否则用 container 自身
def containerView (text : FileMap) (stxsTerm : List Syntax) (container : Syntax) : Option ContainerView :=
  match pickEnclosingBy stxsTerm container with
  | some byC =>
    match byContainerStartStop text byC with
    | some (st, en) => some { start := st, stop := en, kind := byC.getKind, isBy := true }
    | none          => none
  | none =>
    match container.getRange? with
    | some rg => some { start := text.utf8PosToLspPos rg.start, stop := text.utf8PosToLspPos rg.stop, kind := container.getKind, isBy := false }
    | none    => none

/-!
  Shared helpers: choose the smallest enclosing tactic sequence container
  from a syntax path, falling back to the provided leaf if none is present.
-/
private def chooseSmallestTacticSeq (stxs : List Syntax) (fallback : Syntax) : Syntax :=
  let candidates := stxs.filter (fun s => isTacticSeqKind s.getKind)
  match candidates with
  | [] =>
    -- No tacticSeq found, look for byTactic containers
    let containerCandidates := stxs.filter (fun s =>
      s.getKind == `Lean.Parser.Term.byTactic)
    match containerCandidates with
    | [] => fallback
    | c :: cs =>
      let pick (a b : Syntax) : Syntax :=
        match a.getRange?, b.getRange? with
        | some ra, some rb =>
          let lenA := ra.stop.byteIdx - ra.start.byteIdx
          let lenB := rb.stop.byteIdx - rb.start.byteIdx
          if lenA ≤ lenB then a else b
        | _, _ => a
      cs.foldl pick c
  | c :: cs =>
    -- Found tacticSeq candidates, pick the smallest
    let pick (a b : Syntax) : Syntax :=
      match a.getRange?, b.getRange? with
      | some ra, some rb =>
        let lenA := ra.stop.byteIdx - ra.start.byteIdx
        let lenB := rb.stop.byteIdx - rb.start.byteIdx
        if lenA ≤ lenB then a else b
      | _, _ => a
    cs.foldl pick c

-- removed legacy insertHaveAtPosition; unified到 insertHaveByAction

/-!
  在术语/战术语法路径中寻找最小的分支容器：
  - Lean.Parser.Tactic.matchRhs（tactic 侧分支右侧）
  - Lean.Parser.Term.matchAlt（term 侧分支）
  返回最小（range 最短）的一个。
-/
private def smallestMatchAltOrRhsInPath (xs : List Syntax) : Option Syntax :=
  let candidates := xs.filter (fun s =>
    let k := s.getKind
    k == `Lean.Parser.Tactic.matchRhs || k == `Lean.Parser.Term.matchAlt)
  match candidates with
  | [] => none
  | c :: cs =>
    let pick (a b : Syntax) : Syntax :=
      match a.getRange?, b.getRange? with
      | some ra, some rb =>
        let la := ra.stop.byteIdx - ra.start.byteIdx
        let lb := rb.stop.byteIdx - rb.start.byteIdx
        if la ≤ lb then a else b
      | _, _ => a
    some (cs.foldl pick c)

/-! 递归寻找节点内部 `=>` atom 的“结束位置”；用于决定在分支头部 `=>` 之后插入。 -/
private partial def findArrowAtomEndPos (s : Syntax) : Option String.Pos :=
  match s with
  | .atom info val => if val == "=>" then info.getRange?.map (·.stop) else none
  | .node _ _ args =>
    let rec loop (i : Nat) : Option String.Pos :=
      if h : i < args.size then
        match findArrowAtomEndPos (args[i]'h) with
        | some p => some p
        | none   => loop (i+1)
      else none
    loop 0
  | _ => none

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
  buildTag : String := MathEye.buildTag
  deriving FromJson, ToJson

@[server_rpc_method]
def insertHaveByAction (params : InsertHaveByActionParams) : RequestM (RequestTask InsertHaveByActionResult) := do
  do dbgIf s!"[NO_PROBE] insertHaveByAction ENTRY pos={params.pos.line}:{params.pos.character} action='{params.action}'"
  try
    let _ ← appendLog "/tmp/insertHaveByAction_no_probe.log" s!"ENTRY {params.pos.line}:{params.pos.character}\n"
  catch _ => pure ()
  -- 为确保 InfoTree 完整，获取文件末尾位置的快照（而非依赖调用点）。
  let doc ← readDoc
  let text : FileMap := doc.meta.text
  let src := text.source
  let endLsp : Lsp.Position := text.utf8PosToLspPos src.endPos
  withWaitFindSnapAtPos endLsp fun snap => do
    let hoverPos : String.Pos := text.lspPosToUtf8Pos params.pos
    -- 无探针：仅用 hoverPos 的结果
    let results := snap.infoTree.goalsAt? text hoverPos
    do dbgIf s!"[NO_PROBE] insertHaveByAction results kinds={results.map (fun r => r.tacticInfo.stx.getKind.toString)}"
    try
      let _ ← appendLog "/tmp/insertHaveByAction_no_probe.log" s!"KINDS {results.map (fun r => r.tacticInfo.stx.getKind.toString)}\n"
    catch _ => pure ()
    match results.head? with
    | none =>
      -- 位置不在战术节点上：在全文件 AST 中选择“距离最近的 by 容器”，并在其体内进行插入（AST-only，无回退）
      let allBy := collectByNodes snap.infoTree []
      try
        let _ ← appendLog "/tmp/insertHaveByAction_no_probe.log" s!"ALL_BY_COUNT {allBy.length}\n"
      catch _ => pure ()
      match chooseNearestBy allBy hoverPos with
      | none =>
        let rr0 := params.blockRange?.getD { start := params.pos, stop := params.pos }
        return { newText := "", range := rr0, success := false, errorMsg := some "no by container found" }
      | some byC =>
        -- 统一容器范围：by.start → 子 tacticSeq 最右叶 stop（若无子 seq，则用 byC 的 tail/range.stop）
        let startStop? : Option (Lsp.Position × Lsp.Position) := byContainerStartStop text byC
        let some (stLsp, enLsp) := startStop? | return {
          newText := "", range := { start := params.pos, stop := params.pos }, success := false,
          errorMsg := some "no range for by container" }
        -- 夹取稳定锚点到 by 体内部
        if not (validLspRange text stLsp enLsp) then
          return { newText := "", range := { start := params.pos, stop := params.pos }, success := false,
                   errorMsg := some "invalid by-block range" }
        let rr0 : RangeDto := mkRangeDtoLsp stLsp enLsp
        let stablePos := clampUtf8Into text rr0 hoverPos
        let resultsStable := snap.infoTree.goalsAt? text stablePos
        let some r := resultsStable.head? | return {
          newText := "", range := mkRangeDtoLsp stLsp enLsp, success := false,
          errorMsg := some "no goals in selected by container" }
        let env := r.ctxInfo.env
        let stxsTerm := (collectSyntaxPathAt snap.infoTree hoverPos []).filter isRelevantNode
        -- 统一以“最近的 tacticSeq 祖先”为容器；如无则退回 byC 的 tacticSeq 子节点/自身
        let targetStx := (pickNearestTacticSeqInPath stxsTerm).getD ((findTacticSeqChild byC).getD byC)
        let baseArgs := flattenTacticSeqArgs targetStx
        -- 以“包含 stablePos 的子战术”的尾部作为切割点（若无则用 stablePos，避免落在 token seam）
        let (cutPosUtf8, strictAtCut) : (String.Pos × Bool) := Id.run do
          let opt := baseArgs.findSome? (fun a =>
            match a.getRange? with
            | some rg => if decide (rg.start.byteIdx ≤ stablePos.byteIdx ∧ stablePos.byteIdx ≤ rg.stop.byteIdx) then some a else none
            | none => none)
          match opt with
          | some t =>
            match t.getRange? with
            | some rg => (rg.stop, false)
            | none    => (stablePos, false)
          | none =>
            -- 退而求其次：取所有 start < stablePos 的最后一个子战术的 stop
            let last? := baseArgs.foldl (init := none) (fun acc a =>
              match a.getRange? with
              | some rg => if decide (rg.start.byteIdx < stablePos.byteIdx) then some a else acc
              | none => acc)
            match last? with
            | some t => ((t.getRange?).map (·.stop) |>.getD stablePos, false)
            | none   =>
              -- 位于 by 头等无子战术之前的缝隙：取第一个子战术的 stop，确保保留其作为前缀
              match baseArgs[0]? with
              | some t0 => ((t0.getRange?).map (·.stop) |>.getD stablePos, false)
              | none    => (stablePos, false)
        -- 读取目标类型：以 cutPosUtf8 作为锚点
        let anchorGoals := snap.infoTree.goalsAt? text cutPosUtf8
        let tyStr? ← match anchorGoals.head? with
          | some gr => gr.ctxInfo.runMetaM {} do
              try
                let g? := gr.tacticInfo.goalsAfter.head? <|> gr.tacticInfo.goalsBefore.head?
                match g? with
                | some g =>
                  g.withContext do
                    let ty ← instantiateMVars (← g.getType)
                    let fmt ← ppExpr ty
                    return some fmt.pretty
                | none => return none
              catch _ => return none
          | none => pure none
        let some tyStr := tyStr? | return {
          newText := "", range := mkRangeDtoLsp stLsp enLsp, success := false,
          errorMsg := some "failed to read goal type" }
        -- 组装 have/exact 段（AST 解析）
        let name := s!"h_{params.pos.line}_{params.pos.character}"
        let snippet := if params.action.trim == "deny"
          then s!"have {name} : ¬ ({tyStr}) := by human_oracle"
          else s!"have {name} : {tyStr} := by human_oracle\nexact {name}"
        -- 若切割点之后不存在任何战术（如单条 inline rfl），则在等号处采用严格比较，排除当前叶子战术
        let suffixExists : Bool := Id.run do
          baseArgs.any (fun a =>
            match a.getRange? with
            | some rg => decide (rg.start.byteIdx > cutPosUtf8.byteIdx)
            | none => false)
        let strictUse := strictAtCut || (!suffixExists)
        let keptBefore := match targetStx with
          | .node _ kind _ =>
            if isTacticSeqKind kind then
              baseArgs.filter (fun a => match a.getRange? with
                | some rg => if strictUse then decide (rg.stop.byteIdx < cutPosUtf8.byteIdx) else decide (rg.stop.byteIdx ≤ cutPosUtf8.byteIdx)
                | none => true)
            else
              #[]
          | _ => #[]
        let extra := parseTacticSegments env snippet
        -- 丢弃切割点之后的所有后缀战术，只保留切割点之前的前缀战术，并在此处插入 have/exact 片段
        let newArgs := extra.toArray
        let seqInfo := SourceInfo.synthetic (pos := ⟨0⟩) (endPos := ⟨0⟩) (canonical := true)
        let seqStx := Syntax.node seqInfo `Lean.Parser.Tactic.tacticSeq1Indented newArgs
        let body ← r.ctxInfo.runMetaM {} do formatTacticSeq seqStx
        if body == "" then
          return { newText := "", range := { start := stLsp, stop := enLsp }, success := false,
                   errorMsg := some "assemble tacticSeq failed" }
        let contRange : RangeDto := mkRangeDtoLsp stLsp enLsp
        let baseIndent := String.mk (List.replicate (contRange.start.character + 2) ' ')
        -- 命中 by 容器，必然需要补 `by`
        let replacementSeg := makeReplacementSeg true baseIndent body
        let retWhole := params.returnWholeFile?.getD true
        if retWhole then
          let (newFull, fullRange) := spliceWholeFile text contRange replacementSeg
          -- 记录选择到的 by 容器范围（用于调试定位）
          try
            let _ ← appendLog "/tmp/insertHaveByAction_no_probe.log" s!"FALLBACK_NEAREST_BY [{contRange.start.line}:{contRange.start.character}-{contRange.stop.line}:{contRange.stop.character}]\n"
          catch _ => pure ()
          return { newText := newFull, range := fullRange, success := true }
        else
          try
            let _ ← appendLog "/tmp/insertHaveByAction_no_probe.log" s!"FALLBACK_NEAREST_BY [{contRange.start.line}:{contRange.start.character}-{contRange.stop.line}:{contRange.stop.character}]\n"
          catch _ => pure ()
          return { newText := replacementSeg, range := contRange, success := true }
      
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
      let stablePos := clampUtf8Into text rr hoverPos
      -- Fetch a reliable ctx for goal type; on failure, return explicit error (no fallback)
      let resultsStable := snap.infoTree.goalsAt? text stablePos
      let name := s!"h_{params.pos.line}_{params.pos.character}"
      let action := params.action.trim
      -- 如果容器不是 tacticSeq，尝试在其子树中找到一个具体的 tactic 节点（如 rfl）作为目标
      let isTacticNode (_ : Syntax) : Bool := true  -- 简化：接受所有节点
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
      -- 若原容器不是 tacticSeq（例如 `by rfl`），优先下钻到其 tacticSeq 子节点，
      -- 使替换范围直接覆盖内层战术（如 `rfl`），从而移除它并避免仅替换到 `by` token。
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

      

      -- 获取子树中最靠右（stop 最大）的节点 stop（AST-only，无窗口扫描）
      let rec lastStopInSubtree (s : Syntax) : Option String.Pos :=
        let cur := s.getRange? |>.map (·.stop)
        match s with
        | .node _ _ args =>
          let rec loop (i : Nat) (best : Option String.Pos) : Option String.Pos :=
            if h : i < args.size then
              let child := args[i]'h
              let best1 :=
                match best, lastStopInSubtree child with
                | some a, some b => if b.byteIdx > a.byteIdx then some b else some a
                | none,   some b => some b
                | some a, none   => some a
                | none,   none   => none
              loop (i+1) best1
            else best
          match loop 0 cur with
          | some p => some p
          | none   => cur
        | _ => cur
      -- 选定用于组装的容器节点：优先 tacticSeq；若原节点不是 tacticSeq，则用 term 路径中最近的 by 容器的 tacticSeq 子节点
      let targetStxPre := (findTacticSeqChild originalStx).getD originalStx
      let targetStx := Id.run do
        if isTacticSeqKind targetStxPre.getKind then
          targetStxPre
        else
          let stxsTerm := (collectSyntaxPathAt snap.infoTree hoverPos []).filter isRelevantNode
          match pickEnclosingBy stxsTerm originalStx with
          | some byC => (findTacticSeqChild byC).getD byC
          | none     => targetStxPre
      -- Try to get goal type strictly（容器内复刻 Lean 的最优选择）：
      -- 1) 收集容器内的候选（沿稳定路径），优先选择容器内最内层的节点
      -- 候选来自路径（稳定优先，然后原始），不再限制于某个容器 range，直接选“最内层”（最短范围）
      let isTacticNode (_ : Syntax) : Bool := true  -- 简化：接受所有节点
      let pathCands : List (GoalsAtResult × String.Range) := resultsStable.filterMap (fun (gr : GoalsAtResult) =>
        let stx := gr.tacticInfo.stx
        match stx.getRange? with
        | some rg => if isTacticNode stx then some (gr, rg) else none
        | none => none)
      -- 在稳定路径候选中选“最内层”（范围最短），不再退回原始路径
      let chosen? : Option (GoalsAtResult × String.Range) :=
        pathCands.foldl
          (fun (acc : Option (GoalsAtResult × String.Range)) (cur : (GoalsAtResult × String.Range)) =>
            match acc with
            | none => some cur
            | some prA =>
              let rgA := prA.snd
              let rgB := cur.snd
              let lenA := rgA.stop.byteIdx - rgA.start.byteIdx
              let lenB := rgB.stop.byteIdx - rgB.start.byteIdx
              if lenB < lenA then some cur else acc)
          none
      -- 2) 依据 Lean 的 useAfter 定义（无嵌套即最内层），读取 before/after 目标；若路径上无战术节点，做一次“结构化探针”（用子战术range.start+1）
      let tyStr? ← do
        match chosen? with
        | none =>
          -- 结构化探针：选 lastKept 或第一个战术，进入其体内的两个严格结构位置（pos+1 / tail-1）查询
          let baseArgs := flattenTacticSeqArgs targetStx
          let lastKept? := baseArgs.foldl (init := none) (fun acc a =>
            match a.getRange? with | some rg => if decide (rg.start.byteIdx < stablePos.byteIdx) then some a else acc | none => acc)
          let probe? := lastKept? <|> baseArgs[0]?
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
                        | some g =>
                          g.withContext do
                            let ty ← instantiateMVars (← g.getType)
                            let fmt ← ppExpr ty
                            return some fmt.pretty
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
                  g1.withContext do
                    let ty ← instantiateMVars (← g1.getType)
                    let fmt ← ppExpr ty
                    return some fmt.pretty
                | none =>
                  let g2? := if afterFirst then gr.tacticInfo.goalsBefore.head? else gr.tacticInfo.goalsAfter.head?
                  match g2? with
                  | some g2 =>
                    g2.withContext do
                      let ty ← instantiateMVars (← g2.getType)
                      let fmt ← ppExpr ty
                      return some fmt.pretty
                  | none => return none
              let afterFirst := useAfter
              pick afterFirst
            catch _ => pure none
      -- 不做多层回退：若无法从选中的最内层节点读取类型，则直接失败
      -- 最终若仍无，明确报错（不做 `_` 回退）
      let some tyStr := tyStr? |
        let dbg :=
          let chosenStr := match chosen? with
            | some (gr, rg) => s!"{gr.tacticInfo.stx.getKind.toString}@{rg.start.byteIdx}-{rg.stop.byteIdx}"
            | none => "none"
          s!"failed to read goal type at stable position; chosen={chosenStr}; pathStable={resultsStable.length}; results={results.length}; stablePos={stablePos.byteIdx}"
        do dbgIf s!"[insertHaveByAction] FAILURE: failed to read goal type - {dbg}"
        return { newText := "", range := rr, success := false, errorMsg := some ("[DEBUG] failed to read goal type - this is path 2: " ++ dbg) }
      let snippet := if action == "deny"
        then s!"have {name} : ¬ ({tyStr}) := by human_oracle"
        else s!"have {name} : {tyStr} := by human_oracle\nexact {name}"
      -- Reconstruct: 在 cutPosUtf8 处插入 snippet，保留前后两侧所有战术
      -- Choose actual container from stable path
      let env := (resultsStable.head?.getD r).ctxInfo.env
      let stxsTerm := (collectSyntaxPathAt snap.infoTree hoverPos []).filter isRelevantNode
      let targetStx := (pickNearestTacticSeqInPath stxsTerm).getD ((findTacticSeqChild originalStx).getD originalStx)
      let baseArgs := flattenTacticSeqArgs targetStx
      -- 首选使用当前最内层战术节点的 stop 作为切割点；若不在 baseArgs 中，退化为基于 stablePos 的包含/前驱定位
      let (cutPosUtf8, strictAtCut) : (String.Pos × Bool) := Id.run do
        let primaryRg? := (resultsStable.head?.getD r).tacticInfo.stx.getRange?
        let primaryCut? : Option String.Pos :=
          match primaryRg? with
          | some prg =>
            let m? := baseArgs.findSome? (fun a =>
              match a.getRange? with
              | some rg => if decide (rg.start.byteIdx ≤ prg.start.byteIdx ∧ prg.stop.byteIdx ≤ rg.stop.byteIdx) then some a else none
              | none => none)
            match m? with
            | some a => (a.getRange?).map (·.stop)
            | none   => none
          | none => none
        match primaryCut? with
        | some res => (res, false)
        | none =>
          let opt := baseArgs.findSome? (fun a =>
            match a.getRange? with
            | some rg => if decide (rg.start.byteIdx ≤ stablePos.byteIdx ∧ stablePos.byteIdx ≤ rg.stop.byteIdx) then some a else none
            | none => none)
          match opt with
          | some t =>
            match t.getRange? with
            | some rg => (rg.stop, false)
            | none    => (stablePos, false)
          | none =>
            let last? := baseArgs.foldl (init := none) (fun acc a =>
              match a.getRange? with
              | some rg => if decide (rg.start.byteIdx < stablePos.byteIdx) then some a else acc
              | none => acc)
            match last? with
            | some t => ((t.getRange?).map (·.stop) |>.getD stablePos, false)
            | none   =>
            match baseArgs[0]? with
              | some t0 => ((t0.getRange?).map (·.stop) |>.getD stablePos, true)
              | none    => (stablePos, false)
      -- 优先采用“基于当前战术语法节点索引”的前缀截取，避免误判 cutPos 落在缝隙导致丢失已有前缀战术。
      -- 若无法定位当前战术在容器子序列中的索引，再退回到 cutPosUtf8 的区间比较。
      let primaryStx := (resultsStable.head?.getD r).tacticInfo.stx
      let idxOpt : Option Nat := Id.run do
        let rec findIdx (i : Nat) : Option Nat :=
          if h : i < baseArgs.size then
            let a := baseArgs[i]'h
            match a.getRange?, primaryStx.getRange? with
            | some ra, some rp =>
              if decide (ra.start.byteIdx ≤ rp.start.byteIdx ∧ rp.stop.byteIdx ≤ ra.stop.byteIdx)
              then some i else findIdx (i+1)
            | _, _ => findIdx (i+1)
          else none
        findIdx 0
      let suffixExists : Bool := Id.run do
        baseArgs.any (fun a =>
          match a.getRange? with
          | some rg => decide (rg.start.byteIdx > cutPosUtf8.byteIdx)
          | none => false)
      let strictUse := strictAtCut || (!suffixExists)
      let keptBefore := match targetStx with
        | .node _ kind _ =>
          if isTacticSeqKind kind then
            match idxOpt with
            | some i => baseArgs.extract 0 (i+1)
            | none =>
              baseArgs.filter (fun a => match a.getRange? with
                | some rg => if strictUse then decide (rg.stop.byteIdx < cutPosUtf8.byteIdx) else decide (rg.stop.byteIdx ≤ cutPosUtf8.byteIdx)
                | none => true)
          else #[]
        | _ => #[]
      -- 直接以稳定位置选择“包含 stablePos 的子战术”索引，用于精准定位切点
      let cutIdxFromPos? : Option Nat := Id.run do
        let rec goCut (i : Nat) : Option Nat :=
          if h : i < baseArgs.size then
            match (baseArgs[i]'h).getRange? with
            | some rg =>
              if decide (rg.start.byteIdx ≤ stablePos.byteIdx ∧ stablePos.byteIdx ≤ rg.stop.byteIdx)
              then some i else goCut (i+1)
            | none => goCut (i+1)
          else none
        goCut 0
      -- 计算 by 容器范围（供整体替换与缩进、类型读取使用）
      let stxsTerm := (collectSyntaxPathAt snap.infoTree hoverPos []).filter isRelevantNode
      let (contRangeRaw, usedByContainer) : (RangeDto × Bool) := Id.run do
        let byCont? : Option Syntax := pickEnclosingBy stxsTerm targetStx
        let useBy (byC : Syntax) : Option (RangeDto × Bool) :=
          let st? := byC.getRange? |>.map (fun rg => text.utf8PosToLspPos rg.start)
          let child? := findTacticSeqChild byC
          let en? : Option Lsp.Position :=
            match child? with
            | some seq =>
              match lastStopInSubtree seq with
              | some p => some (text.utf8PosToLspPos p)
              | none   =>
                match byC.getTailPos? with
                | some q => some (text.utf8PosToLspPos q)
                | none   =>
                  match byC.getRange? with
                  | some rg => some (text.utf8PosToLspPos rg.stop)
                  | none    => none
            | none =>
              match lastStopInSubtree byC with
              | some p => some (text.utf8PosToLspPos p)
              | none   =>
                match byC.getTailPos? with
                | some q => some (text.utf8PosToLspPos q)
                | none   =>
                  match byC.getRange? with
                  | some rg => some (text.utf8PosToLspPos rg.stop)
                  | none    => none
          match st?, en? with
          | some st, some en => some (({ start := st, stop := en } : RangeDto), true)
          | _, _ => none
        match byCont? with
        | some byC =>
          match useBy byC with
          | some res => res
          | none => (rr, false)
        | none =>
          let allBy := collectByNodes snap.infoTree []
          match chooseNearestBy allBy hoverPos with
          | some byC =>
            match useBy byC with
            | some res => res
            | none => (rr, false)
          | none =>
            match targetStx.getRange? with
            | some rg => ({ start := text.utf8PosToLspPos rg.start, stop := text.utf8PosToLspPos rg.stop }, false)
            | none    => (rr, false)
      -- snippet 的目标类型严格取自当前光标处的 InfoTree 目标（与 InfoView 一致）
      let snippet := if params.action.trim == "deny"
        then s!"have {name} : ¬ ({tyStr}) := by human_oracle"
        else s!"have {name} : {tyStr} := by human_oracle\nexact {name}"
      do dbgIf s!"[insertHaveByAction] About to parse snippet: '{snippet}'"
      let extra := parseTacticSegments env snippet
      do dbgIf s!"[insertHaveByAction] Parsed {extra.length} segments"
      let segKinds := extra.map (fun s => s.getKind.toString)
      let kindsStr := String.intercalate ", " segKinds
      let mut dbgAll := s!"Segments kinds: [{kindsStr}] at pos {params.pos.line}:{params.pos.character}\n"
      -- 逐段尝试 PrettyPrinter，定位是哪一段触发异常
      let perSegLogs ← (resultsStable.head?.getD r).ctxInfo.runMetaM {} do
        let rec loop (xs : List Syntax) (acc : String) : MetaM String :=
          match xs with
          | [] => pure acc
          | s :: ss => do
            let kind := s.getKind
            let acc1 := acc ++ s!"pp[{kind}]: "
            let acc2 ← (do
              try
                let fmt ← PrettyPrinter.ppCategory `tactic s
                pure (acc1 ++ "OK: " ++ fmt.pretty ++ "\n")
              catch e => do
                let msg ← e.toMessageData.toString
                pure (acc1 ++ s!"ERR: {msg}\n"))
            loop ss acc2
        loop extra ("")
      dbgAll := dbgAll ++ perSegLogs
      -- 丢弃切割点之后的所有后缀战术
      -- 仅替换后缀：前缀保持不变
      let newArgs := keptBefore ++ extra.toArray
      -- 纯 AST 组装：直接构造规范的 tacticSeq1Indented 节点并整段 pretty-print（无字符串拼接/解析）。
      let (body, dbgPP) ← (resultsStable.head?.getD r).ctxInfo.runMetaM {} do
        -- 直接在 AST 上构造 tacticSeq1Indented 节点，再用健壮的 formatTacticSeq 渲染（内部自带回退到子战术渲染）。
        let seqInfo := SourceInfo.synthetic (pos := ⟨0⟩) (endPos := ⟨0⟩) (canonical := true)
        let seqStx := Syntax.node seqInfo `Lean.Parser.Tactic.tacticSeq1Indented newArgs
        try
          let out ← formatTacticSeq seqStx
          let dbg := s!"assembleSeq(AST:tacticSeq1Indented) OK len={out.length}\n"
          return (out, dbg)
        catch e =>
          let msg ← e.toMessageData.toString
          let dbg := s!"assembleSeq(AST:tacticSeq1Indented) formatTacticSeq error: {msg}\n"
          return ("", dbg)
      dbgAll := dbgAll ++ s!"keptCount={keptBefore.size} targetKind={targetStx.getKind} stablePos={stablePos.byteIdx} tyStr={tyStr}\n" ++ dbgPP
      -- term 路径（用于定位 by 容器）
      let stxsTerm := (collectSyntaxPathAt snap.infoTree hoverPos []).filter isRelevantNode
      if body == "" then
        -- 失败时，保留现场信息并明确失败（不做字符串替换回退）
        let _ ← writeFileIfDebug "/tmp/insertHaveByAction_debug.log" (dbgAll ++ "assemble failed; aborting.\n")
        return { newText := "", range := rr, success := false, errorMsg := some "assemble tacticSeq failed" }
      dbgAll := dbgAll ++ s!"formattedOK len={body.length}\n"
      -- Indent and compute the replacement segment for the chosen container（纯 AST）
      -- 计算替换范围统一封装：与 getByBlockRange 共享同一逻辑；若 term 路径未命中 by，则全文件收集最近的 by
      let (contRangeRaw, usedByContainer) : (RangeDto × Bool) := Id.run do
        let byCont? : Option Syntax := pickEnclosingBy stxsTerm targetStx
        let useBy (byC : Syntax) : Option (RangeDto × Bool) :=
          let st? := byC.getRange? |>.map (fun rg => text.utf8PosToLspPos rg.start)
          let child? := findTacticSeqChild byC
          let en? : Option Lsp.Position :=
            match child? with
            | some seq =>
              match lastStopInSubtree seq with
              | some p => some (text.utf8PosToLspPos p)
              | none   =>
                match byC.getTailPos? with
                | some q => some (text.utf8PosToLspPos q)
                | none   =>
                  match byC.getRange? with
                  | some rg => some (text.utf8PosToLspPos rg.stop)
                  | none    => none
            | none =>
              match lastStopInSubtree byC with
              | some p => some (text.utf8PosToLspPos p)
              | none   =>
                match byC.getTailPos? with
                | some q => some (text.utf8PosToLspPos q)
                | none   =>
                  match byC.getRange? with
                  | some rg => some (text.utf8PosToLspPos rg.stop)
                  | none    => none
          match st?, en? with
          | some st, some en => some (({ start := st, stop := en } : RangeDto), true)
          | _, _ => none
        match byCont? with
        | some byC =>
          match useBy byC with
          | some res => res
          | none => (rr, false)
        | none =>
          -- 全文件最近 by 容器
          let allBy := collectByNodes snap.infoTree []
          match chooseNearestBy allBy hoverPos with
          | some byC =>
            match useBy byC with
            | some res => res
            | none => (rr, false)
          | none =>
            -- tactic context（不包 by）：targetStx 应为 tacticSeq
            match targetStx.getRange? with
            | some rg => ({ start := text.utf8PosToLspPos rg.start, stop := text.utf8PosToLspPos rg.stop }, false)
            | none    => (rr, false)
      -- 若位于分支（matchAlt/matchRhs），将起点调整到 `=>` 之后，避免覆盖头部符号
      let contRange : RangeDto := Id.run do
        match smallestMatchAltOrRhsInPath stxsTerm with
        | some alt =>
          match (alt.getRange?), findArrowAtomEndPos alt with
          | some rgAlt, some arrowEnd =>
            let st' := text.utf8PosToLspPos arrowEnd
            let en' := text.utf8PosToLspPos rgAlt.stop
            { start := st', stop := en' }
          | _, _ => contRangeRaw
        | none => contRangeRaw
      -- 若能定位当前战术在容器中的索引，则从“已保留的最后一个战术的 stop”开始替换，仅替换后缀（保持 by 体及前缀不变）。
      -- 若无法定位索引但已存在前缀，则用 cutPosUtf8 作为替换起点；否则保持整个容器范围。
      let contRange := Id.run do
        match targetStx with
        | .node _ kind _ =>
          if isTacticSeqKind kind then
            -- 优先使用“包含 stablePos 的子战术”作为切点；否则退回 idxOpt；再退回首个子战术/稳定位置
            match cutIdxFromPos? with
            | some j =>
              match (baseArgs[j]!.getRange?) with
              | some rgJ => ({ start := text.utf8PosToLspPos rgJ.stop, stop := contRangeRaw.stop } : RangeDto)
              | none     => ({ start := text.utf8PosToLspPos cutPosUtf8, stop := contRangeRaw.stop } : RangeDto)
            | none =>
              match idxOpt with
              | some i =>
                match (baseArgs[i]!.getRange?) with
                | some rgI => ({ start := text.utf8PosToLspPos rgI.stop, stop := contRangeRaw.stop } : RangeDto)
                | none     => ({ start := text.utf8PosToLspPos cutPosUtf8, stop := contRangeRaw.stop } : RangeDto)
              | none =>
                match baseArgs[0]? with
                | some t0 =>
                  match t0.getRange? with
                  | some rg0 => ({ start := text.utf8PosToLspPos rg0.start, stop := contRangeRaw.stop } : RangeDto)
                  | none     => ({ start := text.utf8PosToLspPos cutPosUtf8, stop := contRangeRaw.stop } : RangeDto)
                | none => ({ start := text.utf8PosToLspPos cutPosUtf8, stop := contRangeRaw.stop } : RangeDto)
          else contRangeRaw
        | _ => contRangeRaw
      -- 以容器首个子战术的起始列作为 by 体的基线缩进，更符合 Lean 实际的 by 缩进规则
      let baseIndentCol := Id.run do
        match baseArgs[0]? with
        | some t0 =>
          match t0.getRange? with
          | some rg0 => (text.utf8PosToLspPos rg0.start).character
          | none     => contRangeRaw.start.character + 2
        | none => contRangeRaw.start.character + 2
      let baseIndent := String.mk (List.replicate baseIndentCol ' ')
      -- 后缀替换：若 contRange.start ≠ contRangeRaw.start，则必定处于 by 体内，前缀已保留，不应额外补 `by`。
      -- 仅当替换覆盖整个容器（包括 by 头）时，才在片段前补 `by`。
      -- 仅在分支上下文（matchAlt/matchRhs）需要补 `by`，普通 by 体内做后缀追加不再补 `by`
      let includeBy := (smallestMatchAltOrRhsInPath stxsTerm).isSome
      let replacementSeg := makeReplacementSeg includeBy baseIndent body
      dbgAll := dbgAll ++ s!"includeBy={includeBy} contKind={match targetStx with | .node _ k _ => k | _ => Name.anonymous} replacementPreview={(replacementSeg.take 800)}\n"
      let retWhole := params.returnWholeFile?.getD true
      dbgAll := dbgAll ++ s!"contRange.lsp=[{contRange.start.line}:{contRange.start.character}-{contRange.stop.line}:{contRange.stop.character}] includeBy={includeBy}\n"
      do dbgIf s!"[NO_PROBE] insertHaveByAction includeBy={includeBy} contRange=[{contRange.start.line}:{contRange.start.character}-{contRange.stop.line}:{contRange.stop.character}]"
      try
        let _ ← writeFileIfDebug "/tmp/insertHaveByAction_no_probe.log" s!"RANGE [{contRange.start.line}:{contRange.start.character}-{contRange.stop.line}:{contRange.stop.character}] includeBy={includeBy}\n"
      catch _ => pure ()
      if retWhole then
        -- Splice into whole file deterministically and return whole-file replacement（范围由 AST 严格确定）
        let (newFull, fullRange) := spliceWholeFile text contRange replacementSeg
        dbgAll := dbgAll ++ s!"returningWhole success=true newFull.len={newFull.length}\n"
        let _ ← writeFileIfDebug "/tmp/insertHaveByAction_debug.log" dbgAll
        return { newText := newFull, range := fullRange, success := true }
      else
        dbgAll := dbgAll ++ s!"returningPartial success=true seg.len={replacementSeg.length}\n"
        let _ ← writeFileIfDebug "/tmp/insertHaveByAction_debug.log" dbgAll
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
  buildTag : String := MathEye.buildTag
  deriving FromJson, ToJson

@[server_rpc_method]
def getByBlockRange (params : ByBlockRangeParams) : RequestM (RequestTask ByBlockRangeResult) := do
  -- 使用文件末尾位置以获得完整 InfoTree，再在其上以 params.pos 作为查询点决策容器
  let doc ← readDoc
  let text : FileMap := doc.meta.text
  let src := text.source
  let endLsp : Lsp.Position := text.utf8PosToLspPos src.endPos
  withWaitFindSnapAtPos endLsp fun snap => do
    -- 注意：hoverPos 仍取调用点，InfoTree 来自文件末尾的完整快照
    let hoverPos : String.Pos := text.lspPosToUtf8Pos params.pos
    do dbgIf s!"[NO_PROBE] getByBlockRange ENTRY pos={params.pos.line}:{params.pos.character}"
    try
      let _ ← appendLog "/tmp/getByBlockRange_no_probe.log" s!"ENTRY {params.pos.line}:{params.pos.character}\n"
    catch _ => pure ()

    -- Check both tactic and term contexts（无探针）
    let tacticResults := snap.infoTree.goalsAt? text hoverPos
    let termResults := snap.infoTree.termGoalAt? hoverPos
    let isTacticContext := tacticResults.length > 0
    let isTermContext := termResults.isSome

    match tacticResults.head? with
    | some r0 =>
      -- Get the complete syntax path by walking up from the tactic node
      -- We need to find the parent containers that contain this tactic
      -- let tacticStx := r0.tacticInfo.stx
      -- 语法路径：不探针，直接取同一 hover 位置的所有 tactic 节点（由 infoTree 提供）
      let stxs := tacticResults.map (fun res => res.tacticInfo.stx)
      let stxsTerm := (collectSyntaxPathAt snap.infoTree hoverPos []).filter isRelevantNode
      let _ ← writeFileIfDebug "/tmp/getByBlockRange_debug.log" s!"TERM path kinds: {stxsTerm.map (fun s => s.getKind.toString)}\n"
      let byNodesDbg := stxsTerm.filter (fun s => s.getKind == `Lean.Parser.Term.byTactic)
      let byRanges := byNodesDbg.map (fun s => match s.getRange? with | some rg => s!"[{(text.utf8PosToLspPos rg.start).line}:{(text.utf8PosToLspPos rg.start).character}-{(text.utf8PosToLspPos rg.stop).line}:{(text.utf8PosToLspPos rg.stop).character}]" | none => "[nr]")
      let _ ← appendLog "/tmp/getByBlockRange_debug.log" s!"TERM by ranges: {byRanges}\n"

      -- Collect syntax context information
      let parentKinds : Array String := stxs.toArray.map (fun s => s.getKind.toString)
      let hasMatchAlt := parentKinds.any (fun k => k.startsWith "Lean.Parser.Term.matchAlt" || k.startsWith "Lean.Parser.Tactic.matchRhs")

      -- Debug: log syntax path and container selection
      let debugMsg := s!"=== getByBlockRange Debug ===
Position: line {params.pos.line}, char {params.pos.character}
Complete syntax path nodes: {parentKinds.toList}
Tactic results count: {tacticResults.length}
"
      let _ ← appendLog "/tmp/getByBlockRange_debug.log" debugMsg

      -- Prefer the smallest enclosing tactic sequence container as the by-block range
      let debugMsg2 := s!"About to call chooseSmallestTacticSeq with {stxs.length} nodes
"
      let _ ← appendLog "/tmp/getByBlockRange_debug.log" (debugMsg ++ debugMsg2)
      let container0 := chooseSmallestTacticSeq stxs r0.tacticInfo.stx
      let debugMsg3 := s!"chooseSmallestTacticSeq returned: {container0.getKind}
Selected container0: {container0.getKind}
"
      let _ ← appendLog "/tmp/getByBlockRange_debug.log" (debugMsg ++ debugMsg2 ++ debugMsg3)

      -- 使用顶层工具：tacticSeq 子节点与子树最右 stop

      -- Prefer tacticSeq child if available; otherwise use container0
      let containerPre := match findTacticSeqChild container0 with
        | some seq => seq
        | none     => container0
      -- 若在分支上下文（matchAlt/matchRhs），优先用分支容器
      let container :=
        match smallestMatchAltOrRhsInPath stxsTerm with
        | some alt => alt
        | none     => containerPre
      -- 统一容器范围计算：优先 by 容器（起点=by.start；终点=子 tacticSeq 的最末叶 stop），否则退回 tacticSeq 容器完整范围
      let view? := containerView text stxsTerm container

      -- 为返回值选择“有效语法种类”：若命中 by 容器，则以 byTactic 为准；否则以 container 为准
      let effectiveKind : Name := Id.run do
        match pickEnclosingBy stxsTerm container with
        | some byC => byC.getKind
        | none     => container.getKind
      let _ ← appendLog "/tmp/getByBlockRange_debug.log" s!"effectiveKind={effectiveKind}\n"

      let finalMsg := match view? with
        | some v => s!"Final container: {container.getKind}
Container range(LSP): [{v.start.line}:{v.start.character}-{v.stop.line}:{v.stop.character}]
"
        | none => s!"Final container: {container.getKind}
Container has no range!
"
      let _ ← appendLog "/tmp/getByBlockRange_debug.log" (debugMsg ++ debugMsg2 ++ debugMsg3 ++ finalMsg)
      do dbgIf s!"[NO_PROBE] getByBlockRange container={container.getKind}"
      try
        let _ ← appendLog "/tmp/getByBlockRange_no_probe.log" s!"CONTAINER {container.getKind}\n"
      catch _ => pure ()

      -- 对分支容器：调整范围起点为 `=>` 之后，确保保留头部 `=>`
      let viewAdj? : Option ContainerView := Id.run do
        match view?, (smallestMatchAltOrRhsInPath stxsTerm) with
        | some v, some alt =>
          match findArrowAtomEndPos alt with
          | some arrowEnd => some { v with start := text.utf8PosToLspPos arrowEnd }
          | none          => view?
        | _, _ => view?
      let some v := viewAdj? | return {
        range := { start := params.pos, stop := params.pos },
        success := false,
        errorMsg := some "no range"
      }
      -- Guard against degenerate range strictly
      if not (validLspRange text v.start v.stop) then
        return {
          range := { start := params.pos, stop := params.pos },
          success := false,
          errorMsg := some "invalid by-block range"
        }
      let outRange : RangeDto := mkRangeDtoLsp v.start v.stop
      let finalRangeMsg := s!"Returning range LSP: [{outRange.start.line}:{outRange.start.character}-{outRange.stop.line}:{outRange.stop.character}] kind={container.getKind}"
      let _ ← appendLog "/tmp/getByBlockRange_debug.log" (debugMsg ++ debugMsg2 ++ debugMsg3 ++ finalMsg ++ finalRangeMsg)
      do dbgIf s!"[NO_PROBE] getByBlockRange outRange=[{outRange.start.line}:{outRange.start.character}-{outRange.stop.line}:{outRange.stop.character}]"
      try
        let _ ← appendLog "/tmp/getByBlockRange_no_probe.log" s!"OUT [{outRange.start.line}:{outRange.start.character}-{outRange.stop.line}:{outRange.stop.character}]\n"
      catch _ => pure ()
      return {
        range := outRange,
        success := true,
        syntaxKind := some ((view?.map (·.kind.toString)).getD ""),
        isMatchAlt := hasMatchAlt,
        parentKinds := parentKinds,
        isTacticContext := isTacticContext,
        isTermContext := isTermContext
      }
    | none =>
      -- 位置不在战术节点上：以 AST 遍历收集所有 by 容器，选取与 pos 最近的一个（确定性规则）
      let allBy := collectByNodes snap.infoTree []
      match chooseNearestBy allBy hoverPos with
      | none =>
        return {
          range := { start := params.pos, stop := params.pos }, success := false,
          errorMsg := some "no by container in file",
          isTacticContext := false,
          isTermContext := isTermContext
        }
      | some byC =>
        let st? := byC.getRange? |>.map (fun rg => text.utf8PosToLspPos rg.start)
        let child? := findTacticSeqChild byC
        let en? : Option Lsp.Position :=
          match child? with
          | some seq =>
            match lastStopInSubtree seq with
            | some p => some (text.utf8PosToLspPos p)
            | none   =>
              match byC.getTailPos? with
              | some q => some (text.utf8PosToLspPos q)
              | none   =>
                match byC.getRange? with
                | some rg => some (text.utf8PosToLspPos rg.stop)
                | none    => none
          | none =>
            match lastStopInSubtree byC with
            | some p => some (text.utf8PosToLspPos p)
            | none   =>
              match byC.getTailPos? with
              | some q => some (text.utf8PosToLspPos q)
              | none   =>
                match byC.getRange? with
                | some rg => some (text.utf8PosToLspPos rg.stop)
                | none    => none
        match st?, en? with
        | some st, some en =>
          if not (validLspRange text st en) then
            return { range := { start := params.pos, stop := params.pos }, success := false,
                     errorMsg := some "invalid by-block range" }
          let outRange : RangeDto := mkRangeDtoLsp st en
          return {
            range := outRange,
            success := true,
            syntaxKind := some byC.getKind.toString,
            isMatchAlt := false,
            parentKinds := #[],
            isTacticContext := false,
            isTermContext := true
          }
        | _, _ =>
          return {
            range := { start := params.pos, stop := params.pos }, success := false,
            errorMsg := some "no range",
            isTacticContext := false,
            isTermContext := true
          }

/- Anchor path item for identifying a container deterministically (MVP keeps it empty) -/
structure AnchorPathItem where
  kind : String
  idx  : Nat
  deriving FromJson, ToJson

-- Legacy anchor APIs removed

  /-
    Restore an entire by-block from recorded range and original text using AST-only operations.
    Steps:
    - Anchor at recorded block start to obtain environment
    - Parse `originalByBlockContent` into a tactic sequence AST
    - Replace the node at `blockRange` with the pretty-printed sequence
    - Return whole-file text to enforce deterministic formatting
  -/
  structure RestoreByBlockParams where
    blockRange : RangeDto
    originalByBlockContent : String
    deriving FromJson, ToJson

  structure RestoreByBlockResult where
    newText : String := ""
    range   : RangeDto := { start := { line := 0, character := 0 }, stop := { line := 0, character := 0 } }
    success : Bool
    errorMsg : Option String := none
    deriving FromJson, ToJson

  @[server_rpc_method]
  def restoreByBlock (params : RestoreByBlockParams) : RequestM (RequestTask RestoreByBlockResult) := do
    -- 使用文件末尾快照，避免在边界位置取不到上下文
    let doc ← readDoc
    let text : FileMap := doc.meta.text
    let src := text.source
    let endLsp : Lsp.Position := text.utf8PosToLspPos src.endPos
    withWaitFindSnapAtPos endLsp fun snap => do
      -- 将起点 clamp 到 by 块内部，避免落在 token seam 上
      let startUtf8 := text.lspPosToUtf8Pos params.blockRange.start
      let stableUtf8 := clampUtf8Into text params.blockRange startUtf8
      let results := snap.infoTree.goalsAt? text stableUtf8
      match results.head? with
      | none => return { success := false, errorMsg := some "Missing context at block start" }
      | some r =>
        let env := r.ctxInfo.env
        -- 解析原始 by 块内容：优先将其作为 tacticSeq1Indented；失败则尝试作为 term（含 by），抽出其子 tacticSeq
        let trySeq : Except String Syntax :=
          match Parser.runParserCategory env `tacticSeq1Indented params.originalByBlockContent with
          | .ok seq => .ok seq
          | .error _ =>
            -- 尝试直接把原文当成 term（可能是完整的 `by ...`）
            match Parser.runParserCategory env `term params.originalByBlockContent with
            | .ok t =>
              match findTacticSeqChild t with
              | some seq => .ok seq
              | none => .error "No tacticSeq child in term"
            | .error _ => .error "ParseError"
        match trySeq with
        | .error e => return { success := false, errorMsg := some e }
        | .ok seqNew =>
          -- Pretty print via Lean formatter, then splice back at recorded范围（补 by 头）
          let body ← (r.ctxInfo).runMetaM {} do
            formatTacticSeq seqNew
          let contRange := params.blockRange
          let baseIndent := String.mk (List.replicate (contRange.start.character + 2) ' ')
          let replacementSeg := makeReplacementSeg true baseIndent body
          let (newFull, fullRange) := spliceWholeFile text contRange replacementSeg
          return { success := true, newText := newFull, range := fullRange }

end MathEye
