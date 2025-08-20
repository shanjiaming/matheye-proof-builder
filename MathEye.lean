import Lean
import Lean.Meta.Basic
import Lean.Elab.Tactic
import Lean.Server.Rpc.Basic

open Lean Elab Meta Server RequestM

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

/-- Main RPC method to get current proof goals -/
@[server_rpc_method]
def getProofGoals (params : InputParams) : RequestM (RequestTask OutputParams) := do
  withWaitFindSnapAtPos params.pos fun snap => do
    let doc ← readDoc
    let text : FileMap := doc.meta.text
    let hoverPos : String.Pos := text.lspPosToUtf8Pos params.pos
    
    -- Use infoTree.goalsAt? to find tactic info at position
    let results := snap.infoTree.goalsAt? text hoverPos
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
    let results := snap.infoTree.goalsAt? text hoverPos
    match results.head? with
    | some r =>
      -- Prefer appending at the end of the current tactic block (lightweight mode)
      -- Use the tactic syntax tail position if available; otherwise fall back to start
      let stx := r.tacticInfo.stx
      let stxTailPos := stx.getTailPos?.getD (stx.getPos?.getD hoverPos)
      let tailLsp := text.utf8PosToLspPos stxTailPos
      -- Return the tail position; client will insert a new indented line here
      return { pos := tailLsp }
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
      let goal? ← r.tacticInfo.runMetaM ctxInfo do
        -- Prefer the first goal after, fallback to before
        let some g := r.tacticInfo.goalsAfter.head? <|> r.tacticInfo.goalsBefore.head?
          | return none
        let ty ← instantiateMVars (← g.getType)
        let pretty ← ppExpr ty
        let fvars := (← ty.collectFVars.run {}).2.fvarIds.map (·.name)
        return some { pretty := pretty.pretty, freeVars := fvars }
      -- locals
      let locals ← r.tacticInfo.runMetaM ctxInfo do
        let lctx ← getLCtx
        let arr := lctx.decls.toList.filterMap id |>.toArray
        arr.mapM fun d => do
          let t ← instantiateMVars d.type
          let tPretty ← ppExpr t
          let fvs := (← t.collectFVars.run {}).2.fvarIds.map (·.name)
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

end MathEye