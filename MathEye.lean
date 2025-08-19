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

end MathEye