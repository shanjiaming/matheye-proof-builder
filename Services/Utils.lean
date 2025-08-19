import Lean
import Lean.Meta.Basic

open Lean Elab Meta

namespace MathEye.Services

/-- Convert Info to JSON for basic debugging -/
def infoToJson (info : Info) : Json :=
  match info with
  | Info.ofTacticInfo tacticInfo =>
    Json.mkObj [
      ("kind", "TacticInfo"),
      ("goalsBefore", Json.arr (tacticInfo.goalsBefore.map (fun g => Json.str (toString g.name))).toArray),
      ("goalsAfter", Json.arr (tacticInfo.goalsAfter.map (fun g => Json.str (toString g.name))).toArray)
    ]
  | Info.ofTermInfo _ =>
    Json.mkObj [
      ("kind", "TermInfo")
    ]
  | Info.ofCommandInfo _ =>
    Json.mkObj [
      ("kind", "CommandInfo")
    ]
  | _ =>
    Json.mkObj [
      ("kind", "Other")
    ]

/-- Format goal information for display -/
def formatGoal (goal : MVarId) : MetaM String := do
  let decl ← goal.getDecl
  let type ← instantiateMVars decl.type
  let typeStr ← ppExpr type
  return s!"{typeStr}"

/-- Check if two positions overlap -/
def positionsOverlap (pos1 : Lsp.Position) (pos2 : Lsp.Position) : Bool :=
  pos1.line == pos2.line && 
  (pos1.character <= pos2.character + 10 && pos2.character <= pos1.character + 10)

end MathEye.Services