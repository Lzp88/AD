import PaperVerifier.ADComplete.InstructionResources
import PaperVerifier.ADComplete.PSDFactoryDefinition
import Lean.Data.Json.FromToJson

/-! Finite instruction exports are regression data, not universal emitter proofs. -/
namespace ADComplete.CircuitExports
open CircuitAudit.CircuitCosts Lean

def gateJson : Gate → Json
  | .zero => Json.mkObj [("op", .str "zero")]
  | .ident => Json.mkObj [("op", .str "I")]
  | .atomA => Json.mkObj [("op", .str "A")]
  | .atomD => Json.mkObj [("op", .str "D")]
  | .add i j => Json.mkObj [("op", .str "add"), ("args", toJson [i,j])]
  | .mul i j => Json.mkObj [("op", .str "mul"), ("args", toJson [i,j])]
  | .scale b i => Json.mkObj [("op", .str "scale"),
      ("constant", .str (toString b)), ("args", toJson [i])]

def instructions : Circuit → Array Json
  | .empty => #[]
  | .snoc c g => (instructions c).push (gateJson g)

def resultJson (kind : String) (N : ℕ) (r : Result) : Json := Json.mkObj [
  ("kind", .str kind), ("N", toJson N), ("nodes", Json.arr (instructions r.1)),
  ("output", toJson r.2.forward), ("reverse_output", toJson r.2.reverse)]

def main : IO Unit := do
  for k in List.range 15 do
    let N := k+1
    let r := InstructionDegrees.compiled N (IntegerBounds.radixNat N)
    IO.println ((resultJson "linear" N r).compress)
  for k in List.range 4 do
    let N := k+1
    IO.println ((resultJson "psd" N (PSDFactory.compiled N)).compress)

end ADComplete.CircuitExports
#eval ADComplete.CircuitExports.main
