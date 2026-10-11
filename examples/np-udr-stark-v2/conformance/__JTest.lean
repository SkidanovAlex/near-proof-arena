import Lean.Data.Json
inductive NKid where
  | none
  | hash (h : List Nat)
  | node (c l r : Nat) (pre post : List Nat)
  deriving Repr, Inhabited
deriving instance FromJson for NKid
deriving instance ToJson for NKid
def main : IO UInt32 := do
  IO.println (toJson (NKid.node 3 4 5 [6] [7])).compress
  IO.println (toJson (NKid.none)).compress
  IO.println (toJson (NKid.hash [1,2])).compress
  match fromJson? (← Json.parse "{\"node\":{\"c\":3,\"l\":4,\"r\":5,\"pre\":[6],\"post\":[7]}}") with
  | .ok (k : NKid) => IO.println s!"parsed {repr k}"
  | .error e => IO.println s!"err {e}"
  return 0
