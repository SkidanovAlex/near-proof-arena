import NearCompression.TerminalDAGArithmetic
import NearCompression.TerminalSignedExpansion
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

inductive TerminalJoinRoute (nodes : Nat → TerminalDAGNode K) :
    (Nat × Bool) → (Nat × Bool) → (Nat × Bool) → Prop where
  | same {x y z sign} : TerminalArithmeticRoute nodes .add x y z →
      TerminalJoinRoute nodes (x,sign) (y,sign) (z,sign)
  | positiveNegative {x y z} : TerminalArithmeticRoute nodes .sub x y z →
      TerminalJoinRoute nodes (x,true) (y,false) (z,true)
  | negativePositive {x y z} : TerminalArithmeticRoute nodes .sub y x z →
      TerminalJoinRoute nodes (x,false) (y,true) (z,true)

inductive TerminalPassRoute (nodes : Nat → TerminalDAGNode K) :
    List (Nat × Bool) → List (Nat × Bool) → Prop where
  | empty : TerminalPassRoute nodes [] []
  | singleton (a) : TerminalPassRoute nodes [a] [a]
  | pair {a b c rest output} : TerminalJoinRoute nodes a b c → TerminalPassRoute nodes rest output →
      TerminalPassRoute nodes (a::b::rest) (c::output)

inductive TerminalBalanceRoute (nodes : Nat → TerminalDAGNode K) :
    List (Nat × Bool) → Nat → Prop where
  | empty {z} : nodes z=.constant 0 → TerminalBalanceRoute nodes [] z
  | positive (x) : TerminalBalanceRoute nodes [(x,true)] x
  | negative {x zeroNode z} : nodes zeroNode=.constant 0 →
      TerminalArithmeticRoute nodes .sub zeroNode x z → TerminalBalanceRoute nodes [(x,false)] z
  | pass {a b rest reduced z} : TerminalPassRoute nodes (a::b::rest) reduced →
      TerminalBalanceRoute nodes reduced z → TerminalBalanceRoute nodes (a::b::rest) z

theorem terminal_join_route_value (inputs values : Nat → K) (nodes : Nat → TerminalDAGNode K)
    (equations : ∀ i,values i=terminalNodeValue inputs values (nodes i))
    (a b c : Nat × Bool) (route : TerminalJoinRoute nodes a b c) :
    terminalSignedValue (values c.1,c.2)=terminalSignedValue (values a.1,a.2)+terminalSignedValue (values b.1,b.2) := by
  cases route with
  | same h =>
    have eq := terminal_arithmetic_route_value nodes inputs values equations _ _ _ _ h
    simp only [gkrGateValue] at eq
    simp only [terminalSignedValue]
    split <;> rw [eq] <;> grind
  | positiveNegative h | negativePositive h =>
    have eq := terminal_arithmetic_route_value nodes inputs values equations _ _ _ _ h
    simp only [gkrGateValue] at eq
    simp only [terminalSignedValue,ite_true,Bool.false_eq_true,ite_false]
    rw [eq]
    grind

theorem terminal_pass_route_value (inputs values : Nat → K) (nodes : Nat → TerminalDAGNode K)
    (equations : ∀ i,values i=terminalNodeValue inputs values (nodes i))
    (a b : List (Nat × Bool)) (route : TerminalPassRoute nodes a b) :
    terminalRegisterSignedSum values b=terminalRegisterSignedSum values a := by
  induction route with
  | empty => rfl
  | singleton => rfl
  | @pair a b c rest output join pass ih =>
    have eq := terminal_join_route_value inputs values nodes equations a b c join
    unfold terminalRegisterSignedSum at ih ⊢
    simp only [List.map_cons,List.sum_cons,eq,ih]
    grind

theorem terminal_balance_route_value (inputs values : Nat → K) (nodes : Nat → TerminalDAGNode K)
    (equations : ∀ i,values i=terminalNodeValue inputs values (nodes i))
    (terms : List (Nat × Bool)) (z : Nat) (route : TerminalBalanceRoute nodes terms z) :
    values z=terminalRegisterSignedSum values terms := by
  induction route with
  | @empty z node =>
    have h := equations z
    simpa only [node,terminalNodeValue,terminalRegisterSignedSum,List.map_nil,List.sum_nil] using h
  | positive x =>
    simp only [terminalRegisterSignedSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,terminalSignedValue,ite_true]
    grind
  | @negative x zeroNode z zero route =>
    have h := terminal_arithmetic_route_value nodes inputs values equations _ _ _ _ route
    have h0 := equations zeroNode
    simp only [zero,terminalNodeValue] at h0
    simp only [terminalRegisterSignedSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      terminalSignedValue,Bool.false_eq_true,ite_false]
    simp only [gkrGateValue,h0] at h
    grind
  | @pass a b rest reduced z route balance ih =>
    rw [ih,terminal_pass_route_value inputs values nodes equations _ _ route]

/-- Partial register mapping: only collect's retained leaves require emitted
nodes. The optimized compiler need not emit eliminated intermediate registers. -/
theorem terminal_rebuilt_expansion_value
    (sourceInputs sourceValues targetInputs targetValues : Nat → K)
    (sourceNodes targetNodes : Nat → TerminalDAGNode K)
    (sourceEquations : ∀ i,sourceValues i=terminalNodeValue sourceInputs sourceValues (sourceNodes i))
    (targetEquations : ∀ i,targetValues i=terminalNodeValue targetInputs targetValues (targetNodes i))
    (root z : Nat) (terms : List (Nat × Bool)) (mapping : Nat → Nat)
    (expansion : TerminalSignedExpansion sourceNodes root true terms)
    (leaves : ∀ t∈terms,targetValues (mapping t.1)=sourceValues t.1)
    (balance : TerminalBalanceRoute targetNodes (terms.map (fun t => (mapping t.1,t.2))) z) :
    targetValues z=sourceValues root := by
  rw [terminal_balance_route_value targetInputs targetValues targetNodes targetEquations _ _ balance]
  have mapped : terminalRegisterSignedSum targetValues (terms.map (fun t => (mapping t.1,t.2)))=
      terminalRegisterSignedSum sourceValues terms := by
    unfold terminalRegisterSignedSum
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro t ht
    dsimp only [Function.comp_apply]
    rw [leaves t ht]
  rw [mapped,terminal_signed_expansion_value sourceInputs sourceValues sourceNodes sourceEquations _ _ _ expansion]
  rfl
end NearCompression
