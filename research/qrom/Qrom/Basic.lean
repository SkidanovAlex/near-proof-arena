import Mathlib

/-!
# Qrom.Basic — research package with Mathlib

Scratch space for QROM work that needs Mathlib. Nothing here is part of the
gated `zk-formal` package (DESIGN.md F4 forbids Mathlib there).
-/

theorem qrom_smoke (a b : Nat) (h : a ≤ b) : a ≤ b := h
