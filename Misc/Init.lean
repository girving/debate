import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Registrations that have to occur before other files
-/

/-- Simp lemmas for showing that primitives are allowed in circuits -/
register_simp_attr prim_mem

/-- Simp lemmas for bounding circuit complexity -/
register_simp_attr circuit_subs

/-- Simp lemmas for evaluating circuits -/
register_simp_attr circuit_eval
