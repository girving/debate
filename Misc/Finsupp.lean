import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Topology.Constructions

/-!
# `Finsupp` facts
-/

variable {α β : Type}
variable {R : Type} [Semiring R]
variable {M : Type} [AddCommMonoid M] [Module R M]

lemma Finsupp.sum_smul (b : M) (s : α →₀ R) {f : α → R → R} :
    s.sum f • b = s.sum fun a c ↦ f a c • b := by
  simp only [Finsupp.sum, Finset.sum_smul]

lemma Finsupp.support_pointwise_smul_eq [NoZeroDivisors R] {s : α →₀ R} {f : α → R}
    (f0 : ∀ x, x ∈ s.support → f x ≠ 0) : (f • s).support = s.support := by
  ext x
  simpa using f0 x

/-!
### Topological structure
-/

variable [TopologicalSpace β] [Zero β]

instance : TopologicalSpace (α →₀ β) :=
  TopologicalSpace.induced Finsupp.toFun (by infer_instance : TopologicalSpace (α → β))

lemma Finsupp.isOpen_iff {s : Set (α →₀ β)} :
    IsOpen s ↔ ∃ (t : Set (α → β)), IsOpen t ∧ Finsupp.toFun ⁻¹' t = s := by
  rfl

lemma Finsupp.isInducing_toFun : Topology.IsInducing (Finsupp.toFun : (α →₀ β) → α → β) where
  eq_induced := rfl
