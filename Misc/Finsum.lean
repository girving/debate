import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.Constructions
import Misc.Init

/-!
# Sum over `Set.univ` if a function is finite

This is some machinery that makes it easier to manipulate sums that are finite, but not manifestly
finite. `Finsupp` is a bit messy to work with directly, and dealing with `Finset.sum` often requires
tracking exactly when things are zero.
-/

open Classical
open Set
variable {α β : Type}
variable {A : Type} [AddCommMonoid A]
variable {R : Type} [Semiring R]
variable {M : Type} [AddCommMonoid M] [Module R M]
variable {n : ℕ}

/-- Partial `∑ᶠ` sums inherit finiteness -/
lemma Set.Finite.finsum_snd {f : α × β → A} (h : f.support.Finite) :
    (fun x ↦ ∑ᶠ y, f (x, y)).support.Finite := by
  refine Set.Finite.subset (s := h.toFinset.image Prod.fst) ?_ ?_
  · apply Finset.finite_toSet
  · intro x m
    contrapose m
    simp_all

/-- Finite support from the left product -/
lemma Set.Finite.mul_left {f g : α → R} (h : f.support.Finite) :
    (fun x ↦ f x * g x).support.Finite :=
  h.subset (by aesop)

/-- Finite support from the left product -/
lemma Set.Finite.smul_left {f : α → R} {g : α → M} (h : f.support.Finite) :
    (fun x ↦ f x • g x).support.Finite :=
  h.subset (by aesop)

/-- `∑ᶠ` is `Finset.sum` if support is finite -/
lemma finsum_of_finite (f : α → A) (h : f.support.Finite) : ∑ᶠ x, f x = ∑ x ∈ h.toFinset, f x := by
  simp only [finsum_def, h, dite_true]

/-- `∑ᶠ` respects products -/
lemma finsum_product {f : α × β → A} (h : f.support.Finite) :
    ∑ᶠ z : α × β, f z = ∑ᶠ (x : α) (y : β), f (x, y) := by
  have hx : ∀ x, (fun y ↦ f (x, y)).support.Finite :=
    fun _ ↦ Function.support_along_fiber_finite_of_finite _ _ h
  simp only [finsum_of_finite, h, h.finsum_snd]
  simp only [finsum_of_finite, hx]
  trans ∑ x ∈ h.toFinset.image Prod.fst, ∑ y ∈ h.toFinset.image Prod.snd, f (x, y)
  · rw [← Finset.sum_product]
    apply Finset.sum_subset
    · simp only [Finite.toFinset_subset, Finset.coe_product, Finset.coe_image, Finite.coe_toFinset,
        Function.support_subset_iff, ne_eq, mem_prod, mem_image, Function.mem_support, Prod.exists,
        exists_and_right, exists_eq_right, Prod.forall]
      intro x y e
      exact ⟨⟨y, e⟩, ⟨x, e⟩⟩
    · intro x m n
      simp only [Finite.mem_toFinset, Function.mem_support, ne_eq, Decidable.not_not] at n
      exact n
  · have e : ∀ x, ∑ y ∈ (hx x).toFinset, f (x, y) = ∑ y ∈ Finset.image Prod.snd h.toFinset, f (x, y) := by
      intro x
      apply Finset.sum_subset
      · intro y m
        simp only [Finite.mem_toFinset, Function.mem_support, ne_eq, Finset.mem_image, Prod.exists,
          exists_eq_right] at m ⊢
        exact ⟨_, m⟩
      · aesop
    symm
    apply Finset.sum_subset_zero_on_sdiff
    · intro x m
      contrapose m
      simp only [Finset.mem_image, Finite.mem_toFinset, Function.mem_support, ne_eq, Prod.exists,
        exists_and_right, exists_eq_right, not_exists, Decidable.not_not] at m ⊢
      simp only [m, Function.support_zero, toFinite_toFinset, toFinset_empty, Finset.sum_const_zero]
    · intro x m
      simp only [Finset.mem_sdiff, Finset.mem_image, Finite.mem_toFinset, Function.mem_support,
        ne_eq, Prod.exists, exists_and_right, exists_eq_right, Decidable.not_not] at m ⊢
      simp only [← e, m.2]
    · simp [e]

/-- Commute two `∑ᶠ`s -/
lemma finsum_comm (f : α × β → A) (h : f.support.Finite) :
    ∑ᶠ (x : α) (y : β), f (x, y) = ∑ᶠ (y : β) (x : α), f (x, y) := by
  rw [← finsum_product h, ← finsum_product (f := fun z ↦ f ⟨z.2,z.1⟩),
    ← finsum_comp_equiv (Equiv.prodComm _ _)]
  · simp only [Equiv.prodComm_apply, Prod.swap]
  · exact h.of_injOn (f := Prod.swap) (fun _ m ↦ m) Prod.swap_injective.injOn

/-- Specialize case of `finsum_product` for `Fin (n + 1) → α` -/
lemma finsum_fin_succ (f : (Fin (n + 1) → α) → A) (h : f.support.Finite) :
    ∑ᶠ x, f x = ∑ᶠ (x : Fin n → α) (y : α), f (Fin.snoc x y) := by
  rw [finsum_comm (fun z : (Fin n → α) × α ↦ f (Fin.snoc z.1 z.2)),
    ← finsum_comp_equiv (Fin.snocEquiv _), finsum_product]
  · rfl
  · refine h.of_injOn (f := fun z ↦ Fin.snocEquiv _ z) (fun _ m ↦ m) ?_
    intro x m y n e
    aesop
  · refine h.of_injOn (f := fun z ↦ Fin.snoc z.1 z.2) (fun _ m ↦ m) ?_
    intro x m y n e
    aesop

/-- Pull a constant scaling out of a `∑ᶠ` -/
lemma finsum_const_mul [NoZeroDivisors R] (f : α → R) (c : R) : ∑ᶠ x, c * f x = c * ∑ᶠ x, f x := by
  by_cases c0 : c = 0
  · aesop
  · simp only [finsum_def]
    have e : (fun i ↦ c * f i).support = f.support := by ext x; simp [c0]
    split_ifs with a b d
    · simp only [← Finset.mul_sum]
      refine congr_arg₂ _ rfl (congr_arg₂ _ ?_ rfl)
      exact Finite.toFinset_inj.mpr e
    · simp only [e] at a; aesop
    · simp only [e] at a; aesop
    · simp only [mul_zero]

/-- Pull a constant scaling out of a `∑ᶠ` -/
lemma finsum_mul_const [NoZeroDivisors R] (f : α → R) (c : R) :
    ∑ᶠ x, f x * c = (∑ᶠ x, f x) * c := by
  by_cases c0 : c = 0
  · aesop
  · simp only [finsum_def]
    have e : (fun i ↦ f i * c).support = f.support := by ext x; simp [c0]
    split_ifs with a b d
    · simp only [← Finset.sum_mul]
      refine congr_arg₂ _ (congr_arg₂ _ ?_ rfl) rfl
      exact Finite.toFinset_inj.mpr e
    · simp only [e] at a; aesop
    · simp only [e] at a; aesop
    · simp only [zero_mul]

/-- Simplify a `∑ᶠ` that's obviously a singleton -/
@[simp] lemma finsum_ite_eq {f : α → A} (a : α) {d : (x : α) → Decidable (x = a)}
    (h : f.support.Finite) : ∑ᶠ x, ite (x = a) (h := d x) (f x) 0 = f a := by
  have t : (fun x ↦ ite (x = a) (h := d x) (f x) 0).support.Finite := h.subset (by aesop)
  simp only [finsum_def, t, ↓reduceDIte]
  rw [Finset.sum_eq_single (a := a)]
  all_goals simp
