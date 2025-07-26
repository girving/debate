import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Data.Fintype.Pi

/-!
# `Fin` facts
-/

open Classical
variable {n : ℕ}
variable {α β : Type}

lemma Fin.snoc_eq_iff {x : Fin n → α} {y : α} {z : Fin (n + 1) → α} :
    Fin.snoc x y = z ↔ x = Fin.init z ∧ y = z (last n) := by
  simp [Fin.init_def, funext_iff, snoc, Fin.forall_iff_castSucc, and_comm]

lemma Fin.take_snoc {n : ℕ} {k : Fin n} {h : (k : ℕ) ≤ n + 1} {x : Fin n → α} {y : α} :
    (Fin.take (α := fun _ ↦ α) k h (snoc x y)) = (Fin.take k (by omega : k ≤ n) x) := by
  ext i
  have p : i < n := by omega
  simp only [Fin.take_apply, snoc, Fin.coe_castLE, p, ↓reduceDIte, Fin.castSucc_castLT, cast_eq]
  exact congr_arg _ rfl

/-- Sum over `n + 1` values by summing over the first `n` and the last -/
lemma Fin.sum_comp_snoc [AddCommMonoid β] (n : ℕ) (s : Finset (Fin (n + 1) → α))
    (f : (Fin (n + 1) → α) → β) :
    ∑ x ∈ s, f x = ∑ x ∈ s.image init,
      ∑ y ∈ (s.filter fun y ↦ init y = x).image (fun x ↦ x (last n)), f (snoc x y) := by
  have e : s = Finset.biUnion (s.image init) (fun x ↦ s.filter fun y ↦ init y = x) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_image, exists_exists_and_eq_and, Finset.mem_filter]
    aesop
  nth_rw 1 [e]
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.sum_image]
    · simp only [Finset.sum_filter]
      refine Finset.sum_congr rfl fun y ys ↦ ?_
      by_cases yx : init y = x
      · simp only [← yx, ↓reduceIte, snoc_init_self]
      · simp only [yx, ↓reduceIte]
    · simp only [Set.InjOn, Finset.coe_filter, Set.mem_setOf_eq, and_imp]
      intro u us ux y ys yx uy
      rw [← yx] at ux
      rw [← Fin.snoc_init_self u, ← Fin.snoc_init_self y, uy, ux]
  · simp only [Finset.coe_image]
    intro u _ v _ uv
    simp [Function.onFun, Finset.disjoint_iff_ne]
    intro a as au b bs bv
    contrapose uv
    simp only [not_not] at uv
    simp only [← au, uv, ← bv, not_not]

/-- `InjOn` variant of `Fin.snoc_inj` -/
lemma Fin.snoc_injOn {x : Fin n → α} {s : Set α} : Set.InjOn (snoc (α := fun _ ↦ α) x) s := by
  intro a as b bs e
  simpa [Fin.snoc_inj] using e
