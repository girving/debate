import Mathlib.Analysis.Convex.Deriv

/-!
# Convexity facts
-/

open Set
noncomputable section

/-- Multidimensional version of `ConvexOn.deriv_le_slope` -/
lemma ConvexOn.le_fderiv {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : V → ℝ}
    {s : Set V} (sc : Convex ℝ s) (fc : ConvexOn ℝ s f) {x y : V} (fd : DifferentiableAt ℝ f x)
    (xs : x ∈ s) (ys : y ∈ s) : fderiv ℝ f x (y - x) ≤ f y - f x := by
  set g : ℝ → ℝ := f ∘ AffineMap.lineMap x y
  have gc : ConvexOn ℝ (Icc 0 1) g := by
    refine (fc.comp_affineMap _).subset ?_ (convex_Icc 0 1)
    exact fun _ ↦ Convex.lineMap_mem sc xs ys
  have gd : DifferentiableAt ℝ g 0 := by
    apply DifferentiableAt.comp
    · simp [fd]
    · apply AffineMap.differentiableAt
  trans g 1 - g 0
  · have le : deriv g 0 ≤ slope g 0 1 := gc.deriv_le_slope (by simp) (by simp) zero_lt_one gd
    simp only [slope, sub_zero, inv_one, vsub_eq_sub, smul_eq_mul, one_mul] at le
    refine le_trans (le_of_eq ?_) le
    simp only [g, ← fderiv_deriv]
    rw [fderiv_comp]
    · simp
    · simpa
    · apply AffineMap.differentiableAt
  · simp [g]
