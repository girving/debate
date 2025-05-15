import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Operations
import Mathlib.Tactic.Bound

/-!
# `Finset` facts
-/

open Classical
open Option (some none)
open scoped Real NNReal
noncomputable section

variable {α β γ : Type}

/-- We can swap one set for another in `Finset.sum` if the function is zero off the intersection -/
lemma Finset.sum_eq_sum_zero_off_inter {s0 s1 : Finset α} {g : α → ℝ}
    (h : ∀ x, x ∉ s0 ∨ x ∉ s1 → g x = 0) : s0.sum g = s1.sum g := by
  have e0 : s0.sum g = (s0 ∪ s1).sum g := by
    apply Finset.sum_subset_zero_on_sdiff Finset.subset_union_left
    · intro x m; apply h; left; rw [Finset.mem_sdiff] at m; exact m.2
    · simp only [Prod.mk.eta, implies_true, Prod.forall, forall_const]
  have e1 : s1.sum g = (s0 ∪ s1).sum g := by
    apply Finset.sum_subset_zero_on_sdiff Finset.subset_union_right
    · intro x m; apply h; right; rw [Finset.mem_sdiff] at m; exact m.2
    · simp only [Prod.mk.eta, implies_true, Prod.forall, forall_const]
  rw [e0, e1]

/-- Bound one `Finset.sum` by another on a different space, but injecting between the spaces -/
lemma Finset.sum_le_sum_of_map {s : Finset α} {t : Finset β} {u : α → ℝ} {v : β → ℝ} (i : α → β)
    (inj : ∀ x0 x1, u x0 ≠ 0 → u x1 ≠ 0 → i x0 = i x1 → x0 = x1)
    (le : ∀ x, u x ≠ 0 → u x ≤ v (i x))
    (tv : ∀ y, y ∉ t → v y = 0)
    (v0 : ∀ y, y ∈ t → 0 ≤ v y) :
    s.sum u ≤ t.sum v := by
  rw [←Finset.sum_filter_ne_zero]
  set s' := s.filter (λ x ↦ u x ≠ 0)
  have e : t.sum v = (s'.image i).sum v + (t \ s'.image i).sum v := by
    rw [←Finset.sum_union disjoint_sdiff]; apply Finset.sum_subset_zero_on_sdiff
    · simp only [union_sdiff_self_eq_union, Finset.subset_union_right]
    · intro y m; simp only [union_sdiff_self_eq_union, mem_sdiff, mem_union] at m
      exact tv _ m.2
    · intro _ _; rfl
  rw [e]; clear e
  refine le_trans ?_ (le_add_of_nonneg_right ?_)
  · rw [Finset.sum_image]
    · apply Finset.sum_le_sum; intro x m; simp only [mem_filter, s'] at m; exact le _ m.2
    · intro x m y n; simp only [mem_filter, s'] at m n; apply inj _ _ m.2 n.2
  · apply Finset.sum_nonneg; intro y m
    simp only [mem_sdiff, not_exists, not_and] at m; exact v0 _ m.1

/-- `ENNReal.ofReal` commutes with `Finset.sum` for nonnegative maps -/
lemma Finset.sum_ofReal {s : Finset α} {f : α → ℝ} (f0 : ∀ x, 0 ≤ f x) :
    s.sum (fun x => ENNReal.ofReal (f x)) = .ofReal (s.sum f) := by
  lift f to α → ℝ≥0 using f0
  simp only [ENNReal.ofReal_coe_nnreal, ← ENNReal.coe_finset_sum, ← NNReal.coe_sum]

/-- `Finset.sum` of finite `ENNReals` is finite -/
lemma Finset.sum_ne_top {s : Finset α} {f : α → ENNReal} (ft : ∀ x, f x ≠ ⊤) : s.sum f ≠ ⊤ := by
  lift f to α → ℝ≥0 using ft
  simpa only [← ENNReal.coe_finset_sum] using ENNReal.coe_ne_top

/-- `ENNReal.ofReal` commutes with `Finset.sum` for finite maps -/
lemma Finset.sum_toReal {s : Finset α} {f : α → ENNReal} (ft : ∀ x, f x ≠ ⊤) :
    s.sum (fun x => ENNReal.toReal (f x)) = ENNReal.toReal (s.sum f) := by
  lift f to α → ℝ≥0 using ft
  simp only [← ENNReal.coe_finset_sum, ← NNReal.coe_sum, ENNReal.coe_toReal]

/-- `Finset` sums are the same as `HasSum` if the support is in the set -/
lemma Finset.hasSum_sum [AddCommMonoid β] [TopologicalSpace β] {s : Finset α} {f : α → β}
    (h : ∀ x, x ∉ s → f x = 0) : HasSum f (s.sum f) := by
  apply tendsto_nhds_of_eventually_eq; simp only [Filter.eventually_atTop]; use s
  intro t st; rw [←Finset.sum_subset st]
  · intro x _ m; apply h _ m

lemma Finset.prod_attach_insert [CommMonoid β] {s : Finset α} {a : α} (m : a ∉ s)
    (f : (x : {x // x ∈ insert a s}) → β) :
    ∏ x ∈ (insert a s).attach, f x = f ⟨a, Finset.mem_insert_self a s⟩ *
      ∏ x ∈ s.attach, f ⟨x.1, Finset.mem_insert_of_mem x.2⟩ := by
  rw [Finset.attach_insert, Finset.prod_insert (by simpa)]
  simp

lemma Finset.sum_pi_insert [AddCommMonoid γ] {s : Finset α} {a : α} (m : a ∉ s) {β : α → Type}
    (t : (x : α) → Finset (β x)) (f : (Π x ∈ insert a s, β x) → γ) :
    ∑ x ∈ (insert a s).pi t, f x = ∑ x ∈ t a, ∑ y ∈ s.pi t, f (Finset.Pi.cons s a x y) := by
  rw [Finset.pi_insert m, Finset.sum_biUnion]
  · apply congr_arg₂ _ rfl
    ext x
    rw [Finset.sum_image]
    intro z zm y ym e
    rwa [(Finset.Pi.cons_injective m).eq_iff] at e
  · simp only [Finset.pairwiseDisjoint_iff]
    intro i im j jm ne
    obtain ⟨g,gm⟩ := ne
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_pi] at gm
    obtain ⟨⟨u,_,ue⟩,⟨v,_,ve⟩⟩ := gm
    rw [← Finset.Pi.cons_same s a i u (Finset.mem_insert_self a s), ue,
      ← Finset.Pi.cons_same s a j v (Finset.mem_insert_self a s), ve]

/-- Special case of `Finset.Pi.cons_ne` -/
lemma Finset.Pi.cons_mem {β : α → Type} [DecidableEq α] {s : Finset α} {a : α} {b : β a}
    {f : (a : α) → a ∈ s → β a} (as : a ∉ s) (c : {x // x ∈ s}) (h : ↑c ∈ insert a s) :
    Finset.Pi.cons s a b f c h = f c c.2 := by
  rw [Finset.Pi.cons_ne]
  aesop

lemma Finset.card_sup_le_sum_card (s : Finset α) (f : α → Finset β) :
    (s.sup f).card ≤ ∑ x ∈ s, (f x).card := by
  induction' s using Finset.induction with a s m h
  · simp
  · simp only [Finset.sup_insert, Finset.sup_eq_union, m, not_false_eq_true, Finset.sum_insert]
    exact le_trans (Finset.card_union_le _ _) (by bound)

lemma Finset.card_sdiff_le (s t : Finset α) : (s \ t).card ≤ s.card := by
  have h := Finset.card_sdiff_add_card_inter (s := s) (t := t)
  omega

lemma Finset.sup_sdiff_distrib (s : Finset β) (f : β → Finset α) (t : Finset α) :
    s.sup f \ t = s.sup fun x ↦ f x \ t := by
  induction' s using Finset.induction with a s m h
  · simp
  · simp [Finset.union_sdiff_distrib, h]

lemma Finset.sup_union_distrib (s : Finset α) (f g : α → Finset β) :
    (s.sup f ∪ s.sup g) = s.sup fun x ↦ f x ∪ g x := by
  induction' s using Finset.induction with a s m h generalizing g
  · simp
  · simp only [sup_insert, sup_eq_union, ← union_assoc, union_comm _ (g a)]
    simp only [union_assoc, h]

lemma Finset.sup_const_union (s : Finset α) (n : s.Nonempty) (f : Finset β) (g : α → Finset β) :
    s.sup (fun x ↦ f ∪ g x) = f ∪ s.sup g := by
  rw [← Finset.sup_union_distrib s (f := fun _ ↦ f) g, Finset.sup_const n]

lemma Finset.sup_union_const (s : Finset α) (n : s.Nonempty) (f : α → Finset β) (g : Finset β) :
    s.sup (fun x ↦ f x ∪ g) = s.sup f ∪ g := by
  rw [← Finset.sup_union_distrib s f (g := fun _ ↦ g), Finset.sup_const n]

lemma Finset.univ_sup_const_union [Fintype α] [Nonempty α] (f : Finset β) (g : α → Finset β) :
    Finset.univ.sup (fun x ↦ f ∪ g x) = f ∪ Finset.univ.sup g := by
  apply Finset.sup_const_union; simp

lemma Finset.univ_sup_union_const [Fintype α] [Nonempty α] (f : α → Finset β) (g : Finset β) :
    Finset.univ.sup (fun x ↦ f x ∪ g) = Finset.univ.sup f ∪ g := by
  apply Finset.sup_union_const; simp

@[simp] lemma Finset.union_singleton {s : Finset α} {a : α} : s ∪ {a} = insert a s := by
  ext x; aesop

@[simp] lemma Finset.singleton_union {s : Finset α} {a : α} : {a} ∪ s = insert a s := by
  rw [union_comm, Finset.union_singleton]

@[simp] lemma Finset.univ_sup_comp_equivFin_symm [Fintype β] [SemilatticeSup α] [OrderBot α]
    (f : β → α) : univ.sup (fun x ↦ f ((Fintype.equivFin β).symm x)) = univ.sup f := by
  set i : Fin (Fintype.card β) ↪ β := ↑(Fintype.equivFin β).symm
  trans Finset.univ.sup (f ∘ i)
  · rfl
  · rw [← Finset.sup_map]
    exact Finset.sup_congr (by simp [i]) (fun x _ ↦ rfl)

@[simp] lemma Finset.univ_sup_const [Fintype α] [Nonempty α] [SemilatticeSup β] [OrderBot β]
    (x : β) : (.univ : Finset α).sup (fun _ ↦ x) = x := by
  apply Finset.sup_const; simp
