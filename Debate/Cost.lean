import Comp.Basic
import Debate.Details
import Debate.Protocol
import Mathlib.Data.Complex.ExponentialBounds
import Misc.Bound

/-!
# Query complexity for each agent in the debate protocol

See `Correct.lean` for the summary.
-/

open Classical
open Prob
open Option (some none)
open Real (log)
open Set
open scoped Real
noncomputable section

variable {ι I α β: Type}
variable {i : OracleId}
variable {o : BOracle ι}
variable {u : Set I}
variable {n : ℕ}
variable {k c s b e p q v : ℝ}
variable {y : ι}

/-!
### Costs for a single player invocation
-/

/-- Alice takes the expected number of samples -/
@[simp] lemma alice_cost : (alice c q y).cost (fun _ ↦ o) AliceId = samples c q := by
  simp only [alice, alice', Comp.cost_estimate, Comp.cost_query, mul_one]

/-- Bob takes the expected number of samples -/
@[simp] lemma bob_cost : (bob s b q y p).cost (fun _ => o) BobId = samples ((b-s)/2) q := by
  simp only [bob, bob', alice', Comp.cost_bind, Comp.cost_estimate, Comp.cost_query, mul_one,
    Comp.prob_estimate, Comp.prob_query, Comp.cost_pure, exp_const, add_zero]

/-- Vera takes the expected number of samples -/
@[simp] lemma vera_cost : (vera c s v y p).cost (fun _ => o) VeraId = samples ((s-c)/2) v := by
  simp only [vera, bob', alice', Comp.cost_bind, Comp.cost_estimate, Comp.cost_query, mul_one,
    Comp.prob_estimate, Comp.prob_query, Comp.cost_pure, exp_const, add_zero]

/-!
### Alice and Bob cost
-/

/-- Alice makes few queries, regardless of Bob and Vera -/
lemma alice_steps_cost (bob : Bob ι) (vera : Vera ι) (f : BComp ι u α) :
    (steps (alice c q) bob vera f).cost (fun _ ↦ o) AliceId ≤ f.worst * samples c q := by
  induction' f with x n p g h i m y f h
  · simp only [steps, Comp.cost_pure']
    bound
  · simp only [steps, Comp.cost_sample', Comp.worst_sample']
    exact exp_le_of_forall_le fun x x0 ↦ le_trans (h _) (by bound)
  · simp only [steps, step, bind_assoc, Comp.cost_bind, exp_const, Comp.cost_allow_all, alice_cost,
      mem_singleton_iff, reduceCtorEq, not_false_eq_true, Comp.cost_eq_zero, zero_add, ite_self,
      Comp.cost_pure, Comp.worst_query', Nat.cast_add, Nat.cast_succ, CharP.cast_eq_zero, add_mul,
      one_mul, add_le_add_iff_left, Comp.cost_map, Comp.cost_sample,
      apply_ite (f := fun c ↦ Comp.cost c (fun _ ↦ o) AliceId)]
    refine exp_le_of_forall_le fun p _ ↦ exp_le_of_forall_le fun x _ ↦ ?_
    match x with
    | true =>
      refine exp_le_of_forall_le fun z _ ↦ ?_
      match z with
      | .ok _ => exact le_trans (h _) (by bound)
      | .error _ => simp; bound
    | false => simp [exp_map, Function.comp_def]; bound

/-- Bob makes few queries, regardless of Alice and Vera -/
lemma bob_steps_cost (alice : Alice ι) (vera : Vera ι) (f : BComp ι u α) :
    (steps alice (bob s b q) vera f).cost (fun _ ↦ o) BobId ≤ f.worst * samples ((b-s)/2) q := by
  induction' f with x n p g h i m y f h
  · simp only [steps, Comp.cost_pure', Comp.worst_pure', CharP.cast_eq_zero, zero_mul, le_refl]
  · simp only [steps, Comp.cost_sample', Comp.worst_sample']
    exact exp_le_of_forall_le fun x x0 ↦ le_trans (h _) (by bound)
  · simp only [steps, step, bind_pure_comp, bind_assoc, Comp.cost_bind, Comp.cost_allow_all,
      mem_singleton_iff, reduceCtorEq, not_false_eq_true, Comp.cost_eq_zero, Comp.prob_allow_all,
      bob_cost, exp_const_add, zero_add, Comp.worst_query', Nat.cast_add, Nat.cast_one, add_mul,
      one_mul, add_le_add_iff_left]
    refine exp_le_of_forall_le fun p _ ↦ exp_le_of_forall_le fun x _ ↦ ?_
    match x with
    | true =>
      simp only [↓reduceIte, Comp.cost_map, Comp.cost_sample, Comp.cost_pure, exp_const, zero_add,
        Comp.prob_map, Comp.prob_sample, Comp.prob_pure, bind_pure, exp_map, Function.comp_def]
      exact exp_le_of_forall_le fun x _ ↦ le_trans (h _) (by bound)
    | false => simp [exp_map, Function.comp_def]; bound

/-- Alice makes few queries, regardless of Bob and Vera -/
theorem alice_debate_cost (bob : Bob ι) (vera : Vera ι) (f : BComp ι u Bool) :
    (debate (alice c q) bob vera f).cost' o AliceId ≤ f.worst * samples c q := by
  simp only [debate, Comp.cost', Comp.cost_bind]
  rw [← add_zero (_ * _)]
  apply add_le_add
  · apply alice_steps_cost
  · refine exp_le_of_forall_le fun y _ ↦ ?_
    induction y; repeat simp only [Comp.cost_pure, le_refl]

/-- Bob makes few queries, regardless of Alice and Vera -/
theorem bob_debate_cost (alice : Alice ι) (vera : Vera ι) (f : BComp ι u Bool) :
    (debate alice (bob s b q) vera f).cost' o BobId ≤ f.worst * samples ((b-s)/2) q := by
  simp only [debate, Comp.cost', Comp.cost_bind]
  rw [← add_zero (_ * _)]
  apply add_le_add
  · apply bob_steps_cost
  · refine exp_le_of_forall_le fun y _ ↦ ?_
    induction y; repeat simp only [Comp.cost_pure, le_refl]

/-- Alice makes `O(k^2 t log t)` queries with default parameters -/
theorem alice_fast (k : ℝ) (k0 : 0 < k) (f : BComp ι u Bool) (bob : Bob ι) (vera : Vera ι) :
    let p := defaults k f.worst k0
    (debate (alice p.c p.q) bob vera f).cost' o AliceId ≤
      f.worst * (5000 * k^2 * Real.log (200 * f.worst) + 1) := by
  refine le_trans (alice_debate_cost _ _ _) ?_
  by_cases f0 : f.worst = 0
  · simp only [f0, CharP.cast_eq_zero, zero_mul, Real.log_zero, zero_add, mul_one, le_refl]
  · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have f1 : max 1 f.worst = f.worst := by omega
    simp only [defaults, samples, ← Real.log_inv, f1]
    generalize hn : (f.worst : ℝ) = n
    have n1 : 1 ≤ n := by rw [← hn, Nat.one_le_cast]; omega
    field_simp
    simp only [mul_pow, mul_div_assoc (Real.log _), mul_div_right_comm, mul_right_comm _ _ (2 : ℝ)]
    norm_num
    simp only [mul_comm (Real.log _)]
    exact (Nat.ceil_lt_add_one (by bound)).le

/-- Bob makes `O(k^2 t log t)` queries with default parameters -/
theorem bob_fast (k : ℝ) (k0 : 0 < k) (f : BComp ι u Bool) (alice : Alice ι) (vera : Vera ι) :
    let p := defaults k f.worst k0
    (debate alice (bob p.s p.b p.q) vera f).cost' o BobId ≤
      f.worst * (20000 / 9 * k^2 * Real.log (200 * f.worst) + 1) := by
  generalize hd : (20000 / 9 : ℝ) = d
  refine le_trans (bob_debate_cost _ _ _) ?_
  by_cases f0 : f.worst = 0
  · simp only [f0, CharP.cast_eq_zero, zero_mul, mul_zero, zero_add, mul_one, le_refl]
  · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have f1 : max 1 f.worst = f.worst := by omega
    simp only [defaults, samples, ← Real.log_inv, f1]
    generalize hn : (f.worst : ℝ) = n
    have n1 : 1 ≤ n := by rw [← hn, Nat.one_le_cast]; omega
    field_simp
    simp only [mul_pow, mul_div_assoc (Real.log _), mul_div_right_comm, mul_right_comm _ _ (2 : ℝ)]
    norm_num
    simp only [hd, mul_comm (Real.log _)]
    exact (Nat.ceil_lt_add_one (by bound)).le

/-!
### Vera cost

Vera runs at most once, so we transpose the algorithm to make that obvious before doing the
cost calculation.
-/

/-- State for use by Vera at the end -/
def StateV (ι α : Type) := Except (ι × ℝ) α

/-- One step of the debate protocol, without Vera
    c and s are the completeness and soundness parameters of the verifier. -/
def stepV (alice : Alice ι) (bob : Bob ι) (y : ι) : BComp ι {AliceId,BobId} (StateV ι Bool) := do
  let p ← (alice y).allow (by subset)
  if ← (bob y p).allow (by subset) then do  -- Bob accepts Alice's probability, so take the step
    let x ← bernoulli p  -- This is Figure 4, steps 2b,2c,2d, as a fixed part of the protocol
    return .ok x
  else  -- Bob rejects, so we record verifier inputs and end the computation
    return .error ⟨y,p⟩

/-- `n` steps of the debate protocol, without Vera -/
def stepsV (alice : Alice ι) (bob : Bob ι) :
    (f : BComp ι u α) → BComp ι {AliceId,BobId} (StateV ι α)
| .pure' x => pure (.ok x)
| .sample' p f => .sample' p fun y ↦ stepsV alice bob (f y)
| .query' _ _ y f => do match ← stepV alice bob y with
  | .ok x => stepsV alice bob (f x)
  | .error r => return .error r

/-- Turn `StateV` into `State` with a Vera call -/
def postV (vera : Vera ι) (x : StateV ι α) : BComp ι AllIds (State α) := match x with
| .ok y => return .ok y
| .error ⟨y,p⟩ => return .error (← (vera y p).allow_all)

/-- Relate `stepsV` and `steps `-/
lemma post_stepsV (alice : Alice ι) (bob : Bob ι) (vera : Vera ι) (f : BComp ι u α) :
    (stepsV alice bob f).allow_all >>= postV vera = steps alice bob vera f := by
  induction' f with x n p g h i m y f h
  · simp only [Comp.allow_all, stepsV, pure, Comp.allow_pure', Comp.pure'_bind, postV, steps]
  · simp only [stepsV, Comp.allow_all_bind, bind_assoc, steps, ← h]; rfl
  · simp only [stepsV, stepV, bind_pure_comp, bind_assoc, Comp.allow_all_bind,
      Comp.allow_all_allow, steps, step, ← h]
    strip p
    strip x
    induction x
    all_goals simp only [↓reduceIte, Comp.allow_all_map, Comp.allow_all_sample, Comp.allow_all_pure,
      bind_map_left, Comp.sample_bind, pure_bind, Bool.false_eq_true, postV, bind_pure_comp]

/-- Vera makes few queries, regardless of Alice and Bob -/
theorem vera_debate_cost (alice : Alice ι) (bob : Bob ι) (f : BComp ι u Bool) :
    (debate alice bob (vera c s v) f).cost' o VeraId ≤ samples ((s-c)/2) v := by
  have z : (stepsV alice bob f).cost (fun _ ↦ o) VeraId = 0 := by zero_cost
  simp only [Comp.cost', debate, ← post_stepsV, bind_assoc, Comp.cost_bind, Comp.cost_allow_all, z,
    Comp.prob_allow_all, zero_add, ge_iff_le]
  refine exp_le_of_forall_le fun x _ ↦ ?_
  refine le_trans (add_le_of_nonpos_right ?_) ?_
  · refine exp_le_of_forall_le fun x _ ↦ ?_
    induction x; repeat simp only [Comp.cost_pure, le_refl]
  · simp only [postV]
    induction x
    · simp only [Comp.cost_bind, Comp.cost_allow_all, vera_cost, Comp.prob_allow_all,
        Comp.cost_pure, exp_const, add_zero, le_refl]
    · simp only [Comp.cost_pure, Nat.cast_nonneg]

/-- A calculation used in `vera_fast` -/
@[bound] lemma log_mul_le : Real.log 200 * 20000 ≤ 106000 := by
  rw [← le_div_iff₀ (by norm_num), Real.log_le_iff_le_exp (by norm_num)]
  norm_num
  rw [← Real.exp_one_rpow, div_eq_mul_inv, Real.rpow_mul (by positivity),
    Real.le_rpow_inv_iff_of_pos (by norm_num) (by positivity) (by norm_num)]
  refine le_trans ?_ (Real.rpow_le_rpow ?_ Real.exp_one_gt_d9.le ?_)
  all_goals norm_num

/-- Vera makes `O(k^2)` queries with default parameters -/
theorem vera_fast (k : ℝ) (k0 : 0 < k) (f : BComp ι u Bool) (alice : Alice ι) (bob : Bob ι) :
    let p := defaults k f.worst k0
    (debate alice bob (vera p.c p.s p.v) f).cost' o VeraId ≤ 106000 * k^2 + 1 := by
  refine le_trans (vera_debate_cost _ _ _) ?_
  simp only [defaults, samples, ← Real.log_inv]
  field_simp
  refine le_trans (Nat.ceil_lt_add_one (by positivity)).le ?_
  simp only [mul_pow, mul_div_assoc (Real.log _), mul_div_right_comm, mul_right_comm _ _ (2 : ℝ)]
  norm_num [← mul_assoc]
  bound
