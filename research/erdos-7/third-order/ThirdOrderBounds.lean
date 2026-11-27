import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Polynomial inequalities for the third-order coprime inclusion-exclusion bound. -/

namespace ThirdOrderBounds

noncomputable def P (t : ℝ) : List ℝ → ℝ
  | [] => 1
  | x :: xs => (1 + t*x) * P t xs

def InCube (xs : List ℝ) : Prop := ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1/2

noncomputable def B (xs : List ℝ) : ℝ :=
  (P 3 xs - 6*P 2 xs + 15*P 1 xs - 10)/6

theorem P_append (t : ℝ) (xs ys : List ℝ) : P t (xs ++ ys) = P t xs * P t ys := by
  induction xs with
  | nil => simp [P]
  | cons x xs ih => simp only [List.cons_append, P, ih]; ring

/-- The multilinear expression is a convex combination of its values at cube
vertices. Each vertex value depends only on how many coordinates equal 1/2. -/
theorem vertex_test (xs : List ℝ) (bounds : InCube xs) (a b c d : ℝ)
    (vertices : ∀ m : ℕ, 0 ≤ a*(5/2)^m + b*2^m + c*(3/2)^m + d) :
    0 ≤ a*P 3 xs + b*P 2 xs + c*P 1 xs + d := by
  induction xs generalizing a b c d with
  | nil => simpa [P] using vertices 0
  | cons x xs ih =>
    obtain ⟨lo, hi⟩ := bounds x (.head _)
    have tail : InCube xs := fun y hy => bounds y (.tail _ hy)
    have at_zero := ih tail a b c d vertices
    have at_half := ih tail (a*(5/2)) (b*2) (c*(3/2)) d (by
      intro m
      convert vertices (m+1) using 1
      ring)
    simp only [P]
    have lower := mul_nonneg (show 0 ≤ 1-2*x by linarith) at_zero
    have upper := mul_nonneg (show 0 ≤ 2*x by linarith) at_half
    linarith only [lower, upper]

private theorem large_power_bound (k : ℕ) (a b : ℝ) (ha : 0 ≤ a)
    (base : b*2^k ≤ a*(5/2)^k) (m : ℕ) (hm : k ≤ m) :
    b*2^m ≤ a*(5/2)^m := by
  induction m, hm using Nat.le_induction with
  | base => exact base
  | succ m _ ih =>
    have positive : 0 ≤ a*(5/2)^m := by positivity
    rw [pow_succ, pow_succ]
    linarith only [ih, positive]

theorem slope_nonnegative (xs : List ℝ) (bounds : InCube xs) :
    0 ≤ 3*P 3 xs - 12*P 2 xs + 15*P 1 xs := by
  have check : ∀ m : ℕ, (0 : ℝ) ≤ 3*(5/2)^m + (-12)*2^m + 15*(3/2)^m + 0 := by
    intro m
    by_cases hm : 7 ≤ m
    · have h := large_power_bound 7 3 12 (by norm_num) (by norm_num) m hm
      have hpos : (0 : ℝ) ≤ (3/2)^m := by positivity
      linarith
    · interval_cases m <;> norm_num
  simpa only [neg_mul, ← sub_eq_add_neg, add_zero] using vertex_test xs bounds 3 (-12) 15 0 check

theorem mass_le_five_B (xs : List ℝ) (bounds : InCube xs) : P 1 xs - 1 ≤ 5*B xs := by
  have check : ∀ m : ℕ, (0 : ℝ) ≤ 5*(5/2)^m + (-30)*2^m + 69*(3/2)^m + (-44) := by
    intro m
    by_cases hm : 9 ≤ m
    · have h := large_power_bound 9 5 30 (by norm_num) (by norm_num) m hm
      have hpos : (1 : ℝ) ≤ (3/2)^m := one_le_pow₀ (by norm_num)
      linarith
    · interval_cases m <;> norm_num
  have h := vertex_test xs bounds 5 (-30) 69 (-44) check
  unfold B
  linarith

/-- Any coordinate may be increased, holding the other coordinates in the half cube. -/
theorem coordinate_monotone (left right : List ℝ) (bounds : InCube (left++right))
    {x y : ℝ} (hxy : x ≤ y) : B (left ++ x :: right) ≤ B (left ++ y :: right) := by
  have hs := mul_nonneg (sub_nonneg.mpr hxy) (slope_nonnegative _ bounds)
  simp only [P_append] at hs
  simp only [B, P_append, P]
  linarith only [hs]

/-- Deleting any selection of coordinates cannot increase the third-order bound. -/
theorem sublist_monotone {small large : List ℝ} (sub : small.Sublist large)
    (bounds : InCube large) : B small ≤ B large := by
  suffices aux : ∀ pre : List ℝ, InCube (pre ++ large) →
      B (pre ++ small) ≤ B (pre ++ large) by simpa using aux [] bounds
  clear bounds
  induction sub with
  | slnil => simp
  | @cons l r x _ ih =>
    intro pre bound
    have tail : InCube (pre ++ r) := by
      intro y hy
      apply bound
      rcases List.mem_append.mp hy with hp | hr
      · exact List.mem_append_left _ hp
      · exact List.mem_append_right _ (.tail _ hr)
    have hpre := ih pre tail
    have hx := (bound x (List.mem_append_right _ (.head _))).1
    have insert := coordinate_monotone pre r tail hx
    have unpadded : B (pre ++ 0 :: r) = B (pre ++ r) := by simp [B, P_append, P]
    exact hpre.trans (unpadded ▸ insert)
  | @cons_cons l r x _ ih =>
    intro pre bound
    simpa using ih (pre ++ [x]) (by simpa using bound)

end ThirdOrderBounds
