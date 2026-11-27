import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! The weighted extension inequality and the alternating tail for an
arbitrary finite hereditary family, including matchings on a hypergraph. -/

open Finset
open scoped BigOperators

namespace ThirdOrderTail

variable {α : Type*} [DecidableEq α] [Fintype α]

def level (F : Finset (Finset α)) (k : ℕ) : Finset (Finset α) := F.filter (fun s => s.card = k)

noncomputable def mass (F : Finset (Finset α)) (w : α → ℝ) (k : ℕ) : ℝ :=
  ∑ s ∈ level F k, ∏ v ∈ s, w v

/-- Mark one member of a (k+1)-set and delete it. For a fixed marked
member, the operation injects the remaining choices into the k-level. -/
theorem extension_bound (F : Finset (Finset α)) (w : α → ℝ) (positive : ∀ v, 0 ≤ w v)
    (hereditary : ∀ s ∈ F, ∀ v ∈ s, s.erase v ∈ F) (k : ℕ) :
    (k+1 : ℝ) * mass F w (k+1) ≤ (∑ v, w v) * mass F w k := by
  classical
  let wt (s : Finset α) := ∏ v ∈ s, w v
  have mark (v : α) :
      ∑ s ∈ (level F (k+1)).filter (fun s => v ∈ s), wt s ≤ w v * mass F w k := by
    let marked := (level F (k+1)).filter (fun s => v ∈ s)
    have facts {s} (hs : s ∈ marked) : (s ∈ F ∧ s.card = k+1) ∧ v ∈ s := by
      simpa [marked, level] using hs
    have included : marked.image (fun s => s.erase v) ⊆ level F k := by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := mem_image.mp ht
      obtain ⟨⟨valid, card⟩, member⟩ := facts hs
      exact mem_filter.mpr ⟨hereditary _ valid _ member,
        by rw [card_erase_of_mem member, card]; omega⟩
    have inject : Set.InjOn (fun s : Finset α => s.erase v) (↑marked) := by
      intro s hs t ht he
      simpa [insert_erase (facts hs).2, insert_erase (facts ht).2] using congrArg (insert v) he
    change (∑ s ∈ marked, wt s) ≤ _
    calc
      _ = ∑ s ∈ marked, w v * wt (s.erase v) := by
        apply sum_congr rfl
        intro s hs
        exact (mul_prod_erase _ _ (facts hs).2).symm
      _ = ∑ t ∈ marked.image (fun s => s.erase v), w v * wt t :=
        by rw [sum_image inject]
      _ ≤ ∑ t ∈ level F k, w v * wt t := by
        apply sum_le_sum_of_subset_of_nonneg included
        intro t _ _
        exact mul_nonneg (positive v) (prod_nonneg fun i _ => positive i)
      _ = _ := by rw [← mul_sum]; rfl
  have count (s : Finset α) : (∑ v : α, if v ∈ s then wt s else 0) = s.card * wt s := by
    simp
  calc
    _ = ∑ s ∈ level F (k+1), ∑ v : α, if v ∈ s then wt s else 0 := by
      unfold mass
      rw [mul_sum]
      apply sum_congr rfl
      intro s hs
      rw [count, (mem_filter.mp hs).2, Nat.cast_add, Nat.cast_one]
    _ = ∑ v : α, ∑ s ∈ (level F (k+1)).filter (fun s => v ∈ s), wt s := by
      rw [sum_comm]
      simp only [sum_filter]
    _ ≤ ∑ v : α, w v * mass F w k := sum_le_sum (fun v _ => mark v)
    _ = _ := by rw [sum_mul]

/-- Pair the 4th and 5th terms, the 6th and 7th, and so on. A final
unpaired term has positive sign. The range length N can be odd or even. -/
theorem alternating_tail_nonnegative (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k)
    (decreases : ∀ k ≥ 4, A (k+1) ≤ A k) (N : ℕ) :
    0 ≤ ∑ j ∈ range N, (-1 : ℝ)^j * A (4+j) := by
  have pairs (n : ℕ) : 0 ≤ ∑ j ∈ range (2*n), (-1 : ℝ)^j * A (4+j) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.mul_succ, sum_range_succ, sum_range_succ]
      have even : (-1 : ℝ)^(2*n) = 1 := by simp [pow_mul]
      rw [pow_succ, even]
      have step := decreases (4+2*n) (by omega)
      rw [Nat.add_assoc] at step
      linarith only [ih, step]
  rcases Nat.even_or_odd N with ⟨n, h⟩ | ⟨n, h⟩
  · simpa [h, two_mul] using pairs n
  · rw [h, sum_range_succ]
    have even : (-1 : ℝ)^(2*n) = 1 := by simp [pow_mul]
    rw [even]
    exact add_nonneg (pairs n) (by simpa using hA (4+2*n))

theorem hereditary_tail_nonnegative (F : Finset (Finset α)) (w : α → ℝ)
    (positive : ∀ v, 0 ≤ w v) (total : (∑ v, w v) ≤ 5)
    (hereditary : ∀ s ∈ F, ∀ v ∈ s, s.erase v ∈ F) (N : ℕ) :
    0 ≤ ∑ j ∈ range N, (-1 : ℝ)^j * mass F w (4+j) := by
  have pos (k : ℕ) : 0 ≤ mass F w k :=
    sum_nonneg fun s _ => prod_nonneg fun v _ => positive v
  apply alternating_tail_nonnegative _ pos _ N
  intro k hk
  have hi := extension_bound F w positive hereditary k
  have hk' : (5 : ℝ) ≤ k+1 := by exact_mod_cast (by omega : 5 ≤ k+1)
  linarith only [hi, mul_le_mul_of_nonneg_right hk' (pos (k+1)),
    mul_le_mul_of_nonneg_right total (pos k)]

/-- The signed polynomial of a finite set family, evaluated at the weights. -/
noncomputable def signed (F : Finset (Finset α)) (w : α → ℝ) : ℝ :=
  ∑ s ∈ F, (-1 : ℝ)^s.card * ∏ v ∈ s, w v

/-- Every finite hereditary family with total vertex weight at most five
has full signed polynomial at least its degree-three truncation. -/
theorem truncation_le_signed (F : Finset (Finset α)) (w : α → ℝ)
    (positive : ∀ v, 0 ≤ w v) (total : (∑ v, w v) ≤ 5)
    (hereditary : ∀ s ∈ F, ∀ v ∈ s, s.erase v ∈ F) :
    mass F w 0 - mass F w 1 + mass F w 2 - mass F w 3 ≤ signed F w := by
  classical
  let n := Fintype.card α
  have bound (s : Finset α) (_ : s ∈ F) : s.card ∈ range (4+n) := by
    have h : s.card ≤ n := Finset.card_le_univ s
    exact mem_range.mpr (by omega)
  have expand : (∑ k ∈ range (4+n), (-1 : ℝ)^k * mass F w k) = signed F w := by
    calc
      _ = ∑ k ∈ range (4+n), ∑ s ∈ F.filter (fun s => s.card = k),
            (-1 : ℝ)^s.card * ∏ v ∈ s, w v := by
        apply sum_congr rfl
        intro k _
        rw [mass, mul_sum]
        apply sum_congr rfl
        intro s hs
        rw [(mem_filter.mp hs).2]
      _ = _ := sum_fiberwise_of_maps_to bound _
  rw [← expand, sum_range_add]
  have head : (∑ k ∈ range 4, (-1 : ℝ)^k * mass F w k) =
      mass F w 0 - mass F w 1 + mass F w 2 - mass F w 3 := by
    simp only [sum_range_succ, sum_range_zero, pow_zero, one_mul, zero_add]
    ring
  rw [head]
  apply le_add_of_nonneg_right
  have fourth : (-1 : ℝ)^4 = 1 := by norm_num
  simpa only [pow_add, fourth, one_mul] using hereditary_tail_nonnegative F w positive total hereditary n

/-- The same truncation comparison in the usual powerset formula for the
independence polynomial, for any predicate closed under deleting one member. -/
theorem truncation_le_powerset_sum (V : Finset α) (I : Finset α → Prop) [DecidablePred I]
    (w : α → ℝ) (positive : ∀ v, 0 ≤ w v) (total : (∑ v, w v) ≤ 5)
    (hereditary : ∀ s, I s → ∀ v ∈ s, I (s.erase v)) :
    let F := V.powerset.filter I
    mass F w 0 - mass F w 1 + mass F w 2 - mass F w 3 ≤
      ∑ s ∈ V.powerset, if I s then ∏ v ∈ s, -w v else 0 := by
  dsimp only
  have closed : ∀ s ∈ V.powerset.filter I, ∀ v ∈ s, s.erase v ∈ V.powerset.filter I := by
    intro s hs v hv
    obtain ⟨sub, ok⟩ := mem_filter.mp hs
    exact mem_filter.mpr ⟨mem_powerset.mpr ((erase_subset v s).trans (mem_powerset.mp sub)),
      hereditary _ ok _ hv⟩
  simpa only [signed, sum_filter, prod_neg] using
    truncation_le_signed (V.powerset.filter I) w positive total closed

end ThirdOrderTail
