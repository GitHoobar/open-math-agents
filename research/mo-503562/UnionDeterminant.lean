import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The variable content of the determinant of a union matrix. -/

open scoped BigOperators
open MvPolynomial

namespace UnionDeterminant

variable {ι σ : Type*} [Fintype ι] [DecidableEq σ]

noncomputable def weight (s : Finset σ) : MvPolynomial σ ℤ :=
  ∏ k ∈ s, X k

noncomputable def unionMatrix (A : ι → Finset σ) : Matrix ι ι (MvPolynomial σ ℤ) :=
  Matrix.of fun i j => weight (A i ∪ A j)

noncomputable def quotientMatrix (A : ι → Finset σ) : Matrix ι ι (MvPolynomial σ ℤ) :=
  Matrix.of fun i j => weight (A j \ A i)

theorem factor_rows [DecidableEq ι] (A : ι → Finset σ) :
    (unionMatrix A).det = (∏ i, weight (A i)) * (quotientMatrix A).det := by
  have rows : unionMatrix A =
      Matrix.of (fun i j => weight (A i) * quotientMatrix A i j) := by
    ext i j : 1
    change weight (A i ∪ A j) = weight (A i) * weight (A j \ A i)
    unfold weight
    rw [← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union]
  rw [rows, Matrix.det_mul_column]

theorem constantCoeff_weight (s : Finset σ) :
    constantCoeff (weight s) = if s = ∅ then 1 else 0 := by
  classical
  by_cases he : s = ∅
  · simp [he, weight]
  · obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr he
    rw [if_neg he, weight, map_prod]
    exact Finset.prod_eq_zero hk (constantCoeff_X ℤ k)

theorem quotient_constant_one [DecidableEq ι] (A : ι → Finset σ) (distinct : Function.Injective A) :
    constantCoeff (quotientMatrix A).det = 1 := by
  classical
  let inc : Matrix ι ι ℤ := Matrix.of fun i j => if A j ⊆ A i then 1 else 0
  have incidence : constantCoeff.mapMatrix (quotientMatrix A) = inc := by
    ext i j : 1
    change constantCoeff (weight (A j \ A i)) = if A j ⊆ A i then 1 else 0
    simp only [constantCoeff_weight, Finset.sdiff_eq_empty_iff_subset]
  rw [RingHom.map_det, incidence, Matrix.det_apply']
  rw [Finset.sum_eq_single (1 : Equiv.Perm ι)]
  · simp [inc]
  · intro π _ hπ
    have hole : ∃ i, ¬ A i ⊆ A (π i) := by
      by_contra! hall
      have hle : ∀ i ∈ (Finset.univ : Finset ι), (A i).card ≤ (A (π i)).card :=
        fun i _ => Finset.card_le_card (hall i)
      have heq := (Finset.sum_eq_sum_iff_of_le hle).mp
        (Equiv.sum_comp π (fun i => (A i).card)).symm
      apply hπ
      ext i
      exact (distinct (Finset.eq_of_subset_of_card_le (hall i)
        (heq i (Finset.mem_univ i)).ge)).symm
    obtain ⟨i, hi⟩ := hole
    have zero : ∏ j, inc (π j) j = 0 := Finset.prod_eq_zero (Finset.mem_univ i)
      (by simp [inc, hi])
    rw [zero, mul_zero]
  · simp

theorem frequency_product [Fintype σ] (A : ι → Finset σ) :
    (∏ i, weight (A i)) = ∏ k, (X k : MvPolynomial σ ℤ) ^
      ((Finset.univ : Finset ι).filter (fun i => k ∈ A i)).card := by
  classical
  calc
    (∏ i, weight (A i)) = ∏ i, ∏ k : σ, if k ∈ A i then X k else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      simp [weight, Finset.prod_ite_mem]
    _ = ∏ k : σ, ∏ i, if k ∈ A i then X k else 1 := Finset.prod_comm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro k _
      simp [Finset.prod_ite]

/-- The quotient has constant term 1, so none of the variables divide it. -/
theorem quotient_has_no_variable_factor [DecidableEq ι] (A : ι → Finset σ)
    (distinct : Function.Injective A)
    (k : σ) : ¬ X k ∣ (quotientMatrix A).det := by
  rintro ⟨Q, hQ⟩
  have h := quotient_constant_one A distinct
  rw [hQ, map_mul, constantCoeff_X, zero_mul] at h
  exact zero_ne_one h

theorem union_determinant [Fintype σ] [DecidableEq ι] (A : ι → Finset σ)
    (distinct : Function.Injective A) :
    ∃ P : MvPolynomial σ ℤ,
      (unionMatrix A).det = P * ∏ k, X k ^
        ((Finset.univ : Finset ι).filter (fun i => k ∈ A i)).card ∧
      constantCoeff P = 1 ∧ ∀ k, ¬ X k ∣ P := by
  refine ⟨(quotientMatrix A).det, ?_, quotient_constant_one A distinct,
    quotient_has_no_variable_factor A distinct⟩
  rw [factor_rows, frequency_product, mul_comm]

end UnionDeterminant
