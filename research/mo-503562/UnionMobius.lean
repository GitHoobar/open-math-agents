import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Group.Int.Units

/-! The Möbius product for the determinant on a union-closed family. -/

open scoped BigOperators
open Finset MvPolynomial

namespace UnionMobius

attribute [local instance] Fintype.toLocallyFiniteOrder

section Incidence

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α] [DecidableLE α]
  [DecidableLT α]

private def entries (g : IncidenceAlgebra ℤ α) : Matrix α α ℤ := Matrix.of fun a b => g a b

private theorem inverse_matrices :
    entries (IncidenceAlgebra.zeta ℤ : IncidenceAlgebra ℤ α) *
      entries (IncidenceAlgebra.mu ℤ) = 1 := by
  classical
  ext a b : 1
  rw [Matrix.mul_apply]
  let z := (IncidenceAlgebra.zeta ℤ : IncidenceAlgebra ℤ α)
  let m := (IncidenceAlgebra.mu ℤ : IncidenceAlgebra ℤ α)
  change (∑ x, z a x * m x b) = _
  have restrict : (∑ x ∈ Icc a b, z a x * m x b) = ∑ x, z a x * m x b := by
    apply sum_subset (subset_univ _)
    intro x _ hx
    by_cases hax : a ≤ x
    · have hxb : ¬x ≤ b := fun h => hx (mem_Icc.mpr ⟨hax, h⟩)
      rw [IncidenceAlgebra.apply_eq_zero_of_not_le hxb m, mul_zero]
    · rw [IncidenceAlgebra.apply_eq_zero_of_not_le hax z, zero_mul]
  rw [← restrict, ← IncidenceAlgebra.mul_apply]
  have hzm : z * m = 1 := IncidenceAlgebra.zeta_mul_mu
  rw [hzm, IncidenceAlgebra.one_apply]
  exact Matrix.one_apply.symm

end Incidence

variable {σ : Type*} [DecidableEq σ]

noncomputable def mon (s : Finset σ) : MvPolynomial σ ℤ := ∏ k ∈ s, X k

/-- Each factor is the Möbius transform on the inclusion poset of the given
family, after taking out the monomial of its lower endpoint. -/
noncomputable def factor (F : Finset (Finset σ)) (a : F) : MvPolynomial σ ℤ :=
  ∑ b : F, (IncidenceAlgebra.mu ℤ a b : ℤ) * mon (b.val \ a.val)

theorem closed_product (F : Finset (Finset σ))
    (closed : ∀ a b : F, a.val ∪ b.val ∈ F) :
    (Matrix.of (fun a b : F => mon (a.val ∪ b.val))).det =
      (∏ a : F, mon a.val) * ∏ a : F, factor F a := by
  classical
  let z := entries (IncidenceAlgebra.zeta ℤ : IncidenceAlgebra ℤ F)
  let m := entries (IncidenceAlgebra.mu ℤ : IncidenceAlgebra ℤ F)
  let φ := Int.castRingHom (MvPolynomial σ ℤ)
  let Z := φ.mapMatrix z
  let U := φ.mapMatrix m
  let w (a : F) := mon a.val
  let d := U.mulVec w
  have inverse : z * m = 1 := inverse_matrices
  have inverse' : Z * U = 1 := by
    change φ.mapMatrix z * φ.mapMatrix m = 1
    rw [← map_mul, inverse, map_one]
  have rowsum : Z.mulVec d = w := by
    rw [show Z.mulVec d = (Z * U).mulVec w from Matrix.mulVec_mulVec _ _ _, inverse',
      Matrix.one_mulVec]
  have zentry (a b : F) : Z a b = if a.val ⊆ b.val then 1 else 0 := by
    change φ (if a ≤ b then 1 else 0) = _
    split_ifs with h k <;> simp_all
  have decomposition : Matrix.of (fun a b : F => mon (a.val ∪ b.val)) =
      Z * Matrix.diagonal d * Z.transpose := by
    ext a b : 1
    let j : F := ⟨a.val ∪ b.val, closed a b⟩
    change w j = _
    rw [← congrFun rowsum j, Matrix.mul_apply]
    change (∑ k, Z j k * d k) = _
    apply sum_congr rfl
    intro k _
    rw [Matrix.mul_diagonal, Matrix.transpose_apply, zentry, zentry, zentry]
    change (if a.val ∪ b.val ⊆ k.val then _ else _) * _ = _
    by_cases ha : a.val ⊆ k.val <;> by_cases hb : b.val ⊆ k.val <;>
      simp [union_subset_iff, ha, hb]
  have det_inv : z.det * m.det = 1 := by rw [← Matrix.det_mul, inverse, Matrix.det_one]
  have detsq : Z.det * Z.det = 1 := by
    change (φ.mapMatrix z).det * (φ.mapMatrix z).det = 1
    rw [← φ.map_det, ← map_mul]
    rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ det_inv) with h | h <;> simp [h]
  have diagonal_factor (a : F) : d a = mon a.val * factor F a := by
    change (∑ b : F, (IncidenceAlgebra.mu ℤ a b : ℤ) * mon b.val) = _
    rw [factor, mul_sum]
    apply sum_congr rfl
    intro b _
    by_cases h : a ≤ b
    · have hab : a.val ⊆ b.val := h
      have hm : mon b.val = mon a.val * mon (b.val \ a.val) := by
        unfold mon
        rw [← prod_union disjoint_sdiff, union_sdiff_self_eq_union, union_eq_right.mpr hab]
      rw [hm]
      ac_rfl
    · rw [IncidenceAlgebra.apply_eq_zero_of_not_le h]
      simp
  rw [decomposition, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  calc
    Z.det * (∏ a, d a) * Z.det = (Z.det * Z.det) * ∏ a, d a := by ac_rfl
    _ = _ := by simp [detsq, diagonal_factor, prod_mul_distrib]

end UnionMobius
