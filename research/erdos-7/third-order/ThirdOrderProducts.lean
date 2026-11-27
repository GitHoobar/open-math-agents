import Mathlib

/-! Assign a finite set of prime coordinates to labeled slots, leaving any
coordinates unused. Each occupied coordinate contributes its own weight.
The fibers of the occupied slots form a family of disjoint nonempty supports. -/

namespace ThirdOrderProducts

open Finset
open scoped BigOperators

variable {C : Type*} [Fintype C] [DecidableEq C]

noncomputable def P (x : C → ℝ) (t : ℕ) : ℝ := ∏ c, (1 + t*x c)

noncomputable def weight {j : ℕ} (x : C → ℝ) (f : C → Option (Fin j)) : ℝ :=
  ∏ c, (f c).elim 1 (fun _ => x c)

private noncomputable def missing {j : ℕ} (v : Fin j) : Finset (C → Option (Fin j)) :=
  univ.filter fun f => ∀ c, f c ≠ some v

/-- Weighted ordered placements in which every slot receives a coordinate. -/
noncomputable def ordered (x : C → ℝ) (j : ℕ) : ℝ :=
  ∑ f ∈ univ.filter (fun f : C → Option (Fin j) => ∀ v, ∃ c, f c = some v), weight x f

private theorem missing_mass (x : C → ℝ) {j : ℕ} (T : Finset (Fin j)) :
    (∑ f ∈ T.inf missing, weight x f) = P x (j - T.card) := by
  classical
  let term (c : C) (o : Option (Fin j)) : ℝ := o.elim 1 (fun v => if v ∈ T then 0 else x c)
  have avoids (f : C → Option (Fin j)) : f ∈ T.inf missing ↔ ∀ v ∈ T, ∀ c, f c ≠ some v := by
    simp [missing, Finset.mem_inf]
  have evaluate (f : C → Option (Fin j)) :
      (if f ∈ T.inf missing then weight x f else 0) = ∏ c, term c (f c) := by
    by_cases H : f ∈ T.inf missing
    · rw [if_pos H, weight]
      apply prod_congr rfl
      intro c _
      cases h : f c with
      | none => rfl
      | some v =>
        have absent : v ∉ T := fun hv => (avoids f).mp H v hv c h
        simp [term, absent]
    · rw [if_neg H]
      rw [avoids] at H
      push Not at H
      obtain ⟨v, hv, c, h⟩ := H
      exact (prod_eq_zero (mem_univ c) (by simp [term, h, hv])).symm
  calc
    _ = ∑ f : C → Option (Fin j), if f ∈ T.inf missing then weight x f else 0 := by
      rw [← sum_filter]; simp
    _ = ∑ f : C → Option (Fin j), ∏ c, term c (f c) :=
      sum_congr rfl (fun f _ => evaluate f)
    _ = ∏ c, ∑ o, term c o := (Fintype.prod_sum term).symm
    _ = _ := by
      apply prod_congr rfl
      intro c _
      rw [Fintype.sum_option]
      change 1 + (∑ v : Fin j, if v ∈ T then 0 else x c) = _
      have eqn : (∑ v : Fin j, if v ∈ T then 0 else x c) = ∑ v ∈ Tᶜ, x c := by
        have flip (v : Fin j) : (if v ∈ T then 0 else x c) = (if v ∉ T then x c else 0) := by
          by_cases h : v ∈ T <;> simp [h]
        simp_rw [flip]
        rw [← sum_filter]
        congr 1
        ext v
        simp
      rw [eqn, sum_const, nsmul_eq_mul, card_compl, Fintype.card_fin]

/-- Inclusion–exclusion over the missing labeled slots, for every number of slots. -/
theorem ordered_formula (x : C → ℝ) (j : ℕ) :
    ordered x j = ∑ k ∈ range (j+1), j.choose k * ((-1 : ℝ)^k * P x (j-k)) := by
  classical
  have specified : (univ.filter (fun f : C → Option (Fin j) => ∀ v, ∃ c, f c = some v)) =
      (univ : Finset (Fin j)).inf (fun v => (missing v)ᶜ) := by
    ext f
    simp [Finset.mem_inf, missing]
  rw [ordered, specified, inclusion_exclusion_sum_inf_compl]
  simp_rw [missing_mass x, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [sum_powerset]
  simp only [card_univ, Fintype.card_fin]
  apply sum_congr rfl
  intro k _
  simpa [nsmul_eq_mul] using sum_powersetCard k (univ : Finset (Fin j))
    (fun r => (-1 : ℝ)^r * P x (j-r))

/-- In an unordered matching of size j, each of its j! orders is a slot placement. -/
noncomputable def normalized (x : C → ℝ) (j : ℕ) : ℝ := ordered x j / j.factorial

theorem cubic_identity (x : C → ℝ) :
    6 * (normalized x 1 - normalized x 2 + normalized x 3) =
      P x 3 - 6 * P x 2 + 15 * P x 1 - 10 := by
  have zero : P x 0 = 1 := by simp [P]
  simp only [normalized, ordered_formula]
  norm_num [sum_range_succ, Nat.choose, Nat.factorial, zero]
  ring

end ThirdOrderProducts
