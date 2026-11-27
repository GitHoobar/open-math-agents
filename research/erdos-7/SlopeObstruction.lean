import Mathlib

/-!
# Necessity of the divisor threshold on separated holes

At depth `e`, count hole representatives together with all residues modulo
`p^e`. A class on level `j` has at most `p^(e-j)` lifts in the second
coordinate. On the first coordinate every mixed class meets at most one hole.
-/

namespace SlopeObstruction

open Finset

private def fiber (N q b : ℕ) := (range N).filter fun y => y % q = b % q

private theorem fiber_bound (q n b : ℕ) (hq : 0 < q) :
    (fiber (n * q) q b).card ≤ n := by
  apply le_trans ?_ (card_range n).le
  apply card_le_card_of_injOn (fun y => y / q)
  · intro y hy
    exact mem_range.mpr ((Nat.div_lt_iff_lt_mul hq).mpr
      (mem_range.mp (mem_filter.mp hy).1))
  · intro y hy z hz heq
    change y / q = z / q at heq
    have hmod := (mem_filter.mp hy).2.trans (mem_filter.mp hz).2.symm
    calc
      y = q * (y / q) + y % q := (Nat.div_add_mod y q).symm
      _ = q * (z / q) + z % q := by rw [heq, hmod]
      _ = z := Nat.div_add_mod z q

private def mixed (H : Finset ℕ) (N q d a b : ℕ) :=
  (H.filter (fun x => x % d = a % d)) ×ˢ fiber N q b

/-- On the CRT grid, covering forces a strict lower bound on the number of
mixed divisor labels. The level index `k` counts backwards from depth `e`. -/
theorem grid_bound (p e : ℕ) (hp : 2 ≤ p) (H D : Finset ℕ) (hne : H.Nonempty)
    (sep : ∀ d ∈ D, ∀ x ∈ H, ∀ y ∈ H, x % d = y % d → x = y)
    (a b : ℕ → ℕ → ℕ) (c : ℕ → ℕ)
    (covers : ∀ x ∈ H, ∀ y < p^e, ∃ k < e,
      y % p^(e-k) = c k % p^(e-k) ∨ ∃ d ∈ D,
        x % d = a k d % d ∧ y % p^(e-k) = b k d % p^(e-k)) :
    (p - 2) * H.card < D.card := by
  classical
  let layer (k : ℕ) := H ×ˢ fiber (p^e) (p^(e-k)) (c k) ∪
    D.biUnion fun d => mixed H (p^e) (p^(e-k)) d (a k d) (b k d)
  have sub : H ×ˢ range (p^e) ⊆ (range e).biUnion layer := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hy⟩ := mem_product.mp hxy
    obtain ⟨k, hk, hit⟩ := covers x hx y (mem_range.mp hy)
    apply mem_biUnion.mpr
    refine ⟨k, mem_range.mpr hk, ?_⟩
    rcases hit with pure | ⟨d, hd, hbase, hprime⟩
    · exact mem_union_left _ (mem_product.mpr ⟨hx, mem_filter.mpr ⟨hy, pure⟩⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨d, hd, mem_product.mpr
        ⟨mem_filter.mpr ⟨hx, hbase⟩, mem_filter.mpr ⟨hy, hprime⟩⟩⟩)
  have per (k : ℕ) (hk : k ∈ range e) : (layer k).card ≤ (H.card + D.card) * p^k := by
    have hk' := mem_range.mp hk
    have bound (v : ℕ) : (fiber (p^e) (p^(e-k)) v).card ≤ p^k := by
      have hpow : p^e = p^k * p^(e-k) := by rw [← pow_add, Nat.add_sub_of_le (by omega : k ≤ e)]
      rw [hpow]
      exact fiber_bound _ _ _ (pow_pos (by omega) _)
    have mcard (d : ℕ) (hd : d ∈ D) :
        (mixed H (p^e) (p^(e-k)) d (a k d) (b k d)).card ≤ p^k := by
      have mono : (H.filter (fun x => x % d = a k d % d)).card ≤ 1 := by
        apply card_le_one.mpr
        intro x hx y hy
        obtain ⟨hx, hax⟩ := mem_filter.mp hx
        obtain ⟨hy, hay⟩ := mem_filter.mp hy
        exact sep d hd x hx y hy (hax.trans hay.symm)
      rw [mixed, card_product]
      simpa only [one_mul] using Nat.mul_le_mul mono (bound (b k d))
    calc
      _ ≤ (H ×ˢ fiber (p^e) (p^(e-k)) (c k)).card +
          (D.biUnion fun d => mixed H (p^e) (p^(e-k)) d (a k d) (b k d)).card :=
        card_union_le _ _
      _ ≤ H.card * p^k + ∑ _d ∈ D, p^k := by
        rw [card_product]
        exact Nat.add_le_add (Nat.mul_le_mul_left _ (bound _))
          (card_biUnion_le.trans (sum_le_sum mcard))
      _ = _ := by simp [add_mul]
  have total : H.card * p^e ≤ (H.card + D.card) * ∑ k ∈ range e, p^k := by
    calc
      _ = (H ×ˢ range (p^e)).card := by simp
      _ ≤ _ := card_le_card sub
      _ ≤ _ := card_biUnion_le
      _ ≤ _ := sum_le_sum per
      _ = _ := (mul_sum _ _ _).symm
  by_contra! small
  have coeff : H.card + D.card ≤ H.card * (p - 1) := by
    have hp' : p - 1 = p - 2 + 1 := by omega
    rw [hp', Nat.mul_add, Nat.mul_one, Nat.mul_comm H.card (p-2)]
    omega
  have g := geom_sum_mul_add (p - 1) e
  rw [Nat.sub_add_cancel (by omega : 1 ≤ p)] at g
  have hh := card_pos.mpr hne
  have upper := total.trans (Nat.mul_le_mul_right _ coeff)
  rw [Nat.mul_assoc, Nat.mul_comm (p-1)] at upper
  nlinarith [congrArg (fun t : ℕ => H.card * t) g]

/-- If the progressions over a separated, nonempty hole set are covered by
one class per modulus of the form `p^j` or `p^j*d`, the divisor budget is
strictly larger than `(p-2)*H.card`. The exponent bound is arbitrary. -/
theorem necessary (M p e : ℕ) (hp : 2 ≤ p) (hc : M.Coprime p)
    (H D : Finset ℕ) (hne : H.Nonempty) (divisors : ∀ d ∈ D, d ∣ M)
    (sep : ∀ d ∈ D, ∀ x ∈ H, ∀ y ∈ H, x % d = y % d → x = y)
    (c : ℕ → ℕ) (r : ℕ → ℕ → ℕ)
    (covers : ∀ z : ℕ, (∃ x ∈ H, z ≡ x [MOD M]) → ∃ j < e,
      z ≡ c j [MOD p^(j+1)] ∨ ∃ d ∈ D, z ≡ r j d [MOD p^(j+1) * d]) :
    (p - 2) * H.card < D.card := by
  apply grid_bound p e hp H D hne sep (fun k => r (e-k-1)) (fun k => r (e-k-1))
    (fun k => c (e-k-1))
  intro x hx y _
  obtain ⟨z, hzM, hzy⟩ := Nat.chineseRemainder (hc.pow_right e) x y
  obtain ⟨j, hj, hcover⟩ := covers z ⟨x, hx, hzM⟩
  let k := e - j - 1
  have hlevel : e - k = j + 1 := by dsimp [k]; omega
  have hindex : e - k - 1 = j := by omega
  have hprime := (hzy.of_dvd (pow_dvd_pow p (by omega : j + 1 ≤ e))).symm
  refine ⟨k, by dsimp [k]; omega, ?_⟩
  rw [hindex, hlevel]
  rcases hcover with hit | ⟨d, hd, hit⟩
  · exact Or.inl (hprime.trans hit)
  · exact Or.inr ⟨d, hd, (hzM.of_dvd (divisors d hd)).symm.trans (hit.of_mul_left _),
      hprime.trans (hit.of_mul_right _)⟩

end SlopeObstruction
