import OddLift
import OddReduction

/-!
# Replacing a family of odd congruence classes by multiples of three

An arbitrary finite family of distinct moduli relatively prime to six can be
covered by a new family with distinct odd moduli all divisible by three. The
new family may cover more integers than the original. As a consequence, a
cover with moduli relatively prime to six, each occurring at most twice, would
give a solution of the odd covering systems problem. The construction adapts
the prime-power branches in Harrington, Sun and Wong, Theorem 3.2
(arXiv:2104.00602). The external divisibility result used in the final
corollary is a hypothesis, corresponding to Dai, Li, Li and Yi,
Theorem 1.1 (arXiv:2611.15110).
-/
namespace MultiplicityLift

/-- At level j the three children have digit 0 (continue), 1 (cover for free),
or 2 (repeat the original classes). A spare divisor s removes one residue
class modulo s from the continuing branch at each level. -/
theorem replace_family (B : Finset ℕ) (b : ℕ → ℕ)
    (valid : ∀ d ∈ B, 1 < d ∧ Odd d ∧ Nat.Coprime 3 d) :
    ∃ T : Finset ℕ, ∃ a : ℕ → ℤ,
      (∀ d ∈ T, 1 < d ∧ Odd d ∧ 3 ∣ d) ∧
      ((∀ d ∈ B, ¬ 5 ∣ d) → ∀ d ∈ T, ¬ 5 ∣ d) ∧
      ∀ z : ℤ, (∃ d ∈ B, (d : ℤ) ∣ z - b d) →
        ∃ d ∈ T, (d : ℤ) ∣ z - a d := by
  classical
  obtain ⟨s, hs, prime⟩ := Nat.exists_infinite_primes (B.sup id + 6)
  have hs3 : 3 < s := by omega
  have hcop : Nat.Coprime 3 s := (Nat.coprime_primes Nat.prime_three prime).mpr (by omega)
  have spare (d : ℕ) (hd : d ∈ B) : d ≠ s := by
    have hle : d ≤ B.sup id := Finset.le_sup (f := id) hd
    omega
  let D := insert 1 (insert s B)
  have labels (d : D) : 0 < d.val ∧ Odd d.val ∧ Nat.Coprime 3 d.val := by
    have hd := d.property
    change d.val ∈ insert 1 (insert s B) at hd
    rcases Finset.mem_insert.mp hd with h | hd
    · rw [h]
      decide
    rcases Finset.mem_insert.mp hd with h | hd
    · rw [h]
      exact ⟨prime.pos, prime.odd_of_ne_two (by omega), hcop⟩
    · exact ⟨by have := (valid _ hd).1; omega, (valid _ hd).2⟩
  let modulus (L : Fin s × D) := 3^(L.1.val + 1) * L.2.val
  have inject : Function.Injective modulus := by
    rintro ⟨i, d⟩ ⟨j, e⟩ eq
    change 3^(i.val+1) * d.val = 3^(j.val+1) * e.val at eq
    have ex := congrArg (fun m : ℕ => m.factorization 3) eq
    simp only [OddLift.exponent_of_class 3 _ _ Nat.prime_three
      (labels _).1 (labels _).2.2] at ex
    have ij : i = j := Fin.ext (by omega)
    subst j
    exact congrArg (Prod.mk i) (Subtype.ext (Nat.eq_of_mul_eq_mul_left (by positivity) eq))
  let digit (d : D) : ℕ := if d.val = 1 then 1 else if d.val = s then 0 else 2
  let target (j : Fin s) (d : D) : ℕ :=
    if d.val = 1 then 0 else if d.val = s then j.val else b d.val
  let residue (L : Fin s × D) : ℤ :=
    (Nat.chineseRemainder ((labels L.2).2.2.pow_left (L.1.val+1))
      (3^L.1.val * digit L.2) (target L.1 L.2)).val
  let a := Function.extend modulus residue (fun _ => 0)
  refine ⟨Finset.univ.image modulus, a, ?_, ?_, ?_⟩
  · intro m hm
    obtain ⟨⟨j, d⟩, _, rfl⟩ := Finset.mem_image.mp hm
    change 1 < 3^(j.val+1) * d.val ∧ Odd (3^(j.val+1) * d.val) ∧ _
    have dv : 3 ∣ 3^(j.val+1) * d.val :=
      dvd_mul_of_dvd_left (dvd_pow_self 3 (Nat.succ_ne_zero _)) _
    have le := Nat.le_of_dvd (Nat.mul_pos (pow_pos (by decide : 0 < 3) _) (labels d).1) dv
    exact ⟨by omega, (by decide : Odd (3 : ℕ)).pow.mul (labels d).2.1, dv⟩
  · intro old m hm
    obtain ⟨⟨j, d⟩, _, rfl⟩ := Finset.mem_image.mp hm
    apply Nat.prime_five.not_dvd_mul
    · exact fun h => (by decide : ¬ 5 ∣ 3) (Nat.prime_five.dvd_of_dvd_pow h)
    · have hd := d.property
      change d.val ∈ insert 1 (insert s B) at hd
      rcases Finset.mem_insert.mp hd with h | hd
      · rw [h]
        decide
      rcases Finset.mem_insert.mp hd with h | hd
      · rw [h, Nat.prime_dvd_prime_iff_eq Nat.prime_five prime]
        omega
      · exact old _ hd
  · rintro z ⟨d, hd, hz⟩
    have hit (j : Fin s) (l : D)
        (h₁ : (3 : ℤ)^j.val * (digit l : ℤ) ≡ z [ZMOD (3 : ℤ)^(j.val+1)])
        (h₂ : (target j l : ℤ) ≡ z [ZMOD (l.val : ℤ)]) :
        ∃ m ∈ Finset.univ.image modulus, (m : ℤ) ∣ z - a m := by
      refine ⟨modulus (j,l), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
      rw [show a (modulus (j,l)) = residue (j,l) from inject.extend_apply _ _ _]
      exact OddLift.crt_spot _ _ _ _ ((labels l).2.2.pow_left (j.val+1)) z
        (by push_cast; exact h₁) h₂
    have hpos : (0 : ℤ) < s := by exact_mod_cast prime.pos
    have h0 := Int.emod_nonneg z (ne_of_gt hpos)
    have hlt := Int.emod_lt_of_pos z hpos
    let i : Fin s := ⟨(z % s).toNat, by omega⟩
    have hi : (i.val : ℤ) = z % s := Int.toNat_of_nonneg h0
    rcases OddLift.first_digit 3 (by decide) z (i.val+1) with zero | ⟨j, hj, r, hr, first⟩
    · let l : D := ⟨s, by simp [D]⟩
      have hs1 : s ≠ 1 := by omega
      apply hit i l
      · simpa [digit, l, hs1] using zero.modEq_zero_int.symm
      · simpa [target, l, hs1, hi] using Int.mod_modEq z (s : ℤ)
    · let n : Fin s := ⟨j, by omega⟩
      by_cases h1 : r.val = 1
      · let l : D := ⟨1, by simp [D]⟩
        apply hit n l
        · simpa [digit, l, n, h1] using first
        · exact Int.modEq_one
      · have h2 : r.val = 2 := by omega
        let l : D := ⟨d, by simp [D, hd]⟩
        have hd1 := ne_of_gt (valid d hd).1
        apply hit n l
        · simpa [digit, l, n, hd1, spare d hd, h2] using first
        · simpa [target, l, hd1, spare d hd] using Int.modEq_iff_dvd.mpr hz

/-- The first copy of each modulus is kept; the second copy is replaced. -/
theorem lift_two_families (A B : Finset ℕ) (a b : ℕ → ℕ)
    (validA : ∀ d ∈ A, 1 < d ∧ Odd d ∧ Nat.Coprime 3 d)
    (validB : ∀ d ∈ B, 1 < d ∧ Odd d ∧ Nat.Coprime 3 d)
    (covers : ∀ z : ℤ, (∃ d ∈ A, (d : ℤ) ∣ z - a d) ∨
      ∃ d ∈ B, (d : ℤ) ∣ z - b d) :
    ∃ S : Finset ℕ, ∃ r : ℕ → ℤ, (∀ d ∈ S, 1 < d ∧ Odd d) ∧
      ((∀ d ∈ A ∪ B, ¬ 5 ∣ d) → ∀ d ∈ S, ¬ 5 ∣ d) ∧
      ∀ z : ℤ, ∃ d ∈ S, (d : ℤ) ∣ z - r d := by
  obtain ⟨T, t, validT, avoids, repair⟩ := replace_family B b validB
  have disjoint {d : ℕ} (hd : d ∈ T) : d ∉ A := fun ha =>
    (Nat.prime_three.coprime_iff_not_dvd.mp (validA d ha).2.2) (validT d hd).2.2
  refine ⟨A ∪ T, fun d => if d ∈ A then (a d : ℤ) else t d, ?_, ?_, ?_⟩
  · intro d hd
    rcases Finset.mem_union.mp hd with ha | ht
    · exact ⟨(validA d ha).1, (validA d ha).2.1⟩
    · exact ⟨(validT d ht).1, (validT d ht).2.1⟩
  · intro old d hd
    rcases Finset.mem_union.mp hd with ha | ht
    · exact old d (Finset.mem_union_left _ ha)
    · exact avoids (fun x hx => old x (Finset.mem_union_right _ hx)) d ht
  · intro z
    rcases covers z with ⟨d, hd, hz⟩ | inB
    · exact ⟨d, Finset.mem_union_left _ hd, by simpa only [if_pos hd] using hz⟩
    · obtain ⟨d, hd, hz⟩ := repair z inB
      exact ⟨d, Finset.mem_union_right _ hd, by simpa only [if_neg (disjoint hd)] using hz⟩

/-- The conclusion here is the precise existential proposition of Erdős problem 7. -/
theorem erdos_seven_of_two_families (A B : Finset ℕ) (a b : ℕ → ℕ)
    (validA : ∀ d ∈ A, 1 < d ∧ Odd d ∧ Nat.Coprime 3 d)
    (validB : ∀ d ∈ B, 1 < d ∧ Odd d ∧ Nat.Coprime 3 d)
    (covers : ∀ z : ℤ, (∃ d ∈ A, (d : ℤ) ∣ z - a d) ∨
      ∃ d ∈ B, (d : ℤ) ∣ z - b d) : type_of% @Erdos7.erdos_7 := by
  obtain ⟨S, r, valid, _, cover⟩ := lift_two_families A B a b validA validB covers
  exact OMA.R_Erdos7_erdos_7_R1.integer_cover S r valid cover

/-- Transfer the factor-five conclusion of Dai–Li–Li–Yi from odd distinct covers
to all covers by two internally distinct families with every modulus prime to six. -/
theorem two_families_force_factor_five
    (distinct_force_five : ∀ (S : Finset ℕ) (r : ℕ → ℤ),
      (∀ d ∈ S, 1 < d ∧ Odd d) →
      (∀ z : ℤ, ∃ d ∈ S, (d : ℤ) ∣ z - r d) → ∃ d ∈ S, 5 ∣ d)
    (A B : Finset ℕ) (a b : ℕ → ℕ)
    (validA : ∀ d ∈ A, 1 < d ∧ Odd d ∧ Nat.Coprime 3 d)
    (validB : ∀ d ∈ B, 1 < d ∧ Odd d ∧ Nat.Coprime 3 d)
    (covers : ∀ z : ℤ, (∃ d ∈ A, (d : ℤ) ∣ z - a d) ∨
      ∃ d ∈ B, (d : ℤ) ∣ z - b d) : ∃ d ∈ A ∪ B, 5 ∣ d := by
  obtain ⟨S, r, valid, transfer, cover⟩ := lift_two_families A B a b validA validB covers
  obtain ⟨d, hd, h5⟩ := distinct_force_five S r valid cover
  by_contra! old
  exact transfer old d hd h5

end MultiplicityLift

#print axioms MultiplicityLift.erdos_seven_of_two_families
#print axioms MultiplicityLift.two_families_force_factor_five
