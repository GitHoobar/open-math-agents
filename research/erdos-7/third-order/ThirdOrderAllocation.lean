import Mathlib

/-! Pairwise coprime ordered divisor tuples are equivalent to independent
choices at each prime. A coordinate is unused or chooses a slot and an
exponent from 1 through its valuation in the period. Slots may be units. -/

namespace ThirdOrderAllocation

abbrev Allocation (L j : ℕ) :=
  (p : ↥L.primeFactors) → Option (Fin j × Fin (L.factorization p.val))

abbrev Tuples (L j : ℕ) :=
  {t : Fin j → ↥L.divisors // Pairwise fun i k => (t i).val.Coprime (t k).val}

def exponent {j b : ℕ} (o : Option (Fin j × Fin b)) (i : Fin j) : ℕ :=
  match o with
  | none => 0
  | some (s, k) => if s = i then k.val + 1 else 0

private lemma bounded {j b : ℕ} (o : Option (Fin j × Fin b)) (i : Fin j) :
    exponent o i ≤ b := by
  rcases o with _ | ⟨s,k⟩
  · exact Nat.zero_le _
  · simp only [exponent]
    split <;> omega

private lemma exclusive {j b : ℕ} (o : Option (Fin j × Fin b)) {i k : Fin j}
    (hi : exponent o i ≠ 0) (hk : exponent o k ≠ 0) : i = k := by
  rcases o with _ | ⟨s,t⟩
  · exact (hi rfl).elim
  · simp [exponent] at hi hk
    exact hi.symm.trans hk

private lemma choice_ext {j b : ℕ} {o o' : Option (Fin j × Fin b)}
    (h : ∀ i, exponent o i = exponent o' i) : o = o' := by
  rcases o with _ | ⟨s,k⟩ <;> rcases o' with _ | ⟨t,l⟩
  · rfl
  · simpa [exponent] using h t
  · simpa [exponent] using h s
  · have st : t = s := by
      by_contra H
      simpa [exponent, H] using h s
    subst t
    have kl : k = l := Fin.ext (by simpa [exponent] using h s)
    subst l
    rfl

private lemma choose_coordinate {j b : ℕ} (f : Fin j → ℕ) (bound : ∀ i, f i ≤ b)
    (unique : ∀ i k, f i ≠ 0 → f k ≠ 0 → i = k) :
    ∃ o : Option (Fin j × Fin b), ∀ i, exponent o i = f i := by
  by_cases use : ∃ i, f i ≠ 0
  · obtain ⟨s, hs⟩ := use
    let a : Fin b := ⟨f s - 1, by have := bound s; omega⟩
    refine ⟨some (s, a), fun i => ?_⟩
    by_cases eq : s = i
    · subst i
      simp [exponent, a]
      omega
    · have zero : f i = 0 := by by_contra hi; exact eq (unique s i hs hi)
      simp [exponent, eq, zero]
  · exact ⟨none, fun i => by simpa [exponent] using (not_ne_iff.mp (fun hi => use ⟨i,hi⟩)).symm⟩

private noncomputable def row {L j : ℕ} (c : Allocation L j) (i : Fin j) : ℕ →₀ ℕ :=
  Finsupp.onFinset L.primeFactors
    (fun p => if h : p ∈ L.primeFactors then exponent (c ⟨p,h⟩) i else 0)
    (by intro p hp; by_contra h; simp [h] at hp)

private lemma row_le {L j : ℕ} (c : Allocation L j) (i : Fin j) :
    row c i ≤ L.factorization := by
  intro p
  simp only [row, Finsupp.onFinset_apply]
  split
  · exact bounded _ _
  · exact Nat.zero_le _

private noncomputable def divisor {L j : ℕ} (hL : L ≠ 0) (c : Allocation L j) (i : Fin j) : ↥L.divisors :=
  ⟨(row c i).prod (· ^ ·), Nat.mem_divisors.mpr ⟨Nat.prod_pow_dvd_of_le_factorization (row_le c i), hL⟩⟩

private lemma val_row {L j : ℕ} (hL : L ≠ 0) (c : Allocation L j) (i : Fin j) :
    (divisor hL c i).val.factorization = row c i :=
  Nat.factorization_prod_pow_eq_self_of_le_factorization (row_le c i)

private lemma valid {L j : ℕ} (hL : L ≠ 0) (c : Allocation L j) :
    Pairwise fun i k => (divisor hL c i).val.Coprime (divisor hL c k).val := by
  intro i k hik
  by_contra h
  obtain ⟨p, hp, hi, hk⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have dz (s : Fin j) := ne_zero_of_dvd_ne_zero hL (Nat.dvd_of_mem_divisors (divisor hL c s).property)
  have mem : p ∈ L.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hi.trans (Nat.dvd_of_mem_divisors (divisor hL c i).property), hL⟩
  have nz (s : Fin j) (hs : p ∣ (divisor hL c s).val) : exponent (c ⟨p,mem⟩) s ≠ 0 := by
    have hh := (hp.factorization_pos_of_dvd (dz s) hs).ne'
    simpa only [val_row, row, Finsupp.onFinset_apply, dif_pos mem] using hh
  exact hik (exclusive (c ⟨p,mem⟩) (nz i hi) (nz k hk))

/-- Build each slot's natural modulus by multiplying its assigned prime powers. -/
noncomputable def decode {L j : ℕ} (hL : L ≠ 0) (c : Allocation L j) : Tuples L j :=
  ⟨divisor hL c, valid hL c⟩

theorem decode_exponent {L j : ℕ} (hL : L ≠ 0) (c : Allocation L j) (p : ↥L.primeFactors)
    (i : Fin j) : ((decode hL c).val i).val.factorization p.val = exponent (c p) i := by
  change (divisor hL c i).val.factorization p.val = _
  simp only [val_row, row, Finsupp.onFinset_apply, dif_pos p.property]

/-- Every ordered tuple of pairwise coprime divisors (including unit slots) has
exactly one such allocation of prime powers, and conversely. -/
noncomputable def allocationEquiv (L j : ℕ) (hL : L ≠ 0) : Allocation L j ≃ Tuples L j :=
  Equiv.ofBijective (decode hL) (by
    constructor
    · intro c c' he
      funext p
      apply choice_ext
      intro i
      simpa only [decode_exponent] using congrArg (fun t : Tuples L j =>
        (t.val i).val.factorization p.val) he
    · intro t
      have dvd (i : Fin j) := Nat.dvd_of_mem_divisors (t.val i).property
      have nz (i : Fin j) := ne_zero_of_dvd_ne_zero hL (dvd i)
      have bound (i : Fin j) := (Nat.factorization_le_iff_dvd (nz i) hL).mpr (dvd i)
      have single (p : ↥L.primeFactors) := choose_coordinate
        (fun i => (t.val i).val.factorization p.val) (fun i => bound i p.val)
        (by
          intro i k hi hk
          by_contra ne
          exact (Nat.Prime.not_coprime_iff_dvd.mpr
            ⟨p.val, Nat.prime_of_mem_primeFactors p.property,
              Nat.dvd_of_factorization_pos hi, Nat.dvd_of_factorization_pos hk⟩) (t.property ne))
      choose c hc using single
      refine ⟨c, Subtype.ext (funext fun i => Subtype.ext ?_)⟩
      have fact : (divisor hL c i).val.factorization = (t.val i).val.factorization := by
        ext p
        by_cases hp : p ∈ L.primeFactors
        · exact (decode_exponent hL c ⟨p,hp⟩ i).trans (hc _ _)
        · have h0 : L.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
          have := bound i p
          simp only [val_row, row, Finsupp.onFinset_apply, dif_neg hp]
          omega
      have nd := ne_zero_of_dvd_ne_zero hL (Nat.dvd_of_mem_divisors (divisor hL c i).property)
      change (divisor hL c i).val = (t.val i).val
      rw [← Nat.prod_factorization_pow_eq_self nd, fact, Nat.prod_factorization_pow_eq_self (nz i)])

/-- An occupied coordinate contributes the reciprocal of its chosen prime power. -/
noncomputable def localWeight {j b : ℕ} (p : ℕ) : Option (Fin j × Fin b) → ℝ
  | none => 1
  | some (_,k) => (1 / (p : ℝ))^(k.val+1)

theorem divisor_product {L j : ℕ} (hL : L ≠ 0) (c : Allocation L j) (i : Fin j) :
    ((decode hL c).val i).val = ∏ p : ↥L.primeFactors, p.val^(exponent (c p) i) := by
  change (row c i).prod (· ^ ·) = _
  rw [Finsupp.prod_of_support_subset (row c i) (Finsupp.support_mono (row_le c i))
      (fun p a : ℕ => p ^ a) (fun p _ => pow_zero p)]
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  rintro ⟨p,hp⟩ _
  simp only [row, Finsupp.onFinset_apply, dif_pos (show p ∈ L.primeFactors from hp)]
  rfl

theorem tuple_weight {L j : ℕ} (hL : L ≠ 0) (c : Allocation L j) :
    (∏ i, (1 / ((((decode hL c).val i).val : ℕ) : ℝ))) =
    ∏ p : ↥L.primeFactors, localWeight p.val (c p) := by
  classical
  simp_rw [divisor_product hL c]
  push_cast
  simp only [one_div, ← Finset.prod_inv_distrib, ← inv_pow]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p _
  cases h : c p with
  | none => simp [exponent, localWeight]
  | some t =>
    obtain ⟨s,k⟩ := t
    simp only [localWeight, exponent, one_div]
    rw [Finset.prod_eq_single s]
    · simp
    · intro t _ hne
      simp [Ne.symm hne]
    · simp

noncomputable instance tupleFintype (L j : ℕ) : Fintype (Tuples L j) :=
  Fintype.ofFinite _

/-- Every tuple, allowing units, contributes its reciprocal product. The
sum factors prime by prime, with a choice among `j` slots at each exponent. -/
theorem all_tuple_mass (L j : ℕ) (hL : L ≠ 0) :
    (∑ t : Tuples L j, ∏ i, (1 / (((t.val i).val : ℕ) : ℝ))) =
    ∏ p : ↥L.primeFactors, (1 + j * ∑ k : Fin (L.factorization p.val),
      (1 / (p.val : ℝ))^(k.val+1)) := by
  classical
  let E := allocationEquiv L j hL
  calc
    _ = ∑ c : Allocation L j, ∏ i, 1 / ((((E c).val i).val : ℕ) : ℝ) :=
      (Equiv.sum_comp E _).symm
    _ = ∑ c : Allocation L j, ∏ p : ↥L.primeFactors, localWeight p.val (c p) :=
      Finset.sum_congr rfl (fun c _ => tuple_weight hL c)
    _ = ∏ p : ↥L.primeFactors, ∑ o : Option (Fin j × Fin (L.factorization p.val)),
        localWeight p.val o := (Fintype.prod_sum (fun (p : ↥L.primeFactors)
          (o : Option (Fin j × Fin (L.factorization p.val))) => localWeight p.val o)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p _
      rw [Fintype.sum_option, Fintype.sum_prod_type]
      simp [localWeight]

end ThirdOrderAllocation
