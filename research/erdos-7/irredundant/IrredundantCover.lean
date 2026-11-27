import Mathlib

/-! A dyadic construction completing an irredundant partial covering of an
odd period, while retaining a private integer for every class. -/

namespace IrredundantCover

inductive Label (β : Type*) (h : ℕ)
  | pure (i : Fin h)
  | mixed (k : Fin 4)
  | old (b : β)
  | repair (i : Fin h)

def prefixOn (i : ℕ) (z : ℤ) : Prop := (2 : ℤ)^i ∣ z+1

def hit {β : Type*} {N h : ℕ} (B : β → Fin N → Prop) (u : Fin h → Fin N) :
    Label β h → ℤ → Fin 5 → Fin N → Prop
  | .pure i, z, _, _ => prefixOn i.val z ∧ ¬ prefixOn (i.val+1) z
  | .mixed k, z, c, _ => prefixOn (k.val+1) z ∧ c.val = k.val
  | .old b, _, _, y => B b y
  | .repair i, z, c, y => prefixOn (i.val+1) z ∧ c.val = 4 ∧ y = u i

private lemma split_prefix (h : ℕ) (z : ℤ) :
    prefixOn h z ∨ ∃ i : Fin h, prefixOn i.val z ∧ ¬prefixOn (i.val+1) z := by
  induction h with
  | zero => simp [prefixOn]
  | succ h ih =>
    by_cases hl : prefixOn (h+1) z
    · exact Or.inl hl
    · rcases ih with prev | ⟨i, hit⟩
      · exact Or.inr ⟨Fin.last h, prev, hl⟩
      · exact Or.inr ⟨i.castSucc, hit⟩

private lemma prefix_down {k h : ℕ} {z : ℤ} (le : k ≤ h) (H : prefixOn h z) : prefixOn k z :=
  (pow_dvd_pow (2 : ℤ) le).trans H

private lemma at_power (i j : ℕ) : prefixOn i ((2 : ℤ)^j-1) ↔ i ≤ j := by
  simp only [prefixOn, sub_add_cancel]
  exact pow_dvd_pow_iff (by norm_num : (2 : ℤ) ≠ 0)
    (by norm_num [Int.isUnit_iff_abs_eq] : ¬ IsUnit (2 : ℤ))

private lemma at_minus_one (i : ℕ) : prefixOn i (-1) := by simp [prefixOn]

/-- Each pure binary layer is the single class `2^i-1` modulo `2^(i+1)`. -/
theorem pure_congruence (i : ℕ) (z : ℤ) :
    (prefixOn i z ∧ ¬prefixOn (i+1) z) ↔ z ≡ (2 : ℤ)^i-1 [ZMOD (2 : ℤ)^(i+1)] := by
  let t := (2 : ℤ)^i
  have pos : 0 < t := pow_pos (by decide) _
  rw [Int.modEq_iff_dvd, pow_succ]
  change (t ∣ z+1 ∧ ¬ t*2 ∣ z+1) ↔ t*2 ∣ t-1-z
  constructor
  · rintro ⟨⟨s, he⟩, no⟩
    have odd : ¬ (2 : ℤ) ∣ s := by rintro ⟨k,hk⟩; exact no ⟨k, by rw [he,hk]; ring⟩
    have hs : (2 : ℤ) ∣ 1-s := by omega
    obtain ⟨k,hk⟩ := hs
    exact ⟨k, by nlinarith [congrArg (fun x : ℤ => t*x) hk]⟩
  · rintro ⟨k,hk⟩
    refine ⟨⟨1-2*k, by nlinarith⟩, ?_⟩
    rintro ⟨s,hs⟩
    have eq : t*(1-2*k) = t*(2*s) := by nlinarith
    have := mul_left_cancel₀ pos.ne' eq
    omega

private theorem full_on_coordinates {β : Type*} {N h : ℕ} (hh : 4 ≤ h)
    (B : β → Fin N → Prop) (u : Fin h → Fin N)
    (base : ∀ y, (∃ b, B b y) ∨ ∃ i, y = u i)
    (z : ℤ) (c : Fin 5) (y : Fin N) : ∃ l, hit B u l z c y := by
  rcases split_prefix h z with full | ⟨i,hi⟩
  · by_cases small : c.val < 4
    · exact ⟨.mixed ⟨c.val,small⟩, prefix_down (by omega) full, rfl⟩
    · rcases base y with ⟨b,hb⟩ | ⟨i,hi⟩
      · exact ⟨.old b, hb⟩
      · exact ⟨.repair i, prefix_down (by omega) full, by omega, hi⟩
  · exact ⟨.pure i, hi⟩

private theorem private_on_coordinates {β : Type*} {N h : ℕ} (hh : 4 ≤ h)
    (B : β → Fin N → Prop) (u : Fin h → Fin N) (inj : Function.Injective u)
    (holes : ∀ b i, ¬B b (u i))
    (own : ∀ b, ∃ y, B b y ∧ ∀ a, B a y → a = b)
    (l : Label β h) : ∃ z c y, hit B u l z c y ∧ ∀ l', hit B u l' z c y → l' = l := by
  let last : Fin h := ⟨h-1, by omega⟩
  cases l with
  | pure i =>
    refine ⟨(2:ℤ)^i.val-1, (4 : Fin 5), u last, ⟨(at_power _ _).mpr le_rfl, ?_⟩, ?_⟩
    · simpa only [at_power] using Nat.not_succ_le_self i.val
    · intro l' hl
      cases l' with
      | pure j =>
        change prefixOn _ _ ∧ ¬prefixOn _ _ at hl
        simp only [at_power] at hl
        exact congrArg Label.pure (Fin.ext (by omega))
      | mixed k => have hk : (4 : Fin 5).val = k.val := hl.2; omega
      | old b => exact (holes b last hl).elim
      | repair j =>
        have eq := inj hl.2.2
        have hle := (at_power _ _).mp hl.1
        have hj : j.val = h-1 := congrArg Fin.val eq.symm
        omega
  | mixed k =>
    let c : Fin 5 := ⟨k.val, by omega⟩
    refine ⟨-1, c, u last, ⟨at_minus_one _,rfl⟩, ?_⟩
    intro l' hl
    cases l' with
    | pure j => exact (hl.2 (at_minus_one _)).elim
    | mixed j => exact congrArg Label.mixed (Fin.ext hl.2.symm)
    | old b => exact (holes b last hl).elim
    | repair j => have eq : k.val = 4 := hl.2.1; omega
  | old b =>
    obtain ⟨y,yes,unique⟩ := own b
    refine ⟨-1, (4 : Fin 5), y, yes, ?_⟩
    intro l' hl
    cases l' with
    | pure j => exact (hl.2 (at_minus_one _)).elim
    | mixed k => have hk : (4 : Fin 5).val = k.val := hl.2; omega
    | old b' => exact congrArg Label.old (unique b' hl)
    | repair i => exact (holes b i (hl.2.2 ▸ yes)).elim
  | repair i =>
    refine ⟨-1, (4 : Fin 5), u i, ⟨at_minus_one _, rfl, rfl⟩, ?_⟩
    intro l' hl
    cases l' with
    | pure j => exact (hl.2 (at_minus_one _)).elim
    | mixed k => have hk : (4 : Fin 5).val = k.val := hl.2; omega
    | old b => exact (holes b i hl).elim
    | repair j => exact congrArg Label.repair (inj hl.2.2).symm

def rem (n : ℕ) (hn : 0 < n) (z : ℤ) : Fin n :=
  ⟨(z % (n : ℤ)).toNat, (Int.toNat_lt (Int.emod_nonneg _ (by exact_mod_cast hn.ne'))).mpr
    (Int.emod_lt_of_pos z (by exact_mod_cast hn))⟩

private lemma rem_congr {n : ℕ} (hn : 0 < n) {z : ℤ} {a : Fin n}
    (hz : z ≡ (a.val : ℤ) [ZMOD (n : ℤ)]) : rem n hn z = a := by
  apply Fin.ext
  change (z % (n : ℤ)).toNat = _
  rw [hz.eq, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast a.isLt)]
  simp

private lemma crt (m n : ℕ) (cop : m.Coprime n) (a b : ℤ) :
    ∃ z : ℤ, z ≡ a [ZMOD (m : ℤ)] ∧ z ≡ b [ZMOD (n : ℤ)] := by
  have bez : IsCoprime (m : ℤ) (n : ℤ) := by simpa [Int.isCoprime_iff_nat_coprime] using cop
  obtain ⟨u,v,eq⟩ := bez
  refine ⟨a + u*m*(b-a), Int.modEq_iff_dvd.mpr ⟨u*(a-b), by ring⟩,
    Int.modEq_iff_dvd.mpr ⟨v*(b-a), ?_⟩⟩
  linear_combination (a-b)*eq

private lemma realize (h N : ℕ) (hn : 0 < N) (c2 : Nat.Coprime 2 N) (c5 : Nat.Coprime 5 N)
    (z : ℤ) (c : Fin 5) (y : Fin N) : ∃ w : ℤ, w ≡ z [ZMOD (2:ℤ)^h] ∧
      rem 5 (by decide) w = c ∧ rem N hn w = y := by
  obtain ⟨v,hv₂,hv₅⟩ := crt (2^h) 5 ((by decide : Nat.Coprime 2 5).pow_left h) z c.val
  obtain ⟨w,hw,hN⟩ := crt (2^h*5) N (Nat.coprime_mul_iff_left.mpr ⟨c2.pow_left h,c5⟩) v y.val
  push_cast at hw hv₂
  exact ⟨w, (hw.of_mul_right _).trans hv₂, rem_congr _ ((hw.of_mul_left _).trans hv₅), rem_congr hn hN⟩

private lemma hit_congr {β : Type*} {h N : ℕ} (hh : 4 ≤ h)
    (B : β → Fin N → Prop) (u : Fin h → Fin N) {z w : ℤ} (hw : w ≡ z [ZMOD (2 : ℤ)^h])
    (l : Label β h) (c : Fin 5) (y : Fin N) : hit B u l w c y ↔ hit B u l z c y := by
  have same (k : ℕ) (hk : k ≤ h) : prefixOn k w ↔ prefixOn k z := by
    have eqv := (hw.of_dvd (pow_dvd_pow (2:ℤ) hk)).add_right 1
    simp only [prefixOn, ← Int.modEq_zero_iff_dvd]
    exact ⟨fun h => eqv.symm.trans h, fun h => eqv.trans h⟩
  cases l with
  | pure i => simp only [hit, same i.val (by omega), same (i.val+1) (by omega)]
  | mixed k => simp only [hit, same (k.val+1) (by omega)]
  | old b => rfl
  | repair i => simp only [hit, same (i.val+1) (by omega)]

/-- Actual membership on the signed integers, using their residues in
the two odd coordinates. -/
def contains {β : Type*} {N h : ℕ} (hn : 0 < N) (B : β → Fin N → Prop)
    (u : Fin h → Fin N) (l : Label β h) (z : ℤ) :=
  hit B u l z (rem 5 (by decide) z) (rem N hn z)

/-- A partial base cover with private base witnesses, and an injective
enumeration of its holes, yields a full cover of the integers in which
every labeled class has a private integer witness. -/
theorem complete_irredundant {β : Type*} {N h : ℕ} (hh : 4 ≤ h) (hn : 0 < N)
    (c2 : Nat.Coprime 2 N) (c5 : Nat.Coprime 5 N)
    (B : β → Fin N → Prop) (u : Fin h → Fin N) (inj : Function.Injective u)
    (base : ∀ y, (∃ b, B b y) ∨ ∃ i, y = u i) (holes : ∀ b i, ¬B b (u i))
    (own : ∀ b, ∃ y, B b y ∧ ∀ a, B a y → a = b) :
    (∀ z : ℤ, ∃ l, contains hn B u l z) ∧
      ∀ l, ∃ w : ℤ, contains hn B u l w ∧ ∀ l', contains hn B u l' w → l' = l := by
  refine ⟨fun z => full_on_coordinates hh B u base z _ _, ?_⟩
  intro l
  obtain ⟨z,c,y,yes,unique⟩ := private_on_coordinates hh B u inj holes own l
  obtain ⟨w,hw,hc,hy⟩ := realize h N hn c2 c5 z c y
  have eqv (i : Label β h) : contains hn B u i w ↔ hit B u i z c y := by
    rw [contains,hc,hy]
    exact hit_congr hh B u hw i c y
  exact ⟨w,(eqv l).mpr yes, fun i hi => unique i ((eqv i).mp hi)⟩

open Finset

def period (Q : Finset ℕ) := 3 * ∏ q ∈ Q, q

abbrev primeHit (Q : Finset ℕ) (q : ↥Q) (y : Fin (period Q)) := 3 * q.val ∣ y.val

def missing (Q : Finset ℕ) := univ.filter (fun y : Fin (period Q) => ∀ q : ↥Q, ¬ primeHit Q q y)

def enumerate (Q : Finset ℕ) (i : Fin (missing Q).card) : Fin (period Q) :=
  ((missing Q).orderIsoOfFin rfl i).val

theorem period_pos (Q : Finset ℕ) (pr : ∀ q ∈ Q, Nat.Prime q) : 0 < period Q :=
  Nat.mul_pos (by decide) (Finset.prod_pos (fun q hq => (pr q hq).pos))

theorem missing_four (Q : Finset ℕ) (nonempty : Q.Nonempty) (pr : ∀ q ∈ Q, Nat.Prime q)
    (gt : ∀ q ∈ Q, 5 < q) : 4 ≤ (missing Q).card := by
  have high : 5 < period Q := by
    obtain ⟨q,hq⟩ := nonempty
    have pos := Finset.prod_pos (fun r hr => (pr r hr).pos)
    have bound := Nat.le_of_dvd pos (Finset.dvd_prod_of_mem id hq)
    change q ≤ ∏ p ∈ Q, p at bound
    have := gt q hq
    unfold period
    omega
  let f (k : Fin 4) : Fin (period Q) := ⟨k.val + 1 + k.val/2, by omega⟩
  have avoid (k : Fin 4) : f k ∈ missing Q := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, fun q h => ?_⟩
    have bad : 3 ∣ k.val + 1 + k.val/2 := (dvd_mul_right 3 q.val).trans h
    fin_cases k <;> norm_num at bad
  have inj : Function.Injective f := by
    intro k l eq
    have vals := congrArg Fin.val eq
    change k.val + 1 + k.val/2 = l.val + 1 + l.val/2 at vals
    exact Fin.ext (by omega)
  simpa only [card_univ, Fintype.card_fin] using
    (card_le_card_of_injOn (s := (univ : Finset (Fin 4))) f (fun k _ => avoid k) inj.injOn)

/-- The concrete old rows have moduli `3*q`, with `q` drawn from any
nonempty finite set of primes greater than five. Every integer is covered
and every row of the completed family has a private integer. -/
theorem prime_family (Q : Finset ℕ) (nonempty : Q.Nonempty) (pr : ∀ q ∈ Q, Nat.Prime q)
    (gt : ∀ q ∈ Q, 5 < q) :
    let member := contains (period_pos Q pr) (primeHit Q) (enumerate Q)
    (∀ z : ℤ, ∃ l, member l z) ∧ ∀ l, ∃ w : ℤ, member l w ∧ ∀ l', member l' w → l' = l := by
  have hn := period_pos Q pr
  have cop (t : ℕ) (p : Nat.Prime t) (small : t ≤ 5) (c : t.Coprime 3) : t.Coprime (period Q) := by
    apply Nat.coprime_mul_iff_right.mpr
    refine ⟨c, Nat.coprime_prod_right_iff.mpr (fun q hq => ?_)⟩
    exact (Nat.coprime_primes p (pr q hq)).mpr (by have := gt q hq; omega)
  apply complete_irredundant (missing_four Q nonempty pr gt) hn (cop 2 (by decide) (by decide) (by decide))
    (cop 5 (by decide) (by decide) (by decide)) (primeHit Q) (enumerate Q)
  · exact Subtype.val_injective.comp ((missing Q).orderIsoOfFin rfl).injective
  · intro y
    by_cases h : ∃ q : ↥Q, primeHit Q q y
    · exact Or.inl h
    · have hy : y ∈ missing Q := mem_filter.mpr ⟨mem_univ _, fun q hq => h ⟨q,hq⟩⟩
      exact Or.inr ⟨((missing Q).orderIsoOfFin rfl).symm ⟨y,hy⟩, by simp [enumerate]⟩
  · intro q i
    exact (mem_filter.mp (((missing Q).orderIsoOfFin rfl i).property)).2 q
  · intro q
    let y : Fin (period Q) := ⟨(3*q.val) % (period Q), Nat.mod_lt _ hn⟩
    have test (r : ↥Q) : primeHit Q r y ↔ 3*r.val ∣ 3*q.val := by
      have hd : 3*r.val ∣ period Q := Nat.mul_dvd_mul_left 3 (Finset.dvd_prod_of_mem id r.property)
      have eq := (Nat.mod_modEq (3*q.val) (period Q)).of_dvd hd
      change 3*r.val ∣ (3*q.val) % period Q ↔ _
      rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
      exact ⟨fun h => eq.symm.trans h, fun h => eq.trans h⟩
    refine ⟨y, (test q).mpr dvd_rfl, fun r hr => Subtype.ext ?_⟩
    apply (Nat.prime_dvd_prime_iff_eq (pr r r.property) (pr q q.property)).mp
    exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 3) ((test r).mp hr)

end IrredundantCover
