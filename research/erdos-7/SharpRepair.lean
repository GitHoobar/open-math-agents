import OddLift
import SlopeObstruction

/-!
# Exact repair criterion for separated holes

An extension with exponent bound `e` may use one integer residue at each
numeric modulus `p^j*d`, for `1 ≤ j ≤ e` and `d ∣ M`. Any unused modulus
may receive an arbitrary residue without removing any covered integer.
-/

namespace SharpRepair

/-- The extension covers every integer lying above one of the listed holes. -/
def CoversAt (M p e : ℕ) (H : Finset ℕ) (a : ℕ → ℤ) : Prop :=
  ∀ z : ℤ, (∃ x ∈ H, (M : ℤ) ∣ z - (x : ℤ)) →
    ∃ j < e, ∃ d ∈ M.divisors, ((p^(j+1) * d : ℕ) : ℤ) ∣ z - a (p^(j+1) * d)

private def representative (q : ℕ) (a : ℤ) : ℕ := (a % (q : ℤ)).toNat

private lemma nat_hit (q z : ℕ) (a : ℤ) (hq : 0 < q) (hit : (q : ℤ) ∣ (z : ℤ) - a) :
    z ≡ representative q a [MOD q] := by
  apply Int.natCast_modEq_iff.mp
  change (z : ℤ) % q = (((a % (q : ℤ)).toNat : ℕ) : ℤ) % q
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hq.ne')), Int.emod_emod]
  exact (Int.modEq_iff_dvd.mpr hit).symm

/-- The constructive direction uses at most one level per hole and does not
require the holes to be separated. -/
theorem covers_at_card (M p : ℕ) (H : Finset ℕ) (prime : p.Prime) (hp : 3 ≤ p)
    (oddM : Odd M) (cop : p.Coprime M) (budget : (p-2)*H.card < (M.divisors.erase 1).card) :
    ∃ a, CoversAt M p H.card H a := by
  let iso := H.orderIsoOfFin (k := H.card) rfl
  let u : Fin H.card → ℕ := fun i => (iso i).val
  obtain ⟨S, a, hs, cover⟩ :=
    OddLift.repair_supported M p H.card u prime hp oddM cop budget
  refine ⟨a, ?_⟩
  rintro z ⟨x, hx, hz⟩
  have hu : u (iso.symm ⟨x, hx⟩) = x := by simp [u]
  obtain ⟨m, hm, hit⟩ := cover z ⟨iso.symm ⟨x, hx⟩, by simpa only [hu] using hz⟩
  obtain ⟨j, hj, d, hd, rfl⟩ := hs m hm
  exact ⟨j, hj, d, hd, hit⟩

/-- On nonempty separated holes, some finite prime-power extension exists
exactly when the number of nontrivial divisor labels exceeds `(p-2)*|H|`. -/
theorem exists_iff (M p : ℕ) (H : Finset ℕ) (prime : p.Prime) (hp : 3 ≤ p)
    (oddM : Odd M) (cop : p.Coprime M) (hne : H.Nonempty)
    (sep : ∀ d ∈ M.divisors.erase 1, ∀ x ∈ H, ∀ y ∈ H, x % d = y % d → x = y) :
    (∃ (e : ℕ) (a : ℕ → ℤ), CoversAt M p e H a) ↔
      (p-2)*H.card < (M.divisors.erase 1).card := by
  constructor
  · rintro ⟨e, a, cover⟩
    let b (q : ℕ) := representative q (a q)
    apply SlopeObstruction.necessary M p e (by omega) cop.symm H (M.divisors.erase 1)
      hne (fun d hd => (Nat.mem_divisors.mp (Finset.mem_of_mem_erase hd)).1)
      sep (fun j => b (p^(j+1))) (fun j d => b (p^(j+1)*d))
    rintro z ⟨x, hx, hz⟩
    obtain ⟨j, hj, d, hd, hit⟩ := cover z ⟨x, hx,
      Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr hz).symm⟩
    refine ⟨j, hj, ?_⟩
    by_cases hd1 : d = 1
    · subst d
      simp only [mul_one] at hit
      exact Or.inl (nat_hit _ _ _ (pow_pos prime.pos _) hit)
    · have hdiv := Nat.mem_divisors.mp hd
      have pos := Nat.pos_of_dvd_of_pos hdiv.1 (Nat.pos_of_ne_zero hdiv.2)
      exact Or.inr ⟨d, Finset.mem_erase.mpr ⟨hd1, hd⟩,
        nat_hit _ _ _ (Nat.mul_pos (pow_pos prime.pos _) pos) hit⟩
  · intro budget
    exact ⟨H.card, covers_at_card M p H prime hp oddM cop budget⟩

end SharpRepair
