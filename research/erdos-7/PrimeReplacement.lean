import SharpRepair

/-! Restricting the allowed digits at a prime preserves the exponent bound
and all base holes, including those already covered by some old classes. -/

namespace PrimeReplacement

private def digits (q p : ℤ) : ℕ → ℤ → ℤ
  | 0, _ => 0
  | e+1, z => p * digits q p e (z / q) + z % q

private theorem reflect_prefix {q p : ℤ} (hq : 0 < q) (hqp : q ≤ p) (e : ℕ) :
    ∀ j ≤ e, ∀ x y : ℤ, digits q p e x ≡ digits q p e y [ZMOD p^j] →
      x ≡ y [ZMOD q^j] := by
  induction e with
  | zero =>
    intro j hj x y _
    have : j = 0 := by omega
    simp [this, Int.ModEq]
  | succ e ih =>
    intro j hj x y hab
    cases j with
    | zero => simp [Int.ModEq]
    | succ j =>
      rw [digits, digits, pow_succ'] at hab
      have low := hab.of_mul_right (p^j)
      rw [Int.modulus_mul_add_modEq_iff, Int.modEq_modulus_mul_add_iff] at low
      have digitEq : x % q = y % q := by
        have a := Int.emod_nonneg x hq.ne'
        have b := Int.emod_nonneg y hq.ne'
        have c := Int.emod_lt_of_pos x hq
        have d := Int.emod_lt_of_pos y hq
        simpa only [Int.ModEq, Int.emod_eq_of_lt a (by omega : x % q < p),
          Int.emod_eq_of_lt b (by omega : y % q < p)] using low
      rw [digitEq] at hab
      have rest := Int.ModEq.mul_left_cancel' (by omega : p ≠ 0)
        (hab.add_right_cancel' (y % q))
      have tail := ih j (by omega) (x / q) (y / q) rest
      have eqv := (tail.mul_left' (c := q)).add_left (y % q)
      rw [← digitEq, Int.emod_add_mul_ediv, digitEq, Int.emod_add_mul_ediv] at eqv
      simpa only [pow_succ'] using eqv

/-- Any finite extension using the prime `p` restricts to the same depth at
a smaller fresh prime `q`, for the original, arbitrary finite hole set. -/
theorem coversAt (M p q e : ℕ) (H : Finset ℕ) (hq : q.Prime) (hqp : q ≤ p)
    (hM : 0 < M) (cp : p.Coprime M) (cq : q.Coprime M) (a : ℕ → ℤ)
    (old : SharpRepair.CoversAt M p e H a) :
    ∃ b : ℕ → ℤ, SharpRepair.CoversAt M q e H b := by
  classical
  have bez : IsCoprime (M : ℤ) ((p : ℤ)^e) := by
    simpa only [← Nat.cast_pow, Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
      using cp.symm.pow_right e
  obtain ⟨u, v, huv⟩ := bez
  let enc := digits (q : ℤ) (p : ℤ) e
  let lift (z : ℤ) := z + u * M * (enc z - z)
  have base (z : ℤ) : z ≡ lift z [ZMOD (M : ℤ)] :=
    Int.modEq_iff_dvd.mpr ⟨u * (enc z - z), by dsimp [lift]; ring⟩
  have digit (z : ℤ) : enc z ≡ lift z [ZMOD (p : ℤ)^e] :=
    Int.modEq_iff_dvd.mpr ⟨v * (z - enc z), by
      dsimp [lift]; linear_combination (enc z - z) * huv⟩
  let modAt (s : ℕ) (L : Fin e × ↥M.divisors) := s^(L.1.val+1) * L.2.val
  have inj : Function.Injective (modAt q) := by
    rintro ⟨i, d⟩ ⟨j, t⟩ he
    change q^(i.val+1)*d.val = q^(j.val+1)*t.val at he
    have fact (x : ↥M.divisors) (n : ℕ) : (q^n*x.val).factorization q = n := by
      have hd := (Nat.mem_divisors.mp x.property).1
      exact OddLift.exponent_of_class _ _ _ hq (Nat.pos_of_dvd_of_pos hd hM) (cq.of_dvd_right hd)
    have hj := congrArg (fun n : ℕ => n.factorization q) he
    simp only [fact] at hj
    have ij : i = j := Fin.ext (by omega)
    subst j
    exact congrArg (Prod.mk i) (Subtype.ext (Nat.eq_of_mul_eq_mul_left (pow_pos hq.pos _) he))
  let P (L : Fin e × ↥M.divisors) (z : ℤ) := (modAt p L : ℤ) ∣ lift z - a (modAt p L)
  let residue (L : Fin e × ↥M.divisors) := if h : ∃ z, P L z then h.choose else 0
  let b := Function.extend (modAt q) residue (fun _ => 0)
  refine ⟨b, ?_⟩
  rintro z ⟨x, hx, hz⟩
  obtain ⟨j, hj, d, hd, hit⟩ := old (lift z) ⟨x, hx,
    Int.modEq_iff_dvd.mp ((Int.modEq_iff_dvd.mpr hz).trans (base z))⟩
  let L : Fin e × ↥M.divisors := (⟨j, hj⟩, ⟨d, hd⟩)
  have hhit : P L z := hit
  have nonempty : ∃ w, P L w := ⟨z, hhit⟩
  have chosen : P L (residue L) := by simpa only [residue, dif_pos nonempty] using nonempty.choose_spec
  have between := (Int.modEq_iff_dvd.mpr chosen).symm.trans (Int.modEq_iff_dvd.mpr hhit)
  change lift (residue L) ≡ lift z [ZMOD ((p^(j+1)*d : ℕ) : ℤ)] at between
  push_cast at between
  have hdvd : (d : ℤ) ∣ (M : ℤ) := by exact_mod_cast (Nat.mem_divisors.mp hd).1
  have hbase := ((base (residue L)).of_dvd hdvd).trans
    ((between.of_mul_left _).trans ((base z).of_dvd hdvd).symm)
  have hpow := pow_dvd_pow (p : ℤ) (by omega : j+1 ≤ e)
  have hprefix := ((digit (residue L)).of_dvd hpow).trans
    ((between.of_mul_right _).trans ((digit z).of_dvd hpow).symm)
  have hsmall := reflect_prefix (q := (q : ℤ)) (p := (p : ℤ))
    (by exact_mod_cast hq.pos) (by exact_mod_cast hqp)
    e (j+1) (by omega) (residue L) z hprefix
  have cop := (cq.of_dvd_right (Nat.mem_divisors.mp hd).1).pow_left (j+1)
  refine ⟨j, hj, d, hd, ?_⟩
  change (modAt q L : ℤ) ∣ z - b (modAt q L)
  rw [show b (modAt q L) = residue L from inj.extend_apply _ _ _]
  change ((q^(j+1)*d : ℕ) : ℤ) ∣ z - residue L
  push_cast
  apply Int.modEq_iff_dvd.mp
  exact (Int.modEq_and_modEq_iff_modEq_mul (by exact_mod_cast cop)).mp ⟨hsmall, hbase⟩

end PrimeReplacement
