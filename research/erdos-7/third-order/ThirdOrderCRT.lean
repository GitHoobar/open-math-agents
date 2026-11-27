import ThirdOrderAvoidance

/-! Exact independence of a single congruence from joint avoidance of
any family of congruences with moduli coprime to its modulus. -/

namespace ThirdOrderCRT

open Finset

/-- The residue class with representative `a` on one complete period. -/
def event (L d a : ℕ) := (range L).filter (fun x => x ≡ a [MOD d])

theorem card_event (L d a : ℕ) (hd : 0 < d) (hdiv : d ∣ L) :
    (event L d a).card = L / d := by
  rw [event, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card L hd a]
  simp [Nat.mod_eq_zero_of_dvd hdiv]

private theorem counts (L d n a : ℕ) (hd : 0 < d) (hn : 0 < n)
    (divides : d*n ∣ L) (cop : d.Coprime n) (H : Finset ℕ) (hH : H ⊆ range n) :
    ((event L d a).filter fun x => x % n ∈ H).card * L =
    (event L d a).card * ((range L).filter fun x => x % n ∈ H).card := by
  have dd : d ∣ L := (dvd_mul_right d n).trans divides
  have nd : n ∣ L := (dvd_mul_left n d).trans divides
  have tally (s : Finset ℕ) (w : ℕ) (hf : ∀ b ∈ H, (s.filter (fun x => x % n = b)).card = w) :
      (s.filter (fun x => x % n ∈ H)).card = H.card * w := by
    rw [← sum_card_fiberwise_eq_card_filter s H (fun x => x % n)]
    exact sum_const_nat hf
  have all := tally (range L) (L/n) (by
    intro b hb
    have hb' := mem_range.mp (hH hb)
    simpa only [event, Nat.ModEq, Nat.mod_eq_of_lt hb'] using card_event L n b hn nd)
  have joint := tally (event L d a) (L/(d*n)) (by
    intro b hb
    let c := Nat.chineseRemainder cop a b
    have same : (event L d a).filter (fun x => x % n = b) = event L (d*n) c.val := by
      ext x
      have hb' := mem_range.mp (hH hb)
      have congr : x % n = b ↔ x ≡ b [MOD n] := by simp [Nat.ModEq, Nat.mod_eq_of_lt hb']
      simp only [event, mem_filter, congr]
      constructor
      · rintro ⟨⟨hx, ha⟩, hxb⟩
        exact ⟨hx, Nat.chineseRemainder_modEq_unique cop ha hxb⟩
      · rintro ⟨hx, hxc⟩
        obtain ⟨hxd, hxn⟩ := (Nat.modEq_and_modEq_iff_modEq_mul cop).mpr hxc
        exact ⟨⟨hx, hxd.trans c.property.1⟩, hxn.trans c.property.2⟩
    rw [same, card_event L (d*n) _ (Nat.mul_pos hd hn) divides])
  rw [joint, all, card_event L d a hd dd]
  obtain ⟨k, rfl⟩ := divides
  rw [Nat.mul_div_cancel_left k (Nat.mul_pos hd hn)]
  have ddiv : d*n*k/d = n*k := by rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ hd]
  have ndiv : d*n*k/n = d*k := by rw [Nat.mul_comm d n, Nat.mul_assoc, Nat.mul_div_cancel_left _ hn]
  rw [ddiv, ndiv]
  ring

/-- Exact integer-count independence in the shape used by
`ThirdOrderAvoidance.finite_avoidance_ge`. Only coprimality of the
distinguished modulus with each avoided modulus is required; the avoided
moduli may share arbitrary factors with one another. -/
theorem independent_avoidance (L d : ℕ) (r : ℕ → ℕ) (T : Finset ℕ)
    (hL : 0 < L) (hd : d ∣ L) (hT : ∀ m ∈ T, m ∣ L)
    (coprime : ∀ m ∈ T, d.Coprime m) :
    (ThirdOrderAvoidance.uncovered (range L) (fun m => event L m (r m)) T ∩ event L d (r d)).card *
        (range L).card =
      (range L ∩ event L d (r d)).card *
        (ThirdOrderAvoidance.uncovered (range L) (fun m => event L m (r m)) T).card := by
  let n := T.lcm id
  have nd : n ∣ L := Finset.lcm_dvd hT
  have hn := Nat.pos_of_dvd_of_pos nd hL
  have hdpos := Nat.pos_of_dvd_of_pos hd hL
  have cp : d.Coprime (∏ m ∈ T, m) := Nat.coprime_prod_right_iff.mpr coprime
  have cn : d.Coprime n := cp.of_dvd_right (Finset.lcm_dvd (fun m hm => Finset.dvd_prod_of_mem id hm))
  let H := (range n).filter fun y => ∀ m ∈ T, ¬ y ≡ r m [MOD m]
  have per (x : ℕ) : x % n ∈ H ↔ ∀ m ∈ T, ¬ x ≡ r m [MOD m] := by
    simp only [H, mem_filter, mem_range, Nat.mod_lt _ hn, true_and]
    have eqv (m : ℕ) (hm : m ∈ T) := (Nat.mod_modEq x n).of_dvd (Finset.dvd_lcm (f := id) hm)
    constructor
    · intro f m hm h
      exact f m hm ((eqv m hm).trans h)
    · intro f m hm h
      exact f m hm ((eqv m hm).symm.trans h)
  have as_filter : ThirdOrderAvoidance.uncovered (range L) (fun m => event L m (r m)) T =
      (range L).filter (fun x => x % n ∈ H) := by
    ext x
    simp only [ThirdOrderAvoidance.uncovered, event, mem_filter, per]
    tauto
  have joint : (range L).filter (fun x => x % n ∈ H) ∩ event L d (r d) =
      (event L d (r d)).filter (fun x => x % n ∈ H) := by
    ext x
    simp only [event, mem_filter, mem_inter]
    tauto
  have inside : event L d (r d) ⊆ range L := filter_subset _ _
  rw [as_filter, joint, card_range, inter_eq_right.mpr inside]
  exact counts L d n (r d) hdpos hn (cn.mul_dvd_of_dvd_of_dvd hd nd) cn H (filter_subset _ _)

end ThirdOrderCRT
