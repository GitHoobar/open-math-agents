import IrredundantCover
import IrredundantScore

/-! Arithmetic assembly of the irredundant coverings. Each labelled
condition is a single congruence for its displayed natural-number modulus. -/

namespace IrredundantMain

open Finset IrredundantCover

def modulus {Q : Finset ℕ} {h : ℕ} (N : ℕ) : Label (↥Q) h → ℕ
  | .pure i => 1 * 2^(i.val+1)
  | .mixed k => 5 * 2^(k.val+1)
  | .old q => 3 * q.val
  | .repair i => (5*N) * 2^(i.val+1)

private theorem rem_iff (n : ℕ) (hn : 0 < n) (x y : ℤ) :
    rem n hn x = rem n hn y ↔ x ≡ y [ZMOD (n : ℤ)] := by
  have hx : 0 ≤ x % (n : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
  have hy : 0 ≤ y % (n : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
  change _ ↔ x % (n : ℤ) = y % (n : ℤ)
  rw [Fin.ext_iff]
  change (x % (n : ℤ)).toNat = (y % (n : ℤ)).toNat ↔ _
  omega

private lemma prefix_iff (k : ℕ) (x : ℤ) :
    prefixOn k x ↔ x ≡ -1 [ZMOD (2 : ℤ)^k] := by
  rw [Int.modEq_iff_dvd]
  unfold prefixOn
  rw [show (-1 : ℤ)-x = -(x+1) by ring, dvd_neg]

private lemma align {a b c n : ℤ} (hb : b ≡ c [ZMOD n]) :
    a ≡ c [ZMOD n] ↔ a ≡ b [ZMOD n] :=
  ⟨fun hx => hx.trans hb.symm, fun hx => hx.trans hb⟩

private theorem combine (a b : ℕ) (c : a.Coprime b) (x w : ℤ) :
    ((x ≡ w [ZMOD (a : ℤ)]) ∧ x ≡ w [ZMOD (b : ℤ)]) ↔ x ≡ w [ZMOD ((a*b : ℕ) : ℤ)] := by
  push_cast
  exact Int.modEq_and_modEq_iff_modEq_mul (by simpa only [Int.natAbs_natCast] using c)

private lemma old_iff {N : ℕ} (hn : 0 < N) {d : ℕ} (hd : d ∣ N) (x : ℤ) :
    d ∣ (rem N hn x).val ↔ x ≡ 0 [ZMOD (d : ℤ)] := by
  have nn : 0 ≤ x % (N : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
  have eq : ((rem N hn x).val : ℤ) = x % (N : ℤ) := Int.toNat_of_nonneg nn
  have congr := (Int.mod_modEq x N).of_dvd (show (d : ℤ) ∣ (N : ℤ) by exact_mod_cast hd)
  rw [← eq] at congr
  rw [← Int.natCast_dvd_natCast, ← Int.modEq_zero_iff_dvd]
  exact ⟨fun e => congr.symm.trans e, fun e => congr.trans e⟩

private theorem small_coprime (Q : Finset ℕ) (hq : ∀ p ∈ Q, Nat.Prime p ∧ 5 < p)
    (t : ℕ) (p : t.Prime) (small : t ≤ 5) (c : t.Coprime 3) : t.Coprime (period Q) := by
  apply Nat.coprime_mul_iff_right.mpr
  refine ⟨c, Nat.coprime_prod_right_iff.mpr (fun q h => ?_)⟩
  exact (Nat.coprime_primes p (hq q h).1).mpr (by have := (hq q h).2; omega)

/-- At any member of a labelled class, membership throughout the integers
is exactly congruence to that integer modulo the displayed modulus. -/
theorem one_congruence (Q : Finset ℕ) (hq : ∀ p ∈ Q, Nat.Prime p ∧ 5 < p)
    (h : ℕ) (u : Fin h → Fin (period Q)) (l : Label (↥Q) h) (x w : ℤ) :
    let hn := period_pos Q (fun q h => (hq q h).1)
    let member := contains hn (primeHit Q) u
    member l w → (member l x ↔ x ≡ w [ZMOD (modulus (period Q) l : ℤ)]) := by
  let N := period Q
  let hn := period_pos Q (fun q h => (hq q h).1)
  change contains hn _ _ l w → (contains hn _ _ l x ↔ _)
  cases l with
  | pure i =>
    change (prefixOn _ _ ∧ _) → ((prefixOn _ _ ∧ _) ↔ x ≡ w [ZMOD ((1 * 2^(i.val+1) : ℕ) : ℤ)])
    simp only [one_mul, Nat.cast_pow, Nat.cast_ofNat, pure_congruence]
    exact align
  | mixed k =>
    change (prefixOn _ w ∧ _) → ((prefixOn _ x ∧ _) ↔ _)
    rintro ⟨wp,wc⟩
    have cc : (5 : ℕ).Coprime (2^(k.val+1)) := (by decide : Nat.Coprime 5 2).pow_right _
    simp only [modulus]
    rw [← combine _ _ cc x w]
    rw [prefix_iff, align ((prefix_iff _ w).mp wp)]
    rw [← rem_iff 5 (by decide), and_comm]
    apply and_congr_left'
    rw [Fin.ext_iff]
    exact ⟨fun e => e.trans wc.symm, fun e => e.trans wc⟩
  | old q =>
    have hd : 3*q.val ∣ period Q := Nat.mul_dvd_mul_left 3 (Finset.dvd_prod_of_mem id q.property)
    change (3*q.val ∣ (rem _ hn w).val) → ((3*q.val ∣ (rem _ hn x).val) ↔ _)
    simp only [old_iff hn hd]
    exact align
  | repair i =>
    change (prefixOn _ w ∧ _ ∧ _) → ((prefixOn _ x ∧ _ ∧ _) ↔ _)
    rintro ⟨wp,wc,wy⟩
    have c₅ : (5 : ℕ).Coprime N := small_coprime Q hq 5 (by decide) (by decide) (by decide)
    have c₂ : (2 : ℕ).Coprime N := small_coprime Q hq 2 (by decide) (by decide) (by decide)
    have cc : (5*N).Coprime (2^(i.val+1)) :=
      (Nat.coprime_mul_iff_left.mpr ⟨(by decide : Nat.Coprime 5 2), c₂.symm⟩).pow_right _
    change _ ↔ x ≡ w [ZMOD ((5*N*2^(i.val+1) : ℕ) : ℤ)]
    rw [← combine _ _ cc x w, ← combine _ _ c₅ x w]
    rw [prefix_iff, align ((prefix_iff _ w).mp wp)]
    rw [← rem_iff 5 (by decide), ← rem_iff _ hn, and_comm]
    apply and_congr_left'
    exact and_congr ⟨fun e => Fin.ext (e.trans wc.symm), fun e => (congrArg Fin.val e).trans wc⟩
      ⟨fun e => e.trans wy.symm, fun e => e.trans wy⟩


open IrredundantScore

private lemma layer_at (m h : ℕ) (i : Fin h) : m*2^(i.val+1) ∈ layer m h :=
  mem_image.mpr ⟨i.val, mem_range.mpr i.isLt, rfl⟩

private lemma old_at {Q : Finset ℕ} (q : ↥Q) : 3*q.val ∈ old Q :=
  mem_image.mpr ⟨q.val, q.property, rfl⟩

private theorem realizes {Q : Finset ℕ} {h N : ℕ} (l : Label (↥Q) h) :
    modulus N l ∈ moduli Q h N := by
  cases l with
  | pure i => exact mem_union_left _ (mem_union_left _ (mem_union_left _ (layer_at _ _ i)))
  | mixed i => exact mem_union_left _ (mem_union_left _ (mem_union_right _ (layer_at _ _ i)))
  | old q => exact mem_union_left _ (mem_union_right _ (old_at q))
  | repair i => exact mem_union_right _ (layer_at _ _ i)

private theorem labels {Q : Finset ℕ} {h N d : ℕ} (hd : d ∈ moduli Q h N) :
    ∃ l : Label (↥Q) h, modulus N l = d := by
  simp only [moduli, layer, old, mem_union, mem_image, mem_range] at hd
  rcases hd with (((⟨i,hi,rfl⟩ | ⟨k,hk,rfl⟩) | ⟨q,hq,rfl⟩) | ⟨i,hi,rfl⟩)
  · exact ⟨.pure ⟨i,hi⟩,rfl⟩
  · exact ⟨.mixed ⟨k,hk⟩,rfl⟩
  · exact ⟨.old ⟨q,hq⟩,rfl⟩
  · exact ⟨.repair ⟨i,hi⟩,rfl⟩

private theorem injective (Q : Finset ℕ) (h N : ℕ) (hp : ∀ p ∈ Q, Nat.Prime p ∧ 5 < p)
    (hN : 0 < N) (three : 3 ∣ N) :
    Function.Injective (modulus (Q := Q) (h := h) N) := by
  obtain ⟨ab,bc,cd⟩ := blocks_disjoint Q h N hp hN three
  have dis {a b : ℕ} {X Y : Finset ℕ} (h : Disjoint X Y) (ha : a ∈ X) (hb : b ∈ Y) : a ≠ b :=
    fun eq => disjoint_left.mp h (eq ▸ ha) hb
  have pm (i : Fin h) (k : Fin 4) := dis ab (layer_at 1 _ i) (layer_at 5 _ k)
  have po (i : Fin h) (q : ↥Q) := dis bc (mem_union_left _ (layer_at 1 _ i)) (old_at q)
  have mo (k : Fin 4) (q : ↥Q) := dis bc (mem_union_right _ (layer_at 5 _ k)) (old_at q)
  have pc (i j : Fin h) := dis cd (mem_union_left _ (mem_union_left _ (layer_at 1 _ i))) (layer_at (5*N) _ j)
  have mc (k : Fin 4) (j : Fin h) := dis cd (mem_union_left _ (mem_union_right _ (layer_at 5 _ k))) (layer_at (5*N) _ j)
  have oc (q : ↥Q) (j : Fin h) := dis cd (mem_union_right _ (old_at q)) (layer_at (5*N) _ j)
  intro l l' eq
  cases l <;> cases l' <;> simp only [modulus] at eq
  all_goals first
    | exact (pm _ _ eq).elim | exact (pm _ _ eq.symm).elim
    | exact (po _ _ eq).elim | exact (po _ _ eq.symm).elim
    | exact (pc _ _ eq).elim | exact (pc _ _ eq.symm).elim
    | exact (mo _ _ eq).elim | exact (mo _ _ eq.symm).elim
    | exact (mc _ _ eq).elim | exact (mc _ _ eq.symm).elim
    | exact (oc _ _ eq).elim | exact (oc _ _ eq.symm).elim
    | exact congrArg Label.pure (Fin.ext (layer_injective (by decide : 0<1) eq))
    | exact congrArg Label.mixed (Fin.ext (layer_injective (by decide : 0<5) eq))
    | exact congrArg Label.old (Subtype.ext (Nat.eq_of_mul_eq_mul_left (by decide : 0<3) eq))
    | exact congrArg Label.repair (Fin.ext (layer_injective (by positivity : 0<5*N) eq))


/-- The HKLT three-term expression. The empty subset cancels the leading
one. A singleton has positive sign, a pair negative sign, and a triple
positive sign. Every subset is unordered and counted once. -/
noncomputable def thirdScore (V : Finset ℕ) : ℝ := by
  classical
  exact 1 - ∑ s ∈ V.powerset,
    if s.card ≤ 3 ∧ (s : Set ℕ).Pairwise Nat.Coprime
    then ∏ d ∈ s, -(1/(d : ℝ)) else 0

private theorem score_of_rank_two (V : Finset ℕ) (positive : ∀ d ∈ V, 0 < d)
    (rank : ∀ S ⊆ V, ThirdOrderDeletion.Independent Nat.primeFactors S → S.card ≤ 2) :
    thirdScore V = hklt V := by
  classical
  unfold thirdScore hklt ThirdOrderDeletion.signedQ
  congr 1
  apply sum_congr rfl
  intro s hs
  have sub := mem_powerset.mp hs
  have compat : (s : Set ℕ).Pairwise Nat.Coprime ↔ ThirdOrderDeletion.Independent Nat.primeFactors s := by
    constructor
    · exact fun hc _ hm _ hn ne => (hc hm hn ne).disjoint_primeFactors
    · exact fun hi x hx y hy ne =>
          (Nat.disjoint_primeFactors (positive x (sub hx)).ne' (positive y (sub hy)).ne').mp (hi hx hy ne)
  have cond : (s.card ≤ 3 ∧ (s : Set ℕ).Pairwise Nat.Coprime) ↔ ThirdOrderDeletion.Independent Nat.primeFactors s :=
    ⟨fun both => compat.mp both.2, fun hi => ⟨(rank s sub hi).trans (by decide), compat.mpr hi⟩⟩
  simp only [cond, ThirdOrderDeletion.signedTerm]

private theorem modulus_gt_one (Q : Finset ℕ) (h N : ℕ) (hN : 0<N)
    (hp : ∀ q ∈ Q, Nat.Prime q ∧ 5 < q) (d : ℕ) (hd : d ∈ moduli Q h N) : 1 < d := by
  obtain ⟨l,rfl⟩ := labels hd
  have big (m i : ℕ) (hm : 0 < m) : 1 < m*2^(i+1) := by
    have hpow := pow_pos (by decide : 0 < (2:ℕ)) i
    rw [pow_succ]
    nlinarith
  cases l with
  | pure i => exact big 1 i.val (by decide)
  | mixed k => exact big 5 k.val (by decide)
  | old q => have := (hp q.val q.property).2; change 1 < 3*q.val; omega
  | repair i => exact big (5*N) i.val (by positivity)


/-- For every real threshold there exists a finite set of distinct moduli
greater than one and one residue class per modulus. They cover every signed
integer, each has a private signed integer, and the classical HKLT
coprime-triple expression is strictly below the threshold. -/
theorem unbounded_irredundant_full_covers (R : ℝ) :
    ∃ D : Finset ℕ, ∃ a : (↥D) → ℤ,
      (∀ d ∈ D, 1 < d) ∧
      (∀ z : ℤ, ∃ d : ↥D, z ≡ a d [ZMOD (d.val : ℤ)]) ∧
      (∀ d : ↥D, ∃ w : ℤ, w ≡ a d [ZMOD (d.val : ℤ)] ∧
        ∀ e : ↥D, w ≡ a e [ZMOD (e.val : ℤ)] → e = d) ∧
      thirdScore D < R := by
  classical
  obtain ⟨Q,ne,hp,small⟩ := unbounded_below R
  let N := period Q
  let h := (missing Q).card
  have pr := fun q (hq : q ∈ Q) => (hp q hq).1
  have gt := fun q (hq : q ∈ Q) => (hp q hq).2
  have hN : 0 < N := period_pos Q pr
  have three : 3 ∣ N := dvd_mul_right 3 _
  let D := moduli Q h N
  let L := Label (↥Q) h
  let mem := contains hN (primeHit Q) (enumerate Q)
  obtain ⟨full, privateWitness⟩ := prime_family Q ne pr gt
  choose center hit uniq using privateWitness
  let pick (d : ↥D) : L := (labels d.property).choose
  have val (d : ↥D) : modulus N (pick d) = d.val := (labels d.property).choose_spec
  let idx (l : L) : ↥D := ⟨modulus N l, realizes l⟩
  have inv (l : L) : pick (idx l) = l := injective Q h N hp hN three (val (idx l))
  have iffC (d : ↥D) (z : ℤ) : mem (pick d) z ↔ z ≡ center (pick d) [ZMOD (d.val : ℤ)] := by
    calc
      _ ↔ z ≡ center (pick d) [ZMOD (modulus N (pick d) : ℤ)] :=
        one_congruence Q hp h (enumerate Q) (pick d) z _ (hit (pick d))
      _ ↔ _ := by rw [val]
  have big := modulus_gt_one Q h N hN hp
  refine ⟨D, fun d => center (pick d), big, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨l,hl⟩ := full z
    refine ⟨idx l,(iffC _ _).mp ?_⟩
    simpa only [inv] using hl
  · intro d
    refine ⟨center (pick d), Int.ModEq.refl _, ?_⟩
    intro e he
    have eq := uniq (pick d) (pick e) ((iffC e _).mpr he)
    exact Subtype.ext ((val e).symm.trans ((congrArg (modulus N) eq).trans (val d)))
  · rw [score_of_rank_two D (fun d hd => Nat.lt_trans (by decide) (big d hd)) (no_triples Q h N hp hN three),
      concrete_score Q h N hp hN three]
    exact small h N (missing_four Q ne pr gt) hN

#print axioms unbounded_irredundant_full_covers

end IrredundantMain
