import ThirdOrderBounds
import ThirdOrderTail
import ThirdOrderDeletion
import ThirdOrderAvoidance
import ThirdOrderCRT

/-!
# The third-order bound for a finite event system

The inputs particular to a divisor model are the three finite weighted
partition identities in `Normalized`, the half-cube bounds for its coordinate
weights, and the integer-count independence of events with disjoint supports.
-/

namespace ThirdOrderMain

open Finset ThirdOrderBounds ThirdOrderDeletion ThirdOrderAvoidance

variable {E C Ω : Type*} [DecidableEq E] [Fintype E] [DecidableEq C] [DecidableEq Ω]

noncomputable def families (support : E → Finset C) (V : Finset E) : Finset (Finset E) := by
  classical
  exact V.powerset.filter (Independent support)

def weightsOn (order : List C) (σ : C → ℝ) (T : Finset C) : List ℝ :=
  (order.filter fun i => i ∈ T).map σ

private theorem weights_all (order : List C) (σ : C → ℝ) :
    weightsOn order σ order.toFinset = order.map σ := by
  unfold weightsOn
  rw [List.filter_eq_self.mpr (fun x hx => by simpa using hx)]

/-- Weighted unordered coprime tuples of sizes one, two and three. -/
structure Normalized (support : E → Finset C) (w : E → ℝ) (order : List C) (σ : C → ℝ) : Prop where
  levels : ∀ T ⊆ order.toFinset,
    let F := families support (complete univ support T)
    let xs := weightsOn order σ T
    ThirdOrderTail.mass F w 1 = P 1 xs - 1 ∧
    ThirdOrderTail.mass F w 2 = (P 2 xs - 2 * P 1 xs + 1) / 2 ∧
    ThirdOrderTail.mass F w 3 = (P 3 xs - 3 * P 2 xs + 3 * P 1 xs - 1) / 6

omit [Fintype E] [DecidableEq C] in
private theorem zero_level (support : E → Finset C) (w : E → ℝ) (V : Finset E) :
    ThirdOrderTail.mass (families support V) w 0 = 1 := by
  classical
  have h : ThirdOrderTail.level (families support V) 0 = {∅} := by
    ext s
    by_cases hs : s = ∅ <;> simp [ThirdOrderTail.level, families, Independent, hs]
  simp [ThirdOrderTail.mass, h]

omit [DecidableEq E] [Fintype E] [DecidableEq C] in
private theorem one_level (support : E → Finset C) (w : E → ℝ) (V : Finset E) :
    ThirdOrderTail.mass (families support V) w 1 = ∑ x ∈ V, w x := by
  classical
  have h : ThirdOrderTail.level (families support V) 1 = V.powersetCard 1 := by
    ext s
    simp only [ThirdOrderTail.level, families, mem_filter, mem_powerset, mem_powersetCard]
    constructor
    · rintro ⟨⟨hsub, _⟩, hc⟩
      exact ⟨hsub, hc⟩
    · rintro ⟨hsub, hc⟩
      obtain ⟨x, rfl⟩ := card_eq_one.mp hc
      exact ⟨⟨hsub, by simp [Independent]⟩, hc⟩
  simp [ThirdOrderTail.mass, h, powersetCard_one]

/-- For every indexed residue/event selection satisfying the displayed finite
identities, the covered proportion is at most the cubic coprime expression.
No hypothesis bounds the number of coordinates. -/
theorem coverage_le (space : Finset Ω) (hspace : space.Nonempty) (event : E → Finset Ω)
    (support : E → Finset C) (order : List C) (σ : C → ℝ)
    (hwithin : ∀ v, support v ⊆ order.toFinset) (hne : ∀ v, (support v).Nonempty)
    (box : InCube (order.map σ))
    (normal : Normalized support (fun v => (space ∩ event v).card / (space.card : ℝ)) order σ)
    (indep : ∀ S v, v ∈ S →
      (uncovered space event (far support S v) ∩ event v).card * space.card =
        (space ∩ event v).card * (uncovered space event (far support S v)).card) :
    1 - (uncovered space event univ).card / (space.card : ℝ) ≤ B (order.map σ) := by
  classical
  let w (v : E) : ℝ := (space ∩ event v).card / (space.card : ℝ)
  have hw (v : E) : 0 ≤ w v := by dsimp [w]; positivity
  by_cases trivialBound : 1 ≤ B (order.map σ)
  · have h : 0 ≤ (uncovered space event (univ : Finset E)).card / (space.card : ℝ) := by positivity
    linarith
  have active : B (order.map σ) < 1 := lt_of_not_ge trivialBound
  have allEvents : complete univ support order.toFinset = univ := by
    ext x
    simp [complete, hwithin]
  have first := (normal.levels order.toFinset (fun _ h => h)).1
  change ThirdOrderTail.mass (families support (complete univ support order.toFinset)) w 1 =
    P 1 (weightsOn order σ order.toFinset) - 1 at first
  rw [allEvents, weights_all, one_level] at first
  have total : (∑ v, w v) ≤ 5 := by
    linarith only [first, mass_le_five_B (order.map σ) box, active]
  have bounds (T : Finset C) (hT : T ⊆ order.toFinset) :
      1 - B (weightsOn order σ T) ≤ signedQ support w (complete univ support T) := by
    let V := complete univ support T
    obtain ⟨h1, h2, h3⟩ := normal.levels T hT
    have tail := ThirdOrderTail.truncation_le_powerset_sum V (Independent support) w hw total
      (fun s hs v _ => hs.mono (Finset.erase_subset v s))
    change ThirdOrderTail.mass (families support V) w 0 -
      ThirdOrderTail.mass (families support V) w 1 + ThirdOrderTail.mass (families support V) w 2 -
      ThirdOrderTail.mass (families support V) w 3 ≤ signedQ support w V at tail
    rw [zero_level, h1, h2, h3] at tail
    unfold B
    linarith only [tail]
  have positive : ∀ T ⊆ order.toFinset, 0 < signedQ support w (complete univ support T) := by
    intro T hT
    have sub : (weightsOn order σ T).Sublist (order.map σ) := List.Sublist.map σ List.filter_sublist
    have mono := sublist_monotone sub box
    linarith only [bounds T hT, mono, active]
  have Qpos := signedQ_positive_induced (univ : Finset E) support w (fun v _ => hne v)
    (fun v _ => hw v) order.toFinset positive
  rw [allEvents] at Qpos
  have avoidance := finite_avoidance_ge space hspace event (signedQ support w) (far support)
    (fun S => Qpos S (subset_univ S)) (signedQ_empty support w)
    (fun S v _ => far_subset_erase support S v (hne v))
    (fun _ v hv => signedQ_deletion support w hv (hne v)) indep univ
  have full := bounds order.toFinset (fun _ h => h)
  rw [weights_all, allEvents] at full
  linarith only [avoidance, full]

/-- The nontrivial positive divisors of a period. -/
abbrev Divisor (L : ℕ) := ↥(L.divisors.erase 1)

/-- The prime-power tower weight, satisfying σ(p,a+1) = (1+σ(p,a))/p. -/
noncomputable def tower (p : ℕ) : ℕ → ℝ
  | 0 => 0
  | a+1 => (1 + tower p a) / p

theorem tower_eq_sum (p a : ℕ) :
    tower p a = ∑ j ∈ range a, (1 / (p : ℝ))^(j+1) := by
  induction a with
  | zero => simp [tower]
  | succ a ih =>
    rw [tower, ih, sum_range_succ']
    simp only [Nat.zero_add, pow_one, div_eq_mul_inv, add_mul, sum_mul, one_mul, ← pow_succ]
    ring

private theorem tower_box (p a : ℕ) (hp : 3 ≤ p) : 0 ≤ tower p a ∧ tower p a ≤ 1/2 := by
  have ppos : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have plarge : (3 : ℝ) ≤ p := by exact_mod_cast hp
  induction a with
  | zero => norm_num [tower]
  | succ a ih =>
    rw [tower]
    exact ⟨div_nonneg (by linarith only [ih.1]) ppos.le,
      (div_le_iff₀ ppos).mpr (by linarith only [ih.2, plarge])⟩

/-- Actual residue classes, arbitrary odd period and arbitrary exponents.
The remaining premise consists only of the three stated finite tuple identities
for the reciprocal weights. In particular CRT independence is proved. -/
theorem odd_divisor_coverage (L : ℕ) (hL : 0 < L) (oddL : Odd L) (r : ℕ → ℕ)
    (normal : Normalized (fun d : Divisor L => d.val.primeFactors)
      (fun d => 1 / (d.val : ℝ)) L.primeFactors.toList (fun p => tower p (L.factorization p))) :
    1 - (uncovered (range L) (fun d : Divisor L => ThirdOrderCRT.event L d.val (r d.val))
      univ).card / (L : ℝ) ≤ B (L.primeFactors.toList.map fun p => tower p (L.factorization p)) := by
  classical
  let event' (d : Divisor L) := ThirdOrderCRT.event L d.val (r d.val)
  let supp (d : Divisor L) := d.val.primeFactors
  have divides (d : Divisor L) : d.val ∣ L :=
    (Nat.mem_divisors.mp (mem_erase.mp d.property).2).1
  have dpos (d : Divisor L) : 0 < d.val := Nat.pos_of_dvd_of_pos (divides d) hL
  have hwithin (d : Divisor L) : supp d ⊆ L.primeFactors.toList.toFinset := by
    simpa [supp] using Nat.primeFactors_mono (divides d) hL.ne'
  have hne (d : Divisor L) : (supp d).Nonempty := by
    apply Nat.nonempty_primeFactors.mpr
    have distinct := (mem_erase.mp d.property).1
    have pos := dpos d
    omega
  have box : InCube (L.primeFactors.toList.map fun p => tower p (L.factorization p)) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    obtain ⟨prime, dividesL, _⟩ := Nat.mem_primeFactors.mp (mem_toList.mp hp)
    have ge2 := prime.two_le
    have ne2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := oddL
      omega
    exact tower_box p _ (by omega)
  have weight : (fun d : Divisor L => ((range L ∩ event' d).card : ℝ) / (range L).card) =
      (fun d => 1 / (d.val : ℝ)) := by
    funext d
    have sub : event' d ⊆ range L := filter_subset _ _
    have dnonzero : (d.val : ℝ) ≠ 0 := by exact_mod_cast (dpos d).ne'
    have Lnonzero : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
    rw [inter_eq_right.mpr sub, card_range, ThirdOrderCRT.card_event L d.val _ (dpos d) (divides d),
      Nat.cast_div (divides d) dnonzero]
    field_simp
  have transport (T : Finset (Divisor L)) :
      uncovered (range L) event' T =
        uncovered (range L) (fun d => ThirdOrderCRT.event L d (r d)) (T.image Subtype.val) := by
    ext x
    simp [uncovered, event']
  have independence (S : Finset (Divisor L)) (d : Divisor L) (_ : d ∈ S) :
      (uncovered (range L) event' (far supp S d) ∩ event' d).card * (range L).card =
      (range L ∩ event' d).card * (uncovered (range L) event' (far supp S d)).card := by
    rw [transport]
    apply ThirdOrderCRT.independent_avoidance L d.val r _ hL (divides d)
    · intro m hm
      obtain ⟨v, _, rfl⟩ := mem_image.mp hm
      exact divides v
    · intro m hm
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hm
      apply (Nat.disjoint_primeFactors (dpos d).ne' (dpos v).ne').mp
      exact (Finset.mem_filter.mp hv).2.symm
  have ans := coverage_le (range L) (nonempty_range_iff.mpr hL.ne') event' supp
    L.primeFactors.toList (fun p => tower p (L.factorization p)) hwithin hne box
    (weight.symm ▸ normal) independence
  simpa only [card_range] using ans

end ThirdOrderMain
