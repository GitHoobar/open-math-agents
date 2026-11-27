import Std

/-! Auxiliary results for an attempt on the odd covering systems problem.
The finite certificate concerns the inverse image of a subset of the
residues modulo 25 under reduction modulo 25 from period 75.
-/

namespace PrimeExtension

/-- Every choice of the two available base classes misses a point of {0,1,2}. -/
theorem base_has_a_hole :
    ∀ a : Fin 5, ∀ b : Fin 25, ∃ u : Fin 3,
      u.val % 5 ≠ a.val ∧ u.val % 25 ≠ b.val := by
  decide

abbrev InTarget (n : Nat) : Prop :=
  n % 25 = 0 ∨ n % 25 = 1 ∨ n % 25 = 2

abbrev InCover (n : Nat) : Prop :=
  n % 5 = 0 ∨ n % 25 = 1 ∨ n % 3 = 0 ∨ n % 15 = 7 ∨ n % 75 = 2

/-- Check all representatives of the common period. -/
theorem lifted_target_is_covered :
    ∀ x : Fin 75, InTarget x.val → InCover x.val := by
  decide

theorem moduli_are_distinct_odd_and_proper :
    let moduli : List Nat := [5, 25, 3, 15, 75]
    moduli.Nodup ∧ moduli.all (fun m => 1 < m && m % 2 == 1) = true := by
  decide

/-- The five classes leave an uncovered residue in the full period. -/
theorem four_escapes : ¬ InCover 4 := by decide

/-- If each nonfree slice can cover the residual target with its own family
of modulus labels, all the families can be realized simultaneously. Each label
gets at most one slice and one residue. The free slice is covered separately.
-/
theorem glue_disjoint_families
    {X : Type _} {F : Type _} {I : Type _} {A : Type _}
    (free : F) (target old : X → Prop)
    (covers : I → A → X → Prop) (family : F → I → Prop) (residue : F → I → A)
    (exclusive : ∀ i f g, family f i → family g i → f = g)
    (sliceCover : ∀ x f, target x → ¬old x → f ≠ free →
      ∃ i, family f i ∧ covers i (residue f i) x) :
    ∃ place : I → Option (F × A), ∀ x f, target x →
      old x ∨ f = free ∨ ∃ i a, place i = some (f, a) ∧ covers i a x := by
  classical
  let place (i : I) : Option (F × A) :=
    if h : ∃ f, family f i then some (h.choose, residue h.choose i) else none
  refine ⟨place, ?_⟩
  intro x f hx
  by_cases ho : old x
  · exact Or.inl ho
  by_cases he : f = free
  · exact Or.inr (Or.inl he)
  obtain ⟨i, hi, hc⟩ := sliceCover x f hx ho he
  have used : ∃ g, family g i := ⟨f, hi⟩
  have chosen : used.choose = f := exclusive i _ _ used.choose_spec hi
  exact Or.inr (Or.inr ⟨i, residue f i, by simp [place, used, chosen], hc⟩)

/-- Conversely, every placement partitions its used labels by their slices.
The result applies to any number of slices and to arbitrary projected classes. -/
theorem placement_iff_disjoint_families
    {X : Type _} {F : Type _} {I : Type _} {A : Type _} [Inhabited A]
    (free : F) (target old : X → Prop) (covers : I → A → X → Prop) :
    (∃ place : I → Option (F × A), ∀ x f, target x →
      old x ∨ f = free ∨ ∃ i a, place i = some (f, a) ∧ covers i a x) ↔
    ∃ (family : F → I → Prop) (residue : F → I → A),
      (∀ i f g, family f i → family g i → f = g) ∧
      (∀ x f, target x → ¬old x → f ≠ free →
        ∃ i, family f i ∧ covers i (residue f i) x) := by
  constructor
  · rintro ⟨place, hp⟩
    let family (f : F) (i : I) := ∃ a, place i = some (f, a)
    let residue (_ : F) (i : I) :=
      match place i with
      | some (_, a) => a
      | none => default
    refine ⟨family, residue, ?_, ?_⟩
    · rintro i f g ⟨a, ha⟩ ⟨b, hb⟩
      exact congrArg Prod.fst (Option.some.inj (ha.symm.trans hb))
    · intro x f hx ho he
      rcases hp x f hx with h | h | ⟨i, a, hi, hc⟩
      · exact False.elim (ho h)
      · exact False.elim (he h)
      · exact ⟨i, ⟨a, hi⟩, by simpa [residue, hi] using hc⟩
  · rintro ⟨family, residue, exclusive, sliceCover⟩
    exact glue_disjoint_families free target old covers family residue exclusive sliceCover

/-- Arithmetic for one lifting step. Natural-number subtraction clips the
number of holes to zero when the mixed classes exhaust the available holes. -/
theorem hole_budget_descends (p h B : Nat) (hp : 3 ≤ p) (hh : 0 < h)
    (budget : (p - 2) * h < B) :
    (p - 1) * h - B < h ∧ (p - 2) * ((p - 1) * h - B) < B := by
  have split : (p - 1) * h = (p - 2) * h + h := by
    have step : p - 1 = (p - 2) + 1 := by omega
    rw [step, Nat.add_mul, Nat.one_mul]
  have decrease : (p - 1) * h - B < h := by omega
  exact ⟨decrease, Nat.lt_of_le_of_lt
    (Nat.mul_le_mul_left (p - 2) (Nat.le_of_lt decrease)) budget⟩

end PrimeExtension

#print axioms PrimeExtension.base_has_a_hole
#print axioms PrimeExtension.lifted_target_is_covered
#print axioms PrimeExtension.moduli_are_distinct_odd_and_proper
#print axioms PrimeExtension.four_escapes
#print axioms PrimeExtension.glue_disjoint_families
#print axioms PrimeExtension.placement_iff_disjoint_families
#print axioms PrimeExtension.hole_budget_descends
