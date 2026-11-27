import Mathlib

/-!
# Shearer's avoidance comparison in deletion form

For a family `S` of bad events and a vertex `v ∈ S`, let `far S v` be
the events outside the closed neighborhood of `v`. The signed independence
polynomial `Q` satisfies the deletion identity. The avoidance probability
`A` satisfies the corresponding inequality, by independence of `v` from
the events in `far S v`. The proof below uses just these two recurrences.
-/

namespace ThirdOrderAvoidance

variable {V : Type*} [DecidableEq V]

/-- If all induced signed independence polynomials are positive, the
ratio of avoidance probability to independence polynomial is monotone
under inclusion. -/
theorem ratio_mono (A Q : Finset V → ℝ) (w : V → ℝ)
    (far : Finset V → V → Finset V)
    (hw : ∀ v, 0 ≤ w v) (hQ : ∀ S, 0 < Q S)
    (hfar : ∀ S v, v ∈ S → far S v ⊆ S.erase v)
    (hdel : ∀ S v, v ∈ S → Q S = Q (S.erase v) - w v * Q (far S v))
    (havoid : ∀ S v, v ∈ S → A (S.erase v) - w v * A (far S v) ≤ A S)
    (S : Finset V) : ∀ T ⊆ S, A T / Q T ≤ A S / Q S := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro T hTS
    by_cases heq : T = S
    · simp [heq]
    obtain ⟨v, hv, sub⟩ := Finset.ssubset_iff_exists_subset_erase.mp
      (Finset.ssubset_iff_subset_ne.mpr ⟨hTS, heq⟩)
    let E := S.erase v
    let R := far S v
    have smaller : E ⊂ S := Finset.erase_ssubset hv
    have ratio := ih E smaller R (hfar S v hv)
    have cross := (div_le_div_iff₀ (hQ R) (hQ E)).mp ratio
    apply (ih E smaller T sub).trans
    apply (div_le_div_iff₀ (hQ E) (hQ S)).mpr
    calc
      A E * Q S = A E * (Q E - w v * Q R) := by rw [hdel S v hv]
      _ ≤ (A E - w v * A R) * Q E := by
        nlinarith only [mul_nonneg (hw v) (sub_nonneg.mpr cross)]
      _ ≤ A S * Q E := mul_le_mul_of_nonneg_right (havoid S v hv) (hQ E).le

/-- At the empty family both normalized quantities equal one, yielding
the lower bound for every finite family. -/
theorem avoidance_ge (A Q : Finset V → ℝ) (w : V → ℝ)
    (far : Finset V → V → Finset V)
    (hw : ∀ v, 0 ≤ w v) (hQ : ∀ S, 0 < Q S)
    (hfar : ∀ S v, v ∈ S → far S v ⊆ S.erase v)
    (hdel : ∀ S v, v ∈ S → Q S = Q (S.erase v) - w v * Q (far S v))
    (havoid : ∀ S v, v ∈ S → A (S.erase v) - w v * A (far S v) ≤ A S)
    (a_empty : A ∅ = 1) (q_empty : Q ∅ = 1) (S : Finset V) : Q S ≤ A S := by
  have ratio := ratio_mono A Q w far hw hQ hfar hdel havoid S ∅ (Finset.empty_subset S)
  simpa only [a_empty, q_empty, div_one, one_mul] using (le_div_iff₀ (hQ S)).mp ratio

variable {Ω : Type*} [DecidableEq Ω]

/-- Outcomes of the finite sample space which avoid every event indexed by `S`. -/
def uncovered (space : Finset Ω) (event : V → Finset Ω) (S : Finset V) : Finset Ω :=
  space.filter fun x => ∀ v ∈ S, x ∉ event v

/-- A finite-event form of the avoidance comparison. The independence premise
is an equality of ordinary integer counts for the event and joint avoidance of
its non-neighbors. The weights in the recurrence are the actual event probabilities. -/
theorem finite_avoidance_ge (space : Finset Ω) (nonempty : space.Nonempty)
    (event : V → Finset Ω) (Q : Finset V → ℝ) (far : Finset V → V → Finset V)
    (hQ : ∀ S, 0 < Q S) (q_empty : Q ∅ = 1)
    (hfar : ∀ S v, v ∈ S → far S v ⊆ S.erase v)
    (hdel : ∀ S v, v ∈ S → Q S = Q (S.erase v) -
      (↑(space ∩ event v).card / (space.card : ℝ)) * Q (far S v))
    (indep : ∀ S v, v ∈ S →
      (uncovered space event (far S v) ∩ event v).card * space.card =
        (space ∩ event v).card * (uncovered space event (far S v)).card)
    (S : Finset V) : Q S ≤ (uncovered space event S).card / (space.card : ℝ) := by
  let N := uncovered space event
  let A (T : Finset V) := (N T).card / (space.card : ℝ)
  let w (v : V) := (space ∩ event v).card / (space.card : ℝ)
  have positive : (0 : ℝ) < space.card := by exact_mod_cast Finset.card_pos.mpr nonempty
  have mono {T U : Finset V} (sub : T ⊆ U) : N U ⊆ N T := by
    intro x hx
    obtain ⟨inSpace, avoids⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨inSpace, fun v hv => avoids v (sub hv)⟩
  apply avoidance_ge A Q w far (fun v => by dsimp [w]; positivity) hQ hfar hdel
  · intro T v hv
    let E := T.erase v
    let R := far T v
    have split : N T = N E \ event v := by
      ext x
      simp only [N, uncovered, Finset.mem_sdiff, Finset.mem_filter]
      constructor
      · rintro ⟨hx, avoid⟩
        exact ⟨⟨hx, fun i hi => avoid i (Finset.mem_of_mem_erase hi)⟩, avoid v hv⟩
      · rintro ⟨⟨hx, avoid⟩, hn⟩
        refine ⟨hx, fun i hi => ?_⟩
        by_cases h : i = v
        · simpa [h] using hn
        · exact avoid i (Finset.mem_erase.mpr ⟨h, hi⟩)
    have part : ((N T).card : ℝ) + ((N E ∩ event v).card : ℝ) = (N E).card := by
      rw [split]
      exact_mod_cast Finset.card_sdiff_add_card_inter (N E) (event v)
    have smaller : ((N E ∩ event v).card : ℝ) ≤ (N R ∩ event v).card := by
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_right (mono (hfar T v hv)))
    have independent : ((N R ∩ event v).card : ℝ) * space.card =
        (space ∩ event v).card * ((N R).card : ℝ) := by exact_mod_cast indep T v hv
    change (N E).card / (space.card : ℝ) -
      ((space ∩ event v).card / (space.card : ℝ)) * ((N R).card / (space.card : ℝ)) ≤
      (N T).card / (space.card : ℝ)
    field_simp
    nlinarith only [independent, mul_le_mul_of_nonneg_right smaller positive.le,
      congrArg (fun z : ℝ => z * space.card) part]
  · change (uncovered space event ∅).card / (space.card : ℝ) = 1
    simp [uncovered, positive.ne']
  · exact q_empty

end ThirdOrderAvoidance
