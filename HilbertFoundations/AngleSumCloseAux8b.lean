import HilbertFoundations.AngleSumCloseAux8

/-!
# Helper module for the angle-sum theorem: the outside lemma, part 2

This module contains no unit of Hilbert's text. Plane geometry with groups I, II, IV.

Continuation of the outside lemma for a Saccheri quadrilateral `A B C D`, a point `P'` on the
summit line beyond `D` and its foot `Q` on the base line beyond `B`: if `QP' < BD` then
`∠BDP' < ∠ACD`, and if `BD ≡ QP'` then `∠ACD ≡ ∠BDP'`. Together with part 1, the comparison of
`BD` with `QP'` decides the type (acute, right, obtuse) of the summit angle `∠CDB`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace AngSum

universe u v

section

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] (hl : ∀ X : P, ∃ l : L, X ∈ l)
  {A B C D E F G H K M N O Q X Y Z A' B' C' D' O' A₁ B₁ O₁ P' : P} {l m : L}
include hC hl

/-- E3 (in the bundled setting): if `QP' < BD`, then `∠BDP' < ∠ACD`. -/
theorem outConf_gt {l s q a b : L} (O : OutConf L A B C D P' Q l s q a b)
    (hgt : SLt Q P' B D) : AngLt (L := L) B D P' A C D := by
  sorry

/-- E3: in the setting of the outside lemma, `QP' < BD` implies `∠BDP' < ∠ACD`. -/
theorem saccheri_out_gt (h : Saccheri L A B C D) (hP : Between C D P') (hQ : Between A B Q)
    (hr : RightAng (L := L) B Q P') (hgt : SLt Q P' B D) : AngLt (L := L) B D P' A C D := by
  obtain ⟨l, s, q, a, b, O⟩ := exists_outConf hl h hP hQ hr
  exact outConf_gt hl O hgt

/-- E4: in the setting of the outside lemma, `BD ≡ QP'` implies `∠ACD ≡ ∠BDP'`. -/
theorem saccheri_out_eq (h : Saccheri L A B C D) (hP : Between C D P') (hQ : Between A B Q)
    (hr : RightAng (L := L) B Q P') (he : SegCong B D Q P') : AngCong A C D B D P' := by
  sorry

/-- E5: in the setting of the outside lemma, `BD < QP'`, `BD ≡ QP'`, `QP' < BD` make the summit
angle `∠CDB` less than, congruent to, greater than its supplement, respectively. -/
theorem saccheri_out_type (h : Saccheri L A B C D) (hP : Between C D P') (hQ : Between A B Q)
    (hr : RightAng (L := L) B Q P') :
    (SLt B D Q P' → LtSupp L C D B) ∧ (SegCong B D Q P' → EqSupp L C D B) ∧
      (SLt Q P' B D → GtSupp L C D B) := by
  sorry

end

end AngSum

end HilbertFoundations
