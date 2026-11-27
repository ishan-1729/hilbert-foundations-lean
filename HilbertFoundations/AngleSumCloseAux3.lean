import HilbertFoundations.AngleSumCloseAux2

/-!
# Helper module for the angle-sum theorem: addition of angles and types of angles

This module contains no unit of Hilbert's text. Plane geometry with groups I, II, IV.

Monotonicity of the addition of angles (`angLt_add`). An angle is compared with its supplement
(obtained by extending its first arm): it is `LtSupp` ("acute"), `EqSupp` ("right") or `GtSupp`
("obtuse"); this never needs a second right angle. The three cases exclude each other and do not
depend on the point chosen on the extension. Two angles have the same type (`SameType`) when they
fall in the same case.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace AngSum

universe u v

section

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]

variable (L) in
/-- `∠AOB` is less than its supplementary angle ("acute"). -/
def LtSupp (A O B : P) : Prop :=
  ¬Collinear (Line := L) A O B ∧ ∃ C, Between A O C ∧ AngLt (L := L) A O B C O B

variable (L) in
/-- `∠AOB` is congruent to its supplementary angle ("right"). -/
def EqSupp (A O B : P) : Prop :=
  ¬Collinear (Line := L) A O B ∧ ∃ C, Between A O C ∧ AngCong A O B C O B

variable (L) in
/-- `∠AOB` is greater than its supplementary angle ("obtuse"). -/
def GtSupp (A O B : P) : Prop :=
  ¬Collinear (Line := L) A O B ∧ ∃ C, Between A O C ∧ AngLt (L := L) C O B A O B

variable (L) in
/-- The angles `∠AOB`, `∠A'O'B'` have the same type (acute, right or obtuse). -/
def SameType (A O B A' O' B' : P) : Prop :=
  (LtSupp L A O B ↔ LtSupp L A' O' B') ∧ (EqSupp L A O B ↔ EqSupp L A' O' B') ∧
    (GtSupp L A O B ↔ GtSupp L A' O' B')

end

section

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] (hl : ∀ X : P, ∃ l : L, X ∈ l)
  {A B C D E F G H K M N O Q X Y Z A' B' C' D' O' A₁ B₁ O₁ P' : P} {l m : L}
include hC hl

/-- B1: if `∠AOB ≤ ∠A'O'B'` and `∠BOC < ∠B'O'C'` (with `B`, `B'` inside `∠AOC`, `∠A'O'C'`),
then `∠AOC < ∠A'O'C'`. -/
theorem angLt_add (h : ¬Collinear (Line := L) A O C) (hB : B ∈ Interior (Line := L) A O C)
    (h' : ¬Collinear (Line := L) A' O' C') (hB' : B' ∈ Interior (Line := L) A' O' C')
    (h1 : AngLt (L := L) A O B A' O' B' ∨ AngCong A O B A' O' B')
    (h2 : AngLt (L := L) B O C B' O' C') : AngLt (L := L) A O C A' O' C' := by
  sorry

/-- B2: `LtSupp` can be tested with any point `C` beyond `O` on the line `AO`. -/
theorem ltSupp_iff (hC : Between A O C) :
    LtSupp L A O B ↔ ¬Collinear (Line := L) A O B ∧ AngLt (L := L) A O B C O B := by
  sorry

/-- `EqSupp` can be tested with any point `C` beyond `O` on the line `AO`. -/
theorem eqSupp_iff (hC : Between A O C) :
    EqSupp L A O B ↔ ¬Collinear (Line := L) A O B ∧ AngCong A O B C O B := by
  sorry

/-- `GtSupp` can be tested with any point `C` beyond `O` on the line `AO`. -/
theorem gtSupp_iff (hC : Between A O C) :
    GtSupp L A O B ↔ ¬Collinear (Line := L) A O B ∧ AngLt (L := L) C O B A O B := by
  sorry

/-- B3: an angle is not both acute and right. -/
theorem not_ltSupp_eqSupp (h1 : LtSupp L A O B) (h2 : EqSupp L A O B) : False := by
  sorry

/-- An angle is not both acute and obtuse. -/
theorem not_ltSupp_gtSupp (h1 : LtSupp L A O B) (h2 : GtSupp L A O B) : False := by
  sorry

/-- An angle is not both right and obtuse. -/
theorem not_eqSupp_gtSupp (h1 : EqSupp L A O B) (h2 : GtSupp L A O B) : False := by
  sorry

/-- `SameType` is reflexive. -/
theorem sameType_refl (A O B : P) : SameType L A O B A O B :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- `SameType` is symmetric. -/
theorem sameType_symm (h : SameType L A O B A' O' B') : SameType L A' O' B' A O B :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

/-- `SameType` is transitive. -/
theorem sameType_trans {A₂ O₂ B₂ : P} (h1 : SameType L A O B A' O' B')
    (h2 : SameType L A' O' B' A₂ O₂ B₂) : SameType L A O B A₂ O₂ B₂ :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

/-- B7: two angles have the same type if, in each of three exhaustive cases, they are both acute,
both right, or both obtuse respectively. -/
theorem sameType_of_cases {c₁ c₂ c₃ : Prop} (hc : c₁ ∨ c₂ ∨ c₃)
    (h₁ : c₁ → LtSupp L A O B ∧ LtSupp L A' O' B')
    (h₂ : c₂ → EqSupp L A O B ∧ EqSupp L A' O' B')
    (h₃ : c₃ → GtSupp L A O B ∧ GtSupp L A' O' B') : SameType L A O B A' O' B' := by
  sorry

end

end AngSum

end HilbertFoundations
