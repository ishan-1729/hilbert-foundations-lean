import HilbertFoundations.AngleSumCloseAux9

/-!
# Helper module for the angle-sum theorem: all Saccheri quadrilaterals have the same type

This module contains no unit of Hilbert's text. Plane geometry with groups I, II, IV.

Shrinking the sides of a Lambert quadrilateral does not change the type of its fourth angle
(`lambert_shrink`, `lambert_shrink2`); the fourth vertex is determined by the other three
(`lambert_unique`); a Lambert quadrilateral can be transported by an isometry (`lambert_transport`).
Hence any two Lambert quadrilaterals have fourth angles of the same type (`lambert_sameType`), and
any two Saccheri quadrilaterals have summit angles of the same type (`saccheri_sameType`).
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

/-- F5(a): replacing the side `MB` of a Lambert quadrilateral `M B D N` by a part `MB₀` gives a
Lambert quadrilateral `M B₀ D₁ N` whose fourth angle has the same type. -/
theorem lambert_shrink {B₀ : P} (h : Lambert L M B D N) (hB₀ : B₀ = B ∨ Between M B₀ B) :
    ∃ D₁, Lambert L M B₀ D₁ N ∧ SameType L B D N B₀ D₁ N := by
  sorry

/-- F5(b): shrinking both sides `MB`, `MN` of a Lambert quadrilateral gives a Lambert
quadrilateral `M B₀ D₀ N₀` whose fourth angle has the same type. -/
theorem lambert_shrink2 {B₀ N₀ : P} (h : Lambert L M B D N) (hB₀ : B₀ = B ∨ Between M B₀ B)
    (hN₀ : N₀ = N ∨ Between M N₀ N) :
    ∃ D₀, Lambert L M B₀ D₀ N₀ ∧ SameType L B D N B₀ D₀ N₀ := by
  sorry

/-- F6: the fourth vertex of a Lambert quadrilateral is determined by the other three. -/
theorem lambert_unique (h : Lambert L M B D N) (h' : Lambert L M B D' N) : D = D' := by
  sorry

/-- F7: a Lambert quadrilateral `M' B' D' N'` can be transported onto a right angle `∠B₁MN₁` with
congruent arms; the transported fourth angle has the same type. -/
theorem lambert_transport {M' N' N₁ : P} (h' : Lambert L M' B' D' N')
    (hr : RightAng (L := L) B₁ M N₁) (sB : SegCong M' B' M B₁) (sN : SegCong M' N' M N₁) :
    ∃ D₁, Lambert L M B₁ D₁ N₁ ∧ SameType L B' D' N' B₁ D₁ N₁ := by
  sorry

/-- Two points `B`, `B₁` on one ray from `M` have a common "lower bound" `B₀`: equal to or
between `M` and each of them. -/
theorem exists_common (hB₁ : B₁ ∈ ray M B) :
    ∃ B₀, (B₀ = B ∨ Between M B₀ B) ∧ (B₀ = B₁ ∨ Between M B₀ B₁) := by
  sorry

/-- F8: the fourth angles of any two Lambert quadrilaterals have the same type. -/
theorem lambert_sameType {M' N' : P} (h : Lambert L M B D N) (h' : Lambert L M' B' D' N') :
    SameType L B D N B' D' N' := by
  sorry

/-- F9: the summit angles of any two Saccheri quadrilaterals have the same type. -/
theorem saccheri_sameType (h : Saccheri L A B C D) (h' : Saccheri L A' B' C' D') :
    SameType L A C D A' C' D' := by
  sorry

end

end AngSum

end HilbertFoundations
