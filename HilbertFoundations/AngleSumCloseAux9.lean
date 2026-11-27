import HilbertFoundations.AngleSumCloseAux8b

/-!
# Helper module for the angle-sum theorem: Lambert quadrilaterals, doubling and nesting

This module contains no unit of Hilbert's text. Plane geometry with groups I, II, IV.

A Lambert quadrilateral `M B D N` (`Lambert`, right angles at `M`, `B`, `N`) is half of a Saccheri
quadrilateral: reflecting it in the line `MN` doubles it. Cutting it by a perpendicular to `MB`
at a point `B₀` between `M` and `B` gives a smaller Lambert quadrilateral `M B₀ D₁ N`, and the
outside lemma shows that the fourth angles `∠BDN` and `∠B₀D₁N` have the same type.
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

/-- F1(a): a Lambert quadrilateral read in the other direction around the vertex `M`. -/
theorem lambert_symm (h : Lambert L M B D N) : Lambert L M N D B :=
  ⟨rt_symm hl h.1, h.2.2, h.2.1⟩

/-- F1(b): in a Lambert quadrilateral `M B D N` the lines `MB` and `ND` do not meet. -/
theorem lambert_not_meets (h : Lambert L M B D N) {l s : L} (hM : M ∈ l) (hB : B ∈ l)
    (hN : N ∈ s) (hD : D ∈ s) : ¬Meets (Point := P) l s := by
  sorry

/-- F1(c): the fourth angle `∠BDN` of a Lambert quadrilateral is genuine. -/
theorem lambert_nc (h : Lambert L M B D N) : ¬Collinear (Line := L) B D N := by
  sorry

/-- F2: reflecting a Lambert quadrilateral `M B D N` in the line `t = MN` doubles it into a
Saccheri quadrilateral whose summit angle is congruent to `∠BDN`. -/
theorem lambert_double (h : Lambert L M B D N) {t : L} (hM : M ∈ t) (hN : N ∈ t) :
    Between B M (Pas.refl t B) ∧ Between D N (Pas.refl t D) ∧
      Saccheri L (Pas.refl t B) B (Pas.refl t D) D ∧
      AngCong B D N (Pas.refl t B) (Pas.refl t D) N := by
  sorry

/-- F3: the perpendicular to `MB` at a point `B₀` between `M` and `B` cuts off a smaller Lambert
quadrilateral `M B₀ D₁ N` with `D₁` between `N` and `D`. -/
theorem lambert_cut {B₀ : P} (h : Lambert L M B D N) (hB₀ : Between M B₀ B) :
    ∃ D₁, Between N D₁ D ∧ Lambert L M B₀ D₁ N := by
  sorry

/-- F4: the fourth angles of a Lambert quadrilateral and of a smaller one cut off from it have the
same type. -/
theorem lambert_nest {B₀ D₁ : P} (h : Lambert L M B D N) (hB₀ : Between M B₀ B)
    (hD₁ : Between N D₁ D) (h₁ : Lambert L M B₀ D₁ N) : SameType L B D N B₀ D₁ N := by
  sorry

end

end AngSum

end HilbertFoundations
