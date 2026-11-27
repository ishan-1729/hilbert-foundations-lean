import TauCeti.Algebra.Order.Ring.Ordering.Semireal
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Semireal.Defs

/-!
# Orderings and separation for sums of squares in a field

This file is not the upstream file `OrderingSeparation.lean`: it keeps one statement of it,
`Hilbert17.RingPreordering.isSumSq_iff_nonneg_all_orders`, under the same name and with the same
type, and proves it from the Tau Ceti library.

The upstream file develops the extension of a preordering of a field to an ordering (adjunction of
one element, unions of chains, Zorn's lemma) on Mathlib's structure `RingPreordering`, which Mathlib
`v4.36.0` has deprecated in favour of the predicate `Subsemiring.IsPreordering`. Tau Ceti proves the
same extension theorem on the new interface (`TauCeti.Algebra.Order.Ring.Ordering.Extension`,
`TauCeti.Algebra.Order.Ring.Ordering.Semireal`); the statements used here are
`Subsemiring.IsPreordering.sumSq`, `Subsemiring.IsPreordering.isPreordering_adjoin` and
`Subsemiring.IsPreordering.exists_linearOrder`.
-/

namespace Hilbert17
namespace RingPreordering

variable {F : Type*} [Field F]

/-- Artin–Schreier separation using ordinary Lean linear orders. -/
theorem isSumSq_iff_nonneg_all_orders [IsSemireal F] (a : F) :
    IsSumSq a ↔ ∀ (o : LinearOrder F), @IsStrictOrderedRing F _ o.toPartialOrder →
      @LE.le F o.toLE 0 a := by
  refine ⟨?_, ?_⟩
  · intro ha o ho
    let : LinearOrder F := o
    let : IsStrictOrderedRing F := ho
    exact ha.nonneg
  · intro ha
    by_contra hs
    have hP : (Subsemiring.sumSq F).IsPreordering := Subsemiring.IsPreordering.sumSq
    have hna : - -a ∉ Subsemiring.sumSq F := by
      rw [neg_neg]
      exact fun h => hs (Subsemiring.mem_sumSq.mp h)
    obtain ⟨o, ho, hpos⟩ := (hP.isPreordering_adjoin hna).exists_linearOrder
    have h1 : @LE.le F o.toLE 0 (-a) := hpos _ (hP.self_mem_adjoin (-a))
    have h2 : @LE.le F o.toLE 0 a := ha o ho
    let : LinearOrder F := o
    let : IsStrictOrderedRing F := ho
    have h0 : a = 0 := le_antisymm (neg_nonneg.mp h1) h2
    exact hs (h0 ▸ IsSumSq.zero)

end RingPreordering
end Hilbert17
