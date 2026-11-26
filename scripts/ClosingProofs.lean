import HilbertFoundations

/-!
# Statements proved outside their chapter file

Some units state a claim as a `Prop` in a chapter file and prove it in a later file (see the root
module `HilbertFoundations.lean`). This file checks that each such proof has exactly the type that
the unit states, with no additional hypothesis: every `example` below type-checks only if the
closing theorem proves the `Prop` of the unit. For the corrected unit `th.18` it checks the
refutation of the claim as printed and the two statements proved instead; for `app.main_theorem`
it checks the refutation of the statement as printed (the empty plane).

Run with `lake env lean scripts/ClosingProofs.lean`.
-/

open HilbertFoundations

/-! ## `th.6` (`OrderPolygon.lean`) -/

example {P : Type*} {L : Type*} [HasLines P L] [HasBetween P] [PlaneOrder P L] :
    PolygonTheorem (L := L) P := polygonTheorem

/-! ## `s8.bolzano`, `s8.real_numbers` (`CompletenessClose.lean`) -/

example : CompletenessGivesBolzano := completenessGivesBolzano
example : CompletenessGivesReals := completenessGivesReals

/-! ## `th.18`, `s7.circle_properties` (`CongruenceClose.lean`) -/

example : ¬SpaceCongruenceGivesTheorem18 := spaceCongruenceGivesTheorem18_false
example : SpaceCongruenceGivesTheorem18Distinct := spaceCongruenceGivesTheorem18Distinct
example {P : Type*} {L : Type*} {Pl : Type*} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P] [SpaceCongruence P L Pl] [Nonempty Pl] :
    Theorem18Statement (L := L) (Pl := Pl) P := theorem18
example : CirclePropertiesClaim := circlePropertiesClaim

/-! ## `s17.space`, `s17.ideal`, `s30.any_dimension` (`CoordinatesClose.lean`) -/

example : SpaceCoordinatesClaim := spaceCoordinatesClaim
example : IdealElementsClaim := idealElementsClaim
example : AnyDimensionClaim := anyDimensionClaim

/-! ## `th.43`, `s39.regular_polygons`, `s39.malfatti` (`ConstructionsClose.lean`) -/

example : Theorem43 := theorem43
example : RegularPolygonsClaim := regularPolygonsClaim
example : MalfattiClaim := malfattiClaim

/-! ## `concl.semi_euclidean`, `concl.non_legendrian`, `concl.legendre_archimedes`,
`app.main_theorem` (`CommentaryClose.lean`) -/

example : Conclusion.SemiEuclideanGeometryExists := Conclusion.semiEuclideanGeometryExists
example : Conclusion.NonLegendrianGeometryExists := Conclusion.nonLegendrianGeometryExists
example : Conclusion.LegendreNeedsArchimedes := Conclusion.legendreNeedsArchimedes
example : ¬Appendix.AppendixMainTheorem := Appendix.not_appendixMainTheorem

/-! ## `app.jordan_theorem` (`JordanCurveClose.lean`) -/

example : Appendix.JordanCurveTheorem := Appendix.jordanCurveTheorem
