import HilbertFoundations.CoordinatesCloseAux6
import HilbertFoundations.NonDesargues
import HilbertFoundations.Desargues

/-!
# Co-ordinates of space (§ 17, § 30): the units left open in Proportion.lean and DesarguesAlgebra.lean

This file proves three units that are only stated in the chapter files:

* `s17.space` (Proportion.lean), `spaceCoordinatesClaim : SpaceCoordinatesClaim`: a geometry of
  space with I–IV having a plane has co-ordinates `x, y, z` in an ordered field in which the planes
  are exactly the solution sets of the linear equations `a x + b y + c z + d = 0`.
* `s17.ideal` (Proportion.lean), `idealElementsClaim : IdealElementsClaim`: every geometry of space
  with I–V having a plane extends to the analytic geometry of space over `ℝ`.
* `s30.any_dimension` (DesarguesAlgebra.lean), `anyDimensionClaim : AnyDimensionClaim`: every
  geometry of space with I, II, III having a plane is a part of the coordinate geometry of any
  dimension `n ≥ 3` over an ordered skew field.

It also proves that the two formulations of "a plane geometry is part of a geometry of space"
(`IsPartOfSpace` of NonDesargues.lean and `PartOfSpace` of Desargues.lean) agree for types in
`Type` (`isPartOfSpace_iff_partOfSpace`).

## The proofs (helper modules `CoordinatesCloseAux` … `CoordinatesCloseAux6`)

**From the co-ordinates of a plane to the co-ordinates of space** (Aux, Aux2; groups I–III only).
Let `α` be a plane of space whose points are co-ordinatized by a vector space `V` of dimension 2
over an ordered skew field `K`, its lines being the lines of `V`. The parallel projections `p₁`,
`p₂` of space onto `α` along two lines `d₁`, `d₂` through a point of `α` (parallelism of lines of
space is transitive: `par_trans`) give a point `X` the co-ordinates `(e (p₁ X), h X) ∈ V × K`, where
`e (p₂ X) = e (p₁ X) + h X • u` and `u` is the direction of the trace of the plane `d₁d₂` in `α`.
Every line of space goes onto a line of `V × K` (`isImg_main`; a third projection handles the lines
of the planes parallel to `d₁d₂`), hence planes go onto planes (`plane_transfer`), and betweenness
is preserved because parallel projection preserves it (`proj_between`, II 5). This is
`exists_space_coords`.

**§ 30** (Aux3). Each plane of a geometry of space with I–III is desarguesian
(`planes_of_space_desarguesian`), so it is co-ordinatized by the vector space `DesAlg.Vec F` over
the opposite `(Seg F)ᵐᵒᵖ` of its skew field of segments; `exists_space_coords` gives co-ordinates of
space in a vector space of dimension 3, which is embedded linearly into `Kⁿ`.

**§ 17, co-ordinates** (Aux3). A plane of a geometry of space with I–IV has rectangular co-ordinates
over its field of segments `Pas.G ax` (Proportion.lean); `exists_space_coords` and the description
of the planes of `K³` by linear equations give `SpaceCoordinatesClaim`.

**§ 17, ideal elements** (Aux4, Aux5, Aux6). With Archimedes's axiom the congruence of space is
computed in these co-ordinates without any solid geometry (no perpendiculars to planes are needed):
the length `slen` of a segment of space is measured in the field of segments `K` of `α`; in every
plane it is proportional to the length of that plane, because an additive positive map between
archimedean ordered fields is linear (`additive_pos_eq_mul`, `slen_plane`); it is invariant under
the translations of the co-ordinates (parallelograms, `clen_translate`), homogeneous on lines
(`cnorm_smul`), and its square satisfies the theorem of Pythagoras on the axes of every plane
(`slen_pyth`), hence is a quadratic form on every plane and so a quadratic form (`quad_three`). A
linear change of co-ordinates makes it `x² + y² + z²` (`exists_metric_coords`). The congruence of
angles is determined by the congruence of segments (Theorems 10 and 16, `angCong_iff_exists`), so it
is the congruence of angles of the coordinate space as well (`psi_angCong_iff`). Finally `K` is
embedded into `ℝ` (`ideal_elements`).
-/

namespace HilbertFoundations

universe u v

/-!
## Unit `s17.space`: Co-ordinates in space

*(§ 17)*

> The corresponding results for the geometry of space may be easily deduced.

**Lean reading.** As in Proportion.lean: `SpaceCoordinatesClaim`.

**Status.** proved (`spaceCoordinatesClaim`)
-/

/-- **Co-ordinates in space** (§ 17): the claim `SpaceCoordinatesClaim` of Proportion.lean. -/
theorem spaceCoordinatesClaim : SpaceCoordinatesClaim.{u, v} := by
  intro P L Pl _ _ _ _ _ hC hP hne
  obtain ⟨α⟩ := hne
  have := hC
  have := hP
  exact SpaceCoord.space_coordinates (P := P) (L := L) α

/-!
## Unit `s17.ideal`: Ideal elements: the ordinary analytic geometry of space

*(§ 17)*

> However, it is always possible to generalize the original system of points, straight lines, and planes by the addition of “ideal” or “irrational” elements, so that, upon any straight line of the corresponding geometry, a point corresponds without exception to every system of three real numbers. By the adoption of suitable conventions, it may also be seen that, in this generalized geometry, all of the axioms I–V are valid. This geometry, generalized by the addition of irrational elements, is nothing else than the ordinary analytic geometry of space.

**Lean reading.** As in Proportion.lean: `IdealElementsClaim`.

**Status.** proved (`idealElementsClaim`)
-/

/-- **Ideal elements** (§ 17): the claim `IdealElementsClaim` of Proportion.lean. -/
theorem idealElementsClaim : IdealElementsClaim := by
  intro P L Pl _ _ _ _ _ hG hne
  obtain ⟨α⟩ := hne
  exact SpaceCoord.ideal_elements hG α

/-!
## Unit `s30.any_dimension`: Every space geometry is part of a geometry of any number of dimensions

*(§ 30)*

> The results obtained so far put us now in the position to show that every geometry of space in which axioms I, II, III are all fulfilled may be always regarded as a part of a “geometry of any number of dimensions whatever.” By a geometry of an arbitrary number of dimensions is to be understood the totality of all points, straight lines, planes, and other linear elements, for which the corresponding axioms of connection and of order, as well as the axiom of parallels, are all valid.

**Lean reading.** As in DesarguesAlgebra.lean: `AnyDimensionClaim`.

**Status.** proved (`anyDimensionClaim`)
-/

/-- **Geometries of any number of dimensions** (§ 30): the claim `AnyDimensionClaim` of
DesarguesAlgebra.lean. -/
theorem anyDimensionClaim : AnyDimensionClaim := by
  intro P L Pl _ _ _ hO hS hne n hn
  obtain ⟨α⟩ := hne
  have := hO
  have := hS
  exact SpaceCoord.any_dimension (P := P) (L := L) α hn

/-! ## The two formulations of "part of a geometry of space" -/

/-- `IsPartOfSpace` (NonDesargues.lean) and `PartOfSpace` (Desargues.lean) are the same notion for
types in `Type`. -/
theorem isPartOfSpace_iff_partOfSpace {P : Type} {L : Type} [HasLines P L] [HasBetween P] :
    IsPartOfSpace P L ↔ PartOfSpace P L := by
  constructor
  · rintro ⟨P', L', Pl', i1, i2, i3, hO, hS, α, f, g, hf, hg, h1, h2, h3, h4, h5, h6⟩
    exact ⟨P', L', Pl', i1, i2, i3, hO, hS,
      ⟨{ plane := α, pt := f, ln := g, pt_injective := hf, pt_mem := h1, pt_surj := h3,
         ln_injective := hg, ln_in := h2, ln_surj := h4, mem_iff := h5, between_iff := h6 }⟩⟩
  · rintro ⟨P', L', Pl', i1, i2, i3, hO, hS, ⟨e⟩⟩
    exact ⟨P', L', Pl', i1, i2, i3, hO, hS, e.plane, e.pt, e.ln, e.pt_injective, e.ln_injective,
      e.pt_mem, e.ln_in, e.pt_surj, e.ln_surj, e.mem_iff, e.between_iff⟩

end HilbertFoundations
