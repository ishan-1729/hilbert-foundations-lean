import HilbertFoundations.Commentary
import HilbertFoundations.CommentaryCloseAux2
import HilbertFoundations.CommentaryCloseAux6
import HilbertFoundations.CommentaryCloseAux7
import Mathlib.Analysis.Real.Hyperreal

/-!
# Conclusion and appendix: Dehn's geometries and the consequences of the main theorem

This file proves units of `Commentary.lean` that are only stated there.

* `concl.semi_euclidean` — **proved**: `Conclusion.semiEuclideanGeometryExists :
  SemiEuclideanGeometryExists`, and with it `Conclusion.parallelsNotReplaceable :
  ParallelsNotReplaceable`. The geometry is Dehn's: the finite part of the plane over the
  non-archimedean Pythagorean field `Ω(t)` (the points whose co-ordinates are bounded by natural
  numbers, with the lines that meet this part; `FinitePart.finPart`, built with the general
  restriction of a plane to a convex part, `ConvexPart`). The last clause, "the semi-euclidean
  geometry is at the same time a non-archimedean geometry", is proved directly for this geometry:
  `Conclusion.semiEuclidean_not_archimedean` (`FinitePart.finPart_not_axiomV`), and all the
  properties together are `Conclusion.semiEuclideanGeometryExists_nonArchimedean`. (The classical
  theorem `ArchimedesAngleSumGivesParallels`, which would give it for every such geometry, stays
  stated.)
* `concl.non_legendrian` — **proved**: `Conclusion.nonLegendrianGeometryExists :
  NonLegendrianGeometryExists`. The geometry is Dehn's: the part of an elliptic plane infinitely
  near to a point, over a non-archimedean ordered field with square roots (here the hyperreal
  numbers `ℝ*`). In the gnomonic chart its points are the pairs of infinitesimal numbers and its
  lines the straight lines (`Elliptic.EPt`, `Elliptic.ELn`, a `ConvexPart` of the plane over `ℝ*`);
  congruence is equality of the elliptic lengths and angles (`Elliptic.cs`, `Elliptic.kc`). Groups
  I, II, IV: `Elliptic.planeCongruence`; infinitely many parallels:
  `Elliptic.infinitelyManyParallels`; every triangle has angle sum greater than two right angles:
  `Elliptic.angleSumGt` (the spherical excess is positive, `Elliptic.excess_pos`).
* `concl.legendre_archimedes` — **proved**: `Conclusion.legendreNeedsArchimedes :
  LegendreNeedsArchimedes`, from the existence of the non-legendrian geometry.
* `app.main_theorem` — still open, but its statement `AppendixMainTheorem` is **false as stated**,
  for a degenerate reason (`Appendix.not_appendixMainTheorem`, in `CommentaryCloseAux7.lean`): the
  empty set of points is a plane in the sense of `IsPlane`, and with the identity as only
  displacement it satisfies axioms I–III (vacuously) without being the euclidean or the
  Bolyai–Lobachevskian plane. The statement Hilbert means, for a plane with at least one point, is
  `Appendix.AppendixMainTheoremNonempty`; it stays open (Hilbert's memoir, *Math. Ann.* 56).
* `app.two_fixed_points`, `app.transitive`, `app.middle`, `app.rotation_group` — still open: they
  are steps of the proof of the main theorem. Proved here (`CommentaryCloseAux7.lean`): they are
  consequences of `AppendixMainTheoremNonempty` (`Appendix.twoFixedPointsIdentity_of_main`,
  `Appendix.displacementsTransitive_of_main`, `Appendix.atMostOneMiddle_of_main`,
  `Appendix.rotationsOfTrueCircle_of_main`, collected in `Appendix.steps_of_main`; they hold in
  every euclidean and in every hyperbolic geometry in the sense of `IsEuclideanGeometry`,
  `IsHyperbolicGeometry`), and `Appendix.atMostOneMiddle_of_twoFixedPoints` reduces `app.middle` to
  `app.two_fixed_points` (if a displacement with two fixed points is the identity, a segment has at
  most one middle).
* `app.true_line`, `app.true_circle_jordan`, `app.invariant_subgroup`, `app.jordan_theorem`,
  `concl.angle_sum`, `concl.pseudo_geometry` — still open, nothing new.
-/

namespace HilbertFoundations

namespace FinitePart

open Coord

universe u

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Three points of the first co-ordinate axis in their order. -/
theorem between_pt2 {a b c : K} (hab : a < b) (hbc : b < c) :
    Between (pt2 a 0 : Coord K 2) (pt2 b 0) (pt2 c 0) := by
  have hac : a < c := hab.trans hbc
  have hca : 0 < c - a := sub_pos.2 hac
  rw [AffPt.between_iff, AffPt.sbtw_iff_param]
  refine ⟨fun e => hac.ne (congrArg xc e), (b - a) / (c - a), div_pos (sub_pos.2 hab) hca,
    (div_lt_one hca).2 (by linarith), ?_⟩
  apply ext2
  · simp only [xc_add, xc_smul, xc_sub, xc_pt2]
    rw [div_mul_cancel₀ _ hca.ne']
    ring
  · simp only [yc_add, yc_smul, yc_sub, yc_pt2]
    ring

/-- **The finite part of the plane over a non-archimedean field is non-archimedean**: if `T` is
infinitely large, the multiples `(k / T, 0)` of the segment from `(0, 0)` to `(1 / T, 0)` never
reach the point `(1, 0)`. -/
theorem finPart_not_axiomV (T : K) (hT : ∀ m : ℕ, (m : K) < T) : ¬AxiomV (finPart K).Pt := by
  intro hV
  have hT1 : (1 : K) < T := by exact_mod_cast hT 1
  have hT0 : (0 : K) < T := zero_lt_one.trans hT1
  have hi : (0 : K) < T⁻¹ := inv_pos.2 hT0
  have hfin : ∀ k : ℕ, FinPt (pt2 ((k : K) * T⁻¹) 0) := fun k =>
    ⟨⟨k, by
      show |(k : K) * T⁻¹| ≤ k
      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg k) hi.le)]
      exact mul_le_of_le_one_right (Nat.cast_nonneg k) (inv_le_one_of_one_le₀ hT1.le)⟩,
      isFin_zero⟩
  have hfinB : FinPt (pt2 (1 : K) 0) := ⟨⟨1, by show |(1 : K)| ≤ ((1 : ℕ) : K); simp⟩, isFin_zero⟩
  have hlt : ∀ k : ℕ, (k : K) * T⁻¹ < ((k + 1 : ℕ) : K) * T⁻¹ := fun k =>
    mul_lt_mul_of_pos_right (by exact_mod_cast Nat.lt_succ_self k) hi
  have hstepv : ∀ m : ℕ, pt2 (((m + 1 : ℕ) : K) * T⁻¹) 0 - pt2 ((m : K) * T⁻¹) 0 =
      (pt2 T⁻¹ 0 : Coord K 2) := fun m => by
    apply ext2
    · simp only [xc_sub, xc_pt2]; push_cast; ring
    · simp only [yc_sub, yc_pt2]; ring
  obtain ⟨N, hN⟩ := hV (fun k => (⟨pt2 ((k : K) * T⁻¹) 0, hfin k⟩ : (finPart K).Pt))
    ⟨pt2 1 0, hfinB⟩
    (by
      show Between (pt2 (((0 : ℕ) : K) * T⁻¹) 0 : Coord K 2) (pt2 (((0 + 1 : ℕ) : K) * T⁻¹) 0)
        (pt2 1 0)
      refine between_pt2 (hlt 0) ?_
      rw [Nat.zero_add, Nat.cast_one, one_mul]
      exact inv_lt_one_of_one_lt₀ hT1)
    (fun n => by
      show Between (pt2 ((n : K) * T⁻¹) 0 : Coord K 2) (pt2 (((n + 1 : ℕ) : K) * T⁻¹) 0)
        (pt2 (((n + 1 + 1 : ℕ) : K) * T⁻¹) 0)
      exact between_pt2 (hlt n) (hlt (n + 1)))
    (fun m n => by
      show SegCong (pt2 ((m : K) * T⁻¹) 0 : Coord K 2) (pt2 (((m + 1 : ℕ) : K) * T⁻¹) 0)
        (pt2 ((n : K) * T⁻¹) 0) (pt2 (((n + 1 : ℕ) : K) * T⁻¹) 0)
      rw [Coord.segCong_iff, hstepv, hstepv])
  have hN' : Between (pt2 (((0 : ℕ) : K) * T⁻¹) 0 : Coord K 2) (pt2 1 0)
      (pt2 ((N : K) * T⁻¹) 0) := hN
  obtain ⟨-, s, hs0, hs1, hs⟩ := AffPt.sbtw_iff_param.1 (AffPt.between_iff.1 hN')
  have hx := congrArg xc hs
  simp only [xc_add, xc_smul, xc_sub, xc_pt2, Nat.cast_zero, zero_mul, sub_zero, add_zero] at hx
  have hq : (N : K) * T⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hT0]
    exact hT N
  have hq0 : (0 : K) ≤ (N : K) * T⁻¹ := mul_nonneg (Nat.cast_nonneg N) hi.le
  nlinarith [mul_le_mul_of_nonneg_left hq.le hs0.le]

end FinitePart

namespace Conclusion

open FinitePart

/-- **The semi-euclidean geometry exists** (Dehn): the finite part of the plane over `Ω(t)`
satisfies groups I, II, IV, has infinitely many parallels through every point outside a line,
every triangle of it has angle sum two right angles, it has similar triangles that are not
congruent, and the ends of equal perpendiculars are collinear. -/
theorem semiEuclideanGeometryExists : SemiEuclideanGeometryExists :=
  ⟨(finPart OmegaT).Pt, (finPart OmegaT).Ln, inferInstance, inferInstance, inferInstance,
    inferInstance, (finPart OmegaT).planeCongruence finPart_layOffClosed,
    finPart_infinitelyManyParallels OmegaT.t OmegaT.natCast_lt_t, finPart_angleSum,
    finPart_similar, finPart_equalPerp⟩

/-- **Without Archimedes's axiom, Euclid's axiom cannot be replaced** by the theorem on the angle
sum, by the existence of similar triangles or by the collinearity of the ends of equal
perpendiculars. -/
theorem parallelsNotReplaceable : ParallelsNotReplaceable :=
  parallelsNotReplaceable_of_semiEuclidean semiEuclideanGeometryExists

/-- **The semi-euclidean geometry is a non-archimedean geometry**: Archimedes's axiom fails in the
finite part of the plane over `Ω(t)`. This is proved directly for the geometry constructed here; the
classical theorem `ArchimedesAngleSumGivesParallels` (which gives it for every semi-euclidean
geometry) is not used. -/
theorem semiEuclidean_not_archimedean : ¬AxiomV (finPart OmegaT).Pt :=
  finPart_not_axiomV OmegaT.t OmegaT.natCast_lt_t

/-- The semi-euclidean geometry with all the properties Hilbert lists, the last one included: it is
a non-archimedean geometry. -/
theorem semiEuclideanGeometryExists_nonArchimedean :
    ∃ (P L : Type) (_ : HasLines P L) (_ : HasBetween P) (_ : HasSegCong P) (_ : HasAngCong P),
      PlaneCongruence P L ∧ InfinitelyManyParallels P L ∧
        (∀ A B C : P, IsTriangle (Line := L) A B C → AngleSumEqTwoRight L A B C) ∧
        ExistSimilarTriangles P L ∧ EqualPerpendicularsCollinear P L ∧ ¬AxiomV P :=
  ⟨(finPart OmegaT).Pt, (finPart OmegaT).Ln, inferInstance, inferInstance, inferInstance,
    inferInstance, (finPart OmegaT).planeCongruence finPart_layOffClosed,
    finPart_infinitelyManyParallels OmegaT.t OmegaT.natCast_lt_t, finPart_angleSum,
    finPart_similar, finPart_equalPerp, semiEuclidean_not_archimedean⟩

/-- The hyperreal numbers are a euclidean ordered field: non-negative elements have square
roots. -/
instance hyperreal_isEuclidean : Elliptic.IsEuclidean Hyperreal :=
  ⟨fun x hx => by
    obtain ⟨f, rfl⟩ := Hyperreal.ofSeq_surjective x
    have h0 : (0 : Hyperreal) = Hyperreal.ofSeq (fun _ => 0) := rfl
    rw [h0, Hyperreal.ofSeq_le_ofSeq] at hx
    refine ⟨Hyperreal.ofSeq (fun n => Real.sqrt (f n)), ?_, ?_⟩
    · rw [h0, Hyperreal.ofSeq_le_ofSeq]
      exact Filter.Eventually.of_forall (fun n => Real.sqrt_nonneg _)
    · have e : Hyperreal.ofSeq (fun n => Real.sqrt (f n)) * Hyperreal.ofSeq (fun n => Real.sqrt (f n)) =
          Hyperreal.ofSeq (fun n => Real.sqrt (f n) * Real.sqrt (f n)) := rfl
      rw [e]
      exact Filter.Germ.coe_eq.2 (hx.mono fun n hn => Real.mul_self_sqrt hn)⟩

/-- The hyperreal numbers contain a positive infinitesimal. -/
instance hyperreal_hasInfinitesimal : Elliptic.HasInfinitesimal Hyperreal :=
  ⟨⟨Hyperreal.epsilon, Hyperreal.epsilon_pos, fun n => by
    have hcast : ((n : ℝ) : Hyperreal) = (n : Hyperreal) := map_natCast Hyperreal.coeRingHom n
    have h1 : (n : Hyperreal) < Hyperreal.omega := hcast ▸ Hyperreal.coe_lt_omega (n : ℝ)
    rw [abs_of_pos Hyperreal.epsilon_pos, ← Hyperreal.inv_omega, ← div_eq_mul_inv,
      div_le_one Hyperreal.omega_pos]
    exact h1.le⟩⟩

/-- **The non-legendrian geometry exists** (Dehn): the part of the elliptic plane over the
hyperreal numbers infinitely near to a point satisfies groups I, II, IV, has infinitely many
parallels through every point outside a line, and every triangle of it has angle sum greater than
two right angles. -/
theorem nonLegendrianGeometryExists : NonLegendrianGeometryExists :=
  ⟨Elliptic.EPt Hyperreal, Elliptic.ELn Hyperreal, inferInstance, inferInstance, inferInstance, inferInstance,
    Elliptic.planeCongruence, Elliptic.infinitelyManyParallels,
    fun A B C h => Elliptic.angleSumGt A B C h⟩

/-- **Legendre's theorem cannot be proved without the axiom of Archimedes.** -/
theorem legendreNeedsArchimedes : LegendreNeedsArchimedes :=
  legendreNeedsArchimedes_of_nonLegendrian nonLegendrianGeometryExists

end Conclusion

namespace Appendix

/-- The four steps of Hilbert's proof that are shown here to be consequences of the main theorem of
the appendix (for a plane that has a point), collected: a displacement with two fixed points is the
identity, the displacements are transitive, a segment has at most one middle, the rotations about
`M` act on a true circle about `M` as the ordinary rotations act on the ordinary circle. -/
theorem steps_of_main (h : AppendixMainTheoremNonempty) :
    TwoFixedPointsIdentity ∧ DisplacementsTransitive ∧ AtMostOneMiddle ∧ RotationsOfTrueCircle :=
  ⟨twoFixedPointsIdentity_of_main h, displacementsTransitive_of_main h, atMostOneMiddle_of_main h,
    rotationsOfTrueCircle_of_main h⟩

end Appendix

end HilbertFoundations
