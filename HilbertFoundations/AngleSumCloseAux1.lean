import HilbertFoundations.PascalAux2

/-!
# Helper module for the angle-sum theorem: plane tools and isometries

This module contains no unit of Hilbert's text. Plane geometry with groups I, II, IV
(`PlaneCongruence`), without any axiom of parallels or continuity.

* **Plane wrappers**: the frame lemmas (crossbar, laying off angles, position of half-rays) stated
  for the plane frame `fr hl`, so that no set argument has to be given.
* **Interiors of angles**: interiors computed with arbitrary lines through the sides, the
  transitivity of "inside", and opposite sides of a half-ray inside an angle.
* **Right angles**: wrappers of the `RightAng` API of the frame.
* **Isometries**: isometries preserve non-collinearity, angles and right angles; an isometry
  mapping a line onto itself preserves its sides. Half-turns and midpoints.
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

/-- The frame of plane geometry: its only plane is the set of all points. -/
abbrev fr : Frame P L := planeFrame hl

/-- The three points of a non-degenerate angle are pairwise distinct. -/
theorem ne_of_nc (h : ¬Collinear (Line := L) A O B) : A ≠ O ∧ B ≠ O ∧ A ≠ B :=
  ne_of_not_collinear h (hl O)

/-- Crossbar theorem: a half-ray inside the angle `∠BAC` meets the segment `BC`. -/
theorem crossbar (h : ¬Collinear (Line := L) B A C) (hD : D ∈ Interior (Line := L) B A C) :
    ∃ Y, Between B Y C ∧ Y ∈ ray A D :=
  (fr hl).crossbar (S := Set.univ) rfl trivial trivial trivial trivial h hD

/-- An angle can be laid off at `O'` on the half-ray `O'A'` of the line `l`, on the side of a
given point `D` not on `l`. -/
theorem layoff (h : ¬Collinear (Line := L) A O B) (hO' : O' ∈ l) (hA' : A' ∈ l) (hne : A' ≠ O')
    (hD : D ∉ l) : ∃ B', SameSide l B' D ∧ AngCong A O B A' O' B' := by
  sorry

/-- Uniqueness of laying off: two copies of an angle on the same side of `l` give the same
half-ray. -/
theorem layoff_unique (h : ¬Collinear (Line := L) A O B) (hO' : O' ∈ l) (hA' : A' ∈ l)
    (hne : A' ≠ O') {B' B'' : P} (hs : SameSide l B' B'') (h1 : AngCong A O B A' O' B')
    (h2 : AngCong A O B A' O' B'') : ray O' B' = ray O' B'' :=
  (fr hl).layoff_unique Set.univ rfl A O B l O' A' B' B'' h (fun _ _ => trivial) hO' hA' hne
    trivial trivial hs h1 h2

/-- If `∠AOB' ≅ ∠AOB` with `B'` on the side of `B` of the line `OA`, then `B'` lies on the
half-ray `OB`. -/
theorem mem_ray_of_angCong (h : ¬Collinear (Line := L) A O B) (hO : O ∈ l) (hA : A ∈ l)
    (hs : SameSide l B B') (hc : AngCong A O B A O B') : B' ∈ ray O B := by
  sorry

/-- Position of a half-ray: of two half-rays on the same side of `OL'`, one lies inside the angle
formed by the other with `OL'`. -/
theorem interior_or_interior {L' : P} (hHL : ¬Collinear (Line := L) H O L') (hLO : L' ≠ O)
    (hs : SameSide (line (Line := L) O L' hLO.symm) H K) (hHK : ¬Collinear (Line := L) H O K) :
    K ∈ Interior (Line := L) H O L' ∨ H ∈ Interior (Line := L) K O L' :=
  (fr hl).interior_or_interior (S := Set.univ) rfl trivial trivial trivial trivial hHL hLO hs hHK

/-- A point of the half-ray `OX` lies inside `∠AOB` when `X` does. -/
theorem mem_interior_of_ray (h : ¬Collinear (Line := L) A O B)
    (hX : X ∈ Interior (Line := L) A O B) (hY : Y ∈ ray O X) : Y ∈ Interior (Line := L) A O B :=
  (fr hl).mem_interior_of_ray (S := Set.univ) rfl trivial trivial trivial trivial h hX hY

/-- The interior of an angle depends only on its half-rays. -/
theorem interior_rays (h : ¬Collinear (Line := L) A O B) (hA' : A' ∈ ray O A)
    (hB' : B' ∈ ray O B) : Interior (Line := L) A O B = Interior (Line := L) A' O B' := by
  sorry

/-- The interior of `∠AOB` described with arbitrary lines `k ∋ O, A` and `n ∋ O, B`. -/
theorem mem_interior_iff {k n : L} (h : ¬Collinear (Line := L) A O B) (hOk : O ∈ k)
    (hAk : A ∈ k) (hOn : O ∈ n) (hBn : B ∈ n) :
    X ∈ Interior (Line := L) A O B ↔ SameSide k X B ∧ SameSide n X A := by
  sorry

/-- A line through the vertex and a point inside `∠AOC` separates `A` from `C`. -/
theorem opp_of_interior (h : ¬Collinear (Line := L) A O C) (hB : B ∈ Interior (Line := L) A O C)
    {k : L} (hO : O ∈ k) (hBk : B ∈ k) : OppositeSides k A C := by
  sorry

/-- If `X` is inside `∠AOC` and `Y` inside `∠XOC`, then `Y` is inside `∠AOC` and `X` inside
`∠AOY`. -/
theorem interior_trans (h : ¬Collinear (Line := L) A O C) (hX : X ∈ Interior (Line := L) A O C)
    (hY : Y ∈ Interior (Line := L) X O C) :
    Y ∈ Interior (Line := L) A O C ∧ X ∈ Interior (Line := L) A O Y := by
  sorry

/-- All points of a line `m` not meeting `k` lie on the same side of `k`. -/
theorem sameSide_of_not_meets {k m : L} (h : ¬Meets (Point := P) m k) (hX : X ∈ m)
    (hY : Y ∈ m) : SameSide k X Y :=
  ⟨fun hk => h ⟨X, hX, hk⟩, fun hk => h ⟨Y, hY, hk⟩,
    fun ⟨Z, hZk, hZ⟩ => h ⟨Z, mem_mid_of_between hZ hX hY, hZk⟩⟩

/-- Not meeting is symmetric. -/
theorem not_meets_symm {k m : L} (h : ¬Meets (Point := P) m k) : ¬Meets (Point := P) k m :=
  fun ⟨Z, hk, hm⟩ => h ⟨Z, hm, hk⟩

/-- A right angle stays right when its second arm is replaced by another point of its line. -/
theorem rt_side (h : RightAng (L := L) A O B) (hB' : B' ≠ O)
    (hc : Collinear (Line := L) O B B') : RightAng (L := L) A O B' :=
  (fr hl).rt_side h hB' hc

/-- A right angle stays right when its first arm is replaced by another point of its line. -/
theorem rt_arm (h : RightAng (L := L) A O B) (hA' : A' ≠ O)
    (hc : Collinear (Line := L) O A A') : RightAng (L := L) A' O B :=
  (fr hl).rt_arm h hA' hc

/-- The arms of a right angle can be exchanged. -/
theorem rt_symm (h : RightAng (L := L) A O B) : RightAng (L := L) B O A :=
  (fr hl).rt_symm h

/-- Any two right angles are congruent. -/
theorem rt_cong (h : RightAng (L := L) A O B) (h' : RightAng (L := L) A' O' B') :
    AngCong A O B A' O' B' :=
  (fr hl).rt_cong h h'

/-- An isometry maps non-collinear points to non-collinear points. -/
theorem isom_nc {f : Equiv.Perm P} (hf : f ∈ Pas.isom (L := L))
    (h : ¬Collinear (Line := L) X Y Z) : ¬Collinear (Line := L) (f X) (f Y) (f Z) :=
  fun hh => h ((Pas.isom_collinear_iff hf).1 hh)

/-- An isometry maps an angle to a congruent angle. -/
theorem isom_angCong {f : Equiv.Perm P} (hf : f ∈ Pas.isom (L := L))
    (h : ¬Collinear (Line := L) X Y Z) : AngCong X Y Z (f X) (f Y) (f Z) := by
  sorry

/-- An isometry maps a right angle to a right angle. -/
theorem isom_rightAng {f : Equiv.Perm P} (hf : f ∈ Pas.isom (L := L))
    (h : RightAng (L := L) X Y Z) : RightAng (L := L) (f X) (f Y) (f Z) :=
  (fr hl).rt_congr h (isom_nc hl hf h.1) (isom_angCong hl hf h.1)

/-- An isometry mapping the line `l` onto itself preserves "same side of `l`". -/
theorem isom_sameSide_self {f : Equiv.Perm P} (hf : f ∈ Pas.isom (L := L))
    (hmap : ∀ Z : P, Z ∈ l ↔ f Z ∈ l) (h : SameSide l X Y) : SameSide l (f X) (f Y) := by
  sorry

/-- An isometry mapping the line `l` onto itself preserves "opposite sides of `l`". -/
theorem isom_opp_self {f : Equiv.Perm P} (hf : f ∈ Pas.isom (L := L))
    (hmap : ∀ Z : P, Z ∈ l ↔ f Z ∈ l) (h : OppositeSides l X Y) :
    OppositeSides l (f X) (f Y) := by
  sorry

/-- The half-turn about `M` maps `X ≠ M` to the point `X'` with `M` between `X` and `X'` and
`MX ≡ MX'`. -/
theorem ht_spec {M : P} (h : X ≠ M) :
    Between X M (Pas.ht (L := L) M X) ∧ SegCong M X M (Pas.ht (L := L) M X) :=
  (Pas.ht_eq_iff (L := L) h).1 rfl

/-- A half-turn about a point of `l` maps `l` onto itself. -/
theorem ht_mem {M : P} (hM : M ∈ l) : X ∈ l ↔ Pas.ht (L := L) M X ∈ l := by
  sorry

/-- The midpoint of `AC` lies between `A` and `C`, and the half-turn about it exchanges `A`
and `C`. -/
theorem midp_spec (h : A ≠ C) :
    Between A (Pas.midp (L := L) A C) C ∧ Pas.ht (L := L) (Pas.midp (L := L) A C) A = C ∧
      Pas.ht (L := L) (Pas.midp (L := L) A C) C = A := by
  sorry

end

end AngSum

end HilbertFoundations
