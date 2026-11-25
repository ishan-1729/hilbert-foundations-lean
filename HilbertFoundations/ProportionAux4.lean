import HilbertFoundations.ProportionAux3
import HilbertFoundations.IndependenceAux3

/-!
# Helper module for `Proportion.lean`: distances, the second co-ordinate, the real correspondence
with Hilbert's normalisation, and the planes of a geometry of space (§ 17)

This module contains no unit of Hilbert's text. It adds, for the units of § 17 (and § 16):

* the **distance formula** `len X Y ² = (Δx)² + (Δy)²` (`len_sq`), from the identity
  `cos² + sin² = 1` of the rotations (`pyth_rot`); lengths on the axis `x` are absolute values of
  differences of co-ordinates (`len_axis`);
* **the perpendicular to the axis `y`** at its point `y` is the set of points with second co-ordinate
  `y` (`perp_iff_py`, through the quarter-turn `J`), so that the point with co-ordinates `(x, y)` is
  the intersection of the two perpendiculars of Hilbert's construction (`coords_perpendiculars`);
* with Archimedes's axiom, **the correspondence of § 17 normalised as Hilbert does it**: the two
  chosen points get `0` and `1`, and congruent segments of the line correspond to equal absolute
  differences of numbers (so the dyadic points of Hilbert's bisection get the dyadic numbers)
  (`exists_real_coord_norm`);
* **the restriction of a space geometry to one of its planes** satisfies the plane axioms I–IV
  (instances from Order.lean and `planeCongruence` from IndependenceAux3.lean) and V
  (`planeArchimedes`); hence the results for lines of a plane geometry hold for every line of a
  geometry of space that has a plane (`exists_real_coord_space`), and every plane of a geometry of
  space with I–IV has rectangular co-ordinates in which its lines are the linear equations
  (`plane_coordinates_space`).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Pas

universe u v w

section Distance

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Axes P L)
include ax

/-- The distance from the origin. -/
theorem len_sq_O (Z : P) : len ax ax.O Z * len ax ax.O Z = px ax Z * px ax Z + py ax Z * py ax Z := by
  by_cases hZ : Z = ax.O
  · subst hZ
    have h0 : len ax ax.O ax.O = 0 := by simp [len]
    have hx : px ax ax.O = 0 := by unfold px; rw [toV_O ax]; exact xc_zero ax
    have hy : py ax ax.O = 0 := by unfold py; rw [toV_O ax]; exact yc_zero ax
    rw [h0, hx, hy]; ring
  obtain ⟨ρ, hρ, e⟩ := exists_rot_of_vec ax hZ
  have h1 : px ax Z = len ax ax.O Z * xc ax (rE ax hρ (eV ax)) := by
    unfold px; rw [e]; exact (rot_coords ax hρ _).1
  have h2 : py ax Z = len ax ax.O Z * yc ax (rE ax hρ (eV ax)) := by
    unfold py; rw [e]; exact (rot_coords ax hρ _).2
  have hp := pyth_rot ax hρ
  rw [h1, h2]
  linear_combination (-(len ax ax.O Z * len ax ax.O Z)) * hp

/-- **The distance formula**: `XY² = (x_X - x_Y)² + (y_X - y_Y)²`. -/
theorem len_sq (X Y : P) : len ax X Y * len ax X Y =
    (px ax X - px ax Y) * (px ax X - px ax Y) + (py ax X - py ax Y) * (py ax X - py ax Y) := by
  have e1 : len ax X Y = len ax ax.O (trTo ax Y X) := by
    have h := len_isom ax (trTo_isom ax Y) X Y
    rw [trTo_self] at h
    rw [len_comm ax ax.O, h]
  have hx : px ax (trTo ax Y X) = px ax X - px ax Y := by
    unfold px; rw [trTo_apply]; exact xc_sub ax _ _
  have hy : py ax (trTo ax Y X) = py ax X - py ax Y := by
    unfold py; rw [trTo_apply]; exact yc_sub ax _ _
  rw [e1, len_sq_O, hx, hy]

theorem len_nonneg (X Y : P) : 0 ≤ len ax X Y := by
  by_cases h : X = Y
  · subst h; simp [len]
  · exact le_of_lt (len_pos ax h)

/-- A point lies on the axis `x` iff its second co-ordinate is `0`. -/
theorem mem_x_iff (Z : P) : Z ∈ ax.x ↔ py ax Z = 0 := by
  constructor
  · intro h
    exact (coords_x ax ⟨toV ax.O Z, h⟩).2
  · intro h
    have e := coords_eq ax (toV ax.O Z)
    show toV ax.O Z ∈ Xs ax
    have : yc ax (toV ax.O Z) = 0 := h
    rw [e, this]
    simp only [ZeroMemClass.coe_zero, map_zero, add_zero]
    exact (xc ax _).2

/-- A point lies on the axis `y` iff its first co-ordinate is `0`. -/
theorem mem_y_iff (Z : P) : Z ∈ ax.y ↔ px ax Z = 0 := mem_Ys_iff ax (toV ax.O Z)

/-- **Lengths on the axis `x`** are absolute values of differences of co-ordinates. -/
theorem len_axis {X Y : P} (hX : X ∈ ax.x) (hY : Y ∈ ax.x) : len ax X Y = |px ax X - px ax Y| := by
  have h := len_sq ax X Y
  rw [(mem_x_iff ax X).1 hX, (mem_x_iff ax Y).1 hY, sub_zero, mul_zero, add_zero] at h
  have h2 : len ax X Y ^ 2 = |px ax X - px ax Y| ^ 2 := by rw [sq_abs, sq, sq, h]
  exact (pow_left_inj₀ (len_nonneg ax X Y) (abs_nonneg _) two_ne_zero).1 h2

end Distance

/-! ### The second co-ordinate -/

section SecondCoord

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Axes P L)
include ax

theorem jE_inj {v w : V ax} (h : jE ax v = jE ax w) : v = w := by
  have : jE ax (v - w) = 0 := by rw [map_sub, h, sub_self]
  exact sub_eq_zero.1 (jE_injective ax this)

/-- The inverse quarter-turn in co-ordinates: `(x, y) ↦ (y, -x)`. -/
theorem Jinv_coords (Z : P) :
    px ax (ax.J⁻¹ Z) = py ax Z ∧ py ax (ax.J⁻¹ Z) = -px ax Z := by
  have hinv := (rot (L := L) ax.O).inv_mem ax.hJ
  have e : jE ax (toV ax.O (ax.J⁻¹ Z)) = toV ax.O Z := by
    show toV ax.O (ax.J (ofV (toV ax.O (ax.J⁻¹ Z)))) = toV ax.O Z
    simp only [ofV_toV, perm_apply_inv]
  obtain ⟨e1, e2⟩ := coords_jE ax (toV ax.O (ax.J⁻¹ Z))
  rw [e] at e1 e2
  refine ⟨e2.symm, ?_⟩
  show yc ax (toV ax.O (ax.J⁻¹ Z)) = -xc ax (toV ax.O Z)
  rw [e1, neg_neg]

theorem Jinv_isom : ax.J⁻¹ ∈ isom (L := L) := (isom (L := L)).inv_mem (rot_isom ax.hJ)

theorem Jinv_O : ax.J⁻¹ ax.O = ax.O := by
  rw [Equiv.Perm.inv_eq_iff_eq]; exact (rot_fix ax.hJ).symm

/-- The point `y` of the axis `y`. -/
theorem Jinv_mkPt (y : G ax) : ax.J⁻¹ (mkPt ax 0 y) = ofV (y : V ax) := by
  apply (coords_bijective ax).1
  obtain ⟨a1, a2⟩ := Jinv_coords ax (mkPt ax 0 y)
  obtain ⟨b1, b2⟩ := mkPt_coords ax 0 y
  obtain ⟨c1, c2⟩ := coords_x ax y
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [a1, b2]; exact c1.symm
  · rw [a2, b1, neg_zero]; exact c2.symm

theorem isom_rightAngle_iff {f : Equiv.Perm P} (hf : f ∈ isom (L := L)) {A O B : P} :
    IsRightAngle (L := L) (f A) (f O) (f B) ↔ IsRightAngle (L := L) A O B := by
  refine ⟨fun h => ?_, isom_rightAngle ax hf⟩
  have := isom_rightAngle ax ((isom (L := L)).inv_mem hf) h
  simpa only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] using this

/-- **The perpendicular to the axis `y`** at its point `y ≠ 0` consists of the points with second
co-ordinate `y`. -/
theorem perp_iff_py {y : G ax} (hy : y ≠ 0) {Z : P} (hZ : Z ∉ ax.y) :
    IsRightAngle (L := L) ax.O (mkPt ax 0 y) Z ↔ py ax Z = y := by
  rw [← isom_rightAngle_iff ax (Jinv_isom ax), Jinv_O, Jinv_mkPt]
  have hZ' : ax.J⁻¹ Z ∉ ax.x := by
    rw [mem_x_iff, (Jinv_coords ax Z).2, neg_eq_zero, ← mem_y_iff]; exact hZ
  rw [perp_iff_px ax hy hZ', (Jinv_coords ax Z).1]

/-- **Hilbert's construction of the co-ordinates**: for `x ≠ 0`, `y ≠ 0`, the perpendiculars to the
axes at the points `x` and `y` meet in exactly one point, the point with co-ordinates `(x, y)`. -/
theorem coords_perpendiculars {x y : G ax} (hx : x ≠ 0) (hy : y ≠ 0) (Z : P) :
    (IsRightAngle (L := L) ax.O (ofV (x : V ax)) Z ∧ IsRightAngle (L := L) ax.O (mkPt ax 0 y) Z) ↔
      Z = mkPt ax x y := by
  constructor
  · rintro ⟨h1, h2⟩
    have hZx : Z ∉ ax.x := fun hh => h1.1 (collinear_of_mem ax.hOx
      (by rw [mem_x_iff]; exact (coords_x ax x).2) hh)
    have hZy : Z ∉ ax.y := fun hh => h2.1 (collinear_of_mem ax.hOy
      (by rw [mem_y_iff, (mkPt_coords ax 0 y).1]) hh)
    apply (coords_bijective ax).1
    simp only [Prod.mk.injEq, mkPt_coords]
    exact ⟨(perp_iff_px ax hx hZx).1 h1, (perp_iff_py ax hy hZy).1 h2⟩
  · rintro rfl
    obtain ⟨c1, c2⟩ := mkPt_coords ax x y
    have hZx : mkPt ax x y ∉ ax.x := by rw [mem_x_iff, c2]; exact hy
    have hZy : mkPt ax x y ∉ ax.y := by rw [mem_y_iff, c1]; exact hx
    exact ⟨(perp_iff_px ax hx hZx).2 c1, (perp_iff_py ax hy hZy).2 c2⟩

end SecondCoord

/-! ### The real correspondence, normalised as in § 17 -/

section RealNorm

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L] [hV : Archimedes P L]
include hC hP hV

/-- **The correspondence of § 17 between the points of a line and the real numbers**, normalised as
Hilbert does it: two chosen points `O ≠ E` of the line `ℓ` get the numbers `0` and `1`; the map is
one-to-one on `ℓ`; betweenness goes over into the order of `ℝ`; congruent segments of `ℓ` are
exactly the segments whose extremities have equal absolute differences (so the midpoint of two
points gets the mean of their numbers, and the dyadic points of Hilbert's bisections get the dyadic
numbers `± m / 2ⁿ`); and every number of `Ω` is the number of a point of `ℓ`. -/
theorem exists_real_coord_norm (ℓ : L) {O E : P} (hO : O ∈ ℓ) (hE : E ∈ ℓ) (hOE : O ≠ E) :
    ∃ f : P → ℝ, f O = 0 ∧ f E = 1 ∧ (∀ Z W : P, Z ∈ ℓ → W ∈ ℓ → f Z = f W → Z = W) ∧
      (∀ A B C : P, A ∈ ℓ → B ∈ ℓ → C ∈ ℓ → Between A B C →
        (f A < f B ∧ f B < f C) ∨ (f C < f B ∧ f B < f A)) ∧
      (∀ X Y Z W : P, X ∈ ℓ → Y ∈ ℓ → Z ∈ ℓ → W ∈ ℓ → X ≠ Y → Z ≠ W →
        (SegCong X Y Z W ↔ |f X - f Y| = |f Z - f W|)) ∧
      ∀ ω : ℝ, ω ∈ Omega → ∃ Z : P, Z ∈ ℓ ∧ f Z = ω := by
  obtain ⟨ax, hO', hE'⟩ := exists_axes (L := L) hOE
  subst hO' hE'
  have hℓ : ℓ = ax.x := line_unique ax.hOE hO hE ax.hOx ax.hEx
  subst hℓ
  have := archimedean_G ax
  obtain ⟨ι⟩ := Real.nonemptyOrderRingHom (G ax)
  have hinj : Function.Injective ι := ι.toRingHom.injective
  have hmono : StrictMono ι := (OrderHomClass.mono ι).strictMono_of_injective hinj
  have habs : ∀ t : G ax, ι |t| = |ι t| := by
    intro t
    rcases le_total 0 t with h | h
    · have h' : 0 ≤ ι t := by simpa using OrderHomClass.mono ι h
      rw [abs_of_nonneg h, abs_of_nonneg h']
    · have h' : ι t ≤ 0 := by simpa using OrderHomClass.mono ι h
      rw [abs_of_nonpos h, abs_of_nonpos h', map_neg]
  refine ⟨fun Z => ι (px ax Z), ?_, ?_, fun Z W hZ hW h => ?_, fun A B C hA hB hC hb => ?_,
    fun X Y Z W hX hY hZ hW hXY hZW => ?_, ?_⟩
  · show ι (xc ax (toV ax.O ax.O)) = 0
    rw [toV_O ax, xc_zero ax, map_zero]
  · show ι (xc ax (eV ax)) = 1
    rw [← coe_oneG ax, (coords_x ax 1).1, map_one]
  · rw [eq_of_mem_x ax hZ, eq_of_mem_x ax hW, hinj h]
  · rw [eq_of_mem_x ax hA, eq_of_mem_x ax hB, eq_of_mem_x ax hC, between_iff_lt] at hb
    rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hmono h1, hmono h2⟩
    · exact Or.inr ⟨hmono h1, hmono h2⟩
  · rw [← len_eq_iff ax hXY hZW, len_axis ax hX hY, len_axis ax hZ hW, ← map_sub, ← map_sub,
      ← habs, ← habs]
    exact hinj.eq_iff.symm
  · -- the image of `ι` is a subfield closed under `√(1 + w²)`
    have hS : ∀ w ∈ (ι : G ax →+* ℝ).fieldRange, Real.sqrt (1 + w ^ 2) ∈
        (ι : G ax →+* ℝ).fieldRange := by
      intro w hw
      obtain ⟨t, rfl⟩ := RingHom.mem_fieldRange.1 hw
      obtain ⟨h, hh, e⟩ := pythagorean ax t
      refine RingHom.mem_fieldRange.2 ⟨h, ?_⟩
      have h0 : 0 ≤ ι h := by
        have := OrderHomClass.mono ι (le_of_lt hh); rwa [map_zero] at this
      have e2 : ι h * ι h = 1 + (ι t) ^ 2 := by
        rw [← map_mul, e, map_add, map_one, map_mul, sq]
      show ι h = _
      conv_lhs => rw [← Real.sqrt_mul_self h0]
      rw [e2]
      rfl
    intro ω hω
    obtain ⟨t, rfl⟩ := RingHom.mem_fieldRange.1 (Omega_le_of_closed _ hS hω)
    refine ⟨ofV (t : V ax), t.2, ?_⟩
    show ι (xc ax (toV ax.O (ofV (t : V ax)))) = ι t
    rw [toV_ofV, (coords_x ax t).1]

end RealNorm

end Pas

/-! ### The planes of a geometry of space -/

section SpacePlanes

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [HasSegCong P] [HasAngCong P]

/-- **Axiom V holds in every plane of a geometry of space** (with the congruence of space). -/
theorem planeArchimedes [hO : SpaceOrder P L Pl] [hV : Archimedes P L] (α : Pl) :
    Archimedes {A : P // A ∈ α} {a : L // LiesInPlane (Point := P) a α} where
  toLineOrder := (planeOrder (L := L) α).toLineOrder
  ax_V := by
    intro A B h1 h2 h3
    obtain ⟨n, hn⟩ := hV.ax_V (fun n => (A n : P)) (B : P) h1 h2 h3
    exact ⟨n, hn⟩

/-- In a geometry of space, a point of a plane lies on some line (I 7: a point outside the plane). -/
theorem exists_line_through_of_mem [SpaceConnection P L Pl] {α : Pl} {X : P} (hX : X ∈ α) :
    ∃ l : L, X ∈ l := by
  obtain ⟨A, B, C, D, h⟩ := SpaceConnection.ax_I7_space (Point := P) (Line := L) (Plane := Pl)
  have hW : ∃ W : P, W ≠ X := by
    by_contra hno
    push_neg at hno
    exact h ⟨α, by rw [hno A]; exact hX, by rw [hno B]; exact hX, by rw [hno C]; exact hX,
      by rw [hno D]; exact hX⟩
  obtain ⟨W, hW⟩ := hW
  obtain ⟨l, -, hl⟩ := exists_line (Line := L) hW
  exact ⟨l, hl⟩

/-- In a geometry of space having a plane, every line lies in a plane. -/
theorem exists_plane_of_line [SpaceConnection P L Pl] (α0 : Pl) (ℓ : L) :
    ∃ α : Pl, LiesInPlane (Point := P) ℓ α := by
  obtain ⟨X, Y, Z, -, -, -, hn⟩ := SpaceConnection.ax_I7_plane (Point := P) (Line := L) α0
  have hW : ∃ W : P, W ∉ ℓ := by
    by_contra hno
    push_neg at hno
    exact hn ⟨ℓ, hno X, hno Y, hno Z⟩
  obtain ⟨W, hW⟩ := hW
  obtain ⟨α, hα, -⟩ := exists_plane_line_point (Pl := Pl) hW
  exact ⟨α, hα⟩

/-- **The correspondence of § 17 for any line of a geometry of space** (groups I–V, with a plane):
as `Pas.exists_real_coord_norm`, through the restriction of the geometry to a plane through the
line. -/
theorem exists_real_coord_space [hC : SpaceCongruence P L Pl] [hP : SpaceParallels P L Pl]
    [hV : Archimedes P L] (α0 : Pl) (ℓ : L) {O E : P} (hO : O ∈ ℓ) (hE : E ∈ ℓ) (hOE : O ≠ E) :
    ∃ f : P → ℝ, f O = 0 ∧ f E = 1 ∧ (∀ Z W : P, Z ∈ ℓ → W ∈ ℓ → f Z = f W → Z = W) ∧
      (∀ A B C : P, A ∈ ℓ → B ∈ ℓ → C ∈ ℓ → Between A B C →
        (f A < f B ∧ f B < f C) ∨ (f C < f B ∧ f B < f A)) ∧
      (∀ X Y Z W : P, X ∈ ℓ → Y ∈ ℓ → Z ∈ ℓ → W ∈ ℓ → X ≠ Y → Z ≠ W →
        (SegCong X Y Z W ↔ |f X - f Y| = |f Z - f W|)) ∧
      ∀ ω : ℝ, ω ∈ Omega → ∃ Z : P, Z ∈ ℓ ∧ f Z = ω := by
  classical
  obtain ⟨α, hℓα⟩ := exists_plane_of_line (L := L) α0 ℓ
  haveI := planeCongruence (L := L) (h := hC) α
  haveI := planeArchimedes (L := L) α
  obtain ⟨f, f0, f1, finj, fbet, fcong, fom⟩ :=
    Pas.exists_real_coord_norm (P := {A : P // A ∈ α}) (L := {a : L // LiesInPlane (Point := P) a α})
      ⟨ℓ, hℓα⟩ (O := ⟨O, hℓα O hO⟩) (E := ⟨E, hℓα E hE⟩) hO hE
      (fun e => hOE (congrArg Subtype.val e))
  let F : P → ℝ := fun Z => if h : Z ∈ α then f ⟨Z, h⟩ else 0
  have hF : ∀ Z (h : Z ∈ ℓ), F Z = f ⟨Z, hℓα Z h⟩ := fun Z h => by
    simp only [F, dif_pos (hℓα Z h)]
  refine ⟨F, by rw [hF O hO]; exact f0, by rw [hF E hE]; exact f1, fun Z W hZ hW h => ?_,
    fun A B C hA hB hC hb => ?_, fun X Y Z W hX hY hZ hW hXY hZW => ?_, fun ω hω => ?_⟩
  · rw [hF Z hZ, hF W hW] at h
    exact congrArg Subtype.val (finj _ _ hZ hW h)
  · rw [hF A hA, hF B hB, hF C hC]
    exact fbet ⟨A, _⟩ ⟨B, _⟩ ⟨C, _⟩ hA hB hC hb
  · rw [hF X hX, hF Y hY, hF Z hZ, hF W hW]
    exact fcong ⟨X, _⟩ ⟨Y, _⟩ ⟨Z, _⟩ ⟨W, _⟩ hX hY hZ hW (fun e => hXY (congrArg Subtype.val e))
      (fun e => hZW (congrArg Subtype.val e))
  · obtain ⟨Z, hZ, e⟩ := fom ω hω
    exact ⟨Z, hZ, by rw [hF (Z : P) hZ]; exact e⟩

/-- **Every plane of a geometry of space with I–IV has rectangular co-ordinates** over an ordered
field, in which the lines of the plane are exactly the solution sets of the linear equations. -/
theorem plane_coordinates_space [hC : SpaceCongruence P L Pl] [hP : SpaceParallels P L Pl]
    (α : Pl) :
    ∃ (K : Type u) (_ : Field K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K)
      (f : {A : P // A ∈ α} ≃ K × K),
      (∀ a : L, LiesInPlane (Point := P) a α → ∃ p q r : K, (p ≠ 0 ∨ q ≠ 0) ∧
        ∀ Z : {A : P // A ∈ α}, (Z : P) ∈ a ↔ p * (f Z).1 + q * (f Z).2 + r = 0) ∧
      (∀ p q r : K, (p ≠ 0 ∨ q ≠ 0) → ∃ a : L, LiesInPlane (Point := P) a α ∧
        ∀ Z : {A : P // A ∈ α}, (Z : P) ∈ a ↔ p * (f Z).1 + q * (f Z).2 + r = 0) := by
  haveI := planeCongruence (L := L) (h := hC) α
  obtain ⟨X, Y, Z, hX, hY, -, hn⟩ := SpaceConnection.ax_I7_plane (Point := P) (Line := L) α
  have hXY : X ≠ Y := (ne_of_not_collinear (L := L) hn (exists_line_through_of_mem (L := L) hY)).1
  obtain ⟨ax, -, -⟩ := Pas.exists_axes (P := {A : P // A ∈ α})
    (L := {a : L // LiesInPlane (Point := P) a α}) (O := ⟨X, hX⟩) (E := ⟨Y, hY⟩)
    (fun e => hXY (congrArg Subtype.val e))
  refine ⟨Pas.G ax, inferInstance, inferInstance, inferInstance,
    Equiv.ofBijective _ (Pas.coords_bijective ax), fun a ha => ?_, fun p q r hpq => ?_⟩
  · obtain ⟨p, q, r, hpq, h⟩ := Pas.exists_line_eq ax ⟨a, ha⟩
    exact ⟨p, q, r, hpq, fun Z => h Z⟩
  · obtain ⟨a, h⟩ := Pas.exists_line_of_eq ax hpq r
    exact ⟨a.1, a.2, fun Z => h Z⟩

end SpacePlanes

end HilbertFoundations
