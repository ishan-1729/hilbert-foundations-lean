import HilbertFoundations.PascalAux2

/-!
# Helper module for `Pascal.lean`: the rotations about a point

This module contains no unit of Hilbert's text. Plane geometry with I 1–2, II, III, IV.

* **Three reflections** (`refl_three`): the product of the reflections in three lines through a
  point `O` is the reflection in a line through `O`; the product of two such reflections is never a
  reflection (`refl_mul_ne_refl`).
* **Rotations** (`rot O`): the products of two reflections in lines through `O`; they form a
  *commutative* group, conjugation by a reflection inverts them, and a rotation is determined by the
  image of one point other than `O`.
* **Axes**: a line `x` through `O` and the perpendicular `y` at `O` (the points equidistant from two
  points of `x` symmetric about `O`); the reflection in `x` is the identity on `x` and the negation
  on `y`, and conversely; a rotation `J` carries `x` onto `y`, and `J * J` is the half-turn about
  `O`, i.e. the negation of vectors.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Pas

universe u v

section Rotations

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable {O : P}

theorem refl_inv (l : L) : (refl (P := P) l)⁻¹ = refl l :=
  inv_eq_of_mul_eq_one_right (refl_mul_self (L := L) l)

theorem refl_apply_eq_iff {l : L} {X Y : P} : refl l X = Y ↔ refl l Y = X := by
  constructor
  · rintro rfl; exact refl_refl (L := L) l X
  · rintro rfl; exact refl_refl (L := L) l Y

/-- Two reflections in lines through `O` never compose to a reflection. -/
theorem refl_mul_ne_refl {a b c : L} (ha : O ∈ a) (hb : O ∈ b) (_hc : O ∈ c) :
    refl (P := P) a * refl b ≠ refl c := by
  intro h
  obtain ⟨X0, X1, hX01, hX0c, hX1c⟩ := exists_two_points (Point := P) c
  obtain ⟨X, hXc, hXO⟩ : ∃ X, X ∈ c ∧ X ≠ O := by
    by_cases e : X0 = O
    · exact ⟨X1, hX1c, fun e' => hX01 (e.trans e'.symm)⟩
    · exact ⟨X0, hX0c, e⟩
  have hfix : (refl (P := P) a * refl (P := P) b) X = X := by rw [h]; exact refl_fix hXc
  have e1 : refl (P := P) b X = refl (P := P) a X := by
    have := congrArg (refl (P := P) a) hfix
    simp only [Equiv.Perm.mul_apply, refl_refl] at this
    exact this
  -- `a = b`
  have hab : a = b := by
    by_cases hY : refl (P := P) a X = X
    · have hXa : X ∈ a := refl_fix_iff.1 hY
      have hXb : X ∈ b := refl_fix_iff.1 (e1.trans hY)
      exact line_unique hXO.symm ha hXa hb hXb
    · obtain ⟨m, hm, -, -⟩ := exists_eqd (L := L) (Ne.symm hY)
      have sub : ∀ (d : L), O ∈ d → refl (P := P) d X = refl (P := P) a X → d = m := by
        intro d hd hdX
        have hXd : X ∉ d := fun h => hY (by rw [← hdX, refl_fix h])
        obtain ⟨Z0, Z1, hZ01, hZ0, hZ1⟩ := exists_two_points (Point := P) d
        obtain ⟨Z, hZd, hZO⟩ : ∃ Z, Z ∈ d ∧ Z ≠ O := by
          by_cases e : Z0 = O
          · exact ⟨Z1, hZ1, fun e' => hZ01 (e.trans e'.symm)⟩
          · exact ⟨Z0, hZ0, e⟩
        have inm : ∀ W : P, W ∈ d → W ∈ m := by
          intro W hW
          rw [hm]
          have hWX : W ≠ X := fun e => hXd (e ▸ hW)
          have hσX : refl (P := P) d X ∉ d := fun h => hXd (by
            have := refl_fix h; rw [refl_refl] at this; exact this ▸ h)
          have hWY : W ≠ refl (P := P) a X := fun e => hσX (by rw [hdX]; exact e ▸ hW)
          refine ⟨hWX, hWY, ?_⟩
          have := refl_isom (P := P) d W X hWX
          rw [refl_fix hW, hdX] at this
          exact this
        exact line_unique hZO.symm hd hZd (inm O hd) (inm Z hZd)
      exact (sub a ha rfl).trans (sub b hb e1).symm
  subst hab
  rw [refl_mul_self] at h
  exact refl_ne_one (P := P) c h.symm

/-- **The theorem of the three reflections**: the product of the reflections in three lines
through `O` is the reflection in a line through `O`. -/
theorem refl_three {a b c : L} (ha : O ∈ a) (hb : O ∈ b) (hc : O ∈ c) :
    ∃ d : L, O ∈ d ∧ refl (P := P) a * refl b * refl c = refl d := by
  obtain ⟨X0, X1, hX01, hX0c, hX1c⟩ := exists_two_points (Point := P) c
  obtain ⟨X, hXc, hXO⟩ : ∃ X, X ∈ c ∧ X ≠ O := by
    by_cases e : X0 = O
    · exact ⟨X1, hX1c, fun e' => hX01 (e.trans e'.symm)⟩
    · exact ⟨X0, hX0c, e⟩
  have hc' : c = line (Line := L) O X (Ne.symm hXO) := eq_line (Ne.symm hXO) hc hXc
  set φ := refl (P := P) a * refl b * refl c
  have hφ : φ ∈ isom (L := L) := (isom (L := L)).mul_mem ((isom (L := L)).mul_mem
    (refl_isom (P := P) a) (refl_isom (P := P) b)) (refl_isom (P := P) c)
  have hφO : φ O = O := by simp only [φ, Equiv.Perm.mul_apply, refl_fix ha, refl_fix hb, refl_fix hc]
  by_cases hX : φ X = X
  · rcases isom_fix2 hφ (Ne.symm hXO) hφO hX with h | h
    · exfalso
      have : refl (P := P) a * refl b = refl c := by
        rw [← mul_one (refl (P := P) a * refl b), ← refl_mul_self (L := L) c, ← mul_assoc]
        show φ * refl c = refl c
        rw [h, one_mul]
      exact refl_mul_ne_refl ha hb hc this
    · exact ⟨c, hc, by rw [h, ← hc']⟩
  · have sOX : SegCong O X O (φ X) := by have := hφ O X (Ne.symm hXO); rwa [hφO] at this
    obtain ⟨d, hd, hdX, -⟩ := exists_eqd (L := L) (Ne.symm hX)
    have hOd : O ∈ d := by
      rw [hd]
      exact ⟨Ne.symm hXO, fun e => hXO (φ.injective (e.symm.trans hφO.symm)), sOX⟩
    refine ⟨d, hOd, ?_⟩
    set ψ := refl (P := P) d * φ
    have hψ : ψ ∈ isom (L := L) := (isom (L := L)).mul_mem (refl_isom (P := P) d) hφ
    have hψO : ψ O = O := by simp only [ψ, Equiv.Perm.mul_apply, hφO, refl_fix hOd]
    have hψX : ψ X = X := by
      simp only [ψ, Equiv.Perm.mul_apply]
      exact refl_apply_eq_iff.1 hdX
    rcases isom_fix2 hψ (Ne.symm hXO) hψO hψX with h | h
    · have := eq_inv_of_mul_eq_one_right h
      rw [this, refl_inv]
    · exfalso
      rw [← hc'] at h
      have h2 : refl (P := P) d * (refl a * refl b) = 1 := by
        have : refl (P := P) d * (refl a * refl b) * refl c = 1 * refl c := by
          rw [one_mul]; simp only [ψ, φ, mul_assoc] at h ⊢; exact h
        exact mul_right_cancel this
      have h3 : refl (P := P) a * refl b = refl d := by
        rw [eq_inv_of_mul_eq_one_right h2, refl_inv]
      exact refl_mul_ne_refl ha hb hOd h3

/-- The **rotations** about `O`: products of two reflections in lines through `O`. -/
def rot (O : P) : Subgroup (Equiv.Perm P) where
  carrier := {ρ | ρ = 1 ∨ ∃ a b : L, O ∈ a ∧ O ∈ b ∧ ρ = refl (P := P) a * refl b}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro ρ ρ' (rfl | ⟨a, b, ha, hb, rfl⟩) (rfl | ⟨c, e, hc, he, rfl⟩)
    · exact Or.inl (one_mul 1)
    · rw [one_mul]; exact Or.inr ⟨c, e, hc, he, rfl⟩
    · rw [mul_one]; exact Or.inr ⟨a, b, ha, hb, rfl⟩
    · obtain ⟨d, hd, e1⟩ := refl_three (L := L) hb hc he
      exact Or.inr ⟨a, d, ha, hd, by rw [← e1]; simp only [mul_assoc]⟩
  inv_mem' := by
    rintro ρ (rfl | ⟨a, b, ha, hb, rfl⟩)
    · exact Or.inl inv_one
    · exact Or.inr ⟨b, a, hb, ha, by rw [mul_inv_rev, refl_inv, refl_inv]⟩

theorem refl_mul_mem_rot {a b : L} (ha : O ∈ a) (hb : O ∈ b) :
    refl (P := P) a * refl b ∈ rot (L := L) O := Or.inr ⟨a, b, ha, hb, rfl⟩

/-- A rotation as `refl b * refl c` with a prescribed first line `b` through `O`. -/
theorem rot_eq_refl_mul {ρ : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) O) {b : L} (hb : O ∈ b) :
    ∃ c : L, O ∈ c ∧ ρ = refl (P := P) b * refl c := by
  rcases hρ with rfl | ⟨a, e, ha, he, rfl⟩
  · exact ⟨b, hb, (refl_mul_self (L := L) b).symm⟩
  · obtain ⟨c, hc, e1⟩ := refl_three (L := L) hb ha he
    refine ⟨c, hc, ?_⟩
    rw [← e1, ← mul_assoc, ← mul_assoc, refl_mul_self, one_mul]

/-- **Rotations about a point commute.** -/
theorem rot_comm {ρ ρ' : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) O) (hρ' : ρ' ∈ rot (L := L) O) :
    ρ * ρ' = ρ' * ρ := by
  rcases hρ with rfl | ⟨a, b, ha, hb, rfl⟩
  · rw [one_mul, mul_one]
  obtain ⟨f, hf, rfl⟩ := rot_eq_refl_mul hρ' hb
  obtain ⟨g, hg, e1⟩ := refl_three (L := L) hf ha hb
  have e2 : refl (P := P) b * refl a * refl f = refl g := by
    have := congrArg (·⁻¹) e1
    simp only [mul_inv_rev, refl_inv] at this
    rw [← this, mul_assoc]
  calc refl (P := P) a * refl b * (refl b * refl f) = refl (P := P) a * refl f := by
        rw [mul_assoc, ← mul_assoc (refl (P := P) b), refl_mul_self, one_mul]
    _ = refl (P := P) b * (refl b * refl a * refl f) := by
        rw [← mul_assoc, ← mul_assoc, refl_mul_self, one_mul]
    _ = refl (P := P) b * refl f * (refl a * refl b) := by
        rw [e2, ← e1]; simp only [mul_assoc]

/-- Conjugation by a reflection in a line through `O` inverts rotations. -/
theorem refl_conj_rot {ρ : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) O) {x : L} (hx : O ∈ x) :
    refl (P := P) x * ρ * refl x = ρ⁻¹ := by
  rcases hρ with rfl | ⟨a, b, ha, hb, rfl⟩
  · rw [mul_one, refl_mul_self, inv_one]
  obtain ⟨g, hg, e1⟩ := refl_three (L := L) hx ha hb
  have e2 : refl (P := P) b * refl a * refl x = refl g := by
    have := congrArg (·⁻¹) e1
    simp only [mul_inv_rev, refl_inv] at this
    rw [← this, mul_assoc]
  rw [← mul_assoc, e1, ← e2, mul_assoc, refl_mul_self, mul_one, mul_inv_rev, refl_inv, refl_inv]

theorem rot_ne_refl {ρ : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) O) {c : L} (hc : O ∈ c) :
    ρ ≠ refl c := by
  rcases hρ with rfl | ⟨a, b, ha, hb, rfl⟩
  · exact (refl_ne_one (P := P) c).symm
  · exact refl_mul_ne_refl ha hb hc

theorem rot_isom {ρ : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) O) : ρ ∈ isom (L := L) := by
  rcases hρ with rfl | ⟨a, b, ha, hb, rfl⟩
  · exact (isom (L := L)).one_mem
  · exact (isom (L := L)).mul_mem (refl_isom (P := P) a) (refl_isom (P := P) b)

theorem rot_fix {ρ : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) O) : ρ O = O := by
  rcases hρ with rfl | ⟨a, b, ha, hb, rfl⟩
  · rfl
  · simp only [Equiv.Perm.mul_apply, refl_fix ha, refl_fix hb]

/-- A rotation is determined by the image of one point other than `O`. -/
theorem rot_ext {ρ ρ' : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) O) (hρ' : ρ' ∈ rot (L := L) O) {X : P}
    (hX : X ≠ O) (h : ρ X = ρ' X) : ρ = ρ' := by
  have hm : ρ'⁻¹ * ρ ∈ rot (L := L) O := (rot (L := L) O).mul_mem ((rot (L := L) O).inv_mem hρ') hρ
  rcases isom_fix2 (rot_isom hm) (Ne.symm hX)
    (by rw [Equiv.Perm.mul_apply, rot_fix hρ, Equiv.Perm.inv_eq_iff_eq, rot_fix hρ'])
    (by rw [Equiv.Perm.mul_apply, h, Equiv.Perm.inv_eq_iff_eq]) with e | e
  · have := congrArg (ρ' * ·) e
    simpa using this
  · exact absurd e (rot_ne_refl hm (mem_line_left _))

/-- For `X`, `Y` at the same distance from `O` there is a rotation taking `X` to `Y`. -/
theorem exists_rot {x : L} (hx : O ∈ x) {X Y : P} (hXx : X ∈ x) (hXO : X ≠ O) (hYO : Y ≠ O)
    (h : SegCong O X O Y) : ∃ ρ ∈ rot (L := L) O, ρ X = Y := by
  by_cases e : X = Y
  · exact ⟨1, (rot (L := L) O).one_mem, e⟩
  obtain ⟨d, hd, hdX, -⟩ := exists_eqd (L := L) e
  have hOd : O ∈ d := (hd O).2 ⟨Ne.symm hXO, Ne.symm hYO, h⟩
  exact ⟨refl d * refl x, refl_mul_mem_rot hOd hx, by
    simp only [Equiv.Perm.mul_apply, refl_fix hXx, hdX]⟩

end Rotations

section AxesSec

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]

/-- **Rectangular axes**: an origin `O`, a unit point `E`, the line `x = OE`, the perpendicular `y`
at `O` with the point `F` at the distance `OE`, and the rotation `J` taking `E` to `F`. -/
structure Axes (P : Type u) (L : Type v) [HasLines P L] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [PlaneCongruence P L] [PlaneParallels P L] where
  O : P
  E : P
  F : P
  x : L
  y : L
  J : Equiv.Perm P
  hOE : O ≠ E
  hOF : O ≠ F
  hOx : O ∈ x
  hEx : E ∈ x
  hOy : O ∈ y
  hFy : F ∈ y
  hxy : ∀ Z : P, Z ∈ x → Z ∈ y → Z = O
  sOF : SegCong O E O F
  reflx_y : ∀ v : P, v ∈ y → refl x v = ht (L := L) O v
  refly_x : ∀ v : P, v ∈ x → refl y v = ht (L := L) O v
  hJ : J ∈ rot (L := L) O
  JE : J E = F
  Jx : ∀ v : P, v ∈ x → J v ∈ y
  JJ : J * J = ht (L := L) O
  htO : ht (L := L) O ∈ rot (L := L) O

include hC hP

/-- An isometry fixing `O` and keeping a point `v ≠ O` on its line through `O` fixes `v` or sends
it to the symmetric point. -/
theorem isom_on_line {O : P} {f : Equiv.Perm P} (hf : f ∈ isom (L := L)) (hfO : f O = O) {v : P}
    (hv : v ≠ O) {l : L} (hO : O ∈ l) (hvl : v ∈ l) (hfv : f v ∈ l) :
    f v = v ∨ f v = ht (L := L) O v := by
  have s := hf O v (Ne.symm hv)
  rw [hfO] at s
  have hfvO : f v ≠ O := fun e => hv (f.injective (e.trans hfO.symm))
  rcases mem_ray_or_between (L := L) (collinear_of_mem hO hvl hfv) hv hfvO with hr | hb
  · left
    exact eq_of_segCong_ray (L := L) (Ne.symm hv) hr (mem_ray_self' (L := L) hv) s
      (segCong_refl (Line := L) (Ne.symm hv))
  · right
    exact ((ht_eq_iff (L := L) hv).2 ⟨hb, s⟩).symm

/-- Isometries map the line through two points into the line through their images. -/
theorem isom_mem_line {f : Equiv.Perm P} (hf : f ∈ isom (L := L)) {A B Z : P} (hAB : A ≠ B)
    {l m : L} (hA : A ∈ l) (hB : B ∈ l) (hZ : Z ∈ l) (hA' : f A ∈ m) (hB' : f B ∈ m) : f Z ∈ m :=
  mem_of_collinear (isom_collinear hf (collinear_of_mem hA hB hZ)) (f.injective.ne hAB) hA' hB'

theorem exists_axes {O E : P} (hOE : O ≠ E) : ∃ ax : Axes P L, ax.O = O ∧ ax.E = E := by
  set E' := ht (L := L) O E
  have hEO : E ≠ O := Ne.symm hOE
  have hE'O : E' ≠ O := htp_ne hEO
  have hsE := (ht_eq_iff (L := L) hEO).1 rfl
  have hEE' : E ≠ E' := ne13_of_between (Line := L) hsE.1
  obtain ⟨y, hy, hyE, -⟩ := exists_eqd (L := L) hEE'
  have hOy : O ∈ y := (hy O).2 ⟨hOE, Ne.symm hE'O, hsE.2⟩
  have hEy : E ∉ y := fun h => ((hy E).1 h).1 rfl
  set x := line (Line := L) O E hOE
  have hOx : O ∈ x := mem_line_left hOE
  have hEx : E ∈ x := mem_line_right hOE
  have hE'x : E' ∈ x := mem_right_of_between hsE.1 hEx hOx
  have hxy : ∀ Z : P, Z ∈ x → Z ∈ y → Z = O := by
    intro Z hZx hZy
    by_contra hZO
    have : x = y := line_unique (Ne.symm hZO) hOx hZx hOy hZy
    exact hEy (this ▸ hEx)
  have hσx := refl_isom (P := P) x
  have hσy := refl_isom (P := P) y
  have reflx_y : ∀ v : P, v ∈ y → refl x v = ht (L := L) O v := by
    intro v hv
    by_cases hvO : v = O
    · subst hvO; rw [refl_fix hOx, ht_self]
    have hσv : refl x v ∈ y := by
      obtain ⟨hvE, hvE', sv⟩ := (hy v).1 hv
      have s1 := hσx v E hvE
      have s2 := hσx v E' hvE'
      rw [refl_fix hEx] at s1
      rw [refl_fix hE'x] at s2
      have hσvE : refl x v ≠ E := fun e => hvE (by
        have := congrArg (refl (P := P) x) e; rwa [refl_refl, refl_fix hEx] at this)
      have hσvE' : refl x v ≠ E' := fun e => hvE' (by
        have := congrArg (refl (P := P) x) e; rwa [refl_refl, refl_fix hE'x] at this)
      refine (hy _).2 ⟨hσvE, hσvE', ?_⟩
      exact segCong_trans (L := L) hσvE hvE hσvE'
        (segCong_symm (L := L) hvE hσvE s1) (segCong_trans (L := L) hvE hvE' hσvE' sv s2)
    rcases isom_on_line hσx (refl_fix hOx) hvO hOy hv hσv with h | h
    · exact absurd (hxy v (refl_fix_iff.1 h) hv) hvO
    · exact h
  have refly_x : ∀ v : P, v ∈ x → refl y v = ht (L := L) O v := by
    intro v hv
    by_cases hvO : v = O
    · subst hvO; rw [refl_fix hOy, ht_self]
    have hσv : refl y v ∈ x := isom_mem_line hσy hOE hOx hEx hv (by rw [refl_fix hOy]; exact hOx)
      (by rw [hyE]; exact hE'x)
    rcases isom_on_line hσy (refl_fix hOy) hvO hOx hv hσv with h | h
    · exact absurd (hxy v hv (refl_fix_iff.1 h)) hvO
    · exact h
  -- the half-turn about `O` is a rotation
  have hxy_ht : refl (P := P) x * refl y = ht (L := L) O := by
    set ψ := refl (P := P) x * refl y * ht (L := L) O
    have hψ : ψ ∈ isom (L := L) := (isom (L := L)).mul_mem ((isom (L := L)).mul_mem hσx hσy)
      (ht_isom O)
    have hψO : ψ O = O := by simp only [ψ, Equiv.Perm.mul_apply, ht_self, refl_fix hOy,
      refl_fix hOx]
    have hψE : ψ E = E := by
      simp only [ψ, Equiv.Perm.mul_apply]
      rw [show refl (P := P) y (ht (L := L) O E) = E from refl_apply_eq_iff.1 hyE, refl_fix hEx]
    rcases isom_fix2 hψ hOE hψO hψE with h | h
    · rw [eq_inv_of_mul_eq_one_left h, ht_inv]
    · exfalso
      have h1 : refl (P := P) y * ht (L := L) O = 1 := by
        have : refl (P := P) x * (refl (P := P) y * ht (L := L) O) = refl x * 1 := by
          rw [mul_one, ← mul_assoc]; exact h
        exact mul_left_cancel this
      have h2 : ht (L := L) O = refl y := by
        rw [eq_inv_of_mul_eq_one_right h1, refl_inv]
      obtain ⟨Y0, Y1, hY01, hY0, hY1⟩ := exists_two_points (Point := P) y
      obtain ⟨Z, hZy, hZO⟩ : ∃ Z, Z ∈ y ∧ Z ≠ O := by
        by_cases e : Y0 = O
        · exact ⟨Y1, hY1, fun e' => hY01 (e.trans e'.symm)⟩
        · exact ⟨Y0, hY0, e⟩
      have := refl_fix hZy
      rw [← h2] at this
      exact hZO (ht_fix_iff.1 this)
  have htO : ht (L := L) O ∈ rot (L := L) O := by rw [← hxy_ht]; exact refl_mul_mem_rot hOx hOy
  -- the point `F`
  obtain ⟨Y0, Y1, hY01, hY0, hY1⟩ := exists_two_points (Point := P) y
  obtain ⟨Z, hZy, hZO⟩ : ∃ Z, Z ∈ y ∧ Z ≠ O := by
    by_cases e : Y0 = O
    · exact ⟨Y1, hY1, fun e' => hY01 (e.trans e'.symm)⟩
    · exact ⟨Y0, hY0, e⟩
  obtain ⟨F, hFr, sF⟩ := segCong_layoff (L := L) hOE (Ne.symm hZO)
  have hFO : F ≠ O := ne_of_mem_ray hFr
  have hFy : F ∈ y := mem_of_collinear (collinear_of_mem_ray hFr) (Ne.symm hZO) hOy hZy
  have hEF : E ≠ F := fun e => hEy (e ▸ hFy)
  obtain ⟨d, hd, hdE, -⟩ := exists_eqd (L := L) hEF
  have hOd : O ∈ d := (hd O).2 ⟨hOE, Ne.symm hFO, sF⟩
  set J := refl (P := P) d * refl x
  have hJ : J ∈ rot (L := L) O := refl_mul_mem_rot hOd hOx
  have JE : J E = F := by simp only [J, Equiv.Perm.mul_apply, refl_fix hEx, hdE]
  have hJi := rot_isom hJ
  have Jx : ∀ v : P, v ∈ x → J v ∈ y := fun v hv =>
    isom_mem_line hJi hOE hOx hEx hv (by rw [rot_fix hJ]; exact hOy) (by rw [JE]; exact hFy)
  have JJ : J * J = ht (L := L) O := by
    refine rot_ext ((rot (L := L) O).mul_mem hJ hJ) htO hEO ?_
    simp only [Equiv.Perm.mul_apply, JE]
    simp only [J, Equiv.Perm.mul_apply]
    rw [reflx_y F hFy]
    have hconj := isom_conj_ht (refl_isom (P := P) d) O
    rw [refl_fix hOd] at hconj
    have := congrArg (fun g : Equiv.Perm P => g (refl (P := P) d F)) hconj
    simp only [Equiv.Perm.mul_apply, refl_inv, refl_refl] at this
    rw [this, show refl (P := P) d F = E from refl_apply_eq_iff.1 hdE]
  exact ⟨⟨O, E, F, x, y, J, hOE, Ne.symm hFO, hOx, hEx, hOy, hFy, hxy, sF, reflx_y, refly_x, hJ,
    JE, Jx, JJ, htO⟩, rfl, rfl⟩

end AxesSec

end Pas

end HilbertFoundations
