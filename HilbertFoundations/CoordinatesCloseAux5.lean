import HilbertFoundations.CoordinatesCloseAux4
import HilbertFoundations.Areas

/-!
# Helper for § 17 (ideal elements): the length of space in co-ordinates

Helper module of `CoordinatesClose.lean` (unit `s17.ideal`). A geometry of space with I–V and a
plane `α` with rectangular axes has co-ordinates `f : P ≃ K³` over the field of segments `K` of `α`
(CoordinatesCloseAux2/3). Here the length `slen` of the segments of space is computed in these
co-ordinates:

* it is invariant under translations (`clen_translate`: the opposite sides of a parallelogram are
  congruent, `parallelogram_iff` of Areas.lean in the plane of the parallelogram);
* it is homogeneous on every line (`cnorm_smul`, an additive positive map of an archimedean field);
* its square is a quadratic form in every plane (`cnorm_planar`, the theorem of Pythagoras
  `slen_pyth` on the axes of the plane), hence a quadratic form (`quad_three`);
* after a linear change of co-ordinates the square of the length is `x² + y² + z²`
  (`exists_metric_coords`).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace SpaceCoord

open Module

universe u v w

/-! ## Functions that are quadratic forms on every plane -/

section QuadAlg

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]

theorem quad_pair (q : W → K)
    (hq : ∀ v w : W, ∃ a b c : K, ∀ x y : K,
      q (x • v + y • w) = a * (x * x) + b * (x * y) + c * (y * y))
    (v w : W) (x y : K) :
    q (x • v + y • w) = x * x * q v + x * y * (q (v + w) - q v - q w) + y * y * q w := by
  obtain ⟨a, b, c, h⟩ := hq v w
  have h10 := h 1 0
  have h01 := h 0 1
  have h11 := h 1 1
  simp only [one_smul, zero_smul, add_zero, zero_add, mul_one, mul_zero] at h10 h01 h11
  rw [h x y, h10, h01, h11]; ring

theorem quad_par (q : W → K)
    (hq : ∀ v w : W, ∃ a b c : K, ∀ x y : K,
      q (x • v + y • w) = a * (x * x) + b * (x * y) + c * (y * y))
    (v w : W) : q (v + w) + q (v - w) = 2 * q v + 2 * q w := by
  have h1 := quad_pair q hq v w 1 (-1)
  have e : (1 : K) • v + (-1 : K) • w = v - w := by
    rw [one_smul, neg_smul, one_smul, sub_eq_add_neg]
  rw [e] at h1
  linear_combination h1

theorem quad_frechet (q : W → K)
    (hq : ∀ v w : W, ∃ a b c : K, ∀ x y : K,
      q (x • v + y • w) = a * (x * x) + b * (x * y) + c * (y * y))
    (h2 : (2 : K) ≠ 0) (u v w : W) :
    q (u + v + w) = q (u + v) + q (u + w) + q (v + w) - q u - q v - q w := by
  have p1 := quad_par q hq (u + w) v
  have p2 := quad_par q hq (v + w) u
  have p3 := quad_par q hq w (u - v)
  have p4 := quad_par q hq u v
  have e1 : u + w + v = u + v + w := by abel
  have e2 : v + w + u = u + v + w := by abel
  have e3 : u + w - v = w + (u - v) := by abel
  have e4 : v + w - u = w - (u - v) := by abel
  rw [e1, e3] at p1
  rw [e2, e4] at p2
  have key : 2 * q (u + v + w) =
      2 * (q (u + v) + q (u + w) + q (v + w) - q u - q v - q w) := by
    linear_combination p1 + p2 - p3 - 2 * p4
  exact mul_left_cancel₀ h2 key

/-- **A function that is a quadratic form on every plane is a quadratic form**: its values on the
combinations of three vectors. -/
theorem quad_three (q : W → K)
    (hq : ∀ v w : W, ∃ a b c : K, ∀ x y : K,
      q (x • v + y • w) = a * (x * x) + b * (x * y) + c * (y * y))
    (h2 : (2 : K) ≠ 0) (e₁ e₂ e₃ : W) (x y z : K) :
    q (x • e₁ + y • e₂ + z • e₃) = x * x * q e₁ + y * y * q e₂ + z * z * q e₃ +
      x * y * (q (e₁ + e₂) - q e₁ - q e₂) + x * z * (q (e₁ + e₃) - q e₁ - q e₃) +
      y * z * (q (e₂ + e₃) - q e₂ - q e₃) := by
  have s : ∀ (t : K) (e : W), q (t • e) = t * t * q e := by
    intro t e
    have h := quad_pair q hq e e t 0
    rw [zero_smul, add_zero] at h
    rw [h]; ring
  rw [quad_frechet q hq h2, quad_pair q hq e₁ e₂ x y, quad_pair q hq e₁ e₃ x z,
    quad_pair q hq e₂ e₃ y z, s x e₁, s y e₂, s z e₃]
  ring

end QuadAlg

/-! ## Lines and planes in co-ordinates -/

section Coords

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsStrictOrderedRing K] {W : Type*}
  [AddCommGroup W] [Module K W]

/-- A co-ordinate system of a geometry of space: lines and planes go to lines and planes,
betweenness is that of the co-ordinates; the space of co-ordinates is not a line. -/
structure IsCoordSys (f : P ≃ AffPt K W) : Prop where
  line : ∀ ℓ : L, ∃ m : AffLine K W, ∀ X : P, X ∈ ℓ ↔ f X ∈ m
  plane : ∀ π : Pl, ∃ S : AffPlane K W, ∀ X : P, X ∈ π ↔ f X ∈ S
  btw : ∀ X Y Z : P, Between (f X) (f Y) (f Z) ↔ Between X Y Z
  nsm : ∀ d : AffPt K W, d ≠ 0 → ∃ s : AffPt K W, ∀ c : K, s ≠ c • d

variable {f : P ≃ AffPt K W} (H : IsCoordSys (L := L) (Pl := Pl) f)

include H

theorem mem_line_coord {A B : P} (hAB : A ≠ B) {ℓ : L} (hA : A ∈ ℓ) (hB : B ∈ ℓ) (X : P) :
    X ∈ ℓ ↔ ∃ r : K, f X = r • (f B - f A) + f A := by
  obtain ⟨m, hm⟩ := H.line ℓ
  have hne : f A ≠ f B := f.injective.ne hAB
  have e := m.eq_through hne ((hm A).1 hA) ((hm B).1 hB)
  rw [hm X, e]
  exact AffLine.mem_through_iff hne

theorem collinear_coord [Connection P L] {A B : P} (hAB : A ≠ B) (X : P) :
    Collinear (Line := L) A B X ↔ ∃ r : K, f X = r • (f B - f A) + f A := by
  constructor
  · rintro ⟨ℓ, hA, hB, hX⟩
    exact (mem_line_coord H hAB hA hB X).1 hX
  · intro h
    obtain ⟨ℓ, hA, hB⟩ := exists_line (Line := L) hAB
    exact ⟨ℓ, hA, hB, (mem_line_coord H hAB hA hB X).2 h⟩

theorem mem_plane_coord [Connection P L] {π : Pl} {A B C : P} (hAB : A ≠ B) (hA : A ∈ π)
    (hB : B ∈ π) (hC : C ∈ π) (hn : ¬Collinear (Line := L) A B C) (X : P) :
    X ∈ π ↔ ∃ r s : K, f X = r • (f B - f A) + s • (f C - f A) + f A := by
  obtain ⟨S, hS⟩ := H.plane π
  have hfA := (hS A).1 hA
  have hfB := (hS B).1 hB
  have hfC := (hS C).1 hC
  have hu : f B - f A ≠ 0 := sub_ne_zero.2 (f.injective.ne hAB).symm
  have hw : ∀ c : K, f C - f A ≠ c • (f B - f A) := fun c hc =>
    hn ((collinear_coord H hAB C).2 ⟨c, by rw [← hc, sub_add_cancel]⟩)
  have huS := AffPt.sub_mem_direction hfA hfB
  have hwS := AffPt.sub_mem_direction hfA hfC
  rw [hS X]
  constructor
  · intro hX
    have hxS := AffPt.sub_mem_direction hfA hX
    have hu' : (⟨f B - f A, huS⟩ : S.carrier.direction) ≠ 0 := fun h =>
      hu (congrArg Subtype.val h)
    have hw' : ∀ c : K, (⟨f C - f A, hwS⟩ : S.carrier.direction) ≠ c • ⟨f B - f A, huS⟩ :=
      fun c h => hw c (congrArg Subtype.val h)
    obtain ⟨a, b, hab⟩ := exists_comb S.finrank_direction hu' hw' ⟨f X - f A, hxS⟩
    have h3 : f X - f A = a • (f B - f A) + b • (f C - f A) := congrArg Subtype.val hab
    exact ⟨a, b, by rw [← h3, sub_add_cancel]⟩
  · rintro ⟨r, s, h⟩
    show f X ∈ S.carrier
    rw [h]
    exact AffPt.add_mem_of_mem_direction (S.carrier.direction.add_mem
      (S.carrier.direction.smul_mem r huS) (S.carrier.direction.smul_mem s hwS)) hfA

end Coords

/-- In `K³` no vector spans. -/
theorem exists_not_smul {K : Type*} [Field K] (d : AffPt K ((K × K) × K)) :
    ∃ s : AffPt K ((K × K) × K), ∀ c : K, s ≠ c • d := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c₁, h₁⟩ := hcon (AffPt.ofV ((1, 0), 0))
  obtain ⟨c₂, h₂⟩ := hcon (AffPt.ofV ((0, 1), 0))
  have a1 : (1 : K) = c₁ * (AffPt.toV d).1.1 := congrArg (fun v => (AffPt.toV v).1.1) h₁
  have a2 : (0 : K) = c₁ * (AffPt.toV d).1.2 := congrArg (fun v => (AffPt.toV v).1.2) h₁
  have b2 : (1 : K) = c₂ * (AffPt.toV d).1.2 := congrArg (fun v => (AffPt.toV v).1.2) h₂
  have hc1 : c₁ ≠ 0 := by
    rintro rfl
    rw [zero_mul] at a1
    exact one_ne_zero a1
  have h0 : (AffPt.toV d).1.2 = 0 := (mul_eq_zero.1 a2.symm).resolve_left hc1
  rw [h0, mul_zero] at b2
  exact one_ne_zero b2

/-! ## The length in co-ordinates -/

section Metric

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [HasSegCong P] [HasAngCong P] [hC : SpaceCongruence P L Pl] [hS : SpaceParallels P L Pl]
  [hA : Archimedes P L]

local notation "𝒫[" π "]" => {A : P // A ∈ π}
local notation "ℒ[" π "]" => {a : L // LiesInPlane (Point := P) a π}

-- (no local notation in `variable` binders: it makes the variable inaccessible)
variable (α : Pl) (ax : Pas.Axes {A : P // A ∈ α} {a : L // LiesInPlane (Point := P) a α})
variable {W : Type*} [AddCommGroup W] [Module (Pas.G ax) W] (f : P ≃ AffPt (Pas.G ax) W)

include hC hS hA

/-- The length of the segment with given co-ordinates of its extremities. -/
noncomputable def clen (a b : AffPt (Pas.G ax) W) : Pas.G ax :=
  slen α ax (f.symm a) (f.symm b)

/-- The length of a vector. -/
noncomputable def cnorm (v : AffPt (Pas.G ax) W) : Pas.G ax := clen α ax f 0 v

variable {f} (H : IsCoordSys (L := L) (Pl := Pl) f)

include H

/-- **The opposite sides of a parallelogram are congruent.** -/
theorem slen_parallelogram {A B C D : P} (hAB : A ≠ B) (t : AffPt (Pas.G ax) W)
    (hD : f D = f A + t) (hCt : f C = f B + t) (ht : ∀ c : Pas.G ax, t ≠ c • (f B - f A)) :
    slen α ax D C = slen α ax A B := by
  have ht0 : t ≠ 0 := fun e => ht 0 (by rw [e, zero_smul])
  have hDC : D ≠ C := fun e => hAB (by
    have h1 : f A + t = f B + t := by rw [← hD, ← hCt, e]
    exact f.injective (add_right_cancel h1))
  have hAD : A ≠ D := fun e => ht0 (by
    have h1 : f A = f A + t := by rw [← hD, e]
    have h2 := congrArg (fun z => z - f A) h1
    simpa using h2.symm)
  have hBC : B ≠ C := fun e => ht0 (by
    have h1 : f B = f B + t := by rw [← hCt, e]
    have h2 := congrArg (fun z => z - f B) h1
    simpa using h2.symm)
  have hnABD : ¬Collinear (Line := L) A B D := fun h => by
    obtain ⟨r, hr⟩ := (collinear_coord H hAB D).1 h
    rw [hD] at hr
    exact ht r (add_right_cancel ((add_comm t (f A)).trans hr))
  obtain ⟨π, hAπ, hBπ, hDπ⟩ := exists_plane (Plane := Pl) hnABD
  have hCπ : C ∈ π := (mem_plane_coord H hAB hAπ hBπ hDπ hnABD C).2
    ⟨1, 1, by rw [hCt, hD, one_smul, one_smul]; abel⟩
  obtain ⟨bx⟩ := exists_axes_in (P := P) (L := L) π
  have hpar : IsParallelogram (L := ℒ[π]) (⟨A, hAπ⟩ : 𝒫[π]) ⟨B, hBπ⟩ ⟨C, hCπ⟩ ⟨D, hDπ⟩ := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨l, h1, h2, h3⟩
      obtain ⟨r, hr⟩ := (collinear_coord H hAB C).1 ⟨l.1, h1, h2, h3⟩
      rw [hCt] at hr
      have h4 : r • (f B - f A) = f B + t - f A := eq_sub_of_add_eq hr.symm
      exact ht (r - 1) (by rw [sub_smul, one_smul, h4]; abel)
    · rintro ⟨X, ⟨l, h1, h2, h3⟩, ⟨m, k1, k2, k3⟩⟩
      obtain ⟨r, hr⟩ := (collinear_coord H hAB (X : P)).1 ⟨l.1, h1, h2, h3⟩
      obtain ⟨s, hs⟩ := (collinear_coord H hDC (X : P)).1 ⟨m.1, k1, k2, k3⟩
      have e : f C - f D = f B - f A := by rw [hCt, hD]; abel
      rw [e, hD] at hs
      have h3 : r • (f B - f A) + f A = (s • (f B - f A) + t) + f A := by
        rw [← hr, hs]; abel
      have h4 := add_right_cancel h3
      exact ht (r - s) (by rw [sub_smul, h4]; abel)
    · rintro ⟨X, ⟨l, h1, h2, h3⟩, ⟨m, k1, k2, k3⟩⟩
      obtain ⟨r, hr⟩ := (collinear_coord H hAD (X : P)).1 ⟨l.1, h1, h2, h3⟩
      obtain ⟨s, hs⟩ := (collinear_coord H hBC (X : P)).1 ⟨m.1, k1, k2, k3⟩
      have e1 : f D - f A = t := by rw [hD]; abel
      have e2 : f C - f B = t := by rw [hCt]; abel
      rw [e1] at hr
      rw [e2] at hs
      have h5 : r • t + f A = s • t + f B := hr.symm.trans hs
      have h6 : r • t = s • t + f B - f A := eq_sub_of_add_eq h5
      have hk : f B - f A = (r - s) • t := by rw [sub_smul, h6]; abel
      by_cases hrs : r = s
      · rw [hrs, sub_self, zero_smul] at hk
        exact hAB (f.injective (sub_eq_zero.1 hk).symm)
      · exact ht (r - s)⁻¹ (by
          rw [hk, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hrs), one_smul])
  obtain ⟨-, hco⟩ := (parallelogram_iff bx).1 hpar
  have hx : Pas.px bx ⟨C, hCπ⟩ = Pas.px bx ⟨D, hDπ⟩ + Pas.px bx ⟨B, hBπ⟩ - Pas.px bx ⟨A, hAπ⟩ :=
    congrArg Prod.fst hco
  have hy : Pas.py bx ⟨C, hCπ⟩ = Pas.py bx ⟨D, hDπ⟩ + Pas.py bx ⟨B, hBπ⟩ - Pas.py bx ⟨A, hAπ⟩ :=
    congrArg Prod.snd hco
  have hlen : Pas.len bx (⟨D, hDπ⟩ : 𝒫[π]) ⟨C, hCπ⟩ = Pas.len bx (⟨A, hAπ⟩ : 𝒫[π]) ⟨B, hBπ⟩ := by
    apply Areas.len_eq_of_sq bx
    rw [Pas.len_sq bx, Pas.len_sq bx, hx, hy]; ring
  have s : SegCong D C A B :=
    (Pas.len_eq_iff bx (P1 := (⟨D, hDπ⟩ : 𝒫[π])) (P2 := ⟨C, hCπ⟩) (Q1 := ⟨A, hAπ⟩)
      (Q2 := ⟨B, hBπ⟩) (fun e => hDC (congrArg Subtype.val e))
      (fun e => hAB (congrArg Subtype.val e))).1 hlen
  exact (slen_eq_iff α ax hDC hAB).2 s

theorem clen_parallelogram {a b t : AffPt (Pas.G ax) W} (hab : a ≠ b)
    (ht : ∀ c : Pas.G ax, t ≠ c • (b - a)) :
    clen α ax f (a + t) (b + t) = clen α ax f a b := by
  have hAB : f.symm a ≠ f.symm b := fun e => hab (f.symm.injective e)
  refine slen_parallelogram α ax H hAB t ?_ ?_ ?_
  · rw [f.apply_symm_apply, f.apply_symm_apply]
  · rw [f.apply_symm_apply, f.apply_symm_apply]
  · rw [f.apply_symm_apply, f.apply_symm_apply]; exact ht

/-- **The length is invariant under translations.** -/
theorem clen_translate (a b t : AffPt (Pas.G ax) W) :
    clen α ax f (a + t) (b + t) = clen α ax f a b := by
  by_cases hab : a = b
  · subst hab; simp [clen, slen_self]
  by_cases ht : ∀ c : Pas.G ax, t ≠ c • (b - a)
  · exact clen_parallelogram α ax H hab ht
  · push Not at ht
    obtain ⟨c, hc⟩ := ht
    obtain ⟨s, hs⟩ := H.nsm (b - a) (sub_ne_zero.2 (Ne.symm hab))
    have h1 := clen_parallelogram α ax H hab hs
    have hne : a + s ≠ b + s := fun e => hab (add_right_cancel e)
    have hts : ∀ c' : Pas.G ax, t - s ≠ c' • ((b + s) - (a + s)) := by
      intro c' h
      have e : b + s - (a + s) = b - a := by abel
      rw [e] at h
      exact hs (c - c') (by rw [sub_smul, ← hc, ← h]; abel)
    have h2 := clen_parallelogram α ax H hne hts
    have e1 : a + s + (t - s) = a + t := by abel
    have e2 : b + s + (t - s) = b + t := by abel
    rw [e1, e2] at h2
    rw [h2, h1]

theorem clen_eq_cnorm (a b : AffPt (Pas.G ax) W) : clen α ax f a b = cnorm α ax f (b - a) := by
  have h := clen_translate α ax H a b (-a)
  rw [add_neg_cancel, ← sub_eq_add_neg] at h
  exact h.symm

omit H in
theorem cnorm_zero : cnorm α ax f 0 = 0 := slen_self α ax _

omit H in
theorem cnorm_pos {v : AffPt (Pas.G ax) W} (hv : v ≠ 0) : 0 < cnorm α ax f v :=
  slen_pos α ax fun e => hv (f.symm.injective e).symm

omit H in
theorem cnorm_nonneg (v : AffPt (Pas.G ax) W) : 0 ≤ cnorm α ax f v := slen_nonneg α ax _ _

theorem cnorm_neg (v : AffPt (Pas.G ax) W) : cnorm α ax f (-v) = cnorm α ax f v := by
  have h := clen_translate α ax H 0 (-v) v
  rw [zero_add, neg_add_cancel] at h
  rw [cnorm, ← h]
  exact slen_comm α ax _ _

/-- **The length is homogeneous.** -/
theorem cnorm_smul (t : Pas.G ax) (v : AffPt (Pas.G ax) W) :
    cnorm α ax f (t • v) = |t| * cnorm α ax f v := by
  by_cases hv : v = 0
  · subst hv; rw [smul_zero, cnorm_zero, mul_zero]
  have key : ∀ s : Pas.G ax, 0 < s → cnorm α ax f (s • v) = s * cnorm α ax f v := by
    have := Pas.archimedean_G ax
    obtain ⟨ιK⟩ := Real.nonemptyOrderRingHom (Pas.G ax)
    let T : Pas.G ax → ℝ := fun s => ιK (cnorm α ax f (s • v))
    have hadd : ∀ s s' : Pas.G ax, 0 < s → 0 < s' → T (s + s') = T s + T s' := by
      intro s s' hs hs'
      have hsb : Sbtw (Pas.G ax) (0 : AffPt (Pas.G ax) W) (s • v) ((s + s') • v) := by
        have h := (sbtw_param_iff (V := W) (O := (0 : AffPt (Pas.G ax) W)) (d := v) hv 0 s
          (s + s')).2 (Or.inl ⟨hs, lt_add_of_pos_right s hs'⟩)
        rwa [zero_smul, add_zero, add_zero, add_zero] at h
      have hb : Between (f.symm 0) (f.symm (s • v)) (f.symm ((s + s') • v)) :=
        (H.btw _ _ _).1 (by
          rw [f.apply_symm_apply, f.apply_symm_apply, f.apply_symm_apply]; exact hsb)
      have e1 := slen_add α ax hb
      have e2 : slen α ax (f.symm (s • v)) (f.symm ((s + s') • v)) =
          cnorm α ax f (s' • v) := by
        have h := clen_translate α ax H 0 (s' • v) (s • v)
        rw [zero_add, ← add_smul, add_comm s' s] at h
        exact h
      have e3 : cnorm α ax f ((s + s') • v) = cnorm α ax f (s • v) + cnorm α ax f (s' • v) := by
        rw [← e2]; exact e1
      show ιK _ = ιK _ + ιK _
      rw [e3, map_add]
    have hpos : ∀ s : Pas.G ax, 0 < s → 0 < T s := fun s hs =>
      orderRingHom_pos ιK (cnorm_pos α ax (smul_ne_zero hs.ne' hv))
    intro s hs
    have h := additive_pos_eq_mul ιK T hadd hpos hs
    apply ιK.toRingHom.injective
    show ιK _ = ιK _
    rw [map_mul]
    have h' : ιK (cnorm α ax f (s • v)) = ιK s * ιK (cnorm α ax f ((1 : Pas.G ax) • v)) := h
    rwa [one_smul] at h'
  rcases lt_trichotomy t 0 with h | h | h
  · have h1 := key (-t) (neg_pos.2 h)
    rw [neg_smul, cnorm_neg α ax H] at h1
    rw [h1, abs_of_neg h]
  · subst h; rw [zero_smul, cnorm_zero, abs_zero, zero_mul]
  · rw [key t h, abs_of_pos h]

/-- **The theorem of Pythagoras in a plane through the origin**: two independent vectors `v`, `w`
span a plane in which `v` has a perpendicular `u`. -/
theorem cnorm_plane {v w : AffPt (Pas.G ax) W} (hv : v ≠ 0) (hw : ∀ c : Pas.G ax, w ≠ c • v) :
    ∃ (lam mu : Pas.G ax) (u : AffPt (Pas.G ax) W), w = lam • v + mu • u ∧
      ∀ x y : Pas.G ax, cnorm α ax f (x • v + y • u) * cnorm α ax f (x • v + y • u) =
        x * x * (cnorm α ax f v * cnorm α ax f v) + y * y * (cnorm α ax f u * cnorm α ax f u) := by
  obtain ⟨O, hfO⟩ : ∃ O : P, f O = 0 := ⟨f.symm 0, f.apply_symm_apply 0⟩
  obtain ⟨A, hfA⟩ : ∃ A : P, f A = v := ⟨f.symm v, f.apply_symm_apply v⟩
  obtain ⟨B, hfB⟩ : ∃ B : P, f B = w := ⟨f.symm w, f.apply_symm_apply w⟩
  have hOs : f.symm 0 = O := by rw [← hfO, f.symm_apply_apply]
  have hOA : O ≠ A := fun e => hv (by rw [← hfA, ← e, hfO])
  have hn : ¬Collinear (Line := L) O A B := fun h => by
    obtain ⟨r, hr⟩ := (collinear_coord H hOA B).1 h
    rw [hfO, hfA, hfB, sub_zero, add_zero] at hr
    exact hw r hr
  obtain ⟨π, hOπ, hAπ, hBπ⟩ := exists_plane (Plane := Pl) hn
  obtain ⟨bx, hbO, hbE⟩ := Pas.exists_axes (P := 𝒫[π]) (L := ℒ[π]) (O := ⟨O, hOπ⟩)
    (E := ⟨A, hAπ⟩) (fun e => hOA (congrArg Subtype.val e))
  have hOx : O ∈ (bx.x : L) := by
    have h := bx.hOx
    rw [hbO] at h
    exact h
  have hAx : A ∈ (bx.x : L) := by
    have h := bx.hEx
    rw [hbE] at h
    exact h
  have hOy : O ∈ (bx.y : L) := by
    have h := bx.hOy
    rw [hbO] at h
    exact h
  have hFy : (bx.F : P) ∈ (bx.y : L) := bx.hFy
  have hOF : O ≠ (bx.F : P) := fun e => bx.hOF (by rw [hbO]; exact Subtype.ext e)
  obtain ⟨u, hu⟩ : ∃ u : AffPt (Pas.G ax) W, f (bx.F : P) = u := ⟨_, rfl⟩
  have memx : ∀ X : P, X ∈ (bx.x : L) ↔ ∃ r : Pas.G ax, f X = r • v := by
    intro X
    rw [mem_line_coord H hOA hOx hAx X, hfO, hfA, sub_zero]
    simp only [add_zero]
  have memy : ∀ X : P, X ∈ (bx.y : L) ↔ ∃ r : Pas.G ax, f X = r • u := by
    intro X
    rw [mem_line_coord H hOF hOy hFy X, hfO, hu, sub_zero]
    simp only [add_zero]
  obtain ⟨r, s, hrs⟩ := (mem_plane_coord H hOA hOπ hAπ hBπ hn (bx.F : P)).1 bx.F.2
  rw [hfO, hfA, hfB, hu, sub_zero, sub_zero, add_zero] at hrs
  have hs : s ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at hrs
    have hFx : bx.F ∈ bx.x := (memx (bx.F : P)).2 ⟨r, by rw [hu, hrs]⟩
    exact bx.hOF (bx.hxy bx.F hFx bx.hFy).symm
  have hwu : w = (-(s⁻¹ * r)) • v + s⁻¹ • u := by
    rw [hrs, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hs, one_smul, neg_smul]
    abel
  have main : ∀ x y : Pas.G ax,
      cnorm α ax f (y • u - x • v) * cnorm α ax f (y • u - x • v) =
        x * x * (cnorm α ax f v * cnorm α ax f v) + y * y * (cnorm α ax f u * cnorm α ax f u) := by
    intro x y
    have hp : f.symm (x • v) ∈ (bx.x : L) := (memx _).2 ⟨x, f.apply_symm_apply _⟩
    have hq : f.symm (y • u) ∈ (bx.y : L) := (memy _).2 ⟨y, f.apply_symm_apply _⟩
    have pyth := slen_pyth α ax π bx (p := ⟨f.symm (x • v), bx.x.2 _ hp⟩)
      (q := ⟨f.symm (y • u), bx.y.2 _ hq⟩) hp hq
    rw [hbO] at pyth
    have pyth' : slen α ax (f.symm (x • v)) (f.symm (y • u)) *
        slen α ax (f.symm (x • v)) (f.symm (y • u)) =
        slen α ax O (f.symm (x • v)) * slen α ax O (f.symm (x • v)) +
          slen α ax O (f.symm (y • u)) * slen α ax O (f.symm (y • u)) := pyth
    have e1 : slen α ax (f.symm (x • v)) (f.symm (y • u)) = cnorm α ax f (y • u - x • v) :=
      clen_eq_cnorm α ax H (x • v) (y • u)
    have e2 : slen α ax O (f.symm (x • v)) = |x| * cnorm α ax f v := by
      rw [← hOs]; exact cnorm_smul α ax H x v
    have e3 : slen α ax O (f.symm (y • u)) = |y| * cnorm α ax f u := by
      rw [← hOs]; exact cnorm_smul α ax H y u
    rw [e1, e2, e3] at pyth'
    rw [pyth']
    have hx := abs_mul_abs_self x
    have hy := abs_mul_abs_self y
    linear_combination (cnorm α ax f v * cnorm α ax f v) * hx +
      (cnorm α ax f u * cnorm α ax f u) * hy
  refine ⟨-(s⁻¹ * r), s⁻¹, u, hwu, fun x y => ?_⟩
  have h := main (-x) y
  have e : y • u - (-x) • v = x • v + y • u := by rw [neg_smul, sub_neg_eq_add, add_comm]
  rw [e] at h
  rw [h]; ring

/-- **The square of the length is a quadratic form on every plane.** -/
theorem cnorm_planar (v w : AffPt (Pas.G ax) W) :
    ∃ a b c : Pas.G ax, ∀ x y : Pas.G ax,
      cnorm α ax f (x • v + y • w) * cnorm α ax f (x • v + y • w) =
        a * (x * x) + b * (x * y) + c * (y * y) := by
  by_cases hv : v = 0
  · subst hv
    refine ⟨0, 0, cnorm α ax f w * cnorm α ax f w, fun x y => ?_⟩
    rw [smul_zero, zero_add, cnorm_smul α ax H y w]
    have h := abs_mul_abs_self y
    linear_combination (cnorm α ax f w * cnorm α ax f w) * h
  by_cases hw : ∃ c : Pas.G ax, w = c • v
  · obtain ⟨c, rfl⟩ := hw
    refine ⟨cnorm α ax f v * cnorm α ax f v, 2 * c * (cnorm α ax f v * cnorm α ax f v),
      c * c * (cnorm α ax f v * cnorm α ax f v), fun x y => ?_⟩
    have e : x • v + y • c • v = (x + y * c) • v := by rw [add_smul, mul_smul]
    rw [e, cnorm_smul α ax H (x + y * c) v]
    have h := abs_mul_abs_self (x + y * c)
    linear_combination (cnorm α ax f v * cnorm α ax f v) * h
  · push Not at hw
    obtain ⟨lam, mu, u, hwu, h⟩ := cnorm_plane α ax H hv hw
    refine ⟨cnorm α ax f v * cnorm α ax f v, 2 * lam * (cnorm α ax f v * cnorm α ax f v),
      lam * lam * (cnorm α ax f v * cnorm α ax f v) + mu * mu * (cnorm α ax f u * cnorm α ax f u),
      fun x y => ?_⟩
    have e : x • v + y • w = (x + y * lam) • v + (y * mu) • u := by
      rw [hwu, smul_add, smul_smul, smul_smul, add_smul]; abel
    rw [e, h]; ring

end Metric

/-! ## The standard co-ordinates -/

section Std

variable {K : Type*}

/-- The point `(a, b, c)` of `K³`. -/
def mk3 (a b c : K) : Coord K 3 := AffPt.ofV ![a, b, c]

@[simp] theorem mk3_zero (a b c : K) : AffPt.toV (mk3 a b c) 0 = a := rfl
@[simp] theorem mk3_one (a b c : K) : AffPt.toV (mk3 a b c) 1 = b := rfl
@[simp] theorem mk3_two (a b c : K) : AffPt.toV (mk3 a b c) 2 = c := rfl

theorem coord3_ext {X Y : Coord K 3} (h0 : AffPt.toV X 0 = AffPt.toV Y 0)
    (h1 : AffPt.toV X 1 = AffPt.toV Y 1) (h2 : AffPt.toV X 2 = AffPt.toV Y 2) : X = Y := by
  apply AffPt.toV_injective; funext i; fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem mk3_eta (X : Coord K 3) :
    X = mk3 (AffPt.toV X 0) (AffPt.toV X 1) (AffPt.toV X 2) := coord3_ext rfl rfl rfl

variable [Field K]

theorem toV_add_apply (X Y : Coord K 3) (i : Fin 3) :
    AffPt.toV (X + Y) i = AffPt.toV X i + AffPt.toV Y i := rfl

theorem toV_sub_apply (X Y : Coord K 3) (i : Fin 3) :
    AffPt.toV (X - Y) i = AffPt.toV X i - AffPt.toV Y i := rfl

theorem toV_smul_apply (t : K) (X : Coord K 3) (i : Fin 3) :
    AffPt.toV (t • X) i = t * AffPt.toV X i := rfl

theorem ip_three (X Y : Coord K 3) : Coord.ip X Y =
    AffPt.toV X 0 * AffPt.toV Y 0 + AffPt.toV X 1 * AffPt.toV Y 1 +
      AffPt.toV X 2 * AffPt.toV Y 2 := by
  rw [Coord.ip_def, Fin.sum_univ_three]

/-- The linear change of co-ordinates `(x, y, z) ↦ (x + β₁ z, y + β₂ z, ν z)`. -/
def stdMap (β₁ β₂ ν : K) : AffPt K ((K × K) × K) →ₗ[K] Coord K 3 where
  toFun v := mk3 ((AffPt.toV v).1.1 + (AffPt.toV v).2 * β₁)
    ((AffPt.toV v).1.2 + (AffPt.toV v).2 * β₂) ((AffPt.toV v).2 * ν)
  map_add' v w := by
    apply coord3_ext
    · show (AffPt.toV (v + w)).1.1 + (AffPt.toV (v + w)).2 * β₁ =
        (AffPt.toV v).1.1 + (AffPt.toV v).2 * β₁ + ((AffPt.toV w).1.1 + (AffPt.toV w).2 * β₁)
      simp only [AffPt.toV_add, Prod.fst_add, Prod.snd_add]; ring
    · show (AffPt.toV (v + w)).1.2 + (AffPt.toV (v + w)).2 * β₂ =
        (AffPt.toV v).1.2 + (AffPt.toV v).2 * β₂ + ((AffPt.toV w).1.2 + (AffPt.toV w).2 * β₂)
      simp only [AffPt.toV_add, Prod.fst_add, Prod.snd_add]; ring
    · show (AffPt.toV (v + w)).2 * ν = (AffPt.toV v).2 * ν + (AffPt.toV w).2 * ν
      simp only [AffPt.toV_add, Prod.snd_add]; ring
  map_smul' t v := by
    apply coord3_ext
    · show (AffPt.toV (t • v)).1.1 + (AffPt.toV (t • v)).2 * β₁ =
        t * ((AffPt.toV v).1.1 + (AffPt.toV v).2 * β₁)
      simp only [AffPt.toV_smul, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    · show (AffPt.toV (t • v)).1.2 + (AffPt.toV (t • v)).2 * β₂ =
        t * ((AffPt.toV v).1.2 + (AffPt.toV v).2 * β₂)
      simp only [AffPt.toV_smul, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    · show (AffPt.toV (t • v)).2 * ν = t * ((AffPt.toV v).2 * ν)
      simp only [AffPt.toV_smul, Prod.smul_snd, smul_eq_mul]; ring

theorem stdMap_apply (β₁ β₂ ν : K) (v : AffPt K ((K × K) × K)) :
    stdMap β₁ β₂ ν v = mk3 ((AffPt.toV v).1.1 + (AffPt.toV v).2 * β₁)
      ((AffPt.toV v).1.2 + (AffPt.toV v).2 * β₂) ((AffPt.toV v).2 * ν) := rfl

theorem stdMap_injective (β₁ β₂ : K) {ν : K} (hν : ν ≠ 0) :
    Function.Injective (stdMap β₁ β₂ ν) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  rw [stdMap_apply] at hv
  have h0 : (AffPt.toV v).1.1 + (AffPt.toV v).2 * β₁ = 0 := congrArg (fun X : Coord K 3 => AffPt.toV X 0) hv
  have h1 : (AffPt.toV v).1.2 + (AffPt.toV v).2 * β₂ = 0 := congrArg (fun X : Coord K 3 => AffPt.toV X 1) hv
  have h2 : (AffPt.toV v).2 * ν = 0 := congrArg (fun X : Coord K 3 => AffPt.toV X 2) hv
  have hz : (AffPt.toV v).2 = 0 := (mul_eq_zero.1 h2).resolve_right hν
  rw [hz, zero_mul, add_zero] at h0 h1
  exact AffPt.toV_injective (Prod.ext (Prod.ext h0 h1) hz)

theorem stdMap_surjective (β₁ β₂ : K) {ν : K} (hν : ν ≠ 0) :
    Function.Surjective (stdMap β₁ β₂ ν) := by
  intro Y
  refine ⟨AffPt.ofV ((AffPt.toV Y 0 - AffPt.toV Y 2 / ν * β₁,
    AffPt.toV Y 1 - AffPt.toV Y 2 / ν * β₂), AffPt.toV Y 2 / ν), ?_⟩
  rw [stdMap_apply]
  apply coord3_ext
  · show AffPt.toV Y 0 - AffPt.toV Y 2 / ν * β₁ + AffPt.toV Y 2 / ν * β₁ = AffPt.toV Y 0
    ring
  · show AffPt.toV Y 1 - AffPt.toV Y 2 / ν * β₂ + AffPt.toV Y 2 / ν * β₂ = AffPt.toV Y 1
    ring
  · show AffPt.toV Y 2 / ν * ν = AffPt.toV Y 2
    exact div_mul_cancel₀ _ hν

theorem ip_stdMap (β₁ β₂ ν : K) (v : AffPt K ((K × K) × K)) :
    Coord.ip (stdMap β₁ β₂ ν v) (stdMap β₁ β₂ ν v) =
      ((AffPt.toV v).1.1 + (AffPt.toV v).2 * β₁) * ((AffPt.toV v).1.1 + (AffPt.toV v).2 * β₁) +
      ((AffPt.toV v).1.2 + (AffPt.toV v).2 * β₂) * ((AffPt.toV v).1.2 + (AffPt.toV v).2 * β₂) +
      (AffPt.toV v).2 * ν * ((AffPt.toV v).2 * ν) := by
  rw [ip_three, stdMap_apply]; rfl

/-- The linear form `a x + b y + c z` in the new co-ordinates. -/
theorem lin3_stdMap (β₁ β₂ : K) {ν : K} (hν : ν ≠ 0) (a b c : K)
    (v : AffPt K ((K × K) × K)) :
    Coord.ip (mk3 a b ((c - a * β₁ - b * β₂) / ν)) (stdMap β₁ β₂ ν v) = lin3 a b c v := by
  rw [ip_three, stdMap_apply, lin3_apply]
  simp only [mk3_zero, mk3_one, mk3_two]
  have e : (c - a * β₁ - b * β₂) / ν * ((AffPt.toV v).2 * ν) =
      (c - a * β₁ - b * β₂) * (AffPt.toV v).2 := by
    rw [mul_comm (AffPt.toV v).2 ν, ← mul_assoc, div_mul_cancel₀ _ hν]
  rw [e]; ring

end Std

/-! ## The metric co-ordinates of space -/

section Final

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [HasSegCong P] [HasAngCong P] [hC : SpaceCongruence P L Pl] [hS : SpaceParallels P L Pl]
  [hA : Archimedes P L]

local notation "𝒫[" π "]" => {A : P // A ∈ π}
local notation "ℒ[" π "]" => {a : L // LiesInPlane (Point := P) a π}

include hC hS hA

/-- On the plane `α` the length is the euclidean length of the rectangular co-ordinates. -/
theorem cnorm_alpha (α : Pl) (ax : Pas.Axes 𝒫[α] ℒ[α])
    (f : P ≃ AffPt (Pas.G ax) ((Pas.G ax × Pas.G ax) × Pas.G ax))
    (hα : ∀ Z : 𝒫[α], f Z = ((rectEquiv α ax Z, (0 : Pas.G ax)) :
      (Pas.G ax × Pas.G ax) × Pas.G ax)) (x y : Pas.G ax) :
    cnorm α ax f (AffPt.ofV ((x, y), 0)) * cnorm α ax f (AffPt.ofV ((x, y), 0)) =
      x * x + y * y := by
  have hOx : Pas.py ax ax.O = 0 := (Pas.mem_x_iff ax ax.O).1 ax.hOx
  have hOy : Pas.px ax ax.O = 0 := (Pas.mem_y_iff ax ax.O).1 ax.hOy
  have h0 : f.symm 0 = (ax.O : P) := by
    rw [Equiv.symm_apply_eq, hα ax.O, rectEquiv_apply, hOx, hOy]; rfl
  obtain ⟨c1, c2⟩ := Pas.mkPt_coords ax x y
  have h1 : f.symm (AffPt.ofV ((x, y), 0)) = ((Pas.mkPt ax x y : 𝒫[α]) : P) := by
    rw [Equiv.symm_apply_eq, hα (Pas.mkPt ax x y), rectEquiv_apply, c1, c2]; rfl
  have e : cnorm α ax f (AffPt.ofV ((x, y), 0)) = Pas.len ax ax.O (Pas.mkPt ax x y) := by
    rw [cnorm, clen, h0, h1]
    exact slen_of_mem α ax ax.O (Pas.mkPt ax x y)
  rw [e, Pas.len_sq ax, hOx, hOy, c1, c2]; ring

/-- **The metric co-ordinates of space.** A geometry of space with I–V having a plane has
co-ordinates in `K³`, `K` an archimedean Pythagorean ordered field, in which the lines are the lines
of `K³`, the planes the planes of `K³`, betweenness is that of `K³`, and two segments are congruent
iff their co-ordinate lengths are equal. -/
theorem exists_metric_coords (α : Pl) :
    ∃ (K : Type u) (_ : Field K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K)
      (_ : Archimedean K) (_ : IsPythagorean K) (Ψ : P → Coord K 3), Function.Bijective Ψ ∧
      (∀ (ℓ : L) (A B : P), A ≠ B → A ∈ ℓ → B ∈ ℓ →
        ∀ X : P, X ∈ ℓ ↔ ∃ r : K, Ψ X = r • (Ψ B - Ψ A) + Ψ A) ∧
      (∀ π : Pl, ∃ (n : Coord K 3) (d : K), n ≠ 0 ∧ ∀ X : P, X ∈ π ↔ Coord.ip n (Ψ X) + d = 0) ∧
      (∀ X Y Z : P, Sbtw K (Ψ X) (Ψ Y) (Ψ Z) ↔ Between X Y Z) ∧
      (∀ A B C D : P, A ≠ B → C ≠ D → (SegCong (Ψ A) (Ψ B) (Ψ C) (Ψ D) ↔ SegCong A B C D)) := by
  obtain ⟨ax⟩ := exists_axes_in (P := P) (L := L) α
  have hV : finrank (Pas.G ax) (Pas.G ax × Pas.G ax) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  obtain ⟨f, hα, hl1, -, hp1, -, hbt⟩ :=
    exists_space_coords (K := Pas.G ax) hV α (rectEquiv α ax) (rect_lineHyp α ax)
  have H : IsCoordSys (L := L) (Pl := Pl) f :=
    ⟨hl1, hp1, hbt (rect_between α ax), fun d _ => exists_not_smul d⟩
  obtain ⟨q, hqv⟩ : ∃ q : AffPt (Pas.G ax) ((Pas.G ax × Pas.G ax) × Pas.G ax) → Pas.G ax,
      ∀ v, q v = cnorm α ax f v * cnorm α ax f v := ⟨_, fun _ => rfl⟩
  have hq : ∀ v w : AffPt (Pas.G ax) ((Pas.G ax × Pas.G ax) × Pas.G ax),
      ∃ a b c : Pas.G ax, ∀ x y : Pas.G ax,
        q (x • v + y • w) = a * (x * x) + b * (x * y) + c * (y * y) := by
    intro v w
    obtain ⟨a, b, c, h⟩ := cnorm_planar α ax H v w
    exact ⟨a, b, c, fun x y => by rw [hqv]; exact h x y⟩
  have h2 : (2 : Pas.G ax) ≠ 0 := two_ne_zero
  have half : ∀ c : Pas.G ax, ∃ β : Pas.G ax, 2 * β = c := fun c =>
    ⟨c / 2, by rw [mul_comm, div_mul_cancel₀ _ h2]⟩
  have hform := quad_three q hq h2
    (AffPt.ofV ((1, 0), 0)) (AffPt.ofV ((0, 1), 0)) (AffPt.ofV ((0, 0), 1))
  have qa := cnorm_alpha α ax f hα
  have q1 := qa 1 0
  have q2 := qa 0 1
  have q12 := qa 1 1
  have e12 : (AffPt.ofV ((1, 0), 0) : AffPt (Pas.G ax) ((Pas.G ax × Pas.G ax) × Pas.G ax)) +
      AffPt.ofV ((0, 1), 0) = AffPt.ofV ((1, 1), 0) := by
    apply AffPt.toV_injective
    refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp
  obtain ⟨N3, hN3⟩ : ∃ N3 : Pas.G ax, N3 = cnorm α ax f (AffPt.ofV ((0, 0), 1)) *
      cnorm α ax f (AffPt.ofV ((0, 0), 1)) := ⟨_, rfl⟩
  obtain ⟨β₁, hβ₁⟩ := half
    (cnorm α ax f (AffPt.ofV ((1, 0), 0) + AffPt.ofV ((0, 0), 1)) *
      cnorm α ax f (AffPt.ofV ((1, 0), 0) + AffPt.ofV ((0, 0), 1)) - 1 - N3)
  obtain ⟨β₂, hβ₂⟩ := half
    (cnorm α ax f (AffPt.ofV ((0, 1), 0) + AffPt.ofV ((0, 0), 1)) *
      cnorm α ax f (AffPt.ofV ((0, 1), 0) + AffPt.ofV ((0, 0), 1)) - 1 - N3)
  -- the quadratic form in the co-ordinates `x, y, z`
  have hq3 : ∀ v : AffPt (Pas.G ax) ((Pas.G ax × Pas.G ax) × Pas.G ax),
      cnorm α ax f v * cnorm α ax f v =
        (AffPt.toV v).1.1 * (AffPt.toV v).1.1 + (AffPt.toV v).1.2 * (AffPt.toV v).1.2 +
          (AffPt.toV v).2 * (AffPt.toV v).2 * N3 +
          2 * ((AffPt.toV v).1.1 * (AffPt.toV v).2) * β₁ +
          2 * ((AffPt.toV v).1.2 * (AffPt.toV v).2) * β₂ := by
    intro v
    have hv : v = (AffPt.toV v).1.1 • (AffPt.ofV ((1, 0), 0) :
          AffPt (Pas.G ax) ((Pas.G ax × Pas.G ax) × Pas.G ax)) +
        (AffPt.toV v).1.2 • (AffPt.ofV ((0, 1), 0) :
          AffPt (Pas.G ax) ((Pas.G ax × Pas.G ax) × Pas.G ax)) +
        (AffPt.toV v).2 • (AffPt.ofV ((0, 0), 1) :
          AffPt (Pas.G ax) ((Pas.G ax × Pas.G ax) × Pas.G ax)) := by
      apply AffPt.toV_injective
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp
    have h := hform (AffPt.toV v).1.1 (AffPt.toV v).1.2 (AffPt.toV v).2
    rw [← hv] at h
    simp only [hqv] at h
    rw [h, e12, q1, q2, q12, ← hN3]
    linear_combination (-((AffPt.toV v).1.1 * (AffPt.toV v).2)) * hβ₁ -
      ((AffPt.toV v).1.2 * (AffPt.toV v).2) * hβ₂
  -- the third vector of an orthonormal basis
  have hn0 : (AffPt.ofV ((-β₁, -β₂), 1) :
      AffPt (Pas.G ax) ((Pas.G ax × Pas.G ax) × Pas.G ax)) ≠ 0 := fun e => by
    have h : (1 : Pas.G ax) = 0 := congrArg (fun v => (AffPt.toV v).2) e
    exact one_ne_zero h
  obtain ⟨ν, hν⟩ : ∃ ν : Pas.G ax, ν = cnorm α ax f (AffPt.ofV ((-β₁, -β₂), 1)) := ⟨_, rfl⟩
  have hνpos : 0 < ν := by rw [hν]; exact cnorm_pos α ax hn0
  have hνsq : ν * ν = N3 - β₁ * β₁ - β₂ * β₂ := by
    rw [hν, hq3]
    simp only [AffPt.toV_ofV]
    ring
  have hstd : ∀ v : AffPt (Pas.G ax) ((Pas.G ax × Pas.G ax) × Pas.G ax),
      Coord.ip (stdMap β₁ β₂ ν v) (stdMap β₁ β₂ ν v) = cnorm α ax f v * cnorm α ax f v := by
    intro v
    rw [ip_stdMap, hq3]
    linear_combination ((AffPt.toV v).2 * (AffPt.toV v).2) * hνsq
  have hinj := stdMap_injective β₁ β₂ hνpos.ne'
  have hsurj := stdMap_surjective β₁ β₂ hνpos.ne'
  have hpyth : IsPythagorean (Pas.G ax) := ⟨fun x => by
    obtain ⟨h, hh, e⟩ := Pas.pythagorean ax x
    exact ⟨h, hh.le, by rw [sq, e, sq]⟩⟩
  refine ⟨Pas.G ax, inferInstance, inferInstance, inferInstance, Pas.archimedean_G ax, hpyth,
    fun X => stdMap β₁ β₂ ν (f X), ⟨fun X Y h => f.injective (hinj h), fun Y => ?_⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨v, rfl⟩ := hsurj Y
    exact ⟨f.symm v, congrArg (stdMap β₁ β₂ ν) (f.apply_symm_apply v)⟩
  · intro ℓ A B hAB hA hB X
    rw [mem_line_coord H hAB hA hB X]
    refine exists_congr fun r => ?_
    rw [← map_sub (stdMap β₁ β₂ ν), ← map_smul (stdMap β₁ β₂ ν), ← map_add (stdMap β₁ β₂ ν)]
    exact hinj.eq_iff.symm
  · intro π
    obtain ⟨S, hS⟩ := hp1 π
    obtain ⟨a, b, c, d, habc, hS'⟩ := affPlane_eq S
    refine ⟨mk3 a b ((c - a * β₁ - b * β₂) / ν), d, fun e => ?_, fun X => ?_⟩
    · have h0 : a = 0 := congrArg (fun X : Coord (Pas.G ax) 3 => AffPt.toV X 0) e
      have h1 : b = 0 := congrArg (fun X : Coord (Pas.G ax) 3 => AffPt.toV X 1) e
      have h2' : (c - a * β₁ - b * β₂) / ν = 0 := congrArg (fun X : Coord (Pas.G ax) 3 => AffPt.toV X 2) e
      rw [h0, h1, zero_mul, zero_mul, sub_zero, sub_zero, div_eq_zero_iff] at h2'
      rcases h2' with h | h
      · rcases habc with h' | h' | h'
        · exact h' h0
        · exact h' h1
        · exact h' h
      · exact hνpos.ne' h
    · rw [lin3_stdMap β₁ β₂ hνpos.ne']
      exact (hS X).trans (hS' (f X))
  · intro X Y Z
    rw [← H.btw X Y Z]
    exact Function.Injective.sbtw_map_iff (f := (stdMap β₁ β₂ ν).toAffineMap) hinj
  · intro A B C D hAB hCD
    have key : ∀ X Y : P, Coord.ip (stdMap β₁ β₂ ν (f Y) - stdMap β₁ β₂ ν (f X))
        (stdMap β₁ β₂ ν (f Y) - stdMap β₁ β₂ ν (f X)) = slen α ax X Y * slen α ax X Y := by
      intro X Y
      rw [← map_sub (stdMap β₁ β₂ ν), hstd, ← clen_eq_cnorm α ax H (f X) (f Y), clen,
        f.symm_apply_apply,
        f.symm_apply_apply]
    rw [Coord.segCong_iff, key, key, ← slen_eq_iff α ax hAB hCD]
    exact mul_self_inj (slen_nonneg α ax A B) (slen_nonneg α ax C D)

end Final

end SpaceCoord

end HilbertFoundations
