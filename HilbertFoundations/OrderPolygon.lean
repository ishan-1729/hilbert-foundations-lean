import HilbertFoundations.OrderPolygonAux4

/-!
# Theorem 6: every simple polygon divides the plane into an interior and an exterior

This file closes unit `th.6` of `Order.lean` (Hilbert's Theorem 6, the Jordan curve theorem for
polygons), from the axioms of groups I and II only: `polygonTheorem : PolygonTheorem P` in every
plane geometry `PlaneOrder P L`, and `theorem6_space` for the simple polygons of a plane `α` of a
space geometry (in the plane geometry of `α`, as `theorem6_triangle_space`).

The proof (helper modules `OrderPolygonAux.lean` … `OrderPolygonAux4.lean`, namespace
`PolyJordan`):

* All vertices lie on one side of some line `ℓ0` (`exists_line_sameSide`). The **parity**
  `par v ℓ0 X` of a point `X` off the polygon is the number, mod 2, of sides crossed by a segment
  from `X` to a point of `ℓ0` in general position; it does not depend on that point (`cr_indep`,
  by counting the crossings of the polygon with a triangle, `tri_parity`).
* The parity is constant along every segment that does not meet the polygon (`par_eq_of_step`),
  it takes both values (`exists_jump`), and it is `0` on every line that does not meet the polygon
  (`par_zero_of_line`). The **interior** is the set of the points off the polygon of parity `1`,
  the **exterior** the set of those of parity `0`.
* Two points off the polygon of the same parity are joined by a broken line that does not meet
  the polygon (`two_classes`): every point off the polygon sees a point of the polygon
  (`first_hit`), and walking round the polygon (`good_side`, `vertex_good`, with the sweep lemma
  `sweep`) joins it to one of two fixed points `N₁`, `N₂` on either side of the side `v n v 0`.
-/

namespace HilbertFoundations

open PolyJordan

universe u v w

theorem polygonPoints_eq_onPoly {P : Type u} [HasBetween P] {n : ℕ} (v : Fin (n + 1) → P) :
    PolygonPoints v = {X | OnPoly v X} := by
  ext X
  constructor
  · rintro (⟨i, e⟩ | ⟨i, h⟩)
    · exact ⟨i, Or.inl e⟩
    · rw [rot_eq] at h
      exact ⟨i, Or.inr (Or.inr h)⟩
  · rintro ⟨i, e | e | h⟩
    · exact Or.inl ⟨i, e⟩
    · exact Or.inl ⟨i + 1, e⟩
    · exact Or.inr ⟨i, by rw [rot_eq]; exact h⟩

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [hO : PlaneOrder P L]
include hO

/-- **Theorem 6** for a simple polygon with vertices `v 0, …, v n`: the interior is the set of the
points off the polygon of parity `1`, the exterior the set of those of parity `0`. -/
theorem PolyJordan.Simple.divides {n : ℕ} {v : Fin (n + 1) → P} (hs : Simple v) :
    DividesLikePolygon (L := L) {X | OnPoly v X} := by
  classical
  obtain ⟨ℓ0, O, -, hall⟩ := exists_line_sameSide (L := L) (hs.ne 0) (Finset.univ.image v)
  have hside : ∀ j, SameSide ℓ0 O (v j) := fun j =>
    hall (v j) (Finset.mem_image_of_mem v (Finset.mem_univ j))
  obtain ⟨N₁, N₂, hN₁, hN₂, hpar, hcl⟩ := two_classes hs hside
  have hne1 : ∀ x : ZMod 2, x ≠ x + 1 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  -- two points off the polygon of the same parity are joined by a broken line
  have join : ∀ A A', ¬OnPoly v A → ¬OnPoly v A' → par v ℓ0 A = par v ℓ0 A' →
      ∃ (m : ℕ) (w : Fin (m + 1) → P), IsBrokenLine w ∧ w 0 = A ∧ w (Fin.last m) = A' ∧
        Disjoint (BrokenLinePoints w) {X | OnPoly v X} := by
    intro A A' hA hA' hpp
    have hconn : Conn v A A' := by
      rcases hcl A hA with h | h <;> rcases hcl A' hA' with h' | h'
      · exact h.trans h'.symm
      · exfalso
        have e1 := h.par_eq hside
        have e2 := h'.par_eq hside
        exact hne1 (par v ℓ0 N₁) (by rw [← hpar, ← e1, ← e2, hpp])
      · exfalso
        have e1 := h.par_eq hside
        have e2 := h'.par_eq hside
        exact hne1 (par v ℓ0 N₁) (by rw [← hpar, ← e1, ← e2, hpp])
      · exact h.trans h'.symm
    obtain ⟨m, w, hw, h0, hl, hfree⟩ := hconn.exists_brokenLine hA
    exact ⟨m, w, hw, h0, hl, Set.disjoint_left.2 fun p hp hpS => hfree p hp hpS⟩
  refine ⟨{X | ¬OnPoly v X ∧ par v ℓ0 X = 1}, {X | ¬OnPoly v X ∧ par v ℓ0 X = 0},
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases zmod2_cases (par v ℓ0 N₁) with h | h
    · exact ⟨N₂, hN₂, by rw [hpar, h]; decide⟩
    · exact ⟨N₁, hN₁, h⟩
  · rcases zmod2_cases (par v ℓ0 N₁) with h | h
    · exact ⟨N₁, hN₁, h⟩
    · exact ⟨N₂, hN₂, by rw [hpar, h]; decide⟩
  · exact Set.disjoint_left.2 fun X h1 h0 => h10 (h1.2.symm.trans h0.2)
  · ext X
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hX
      rcases zmod2_cases (par v ℓ0 X) with h | h
      · exact Or.inr ⟨hX, h⟩
      · exact Or.inl ⟨hX, h⟩
  · intro A hA B hB m w h0 hl
    by_contra hne
    have hfree : ∀ p, p ∈ BrokenLinePoints w → ¬OnPoly v p := fun p hp hpS =>
      hne ⟨p, hp, hpS⟩
    have hconst : ∀ i : Fin (m + 1), par v ℓ0 (w i) = par v ℓ0 (w 0) := by
      intro i
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih =>
        rw [← ih]
        exact (par_eq_of_step hside (hfree _ (Or.inl ⟨i.castSucc, rfl⟩))
          (hfree _ (Or.inl ⟨i.succ, rfl⟩)) (fun p hp => hfree p (Or.inr ⟨i, hp⟩))).symm
    have h := hconst (Fin.last m)
    rw [hl, h0, hB.2, hA.2] at h
    exact h10 h.symm
  · intro A hA A' hA'
    exact join A A' hA.1 hA'.1 (hA.2.trans hA'.2.symm)
  · intro B hB B' hB'
    exact join B B' hB.1 hB'.1 (hB.2.trans hB'.2.symm)
  · exact ⟨ℓ0, fun X hX => par_zero_of_mem hside hX⟩
  · rintro ⟨l, hl⟩
    obtain ⟨A, B, -, hA, -⟩ := exists_two_points (Point := P) l
    have h0 := par_zero_of_line hside l (fun X hX => (hl X hX).1) hA
    have h1 : par v ℓ0 A = 1 := (hl A hA).2
    rw [h0] at h1
    exact h10 h1.symm

/-- **Theorem 6** (plane geometry, groups I and II): every simple polygon divides the points of
the plane not on it into an interior and an exterior. -/
theorem polygonTheorem : PolygonTheorem P := by
  intro k v hv
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := hv.1; omega⟩
  rw [polygonPoints_eq_onPoly]
  exact (simple_of hv).divides

omit hO in
/-- **Theorem 6** for the simple polygons whose vertices lie in a plane `α` of space: in the plane
geometry of `α` (groups I and II of space geometry). -/
theorem theorem6_space {Pl : Type w} [HasPlanes P Pl] [SpaceOrder P L Pl] (α : Pl) (k : ℕ)
    (v : Fin k → {A : P // A ∈ α}) (hv : IsSimplePolygon v) :
    DividesLikePolygon (L := {a : L // LiesInPlane (Point := P) a α}) (PolygonPoints v) :=
  polygonTheorem k v hv

end HilbertFoundations
