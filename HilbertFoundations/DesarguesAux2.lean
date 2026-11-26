import HilbertFoundations.DesarguesAux

/-!
# Helper for `Desargues.lean` (§ 22): the general theorem of Desargues

This module contains no unit of Hilbert's text.

* `GeneralDesargues P`: the theorem of Desargues "relating to points of intersection in a plane":
  if two triangles `ABC`, `A'B'C'` lie so that the lines `a ∋ A, A'`, `b ∋ B, B'`, `c ∋ C, C'`
  joining homologous vertices pass through one point or are parallel to one another, and the
  homologous sides (distinct lines) meet in points `R` (of `AB`, `A'B'`), `S` (of `BC`, `B'C'`)
  and `T` (of `CA`, `C'A'`), then `R`, `S`, `T` lie on a straight line. No further
  non-degeneracy hypothesis: the centre may be a vertex, homologous vertices may coincide.
* `desargues_model`, `desargues_model_par`: the theorem in the coordinate geometry `AffPt K W` over
  any division ring `K` (any module `W`), with centre `O`, resp. with parallel joins. Proof by
  "homogeneous co-ordinates": `α A + α' A' = β B + β' B' = γ C + γ' C'` with
  `α + α' = β + β' = γ + γ' = κ` (`κ = 1`: this is the centre `O`; `κ = 0`: it is the common
  direction of the joins); then `(α - β) R = α A - β B`, `(β - γ) S = β B - γ C`,
  `(γ - α) T = γ C - α A`, and the three vectors add up to `0`, so `R` is an affine combination of
  `S` and `T`. No commutativity of `K` is used.
* `generalDesargues_of_planeInSpace`: the theorem transfers to every plane geometry with I 1–2 which
  is a part of such a coordinate geometry (the degenerate configurations are settled by I 1–2
  alone); `space_generalDesargues`: every plane of a space geometry with I, II, III satisfies it
  (each such plane is desarguesian in the sense of Theorem 32, hence coordinatized by a skew field,
  §§ 24–30 of DesarguesAlgebra.lean).
* `planeParallels_of_planeInSpace`: a plane geometry which is a part of a space geometry with I, III
  satisfies the plane axioms I 1–2 (with the plane clauses of I 7) and III.
* `exists_cutting_plane`, `segment_meets_iff`: every line of a plane is the intersection of the
  plane with a second plane; in `K³` over an ordered field the segment `XY` meets the plane
  `u x + v y + w z + r = 0` iff `u x + v y + w z + r` has opposite signs at `X` and `Y`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Des

universe u v w

/-- **The general theorem of Desargues** (points of intersection in a plane): two triangles whose
joins of homologous vertices pass through one point or are parallel to one another, and whose
homologous sides (distinct lines) meet in points `R`, `S`, `T`, have these points on a straight
line. -/
def GeneralDesargues (P : Type u) {L : Type v} [HasLines P L] : Prop :=
  ∀ (A B C A' B' C' R S T : P) (a b c ab a'b' bc b'c' ca c'a' : L),
    ¬Collinear A B C → ¬Collinear A' B' C' →
    A ∈ a → A' ∈ a → B ∈ b → B' ∈ b → C ∈ c → C' ∈ c → DesAlg.ConcurrentOrParallel P a b c →
    A ∈ ab → B ∈ ab → A' ∈ a'b' → B' ∈ a'b' → ab ≠ a'b' → R ∈ ab → R ∈ a'b' →
    B ∈ bc → C ∈ bc → B' ∈ b'c' → C' ∈ b'c' → bc ≠ b'c' → S ∈ bc → S ∈ b'c' →
    C ∈ ca → A ∈ ca → C' ∈ c'a' → A' ∈ c'a' → ca ≠ c'a' → T ∈ ca → T ∈ c'a' →
    Collinear R S T

/-! ## The theorem in the coordinate geometry over a division ring -/

section Model

variable {K : Type u} [DivisionRing K] {W : Type v} [AddCommGroup W] [Module K W]

open AffPt

/-- An affine combination of two points of a line lies on the line. -/
theorem comb_mem {A B : AffPt K W} {a : AffLine K W} (hA : A ∈ a) (hB : B ∈ a) {p q : K}
    (h : p + q = 1) : p • A + q • B ∈ a := by
  have e : p • A + q • B = q • (B - A) + A := by
    rw [smul_sub, show p = 1 - q by rw [← h]; abel, sub_smul, one_smul]
    abel
  rw [e, mem_line_iff]
  exact add_mem_of_mem_direction (Submodule.smul_mem _ q (sub_mem_direction (S := a.carrier) hA hB))
    hA

/-- A point `O ≠ A, A'` of the line `AA'` is `α A + α' A'` with `α + α' = 1`, `α, α' ≠ 0`. -/
theorem split {A A' O : AffPt K W} {a : AffLine K W} (hA : A ∈ a) (hA' : A' ∈ a) (hO : O ∈ a)
    (hAA' : A ≠ A') (hOA : O ≠ A) (hOA' : O ≠ A') :
    ∃ α α' : K, α ≠ 0 ∧ α' ≠ 0 ∧ α + α' = 1 ∧ O = α • A + α' • A' := by
  rw [mem_line_iff, AffLine.carrier_eq a hAA' hA hA', mem_affineSpan_pair_iff] at hO
  obtain ⟨s, rfl⟩ := hO
  refine ⟨1 - s, s, fun h => hOA' ?_, fun h => hOA ?_, by abel, ?_⟩
  · rw [show s = 1 by rw [← sub_eq_zero, ← neg_sub, h, neg_zero], one_smul]; abel
  · rw [h, zero_smul, zero_add]
  · rw [smul_sub, sub_smul, one_smul]; abel

/-- If two lines have a common point and directions `Y' - X' = κ (Y - X)`, they coincide. -/
theorem eq_of_dir {ℓ m : AffLine K W} {X Y X' Y' R : AffPt K W} (hX : X ∈ ℓ) (hY : Y ∈ ℓ)
    (hX' : X' ∈ m) (hY' : Y' ∈ m) (hX'Y' : X' ≠ Y') (hR : R ∈ ℓ) (hR' : R ∈ m) (κ : K)
    (h : Y' - X' = κ • (Y - X)) : ℓ = m := by
  have hd : Y - X ∈ ℓ.carrier.direction := sub_mem_direction (S := ℓ.carrier) hX hY
  rw [mem_line_iff, AffLine.carrier_eq m hX'Y' hX' hY', mem_affineSpan_pair_iff] at hR'
  obtain ⟨r, hr⟩ := hR'
  have h1 : X' ∈ ℓ := by
    rw [mem_line_iff, mem_iff_sub_mem_direction (S := ℓ.carrier) hR]
    have : X' - R = -(r * κ) • (Y - X) := by rw [hr, h, neg_smul, mul_smul]; abel
    rw [this]
    exact Submodule.smul_mem _ _ hd
  have h2 : Y' ∈ ℓ := by
    rw [mem_line_iff, mem_iff_sub_mem_direction (S := ℓ.carrier) h1, h]
    exact Submodule.smul_mem _ _ hd
  exact line_unique hX'Y' h1 h2 hX' hY'

/-- The point of intersection of the homologous sides `AB`, `A'B'`:
`(α - β) R = α A - β B`, where `α A + α' A' = β B + β' B'` and `α + α' = β + β' = κ` (`κ = 1`: the
centre `O` of perspective is this point; `κ = 0`: the joins are parallel to this vector). -/
theorem meet_point {A B A' B' R : AffPt K W} {ab a'b' : AffLine K W} {κ α α' β β' : K}
    (hα : α + α' = κ) (hβ : β + β' = κ) (hα' : α' ≠ 0)
    (hO : α • A + α' • A' = β • B + β' • B')
    (hA : A ∈ ab) (hB : B ∈ ab) (hA' : A' ∈ a'b') (hB' : B' ∈ a'b') (hA'B' : A' ≠ B')
    (hne : ab ≠ a'b') (hR : R ∈ ab) (hR' : R ∈ a'b') :
    α - β ≠ 0 ∧ (α - β) • R = α • A - β • B := by
  have hα1 : α' = κ - α := by rw [← hα]; abel
  have hβ1 : β' = κ - β := by rw [← hβ]; abel
  have key : α • A - β • B = β' • B' - α' • A' := by
    rw [sub_eq_sub_iff_add_eq_add, hO, add_comm]
  have hxβ : α - β ≠ 0 := by
    intro h0
    have e : α = β := sub_eq_zero.1 h0
    have e' : α' = β' := by rw [hα1, hβ1, e]
    apply hne
    refine eq_of_dir hA hB hA' hB' hA'B' hR hR' (-(α'⁻¹ * α)) ?_
    have : α' • (B' - A') = α • (A - B) := by
      rw [← e, ← e'] at key
      rw [smul_sub, smul_sub, key]
    rw [neg_smul, ← smul_neg, neg_sub, mul_smul, ← this, smul_smul, inv_mul_cancel₀ hα',
      one_smul]
  refine ⟨hxβ, ?_⟩
  have hR0 : (α - β)⁻¹ • (α • A - β • B) ∈ ab := by
    have : (α - β)⁻¹ • (α • A - β • B) = ((α - β)⁻¹ * α) • A + (-((α - β)⁻¹ * β)) • B := by
      rw [smul_sub, smul_smul, smul_smul, neg_smul, ← sub_eq_add_neg]
    rw [this]
    refine comb_mem hA hB ?_
    rw [← sub_eq_add_neg, ← mul_sub, inv_mul_cancel₀ hxβ]
  have hR0' : (α - β)⁻¹ • (α • A - β • B) ∈ a'b' := by
    have : (α - β)⁻¹ • (α • A - β • B) = ((α - β)⁻¹ * β') • B' + (-((α - β)⁻¹ * α')) • A' := by
      rw [key, smul_sub, smul_smul, smul_smul, neg_smul, ← sub_eq_add_neg]
    rw [this]
    refine comb_mem hB' hA' ?_
    rw [← sub_eq_add_neg, ← mul_sub, hα1, hβ1, show (κ - β) - (κ - α) = α - β by abel,
      inv_mul_cancel₀ hxβ]
  have e : R = (α - β)⁻¹ • (α • A - β • B) := by
    by_contra hRR
    exact hne (line_unique hRR hR hR0 hR' hR0')
  rw [e, smul_smul, mul_inv_cancel₀ hxβ, one_smul]

/-- The last step: `(α - β) R + (β - γ) S + (γ - α) T = 0` with `α ≠ β`, so `R`, `S`, `T` lie on
a line. -/
theorem collinear_of_relations {A B C R S T : AffPt K W} {ab : AffLine K W} (hR : R ∈ ab)
    {α β γ : K} (hx : α - β ≠ 0) (eR : (α - β) • R = α • A - β • B)
    (eS : (β - γ) • S = β • B - γ • C) (eT : (γ - α) • T = γ • C - α • A) :
    Collinear (Line := AffLine K W) R S T := by
  -- `(α - β) (R - T) = -(β - γ) (S - T)`
  have hsum : (α - β) • (R - T) = -(β - γ) • (S - T) := by
    have hT : (α - β) • T + (β - γ) • T = -((γ - α) • T) := by
      rw [← add_smul, ← neg_smul]; congr 1; abel
    rw [neg_smul, eq_neg_iff_add_eq_zero, smul_sub, smul_sub, eR, eS]
    have : α • A - β • B - (α - β) • T + (β • B - γ • C - (β - γ) • T)
        = α • A - γ • C - ((α - β) • T + (β - γ) • T) := by abel
    rw [this, hT, eT]
    abel
  by_cases hST : S = T
  · subst hST
    by_cases hRS : R = S
    · subst hRS; exact ⟨ab, hR, hR, hR⟩
    · obtain ⟨l, hl1, hl2⟩ := exists_line (Line := AffLine K W) hRS
      exact ⟨l, hl1, hl2, hl2⟩
  · have hTS : T ≠ S := Ne.symm hST
    refine ⟨AffLine.through T S hTS, ?_, AffLine.right_mem_through hTS,
      AffLine.left_mem_through hTS⟩
    rw [AffLine.mem_through_iff]
    refine ⟨(α - β)⁻¹ * -(β - γ), ?_⟩
    rw [mul_smul, ← hsum, smul_smul, inv_mul_cancel₀ hx, one_smul, sub_add_cancel]

/-- **The theorem of Desargues in the coordinate geometry, centre `O`** (all points of the figure
distinct from `O`, distinct joins, `A ≠ A'` etc.; the general case is reduced to this one in
`generalDesargues_of_planeInSpace`). -/
theorem desargues_model {A B C A' B' C' O R S T : AffPt K W}
    {a b c ab a'b' bc b'c' ca c'a' : AffLine K W}
    (hAa : A ∈ a) (hA'a : A' ∈ a) (hBb : B ∈ b) (hB'b : B' ∈ b) (hCc : C ∈ c) (hC'c : C' ∈ c)
    (hOa : O ∈ a) (hOb : O ∈ b) (hOc : O ∈ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hAA' : A ≠ A') (hBB' : B ≠ B') (hCC' : C ≠ C')
    (hOA : O ≠ A) (hOA' : O ≠ A') (hOB : O ≠ B) (hOB' : O ≠ B') (hOC : O ≠ C) (hOC' : O ≠ C')
    (h1 : A ∈ ab) (h2 : B ∈ ab) (h3 : A' ∈ a'b') (h4 : B' ∈ a'b') (h5 : ab ≠ a'b') (h6 : R ∈ ab)
    (h7 : R ∈ a'b')
    (k1 : B ∈ bc) (k2 : C ∈ bc) (k3 : B' ∈ b'c') (k4 : C' ∈ b'c') (k5 : bc ≠ b'c') (k6 : S ∈ bc)
    (k7 : S ∈ b'c')
    (m1 : C ∈ ca) (m2 : A ∈ ca) (m3 : C' ∈ c'a') (m4 : A' ∈ c'a') (m5 : ca ≠ c'a') (m6 : T ∈ ca)
    (m7 : T ∈ c'a') :
    Collinear (Line := AffLine K W) R S T := by
  -- distinct primed vertices: two joining lines meet only in `O`
  have ne_of {X Y : AffPt K W} {x y : AffLine K W} (hX : X ∈ x) (hY : Y ∈ y) (hxy : x ≠ y)
      (hOx : O ∈ x) (hOy : O ∈ y) (hOX : O ≠ X) : X ≠ Y := by
    rintro rfl
    exact hxy (line_unique hOX hOx hX hOy hY)
  obtain ⟨α, α', -, hα'0, hα, hOα⟩ := split hAa hA'a hOa hAA' hOA hOA'
  obtain ⟨β, β', -, hβ'0, hβ, hOβ⟩ := split hBb hB'b hOb hBB' hOB hOB'
  obtain ⟨γ, γ', -, hγ'0, hγ, hOγ⟩ := split hCc hC'c hOc hCC' hOC hOC'
  obtain ⟨hx, eR⟩ := meet_point hα hβ hα'0 (hOα.symm.trans hOβ) h1 h2 h3 h4
    (ne_of hA'a hB'b hab hOa hOb hOA') h5 h6 h7
  obtain ⟨-, eS⟩ := meet_point hβ hγ hβ'0 (hOβ.symm.trans hOγ) k1 k2 k3 k4
    (ne_of hB'b hC'c hbc hOb hOc hOB') k5 k6 k7
  obtain ⟨-, eT⟩ := meet_point hγ hα hγ'0 (hOγ.symm.trans hOα) m1 m2 m3 m4
    (ne_of hC'c hA'a (Ne.symm hac) hOc hOa hOC') m5 m6 m7
  exact collinear_of_relations h6 hx eR eS eT

/-- Two lines of a plane (an affine subspace of dimension `2`) without a common point have the same
direction. -/
theorem dir_eq_of_not_meets {Q : AffineSubspace K (AffPt K W)} [FiniteDimensional K Q.direction]
    (hS : Module.finrank K Q.direction = 2) {a c : AffLine K W} (ha : a.carrier ≤ Q)
    (hc : c.carrier ≤ Q) (hmeet : ¬Meets (Point := AffPt K W) c a) :
    c.carrier.direction = a.carrier.direction := by
  obtain ⟨A, hAc⟩ := c.nonempty
  obtain ⟨O, hO⟩ := a.nonempty
  set D := a.carrier.direction
  by_contra hne
  have hinf : Module.finrank K (c.carrier.direction ⊓ D : Submodule K (AffPt K W)) = 0 := by
    have hle : Module.finrank K (c.carrier.direction ⊓ D : Submodule K (AffPt K W)) ≤ 1 := by
      rw [← c.finrank_direction]; exact Submodule.finrank_mono inf_le_left
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h | h
    · exact h
    · exfalso; apply hne
      have h1 := Submodule.eq_of_le_of_finrank_eq (inf_le_left : c.carrier.direction ⊓ D ≤ _)
        (by rw [h, c.finrank_direction])
      have h2 := Submodule.eq_of_le_of_finrank_eq (inf_le_right : c.carrier.direction ⊓ D ≤ _)
        (by rw [h, a.finrank_direction])
      rw [← h1, h2]
  have hsup : c.carrier.direction ⊔ D = Q.direction := by
    apply Submodule.eq_of_le_of_finrank_eq
      (sup_le (AffineSubspace.direction_le hc) (AffineSubspace.direction_le ha))
    have := Submodule.finrank_sup_add_finrank_inf_eq c.carrier.direction D
    rw [hinf, c.finrank_direction, a.finrank_direction] at this
    rw [hS]; omega
  have hAO : A - O ∈ c.carrier.direction ⊔ D := hsup ▸ sub_mem_direction (ha hO) (hc hAc)
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 hAO
  apply hmeet
  refine ⟨w + O, ?_, add_mem_of_mem_direction hw hO⟩
  have : w + O = -u + A := by
    have hw' : w = A - O - u := by rw [← huw]; abel
    rw [hw']; abel
  show w + O ∈ c.carrier
  rw [this]; exact add_mem_of_mem_direction (Submodule.neg_mem _ hu) hAc

/-- Parallel joins: a point pair `X ≠ X'` on a line with the direction of `a` gives
`β X + β' X' = A' - A` with `β + β' = 0`, `β' ≠ 0` (the point at infinity of the joins). -/
theorem par_split {A A' X X' : AffPt K W} {a x : AffLine K W} (hAa : A ∈ a) (hA'a : A' ∈ a)
    (hAA' : A ≠ A') (hX : X ∈ x) (hX' : X' ∈ x)
    (hd : x.carrier.direction = a.carrier.direction) (hXX' : X ≠ X') :
    ∃ β β' : K, β' ≠ 0 ∧ β + β' = 0 ∧ β • X + β' • X' = A' - A := by
  have hd0 : A' - A ≠ 0 := sub_ne_zero.2 (Ne.symm hAA')
  have hdmem : A' - A ∈ a.carrier.direction := sub_mem_direction hAa hA'a
  have hv : X' - X ∈ a.carrier.direction := hd ▸ sub_mem_direction hX hX'
  obtain ⟨μ, hμ⟩ := (finrank_eq_one_iff_of_ne_zero' (K := K)
    (⟨A' - A, hdmem⟩ : a.carrier.direction) (fun h => hd0 (congrArg Subtype.val h))).1
    a.finrank_direction ⟨X' - X, hv⟩
  have hμ' : μ • (A' - A) = X' - X := congrArg Subtype.val hμ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hμ'
    exact hXX' (sub_eq_zero.1 hμ'.symm).symm
  refine ⟨-μ⁻¹, μ⁻¹, inv_ne_zero hμ0, by abel, ?_⟩
  rw [neg_smul, neg_add_eq_sub, ← smul_sub, ← hμ', smul_smul, inv_mul_cancel₀ hμ0, one_smul]

/-- **The theorem of Desargues in the coordinate geometry, parallel joins**: the joins `a`, `b`,
`c` have the same direction ("the centre is a point at infinity"). -/
theorem desargues_model_par {A B C A' B' C' R S T : AffPt K W}
    {a b c ab a'b' bc b'c' ca c'a' : AffLine K W}
    (hAa : A ∈ a) (hA'a : A' ∈ a) (hBb : B ∈ b) (hB'b : B' ∈ b) (hCc : C ∈ c) (hC'c : C' ∈ c)
    (hdb : b.carrier.direction = a.carrier.direction)
    (hdc : c.carrier.direction = a.carrier.direction)
    (hAA' : A ≠ A') (hBB' : B ≠ B') (hCC' : C ≠ C')
    (hA'B' : A' ≠ B') (hB'C' : B' ≠ C') (hC'A' : C' ≠ A')
    (h1 : A ∈ ab) (h2 : B ∈ ab) (h3 : A' ∈ a'b') (h4 : B' ∈ a'b') (h5 : ab ≠ a'b') (h6 : R ∈ ab)
    (h7 : R ∈ a'b')
    (k1 : B ∈ bc) (k2 : C ∈ bc) (k3 : B' ∈ b'c') (k4 : C' ∈ b'c') (k5 : bc ≠ b'c') (k6 : S ∈ bc)
    (k7 : S ∈ b'c')
    (m1 : C ∈ ca) (m2 : A ∈ ca) (m3 : C' ∈ c'a') (m4 : A' ∈ c'a') (m5 : ca ≠ c'a') (m6 : T ∈ ca)
    (m7 : T ∈ c'a') :
    Collinear (Line := AffLine K W) R S T := by
  obtain ⟨α, α', hα'0, hα, hOα⟩ := par_split hAa hA'a hAA' hAa hA'a rfl hAA'
  obtain ⟨β, β', hβ'0, hβ, hOβ⟩ := par_split hAa hA'a hAA' hBb hB'b hdb hBB'
  obtain ⟨γ, γ', hγ'0, hγ, hOγ⟩ := par_split hAa hA'a hAA' hCc hC'c hdc hCC'
  obtain ⟨hx, eR⟩ := meet_point hα hβ hα'0 (hOα.trans hOβ.symm) h1 h2 h3 h4 hA'B' h5 h6 h7
  obtain ⟨-, eS⟩ := meet_point hβ hγ hβ'0 (hOβ.trans hOγ.symm) k1 k2 k3 k4 hB'C' k5 k6 k7
  obtain ⟨-, eT⟩ := meet_point hγ hα hγ'0 (hOγ.trans hOα.symm) m1 m2 m3 m4 hC'A' m5 m6 m7
  exact collinear_of_relations h6 hx eR eS eT

end Model

/-! ## Degenerate configurations in a plane geometry with I 1–2 -/

section Degenerate

variable {P : Type u} {L : Type v} [HasLines P L] [Connection P L]

/-- Two distinct lines have at most one common point. -/
theorem eq_of_two_lines {X Y : P} {l m : L} (hlm : l ≠ m) (hX : X ∈ l) (hX' : X ∈ m) (hY : Y ∈ l)
    (hY' : Y ∈ m) : X = Y := by
  by_contra h
  exact hlm (line_unique h hX hY hX' hY')

theorem collinear_of_eq12 {R S T : P} {l : L} (hR : R ∈ l) (h : R = S) :
    Collinear (Line := L) R S T := by
  subst h
  by_cases hRT : R = T
  · subst hRT; exact ⟨l, hR, hR, hR⟩
  · obtain ⟨m, h1, h2⟩ := exists_line (Line := L) hRT
    exact ⟨m, h1, h1, h2⟩

theorem collinear_of_eq13 {R S T : P} {l : L} (hR : R ∈ l) (h : R = T) :
    Collinear (Line := L) R S T := by
  subst h
  by_cases hRS : R = S
  · subst hRS; exact ⟨l, hR, hR, hR⟩
  · obtain ⟨m, h1, h2⟩ := exists_line (Line := L) hRS
    exact ⟨m, h1, h2, h1⟩

theorem collinear_of_eq23 {R S T : P} {l : L} (hS : S ∈ l) (h : S = T) :
    Collinear (Line := L) R S T := by
  subst h
  by_cases hRS : R = S
  · subst hRS; exact ⟨l, hS, hS, hS⟩
  · obtain ⟨m, h1, h2⟩ := exists_line (Line := L) hRS
    exact ⟨m, h1, h2, h2⟩

/-- **The centre of perspective is the vertex `A`**: then `R = B'`, `T = C'`, and `R`, `S`, `T` lie
on `B'C'`. -/
theorem collinear_of_center_vertex {A B C B' C' R S T : P} {b c ab a'b' b'c' ca c'a' : L}
    (hAB : A ≠ B) (hCA : C ≠ A) (hAb : A ∈ b) (hBb : B ∈ b) (hB'b : B' ∈ b) (hAc : A ∈ c)
    (hCc : C ∈ c) (hC'c : C' ∈ c)
    (h1 : A ∈ ab) (h2 : B ∈ ab) (h4 : B' ∈ a'b') (h5 : ab ≠ a'b') (h6 : R ∈ ab) (h7 : R ∈ a'b')
    (k3 : B' ∈ b'c') (k4 : C' ∈ b'c') (k7 : S ∈ b'c')
    (m1 : C ∈ ca) (m2 : A ∈ ca) (m3 : C' ∈ c'a') (m5 : ca ≠ c'a') (m6 : T ∈ ca)
    (m7 : T ∈ c'a') :
    Collinear (Line := L) R S T := by
  have e1 : ab = b := line_unique hAB h1 h2 hAb hBb
  have e2 : ca = c := line_unique hCA m1 m2 hCc hAc
  subst e1 e2
  have hR : R = B' := eq_of_two_lines h5 h6 h7 hB'b h4
  have hT : T = C' := eq_of_two_lines m5 m6 m7 hC'c m3
  subst hR hT
  exact ⟨b'c', k3, k7, k4⟩

end Degenerate

/-! ## Transfer to plane geometries -/

section Transfer

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [Connection P L]
  {K : Type*} [DivisionRing K] [PartialOrder K] {W : Type*} [AddCommGroup W] [Module K W]
  [Fact (Module.finrank K W = 3)]

/-- A plane geometry which is a part of a coordinate geometry over a division ring satisfies the
general theorem of Desargues. -/
theorem generalDesargues_of_planeInSpace
    (e : DesAlg.PlaneInSpace P L (AffPt K W) (AffLine K W) (AffPlane K W)) : GeneralDesargues P := by
  intro A B C A' B' C' R S T a b c ab a'b' bc b'c' ca c'a' hn hn' hAa hA'a hBb hB'b hCc hC'c hcp
    h1 h2 h3 h4 h5 h6 h7 k1 k2 k3 k4 k5 k6 k7 m1 m2 m3 m4 m5 m6 m7
  have hAB := DesAlg.nc_ne12 hn h1
  have hAC := DesAlg.nc_ne13 hn h1
  have hBC := DesAlg.nc_ne23 hn k1
  have hA'B' := DesAlg.nc_ne12 hn' h3
  have hA'C' := DesAlg.nc_ne13 hn' h3
  have hB'C' := DesAlg.nc_ne23 hn' k3
  -- coinciding homologous vertices
  by_cases eA : A = A'
  · subst eA
    exact collinear_of_eq13 h6 ((eq_of_two_lines h5 h6 h7 h1 h3).trans
      (eq_of_two_lines m5 m6 m7 m2 m4).symm)
  by_cases eB : B = B'
  · subst eB
    exact collinear_of_eq12 h6 ((eq_of_two_lines h5 h6 h7 h2 h4).trans
      (eq_of_two_lines k5 k6 k7 k1 k3).symm)
  by_cases eC : C = C'
  · subst eC
    exact collinear_of_eq23 k6 ((eq_of_two_lines k5 k6 k7 k2 k4).trans
      (eq_of_two_lines m5 m6 m7 m1 m3).symm)
  have rot {X Y Z : P} (h : Collinear (Line := L) Y Z X) : Collinear (Line := L) X Y Z := by
    obtain ⟨l, h1, h2, h3⟩ := h; exact ⟨l, h3, h1, h2⟩
  have rot' {X Y Z : P} (h : Collinear (Line := L) Z X Y) : Collinear (Line := L) X Y Z := by
    obtain ⟨l, h1, h2, h3⟩ := h; exact ⟨l, h2, h3, h1⟩
  have m : ∀ {X : P} {l : L}, X ∈ l → e.pt X ∈ e.ln l := fun h => (e.mem_iff _ _).2 h
  have inj := e.pt_injective
  have injl := e.ln_injective
  -- a configuration of the coordinate geometry, back in the plane
  have back : Collinear (Line := AffLine K W) (e.pt R) (e.pt S) (e.pt T) →
      Collinear (Line := L) R S T := by
    rintro ⟨n, hRn, hSn, hTn⟩
    by_cases hRS : R = S
    · exact collinear_of_eq12 h6 hRS
    · have hm := liesInPlane_of_mem (inj.ne hRS) hRn hSn (e.pt_mem R) (e.pt_mem S)
      obtain ⟨l, rfl⟩ := e.ln_surj n hm
      exact ⟨l, (e.mem_iff _ _).1 hRn, (e.mem_iff _ _).1 hSn, (e.mem_iff _ _).1 hTn⟩
  rcases hcp with ⟨O, hOa, hOb, hOc⟩ | ⟨p1, p2, p3⟩
  · -- the centre `O` is one of the vertices
    by_cases eOA : O = A
    · subst eOA
      exact collinear_of_center_vertex hAB (Ne.symm hAC) hOb hBb hB'b hOc hCc hC'c h1 h2 h4 h5 h6
        h7 k3 k4 k7 m1 m2 m3 m5 m6 m7
    by_cases eOA' : O = A'
    · subst eOA'
      exact collinear_of_center_vertex hA'B' (Ne.symm hA'C') hOb hB'b hBb hOc hC'c hCc h3 h4 h2
        (Ne.symm h5) h7 h6 k1 k2 k6 m3 m4 m1 (Ne.symm m5) m7 m6
    by_cases eOB : O = B
    · subst eOB
      exact rot (collinear_of_center_vertex hBC hAB hOc hCc hC'c hOa hAa hA'a k1 k2 k4
        k5 k6 k7 m3 m4 m7 h1 h2 h3 h5 h6 h7)
    by_cases eOB' : O = B'
    · subst eOB'
      exact rot (collinear_of_center_vertex hB'C' hA'B' hOc hC'c hCc hOa hA'a hAa k3 k4
        k2 (Ne.symm k5) k7 k6 m1 m2 m6 h3 h4 h1 (Ne.symm h5) h7 h6)
    by_cases eOC : O = C
    · subst eOC
      exact rot' (collinear_of_center_vertex (Ne.symm hAC) hBC hOa hAa hA'a hOb hBb
        hB'b m1 m2 m4 m5 m6 m7 h3 h4 h7 k1 k2 k3 k5 k6 k7)
    by_cases eOC' : O = C'
    · subst eOC'
      exact rot' (collinear_of_center_vertex (Ne.symm hA'C') hB'C' hOa hA'a hAa hOb
        hB'b hBb m3 m4 m2 (Ne.symm m5) m7 m6 h1 h2 h6 k3 k4 k1 (Ne.symm k5) k7 k6)
    -- distinct joins
    have dj : ∀ {X Y X' Y' : P} {x y xy x'y' : L}, X ≠ Y → X' ≠ Y' → X ∈ x → X' ∈ x → Y ∈ y →
        Y' ∈ y → X ∈ xy → Y ∈ xy → X' ∈ x'y' → Y' ∈ x'y' → xy ≠ x'y' → x ≠ y := by
      intro X Y X' Y' x y xy x'y' hXY hX'Y' hX hX' hY hY' g1 g2 g3 g4 g5 hxy
      subst hxy
      exact g5 ((line_unique hXY g1 g2 hX hY).trans (line_unique hX'Y' g3 g4 hX' hY').symm)
    have hab := dj hAB hA'B' hAa hA'a hBb hB'b h1 h2 h3 h4 h5
    have hbc := dj hBC hB'C' hBb hB'b hCc hC'c k1 k2 k3 k4 k5
    have hca := dj (Ne.symm hAC) (Ne.symm hA'C') hCc hC'c hAa hA'a m1 m2 m3 m4 m5
    exact back (desargues_model (m hAa) (m hA'a) (m hBb) (m hB'b) (m hCc) (m hC'c) (m hOa)
      (m hOb) (m hOc) (injl.ne hab) (injl.ne (Ne.symm hca)) (injl.ne hbc) (inj.ne eA)
      (inj.ne eB) (inj.ne eC) (inj.ne eOA) (inj.ne eOA') (inj.ne eOB) (inj.ne eOB')
      (inj.ne eOC) (inj.ne eOC')
      (m h1) (m h2) (m h3) (m h4) (injl.ne h5) (m h6) (m h7) (m k1) (m k2) (m k3) (m k4)
      (injl.ne k5) (m k6) (m k7) (m m1) (m m2) (m m3) (m m4) (injl.ne m5) (m m6) (m m7))
  · -- parallel joins: the images have the same direction
    have nm : ∀ {x y : L}, ¬Meets (Point := P) x y → ¬Meets (Point := AffPt K W) (e.ln y) (e.ln x) := by
      rintro x y hn ⟨Y, hy, hx⟩
      obtain ⟨X, rfl⟩ := e.pt_surj Y (e.ln_in x Y hx)
      exact hn ⟨X, (e.mem_iff _ _).1 hx, (e.mem_iff _ _).1 hy⟩
    have hS := (e.plane).finrank_direction
    have le : ∀ x : L, (e.ln x).carrier ≤ e.plane.carrier := fun x =>
      AffPt.liesInPlane_iff.1 (e.ln_in x)
    have hdb := dir_eq_of_not_meets hS (le a) (le b) (nm p1)
    have hdc := dir_eq_of_not_meets hS (le a) (le c) (nm p2)
    exact back (desargues_model_par (m hAa) (m hA'a) (m hBb) (m hB'b) (m hCc) (m hC'c) hdb hdc
      (inj.ne eA) (inj.ne eB) (inj.ne eC) (inj.ne hA'B') (inj.ne hB'C') (inj.ne (Ne.symm hA'C'))
      (m h1) (m h2) (m h3) (m h4) (injl.ne h5) (m h6) (m h7) (m k1) (m k2) (m k3) (m k4)
      (injl.ne k5) (m k6) (m k7) (m m1) (m m2) (m m3) (m m4) (injl.ne m5) (m m6) (m m7))

end Transfer

/-! ## The planes of a space geometry with I, II, III -/

section SpaceThm

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [SpaceOrder P L Pl] [SpaceParallels P L Pl]

/-- **The general theorem of Desargues holds in every plane of a space geometry with I, II, III.** -/
theorem space_generalDesargues (α : Pl) : GeneralDesargues {A : P // A ∈ α} := by
  have := DesAlg.nonempty_lines_of_plane (P := P) (L := L) α
  have hD := planes_of_space_desarguesian (P := P) (L := L) α
  obtain ⟨F⟩ := DesAlg.exists_frame (P := {A : P // A ∈ α})
    (L := {a : L // LiesInPlane (Point := P) a α})
  have : Fact (DesAlg.DesarguesII {A : P // A ∈ α}) := ⟨hD.2⟩
  exact generalDesargues_of_planeInSpace (DesAlg.planeInSpace F)

end SpaceThm

/-! ## A plane geometry which is a part of a space satisfies the plane axioms I, III -/

section PartOfSpace

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
  {P' : Type*} {L' : Type*} {Pl' : Type*} [HasLines P' L'] [HasPlanes P' Pl'] [HasBetween P']
  [SpaceParallels P' L' Pl']

theorem meets_iff_of_planeInSpace (e : DesAlg.PlaneInSpace P L P' L' Pl') (x y : L) :
    Meets (Point := P') (e.ln x) (e.ln y) ↔ Meets (Point := P) x y := by
  constructor
  · rintro ⟨Y, hx, hy⟩
    obtain ⟨X, rfl⟩ := e.pt_surj Y (e.ln_in x Y hx)
    exact ⟨X, (e.mem_iff _ _).1 hx, (e.mem_iff _ _).1 hy⟩
  · rintro ⟨X, hx, hy⟩
    exact ⟨e.pt X, (e.mem_iff _ _).2 hx, (e.mem_iff _ _).2 hy⟩

/-- **A plane geometry which is a part of a space geometry with I, III satisfies the plane axioms of
groups I and III** (I 1–2, the plane clauses of I 7, III), so these need not be assumed. -/
theorem planeParallels_of_planeInSpace (e : DesAlg.PlaneInSpace P L P' L' Pl') :
    PlaneParallels P L := by
  have hm : ∀ (X : P) (l : L), e.pt X ∈ e.ln l ↔ X ∈ l := e.mem_iff
  have hI1 : AxiomI1 P := by
    intro A B h
    obtain ⟨m, hA, hB⟩ := exists_line (Line := L') (e.pt_injective.ne h)
    have hin := liesInPlane_of_mem (e.pt_injective.ne h) hA hB (e.pt_mem A) (e.pt_mem B)
    obtain ⟨l, rfl⟩ := e.ln_surj m hin
    exact ⟨l, (hm _ _).1 hA, (hm _ _).1 hB⟩
  have hI2 : AxiomI2 P := by
    intro A B a b h hA hB hA' hB'
    exact e.ln_injective (line_unique (e.pt_injective.ne h) ((hm _ _).2 hA) ((hm _ _).2 hB)
      ((hm _ _).2 hA') ((hm _ _).2 hB'))
  have hI7 : AxiomI7Line P := by
    intro l
    obtain ⟨Y1, Y2, h, h1, h2⟩ := exists_two_points (Point := P') (e.ln l)
    obtain ⟨X1, rfl⟩ := e.pt_surj Y1 (e.ln_in l Y1 h1)
    obtain ⟨X2, rfl⟩ := e.pt_surj Y2 (e.ln_in l Y2 h2)
    exact ⟨X1, X2, fun h' => h (h' ▸ rfl), (hm _ _).1 h1, (hm _ _).1 h2⟩
  have hNC : ExistsNoncollinear P := by
    obtain ⟨Y1, Y2, Y3, h1, h2, h3, hn⟩ :=
      SpaceConnection.ax_I7_plane (Point := P') (Line := L') (Plane := Pl') e.plane
    obtain ⟨X1, rfl⟩ := e.pt_surj _ h1
    obtain ⟨X2, rfl⟩ := e.pt_surj _ h2
    obtain ⟨X3, rfl⟩ := e.pt_surj _ h3
    exact ⟨X1, X2, X3, fun ⟨l, k1, k2, k3⟩ =>
      hn ⟨e.ln l, (hm _ _).2 k1, (hm _ _).2 k2, (hm _ _).2 k3⟩⟩
  have hIII : AxiomIII P := by
    intro a A hA
    have hA' : e.pt A ∉ e.ln a := fun h => hA ((hm _ _).1 h)
    obtain ⟨n, ⟨hnα, hAn, hnn⟩, huniq⟩ := SpaceParallels.ax_III (Point := P') (Line := L')
      (Plane := Pl') e.plane (e.ln a) (e.pt A) (e.ln_in a) (e.pt_mem A) hA'
    obtain ⟨b, rfl⟩ := e.ln_surj n hnα
    refine ⟨b, ⟨(hm _ _).1 hAn, fun h => hnn ((meets_iff_of_planeInSpace e b a).2 h)⟩, ?_⟩
    rintro b' ⟨hAb', hn'⟩
    exact e.ln_injective (huniq (e.ln b') ⟨e.ln_in b', (hm _ _).2 hAb',
      fun h => hn' ((meets_iff_of_planeInSpace e b' a).1 h)⟩)
  exact { ax_I1 := hI1, ax_I2 := hI2, ax_I7_line := hI7, ax_I7_noncollinear := hNC,
          ax_III := hIII }

end PartOfSpace

/-! ## Sides of a plane and of a line by inequalities -/

section Sides

/-- In a space geometry with I, every line `ℓ` of a plane `π` is the intersection of `π` with
another plane. -/
theorem exists_cutting_plane {P : Type u} {L : Type v} {Pl : Type*} [HasLines P L]
    [HasPlanes P Pl] [SpaceConnection P L Pl] {ℓ : L} {π : Pl}
    (h : LiesInPlane (Point := P) ℓ π) : ∃ π' : Pl, ∀ X : P, X ∈ ℓ ↔ X ∈ π ∧ X ∈ π' := by
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_two_points (Point := P) ℓ
  obtain ⟨S, hS⟩ : ∃ S : P, S ∉ π := by
    obtain ⟨A1, B1, C1, D1, h⟩ := SpaceConnection.ax_I7_space (Point := P) (Line := L) (Plane := Pl)
    by_contra hall
    push Not at hall
    exact h ⟨π, hall A1, hall B1, hall C1, hall D1⟩
  have hSℓ : S ∉ ℓ := fun h' => hS (h S h')
  have hn2 : ¬Collinear (Line := L) A B S := fun ⟨m, h1, h2, h3⟩ =>
    hSℓ ((line_unique hAB hA hB h1 h2) ▸ h3)
  obtain ⟨π', h2A, h2B, h2S⟩ := exists_plane (Line := L) (Plane := Pl) hn2
  refine ⟨π', fun X => ⟨fun hX => ⟨h X hX, liesInPlane_of_mem hAB hA hB h2A h2B X hX⟩,
    fun ⟨h1, h2⟩ => ?_⟩⟩
  by_contra hX
  have hn : ¬Collinear (Line := L) A B X := fun ⟨m, k1, k2, k3⟩ =>
    hX ((line_unique hAB hA hB k1 k2) ▸ k3)
  exact hS ((plane_unique (Line := L) hn (h A hA) (h B hB) h1 h2A h2B h2) ▸ h2S)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The value `u x + v y + w z + r` of the left side of the equation of a plane at a point. -/
def eqVal (u v w r : K) (X : Coord K 3) : K :=
  u * AffPt.toV X 0 + v * AffPt.toV X 1 + w * AffPt.toV X 2 + r

theorem eqVal_comb (u v w r : K) (X Y : Coord K 3) (t : K) :
    eqVal u v w r (t • (Y - X) + X) = (1 - t) * eqVal u v w r X + t * eqVal u v w r Y := by
  simp only [eqVal, AffPt.toV_add, AffPt.toV_smul, AffPt.toV_sub, Pi.add_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul]
  ring

/-- A point between `X` and `Y` is `t (Y - X) + X` with `0 < t < 1`. -/
theorem between_param {X Y Z : Coord K 3} (h : Between X Z Y) :
    ∃ t : K, 0 < t ∧ t < 1 ∧ Z = t • (Y - X) + X := by
  have hs : Sbtw K X Z Y := h
  have hd : Y - X ≠ 0 := sub_ne_zero.2 (Ne.symm hs.left_ne_right)
  obtain ⟨⟨r, -, hr⟩, -, -⟩ := hs
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] at hr
  have k := sbtw_param_iff (O := X) hd (0 : K) r 1
  rw [zero_smul, zero_add, one_smul, sub_add_cancel] at k
  have hs' : Sbtw K X (r • (Y - X) + X) Y := by rw [hr]; exact h
  rcases k.1 hs' with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact ⟨r, h0, h1, hr.symm⟩
  · exact absurd (h0.trans h1) (not_lt.2 zero_le_one)

theorem between_of_param {X Y : Coord K 3} (hXY : X ≠ Y) {t : K} (h0 : 0 < t) (h1 : t < 1) :
    Between X (t • (Y - X) + X) Y := by
  have hd : Y - X ≠ 0 := sub_ne_zero.2 (Ne.symm hXY)
  have k := sbtw_param_iff (O := X) hd (0 : K) t 1
  rw [zero_smul, zero_add, one_smul, sub_add_cancel] at k
  exact k.2 (Or.inl ⟨h0, h1⟩)

/-- **The segment `XY` meets the plane `u x + v y + w z + r = 0` iff the values at `X` and `Y` have
opposite signs** (for `X`, `Y` off the plane). -/
theorem segment_meets_iff (u v w r : K) {X Y : Coord K 3} (hX : eqVal u v w r X ≠ 0)
    (hY : eqVal u v w r Y ≠ 0) :
    (∃ Z : Coord K 3, Between X Z Y ∧ eqVal u v w r Z = 0) ↔
      eqVal u v w r X * eqVal u v w r Y < 0 := by
  constructor
  · rintro ⟨Z, hb, hz⟩
    obtain ⟨t, h0, h1, rfl⟩ := between_param hb
    rw [eqVal_comb] at hz
    have h1' : 0 < 1 - t := sub_pos.2 h1
    rcases hX.lt_or_gt with ha | ha <;> rcases hY.lt_or_gt with hb | hb
    · nlinarith [mul_pos h1' (neg_pos.2 ha), mul_pos h0 (neg_pos.2 hb)]
    · exact mul_neg_of_neg_of_pos ha hb
    · exact mul_neg_of_pos_of_neg ha hb
    · nlinarith [mul_pos h1' ha, mul_pos h0 hb]
  · intro hab
    set a := eqVal u v w r X
    set b := eqVal u v w r Y
    have hXY : X ≠ Y := by
      rintro rfl
      nlinarith [mul_self_nonneg a]
    have hab' : a - b ≠ 0 := by
      intro h
      have : a = b := sub_eq_zero.1 h
      rw [← this] at hab
      nlinarith [mul_self_nonneg a]
    have ht : 0 < a / (a - b) ∧ a / (a - b) < 1 := by
      rcases hX.lt_or_gt with ha | ha
      · have hb : 0 < b := by
          by_contra hc; push Not at hc; nlinarith [mul_nonneg_of_nonpos_of_nonpos ha.le hc]
        have hd : a - b < 0 := by linarith
        exact ⟨div_pos_of_neg_of_neg ha hd, (div_lt_one_of_neg hd).2 (by linarith)⟩
      · have hb : b < 0 := by
          by_contra hc; push Not at hc; nlinarith [mul_nonneg ha.le hc]
        have hd : 0 < a - b := by linarith
        exact ⟨div_pos ha hd, (div_lt_one hd).2 (by linarith)⟩
    refine ⟨(a / (a - b)) • (Y - X) + X, between_of_param hXY ht.1 ht.2, ?_⟩
    rw [eqVal_comb]
    field_simp
    ring

end Sides

end Des

end HilbertFoundations
