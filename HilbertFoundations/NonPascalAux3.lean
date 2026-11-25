import HilbertFoundations.NonPascalAux2

/-!
# Helper for §§ 31–35: checks added in review

Helper module of `NonPascal.lean` (the units are stated there). Contents:

* `PascalTheoremLiteral`: Theorem 21 read literally, without the distinctness of `A, B, C`;
  `not_pascalTheoremLiteral_real`: it fails in the real plane (`A = B`, `A' = B'`), and
  `pascalTheorem_of_literal`: it implies `PascalTheorem`, so the added hypothesis only weakens the
  statement.
* `isTr_add_real`, `archimedesTr_real`: in the real plane the translations are the maps
  `X ↦ X + v`, and axiom V holds for the equality of segments by translation (`TrEqual`), so the
  reading of axiom V used for Theorem 36 is satisfiable (the hypothesis of Theorem 36 is not
  vacuous).
* `ratio_unique_of_solutions`, `line_ratio_unique`: the equation `a x + b y + c = 0` of a line
  (`(a, b) ≠ (0, 0)`) is determined by the line up to a common (left) factor `k ≠ 0` (Hilbert's
  "a ratio of three definite numbers `(u : v : w)`", § 35).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations
namespace NonPascal

open DesAlg

universe u v

/-! ## Pascal's theorem read literally -/

/-- **Theorem 21 read literally**: as `PascalTheorem`, without the hypotheses `A ≠ B`, `B ≠ C`,
`A ≠ C`. -/
def PascalTheoremLiteral (P : Type u) {L : Type v} [HasLines P L] : Prop :=
  ∀ (g h : L) (O A B C A' B' C' : P), g ≠ h → O ∈ g → O ∈ h →
    A ∈ g → B ∈ g → C ∈ g → A' ∈ h → B' ∈ h → C' ∈ h →
    A ≠ O → B ≠ O → C ≠ O → A' ≠ O → B' ≠ O → C' ≠ O →
    ParPts (L := L) C B' B C' → ParPts (L := L) C A' A C' → ParPts (L := L) B A' A B'

theorem pascalTheorem_of_literal {P : Type u} {L : Type v} [HasLines P L]
    (h : PascalTheoremLiteral P (L := L)) : PascalTheorem P (L := L) :=
  fun g h' O A B C A' B' C' hgh hOg hOh hA hB hC hA' hB' hC' h1 h2 h3 h4 h5 h6 _ _ _ hp1 hp2 =>
    h g h' O A B C A' B' C' hgh hOg hOh hA hB hC hA' hB' hC' h1 h2 h3 h4 h5 h6 hp1 hp2

open Coord in
/-- **The literal Theorem 21 is false in the real plane**: `O = (0,0)`, `C = (1,0)`,
`A = B = (2,0)`, `A' = B' = (0,1)`, `C' = (0,2)`. Both hypotheses say `CB' ∥ BC'` (the lines
`x + y = 1` and `x + y = 2`), while `BA'` and `AB'` are the same line. -/
theorem not_pascalTheoremLiteral_real : ¬PascalTheoremLiteral (Coord ℝ 2) (L := CoordLine ℝ 2) := by
  intro hP
  have hOE : pt2 (0 : ℝ) 0 ≠ pt2 1 0 := pt2_ne (Or.inl zero_ne_one)
  have hOF : pt2 (0 : ℝ) 0 ≠ pt2 0 1 := pt2_ne (Or.inr zero_ne_one)
  have mg : ∀ x : ℝ, pt2 x 0 ∈ AffLine.through _ _ hOE := fun x =>
    (mem_through_pt2 hOE).2 ⟨x, by simp⟩
  have mh : ∀ y : ℝ, pt2 0 y ∈ AffLine.through _ _ hOF := fun y =>
    (mem_through_pt2 hOF).2 ⟨y, by simp⟩
  have hgh : AffLine.through _ _ hOE ≠ AffLine.through _ _ hOF := fun e => by
    have h1 := mh 1
    rw [← e] at h1
    obtain ⟨r, hr⟩ := (mem_through_pt2 hOE).1 h1
    have := congrArg yc hr
    simp at this
  have hC1 : pt2 (1 : ℝ) 0 ≠ pt2 0 1 := pt2_ne (Or.inl one_ne_zero)
  have hC2 : pt2 (2 : ℝ) 0 ≠ pt2 0 2 := pt2_ne (Or.inl two_ne_zero)
  have hpar : ParPts (L := CoordLine ℝ 2) (pt2 (1 : ℝ) 0) (pt2 (0 : ℝ) 1) (pt2 (2 : ℝ) 0) (pt2 (0 : ℝ) 2) := by
    refine ⟨AffLine.through _ _ hC1, AffLine.through _ _ hC2, AffLine.left_mem_through hC1,
      AffLine.right_mem_through hC1, AffLine.left_mem_through hC2, AffLine.right_mem_through hC2,
      ?_⟩
    rintro ⟨Z, h1, h2⟩
    obtain ⟨r, rfl⟩ := (mem_through_pt2 hC1).1 h1
    obtain ⟨q, hq⟩ := (mem_through_pt2 hC2).1 h2
    have e1 := congrArg xc hq
    have e2 := congrArg yc hq
    simp only [xc_pt2, yc_pt2] at e1 e2
    linarith
  obtain ⟨a, b, h1, h2, h3, h4, hn⟩ := hP _ _ (pt2 0 0) (pt2 2 0) (pt2 2 0) (pt2 1 0) (pt2 0 1)
    (pt2 0 1) (pt2 0 2) hgh (mg 0) (mh 0) (mg 2) (mg 2) (mg 1) (mh 1) (mh 1) (mh 2)
    (pt2_ne (Or.inl two_ne_zero)) (pt2_ne (Or.inl two_ne_zero)) (pt2_ne (Or.inl one_ne_zero))
    (pt2_ne (Or.inr one_ne_zero)) (pt2_ne (Or.inr one_ne_zero)) (pt2_ne (Or.inr two_ne_zero))
    hpar hpar
  exact hn ⟨_, h1, h3⟩

/-! ## Axiom V with the equality by translation holds in the real plane -/

section RealTranslations

open Coord

attribute [local instance] realLine_nonempty

/-- **The map `X ↦ X + v` is a translation of the real plane** (a dilatation without fixed point,
or the identity). -/
theorem isTr_add_real (v : Coord ℝ 2) :
    IsTr (L := CoordLine ℝ 2) (fun X : Coord ℝ 2 => X + v) := by
  refine ⟨fun X Y hXY => ?_, fun X hX => ?_⟩
  · have e : (ln X Y : CoordLine ℝ 2) = AffLine.through X Y hXY :=
      ln_eq hXY (AffLine.left_mem_through hXY) (AffLine.right_mem_through hXY)
    rw [e]
    have m := mem_pline_through hXY (X + v) 1
    rwa [one_smul, show Y - X + (X + v) = Y + v by abel] at m
  · have hv : v = 0 := by simpa using hX
    funext Z
    simp [hv]

/-- In the real plane every translation is a map `X ↦ X + v`. -/
theorem tr_eq_add_real {τ : Coord ℝ 2 → Coord ℝ 2} (hτ : IsTr (L := CoordLine ℝ 2) τ)
    (X : Coord ℝ 2) : τ = fun Y => Y + (τ X - X) :=
  tr_eq_of hτ (isTr_add_real _) (X := X) (by abel)

/-- **Axiom V, with segments equal when one is a translate of the other (`TrEqual`), holds in the
real plane.** By `tr_eq_add_real` the points `A n` are `A 0 + n (A 1 - A 0)`, and the real numbers
are archimedean. -/
theorem archimedesTr_real :
    ArchimedesWith (Coord ℝ 2) (TrEqual (P := Coord ℝ 2) (CoordLine ℝ 2)) := by
  intro A B hB _ hE
  set d : Coord ℝ 2 := A 1 - A 0 with hd
  have key : ∀ n : ℕ, A (n + 1) = A n + d := fun n => by
    obtain ⟨τ, hτ, h0, h1⟩ := hE 0 n
    have k := congrFun (tr_eq_add_real hτ (A 0)) (A 1)
    simp only [zero_add] at h1 k
    rw [← h1, k, h0, hd, add_sub_left_comm]
  have hA : ∀ n : ℕ, A n = (n : ℝ) • d + A 0 := fun n => by
    induction n with
    | zero => simp
    | succ k ih => rw [key, ih]; push_cast; rw [add_smul, one_smul]; abel
  have hB' : Sbtw ℝ (A 0) (A 1) B := hB
  obtain ⟨⟨t, ⟨ht0, -⟩, ht⟩, -⟩ := sbtw_iff_mem_image_Ioo_and_ne.1 hB'
  have ht' : t • (B - A 0) + A 0 = A 1 := by
    rw [← ht, AffineMap.lineMap_apply]; rfl
  have hd0 : d ≠ 0 := fun h => hB'.ne_left (sub_eq_zero.1 h)
  have hBd : B = t⁻¹ • d + A 0 := by
    rw [hd, ← ht', add_sub_cancel_right, inv_smul_smul₀ ht0.ne', sub_add_cancel]
  have e0 : A 0 = (0 : ℝ) • d + A 0 := by rw [zero_smul, zero_add]
  have e1 : A 1 = (1 : ℝ) • d + A 0 := by rw [one_smul, hd, sub_add_cancel]
  have hsb : Sbtw ℝ ((0 : ℝ) • d + A 0) ((1 : ℝ) • d + A 0) (t⁻¹ • d + A 0) := by
    rw [← e0, ← e1, ← hBd]; exact hB'
  have h1t : 1 < t⁻¹ := by
    rcases (sbtw_param_iff (K := ℝ) hd0 0 1 t⁻¹).1 hsb with h | h
    · exact h.2
    · exact absurd h.2 (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_gt t⁻¹
  refine ⟨n, ?_⟩
  have goal : Sbtw ℝ ((0 : ℝ) • d + A 0) (t⁻¹ • d + A 0) ((n : ℝ) • d + A 0) :=
    (sbtw_param_iff (K := ℝ) hd0 0 t⁻¹ n).2 (Or.inl ⟨by linarith, hn⟩)
  rw [← e0, ← hBd, ← hA n] at goal
  exact goal

end RealTranslations

/-! ## The ratio `(u : v : w)` of a line is definite -/

/-- **Two equations with the same solutions are proportional** (in a division ring, coefficients on
the left): if every solution of `a x + b y + c = 0` solves `a' x + b' y + c' = 0`, with
`(a, b) ≠ (0, 0)` and `(a', b') ≠ (0, 0)`, then `(a', b', c') = k (a, b, c)` with `k ≠ 0`. -/
theorem ratio_unique_of_solutions {K : Type*} [DivisionRing K] {a b c a' b' c' : K}
    (h : a ≠ 0 ∨ b ≠ 0) (h' : a' ≠ 0 ∨ b' ≠ 0)
    (hs : ∀ x y : K, a * x + b * y + c = 0 → a' * x + b' * y + c' = 0) :
    ∃ k : K, k ≠ 0 ∧ a' = k * a ∧ b' = k * b ∧ c' = k * c := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := h.resolve_left (not_not.2 ha)
    subst ha
    have e0 := hs 0 (-(b⁻¹ * c)) (by
      rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ hb, one_mul]; simp)
    have e1 := hs 1 (-(b⁻¹ * c)) (by
      rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ hb, one_mul]; simp)
    rw [mul_zero, zero_add, mul_neg, neg_add_eq_zero] at e0
    rw [mul_one, mul_neg, e0, neg_add_cancel_right] at e1
    have hb' : b' = b' * b⁻¹ * b := by rw [mul_assoc, inv_mul_cancel₀ hb, mul_one]
    refine ⟨b' * b⁻¹, fun hk => ?_, by rw [e1, mul_zero], hb', by rw [← e0, mul_assoc]⟩
    rw [hk, zero_mul] at hb'
    exact h'.elim (fun h => h e1) (fun h => h hb')
  · have e0 := hs (-(a⁻¹ * c)) 0 (by
      rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]; simp)
    have e1 := hs (-(a⁻¹ * (b + c))) 1 (by
      rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ ha, one_mul, mul_one]; abel)
    rw [mul_zero, add_zero, mul_neg, neg_add_eq_zero] at e0
    rw [mul_neg, mul_one, add_assoc, neg_add_eq_zero, mul_add, mul_add, ← e0] at e1
    have ha' : a' = a' * a⁻¹ * a := by rw [mul_assoc, inv_mul_cancel₀ ha, mul_one]
    have hb' : b' = a' * a⁻¹ * b := by
      rw [mul_assoc]; exact add_right_cancel e1.symm
    refine ⟨a' * a⁻¹, fun hk => ?_, ha', hb', by rw [← e0, mul_assoc]⟩
    rw [hk, zero_mul] at ha' hb'
    exact h'.elim (fun h => h ha') (fun h => h hb')

section Plane

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [PlaneOrder P L]
  [PlaneParallels P L] [Nonempty L]

/-- **The equation of a line is determined up to a factor** (§ 35: "for each straight line a ratio
of three definite numbers `(u : v : w)`"): two equations `a x + b y + c = 0`, `a' x + b' y + c' = 0`
(`(a, b), (a', b') ≠ (0, 0)`) of the same line in the co-ordinates of a frame are proportional. -/
theorem line_ratio_unique (hD : DesarguesII P) (F : Frame P) (l : L) {a b c a' b' c' : DesAlg.Seg F}
    (h : a ≠ 0 ∨ b ≠ 0) (h' : a' ≠ 0 ∨ b' ≠ 0)
    (hl : ∀ X : P, X ∈ l ↔ a * F.xc X + b * F.yc X + c = 0)
    (hl' : ∀ X : P, X ∈ l ↔ a' * F.xc X + b' * F.yc X + c' = 0) :
    ∃ k : DesAlg.Seg F, k ≠ 0 ∧ a' = k * a ∧ b' = k * b ∧ c' = k * c := by
  have : Fact (DesarguesII P) := ⟨hD⟩
  refine ratio_unique_of_solutions h h' fun x y hxy => ?_
  obtain ⟨X, hX⟩ := (coords_bijective_nd F).2 (x, y)
  simp only [Prod.mk.injEq] at hX
  rw [← hX.1, ← hX.2] at hxy ⊢
  exact (hl' X).1 ((hl X).2 hxy)

end Plane

end NonPascal
end HilbertFoundations
