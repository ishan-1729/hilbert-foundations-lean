import HilbertFoundations.CommentaryCloseAux3

/-!
# The infinitesimal part of an elliptic plane (helper for `CommentaryClose.lean`)

Dehn's non-legendrian geometry (unit `concl.non_legendrian`). Over an ordered field `K` with square
roots of non-negative elements (`IsEuclidean`) and a positive infinitesimal (`HasInfinitesimal`):

* the points `EPt K` are the points of `K²` with infinitesimal co-ordinates (the part of the
  elliptic plane infinitely near to the centre of the gnomonic chart), the lines `ELn K` the lines of
  `K²` meeting that part, incidence and order those of `K²` (`infPart K`, a `ConvexPart`);
* segments are congruent when the cosines `cs` of their elliptic lengths agree, angles when the
  cosines `kc` of their elliptic measures agree.

`planeCongruence : PlaneCongruence (EPt K) (ELn K)`: groups I, II, IV hold.
-/

namespace HilbertFoundations

namespace Elliptic

open Coord

universe u

/-- An ordered field **with a positive infinitesimal** (a non-archimedean ordered field). -/
class HasInfinitesimal (K : Type u) [Field K] [LinearOrder K] : Prop where
  exists_inf : ∃ ε : K, 0 < ε ∧ ∀ n : ℕ, (n : K) * |ε| ≤ 1

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A point of `K²` with infinitesimal co-ordinates. -/
def InfPt (X : Coord K 2) : Prop := IsInf (xc X) ∧ IsInf (yc X)

theorem InfPt.sub {A B : Coord K 2} (hB : InfPt B) (hA : InfPt A) : InfPt (B - A) :=
  ⟨hB.1.sub hA.1, hB.2.sub hA.2⟩

/-! ### Lines of `K²` in terms of the cross product -/

theorem lin_eq_cr {u v w : K} {O A : Coord K 2} (hO : lin u v w O = 0) (hA : lin u v w A = 0)
    (X : Coord K 2) :
    lin u v w X * ip (A - O) (A - O) =
      (v * (xc A - xc O) - u * (yc A - yc O)) * crossProd2 (A - O) (X - O) := by
  simp only [lin] at hO hA ⊢
  simp only [crossProd2, ip_two, xc_sub, yc_sub]
  linear_combination ((xc A - xc O) * (xc A - xc O) + (yc A - yc O) * (yc A - yc O)) * hO +
    ((xc A - xc O) * (xc X - xc O) + (yc A - yc O) * (yc X - yc O)) * (hA - hO)

theorem kappa_ne_zero {u v w : K} (huv : u ≠ 0 ∨ v ≠ 0) {O A : Coord K 2} (hAO : A ≠ O)
    (hO : lin u v w O = 0) (hA : lin u v w A = 0) :
    v * (xc A - xc O) - u * (yc A - yc O) ≠ 0 := by
  intro hκ
  have hN := (ip_self_pos (sub_ne_zero.2 hAO)).ne'
  simp only [lin] at hO hA
  simp only [ip_two, xc_sub, yc_sub] at hN
  have hu : u * ((xc A - xc O) * (xc A - xc O) + (yc A - yc O) * (yc A - yc O)) = 0 := by
    linear_combination (xc A - xc O) * (hA - hO) - (yc A - yc O) * hκ
  have hv : v * ((xc A - xc O) * (xc A - xc O) + (yc A - yc O) * (yc A - yc O)) = 0 := by
    linear_combination (yc A - yc O) * (hA - hO) + (xc A - xc O) * hκ
  rcases huv with h | h
  · exact h ((mul_eq_zero.1 hu).resolve_right hN)
  · exact h ((mul_eq_zero.1 hv).resolve_right hN)

theorem mem_iff_cr {a : CoordLine K 2} {O A : Coord K 2} (hO : O ∈ a) (hA : A ∈ a) (hAO : A ≠ O)
    (X : Coord K 2) : X ∈ a ↔ crossProd2 (A - O) (X - O) = 0 := by
  obtain ⟨u, v, w, huv, rfl⟩ := exists_eq_of_line a
  rw [mem_lineOfEq] at hO hA ⊢
  have key := lin_eq_cr hO hA X
  have hκ := kappa_ne_zero huv hAO hO hA
  have hN := (ip_self_pos (sub_ne_zero.2 hAO)).ne'
  constructor
  · intro h
    rw [h, zero_mul] at key
    exact (mul_eq_zero.1 key.symm).resolve_left hκ
  · intro h
    rw [h, mul_zero] at key
    exact (mul_eq_zero.1 key).resolve_right hN

theorem sameSide_iff_cr {a : CoordLine K 2} {O A : Coord K 2} (hO : O ∈ a) (hA : A ∈ a)
    (hAO : A ≠ O) (X Y : Coord K 2) :
    SameSide a X Y ↔ 0 < crossProd2 (A - O) (X - O) * crossProd2 (A - O) (Y - O) := by
  obtain ⟨u, v, w, huv, rfl⟩ := exists_eq_of_line a
  rw [mem_lineOfEq] at hO hA
  rw [sameSide_lineOfEq_iff]
  have kX := lin_eq_cr hO hA X
  have kY := lin_eq_cr hO hA Y
  have hκ := kappa_ne_zero huv hAO hO hA
  have hN := ip_self_pos (sub_ne_zero.2 hAO)
  set κ := v * (xc A - xc O) - u * (yc A - yc O)
  have e : lin u v w X * lin u v w Y * (ip (A - O) (A - O) * ip (A - O) (A - O)) =
      κ * κ * (crossProd2 (A - O) (X - O) * crossProd2 (A - O) (Y - O)) := by
    linear_combination (lin u v w Y * ip (A - O) (A - O)) * kX +
      (κ * crossProd2 (A - O) (X - O)) * kY
  have hκ2 : 0 < κ * κ := mul_self_pos.2 hκ
  have hN2 : 0 < ip (A - O) (A - O) * ip (A - O) (A - O) := mul_pos hN hN
  constructor
  · intro h
    have h1 : 0 < κ * κ * (crossProd2 (A - O) (X - O) * crossProd2 (A - O) (Y - O)) := by
      rw [← e]; exact mul_pos h hN2
    exact (pos_iff_pos_of_mul_pos h1).1 hκ2
  · intro h
    have h1 : 0 < lin u v w X * lin u v w Y * (ip (A - O) (A - O) * ip (A - O) (A - O)) := by
      rw [e]; exact mul_pos hκ2 h
    exact (pos_iff_pos_of_mul_pos h1).2 hN2

theorem cr_ne_zero_of_not_collinear {A O B : Coord K 2}
    (h : ¬Collinear (Line := CoordLine K 2) A O B) : crossProd2 (A - O) (B - O) ≠ 0 := by
  intro h0
  obtain ⟨hAO, -, -⟩ := AffPt.not_collinear_of_eq h
  exact h (AffPt.collinear_of_smul hAO _ (exists_smul_of_cr_eq_zero (sub_ne_zero.2 hAO) h0))

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem not_collinear_of_cr {A O B : Coord K 2} (h : crossProd2 (A - O) (B - O) ≠ 0) :
    ¬Collinear (Line := CoordLine K 2) A O B := by
  have h1 : ¬Collinear (Line := CoordLine K 2) O A B :=
    FinitePart.not_collinear_of_det (by simpa only [crossProd2, xc_sub, yc_sub] using h)
  exact fun hc => h1 hc.swap12

/-! ### The part -/

theorem Sf_ge_half {P Q : Coord K 2} (hP : InfPt P) (hQ : InfPt Q) : 1 / 2 ≤ Sf P Q := by
  have h1 := (abs_mul_le_quarter hP.1.abs_le_half hQ.1.abs_le_half).1
  have h2 := (abs_mul_le_quarter hP.2.abs_le_half hQ.2.abs_le_half).1
  unfold Sf; rw [ip_two]; linarith

theorem Sf_pos {P Q : Coord K 2} (hP : InfPt P) (hQ : InfPt Q) : 0 < Sf P Q :=
  lt_of_lt_of_le (by norm_num) (Sf_ge_half hP hQ)

theorem isInf_Gf {P v : Coord K 2} (hP : InfPt P) (hv : InfPt v) : IsInf (Gf P v v) := by
  rw [Gf_self, ip_two, sq, crossProd2]
  exact ((hv.1.mul hv.1).add (hv.2.mul hv.2)).add
    (((hP.1.mul hv.2).sub (hP.2.mul hv.1)).mul ((hP.1.mul hv.2).sub (hP.2.mul hv.1)))

variable (K) in
/-- **The infinitesimal part** of the plane `K²`. -/
def infPart [HasInfinitesimal K] : ConvexPart (Coord K 2) (CoordLine K 2) where
  S := {X | InfPt X}
  convex := by
    rintro A B X ⟨hA1, hA2⟩ ⟨hB1, hB2⟩ hb
    obtain ⟨-, t, ht0, ht1, rfl⟩ := AffPt.sbtw_iff_param.1 (AffPt.between_iff.1 hb)
    have ht : |t| ≤ ((1 : ℕ) : K) := by rw [abs_of_pos ht0]; simpa using ht1.le
    constructor
    · simp only [xc_add, xc_smul, xc_sub]
      rw [mul_comm]; exact ((hB1.sub hA1).mul_bdd 1 ht).add hA1
    · simp only [yc_add, yc_smul, yc_sub]
      rw [mul_comm]; exact ((hB2.sub hA2).mul_bdd 1 ht).add hA2
  ray_meets := by
    rintro O X ⟨hO1, hO2⟩ hXO
    obtain ⟨ε, hε, hεi⟩ := HasInfinitesimal.exists_inf (K := K)
    have hεi' : IsInf ε := hεi
    have hpos : 0 < 1 + |xc X - xc O| + |yc X - yc O| := by positivity
    have hc0 : 0 < ε / (1 + |xc X - xc O| + |yc X - yc O|) := div_pos hε hpos
    refine ⟨(ε / (1 + |xc X - xc O| + |yc X - yc O|)) • (X - O) + O, ⟨?_, ?_⟩,
      (AffPt.mem_ray_iff hXO).2 ⟨_, hc0, rfl⟩⟩
    · simp only [xc_add, xc_smul, xc_sub]
      refine (IsInf.mono hεi' ?_).add hO1
      rw [abs_mul, abs_of_pos hc0, abs_of_pos hε, div_mul_eq_mul_div, div_le_iff₀ hpos]
      nlinarith [abs_nonneg (xc X - xc O), mul_nonneg hε.le (abs_nonneg (yc X - yc O))]
    · simp only [yc_add, yc_smul, yc_sub]
      refine (IsInf.mono hεi' ?_).add hO2
      rw [abs_mul, abs_of_pos hc0, abs_of_pos hε, div_mul_eq_mul_div, div_le_iff₀ hpos]
      nlinarith [abs_nonneg (yc X - yc O), mul_nonneg hε.le (abs_nonneg (xc X - xc O))]
  noncollinear := by
    obtain ⟨ε, hε, hεi⟩ := HasInfinitesimal.exists_inf (K := K)
    have hεi' : IsInf ε := hεi
    refine ⟨pt2 0 0, pt2 ε 0, pt2 0 ε, ⟨isInf_zero, isInf_zero⟩, ⟨hεi', isInf_zero⟩,
      ⟨isInf_zero, hεi'⟩, FinitePart.not_collinear_of_det ?_⟩
    simp only [xc_pt2, yc_pt2, sub_zero, mul_zero]
    exact mul_self_ne_zero.2 hε.ne'

section Model

variable [HasInfinitesimal K]

variable (K) in
/-- The points of the non-legendrian geometry. -/
def EPt : Type u := (infPart K).Pt

variable (K) in
/-- The lines of the non-legendrian geometry. -/
def ELn : Type u := (infPart K).Ln

instance instHasLines : HasLines (EPt K) (ELn K) :=
  inferInstanceAs (HasLines (infPart K).Pt (infPart K).Ln)

instance instHasBetween : HasBetween (EPt K) := inferInstanceAs (HasBetween (infPart K).Pt)

instance instPlaneOrder : PlaneOrder (EPt K) (ELn K) :=
  inferInstanceAs (PlaneOrder (infPart K).Pt (infPart K).Ln)

theorem E_ne_iff {A B : EPt K} : A ≠ B ↔ A.1 ≠ B.1 := not_congr Subtype.ext_iff

theorem E_collinear_iff {A B C : EPt K} :
    Collinear (Line := ELn K) A B C ↔ Collinear (Line := CoordLine K 2) A.1 B.1 C.1 :=
  ConvexPart.collinear_iff (σ := infPart K)

theorem E_sameSide_iff {a : ELn K} {A B : EPt K} : SameSide a A B ↔ SameSide a.1 A.1 B.1 :=
  ConvexPart.sameSide_iff (σ := infPart K)

theorem E_mem_ray_iff {O A X : EPt K} :
    X ∈ ray (Line := ELn K) O A ↔ X.1 ∈ ray (Line := CoordLine K 2) O.1 A.1 :=
  ConvexPart.mem_ray_iff (σ := infPart K)

theorem E_mem_interior_iff {A O B X : EPt K} :
    X ∈ Interior (Line := ELn K) A O B ↔ X.1 ∈ Interior (Line := CoordLine K 2) A.1 O.1 B.1 :=
  ConvexPart.mem_interior_iff (σ := infPart K)

theorem E_ray_eq_of_plane {O A C : EPt K}
    (h : ray (Line := CoordLine K 2) O.1 A.1 = ray (Line := CoordLine K 2) O.1 C.1) :
    ray (Line := ELn K) O A = ray (Line := ELn K) O C :=
  ConvexPart.ray_eq_of_plane (σ := infPart K) h

theorem E_sameAngle {A O B C D : EPt K} (h : SameAngle (Line := ELn K) A O B C D) :
    SameAngle (Line := CoordLine K 2) A.1 O.1 B.1 C.1 D.1 :=
  ConvexPart.sameAngle_of_sameAngle (σ := infPart K) h

/-- A point of the part on a half-ray of the plane emanating from a point of the part. -/
theorem exists_on_ray (O : EPt K) {y : Coord K 2} (hy : y ≠ 0) :
    ∃ (B : EPt K) (c : K), 0 < c ∧ B.1 - O.1 = c • y := by
  have hB₀ : y + O.1 ≠ O.1 := by simpa using hy
  obtain ⟨B₁, hB₁S, hB₁⟩ := (infPart K).ray_meets O.1 (y + O.1) O.2 hB₀
  obtain ⟨c, hc, hB₁e⟩ := (AffPt.mem_ray_iff hB₀).1 hB₁
  exact ⟨⟨B₁, hB₁S⟩, c, hc, by
    show B₁ - O.1 = c • y
    rw [hB₁e, add_sub_cancel_right, add_sub_cancel_right]⟩

/-- Sides of a line of the part in terms of the cross product. -/
theorem E_sameSide_iff_cr {a : ELn K} {O A : EPt K} (hO : O ∈ a) (hA : A ∈ a) (hAO : A ≠ O)
    (X Y : EPt K) :
    SameSide a X Y ↔
      0 < crossProd2 (A.1 - O.1) (X.1 - O.1) * crossProd2 (A.1 - O.1) (Y.1 - O.1) :=
  E_sameSide_iff.trans (sameSide_iff_cr (a := a.1) hO hA (E_ne_iff.1 hAO) X.1 Y.1)

theorem E_mem_iff_cr {a : ELn K} {O A : EPt K} (hO : O ∈ a) (hA : A ∈ a) (hAO : A ≠ O)
    (X : EPt K) : X ∈ a ↔ crossProd2 (A.1 - O.1) (X.1 - O.1) = 0 :=
  mem_iff_cr (a := a.1) hO hA (E_ne_iff.1 hAO) X.1

end Model

/-! ### Congruence -/

section Congruence

variable [IsEuclidean K]

omit [LinearOrder K] [IsStrictOrderedRing K] [IsEuclidean K] in
theorem Sf_param (A u : Coord K 2) (s : K) : Sf A (s • u + A) = W A + s * ip A u := by cring

theorem tn_param (A u : Coord K 2) {s : K} (hs : 0 ≤ s) :
    tn A (s • u + A) = s * rt (Gf A u u) / (W A + s * ip A u) := by
  have e : Gf A (s • u) (s • u) = (s * s) * Gf A u u := by cring
  unfold tn
  rw [add_sub_cancel_right, e, rt_mul (mul_self_nonneg s) (Gf_self_nonneg _ _),
    rt_mul_self_eq hs, Sf_param]

omit [IsEuclidean K] in
theorem ip_sq_le (A u : Coord K 2) : ip A u * ip A u ≤ ip A A * ip u u := by
  have : ip A A * ip u u - ip A u * ip A u = crossProd2 A u ^ 2 := by cring
  nlinarith [sq_nonneg (crossProd2 A u)]

/-- **Laying off a segment** (existence), in co-ordinates. -/
theorem layoff_exists {A B A' C' : Coord K 2} (hA : InfPt A) (hB : InfPt B) (hA' : InfPt A')
    (hAB : A ≠ B) (hC' : C' ≠ A') :
    ∃ s : K, 0 < s ∧ InfPt (s • (C' - A') + A') ∧ cs A' (s • (C' - A') + A') = cs A B := by
  have hu : C' - A' ≠ 0 := sub_ne_zero.2 hC'
  set u := C' - A' with hudef
  have hS := Sf_ge_half hA hB
  have hS0 := Sf_pos hA hB
  have hG0 := Gf_self_pos A (sub_ne_zero.2 hAB.symm)
  have hτ0 : 0 < tn A B := div_pos (rt_pos hG0) hS0
  -- the tangent of the length is infinitesimal
  have hτi : IsInf (tn A B) := by
    apply IsInf.of_mul_self
    have h4 : IsInf (((4 : ℕ) : K) * Gf A (B - A) (B - A)) := (isInf_Gf hA (hB.sub hA)).natMul 4
    refine h4.mono ?_
    have e : tn A B * tn A B = Gf A (B - A) (B - A) / (Sf A B * Sf A B) := by
      unfold tn; rw [div_mul_div_comm, rt_mul_self hG0.le]
    have hSS : 0 < Sf A B * Sf A B := mul_pos hS0 hS0
    rw [abs_of_nonneg (mul_self_nonneg _),
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg 4) hG0.le), e, div_le_iff₀ hSS]
    push_cast
    have hSS4 : 1 / 4 ≤ Sf A B * Sf A B := by nlinarith
    nlinarith [mul_nonneg hG0.le (sub_nonneg.2 hSS4)]
  set τ := tn A B with hτdef
  have hτh : τ ≤ 1 / 2 := (le_abs_self τ).trans hτi.abs_le_half
  -- the point `A'`
  have hWl : W A' ≤ 2 := by
    have h1 := (abs_mul_le_quarter hA'.1.abs_le_half hA'.1.abs_le_half).2
    have h2 := (abs_mul_le_quarter hA'.2.abs_le_half hA'.2.abs_le_half).2
    unfold W; rw [ip_two]; linarith
  have hWp := W_pos A'
  have hgu := Gf_self_pos A' hu
  set g := rt (Gf A' u u) with hgdef
  have hg : 0 < g := rt_pos hgu
  have hgg : g * g = Gf A' u u := rt_mul_self hgu.le
  have hipu : ip u u ≤ g * g := by rw [hgg]; exact ip_le_Gf_self A' u
  have hAA : ip A' A' ≤ 1 := by
    have := hWl; unfold W at this; linarith
  have hh : |ip A' u| ≤ g := by
    apply abs_le_of_sq_le_sq _ hg.le
    have h1 := ip_sq_le A' u
    have h2 := ip_self_nonneg u
    nlinarith
  have hD : g / 2 ≤ g - τ * ip A' u := by
    have h1 : τ * ip A' u ≤ τ * g :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans hh) hτ0.le
    nlinarith
  have hD0 : 0 < g - τ * ip A' u := by linarith
  set s := τ * W A' / (g - τ * ip A' u) with hsdef
  have hs : 0 < s := div_pos (mul_pos hτ0 hWp) hD0
  have hsD : s * (g - τ * ip A' u) = τ * W A' := div_mul_cancel₀ _ hD0.ne'
  -- the point laid off is in the part
  have hbound : ∀ z : K, z * z ≤ ip u u → IsInf (s * z) := by
    intro z hz
    have hzg : |z| ≤ g := by
      apply abs_le_of_sq_le_sq _ hg.le
      nlinarith
    refine (hτi.natMul 4).mono ?_
    have h4τ : (0 : K) < ((4 : ℕ) : K) * τ := mul_pos (by norm_num) hτ0
    rw [abs_mul, abs_of_pos hs, abs_of_pos h4τ, hsdef,
      div_mul_eq_mul_div, div_le_iff₀ hD0]
    push_cast
    have h1 : τ * W A' * |z| ≤ τ * (2 * g) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hWl hzg (abs_nonneg z) (by norm_num)) hτ0.le
    have h2 : τ * (2 * g) ≤ 4 * τ * (g - τ * ip A' u) := by
      have := mul_le_mul_of_nonneg_left hD hτ0.le
      nlinarith
    linarith
  have hInf : InfPt (s • u + A') := by
    constructor
    · simp only [xc_add, xc_smul]
      refine (hbound _ ?_).add hA'.1
      rw [ip_two]; nlinarith [mul_self_nonneg (yc u)]
    · simp only [yc_add, yc_smul]
      refine (hbound _ ?_).add hA'.2
      rw [ip_two]; nlinarith [mul_self_nonneg (xc u)]
  refine ⟨s, hs, hInf, ?_⟩
  have hS' := Sf_pos hA' hInf
  rw [cs_eq_iff_tn hS' hS0, tn_param A' u hs.le]
  rw [Sf_param] at hS'
  rw [div_eq_iff hS'.ne']
  linear_combination hsD

/-- **Laying off a segment** (uniqueness), in co-ordinates. -/
theorem layoff_unique {A' u : Coord K 2} (hu : u ≠ 0) {s₁ s₂ : K} (h1 : 0 < s₁) (h2 : 0 < s₂)
    (hS1 : 0 < Sf A' (s₁ • u + A')) (hS2 : 0 < Sf A' (s₂ • u + A'))
    (h : cs A' (s₁ • u + A') = cs A' (s₂ • u + A')) : s₁ = s₂ := by
  rw [cs_eq_iff_tn hS1 hS2, tn_param A' u h1.le, tn_param A' u h2.le] at h
  rw [Sf_param] at hS1 hS2
  rw [div_eq_div_iff hS1.ne' hS2.ne'] at h
  have hg := rt_pos (Gf_self_pos A' hu)
  have hW := W_pos A'
  have h3 : rt (Gf A' u u) * W A' * (s₁ - s₂) = 0 := by linear_combination h
  have := (mul_eq_zero.1 h3).resolve_left (mul_pos hg hW).ne'
  linarith

/-- Addition of segments, from the three relations between the metric at `B` on `A - B`, `C - B`. -/
theorem cs_add_of {A B C : Coord K 2} {t G : K} (ht0 : 0 ≤ t) (ht1 : 0 ≤ 1 - t) (hG : 0 ≤ G)
    (e1 : Gf B (A - B) (A - B) = (t * t) * G)
    (e2 : Gf B (C - B) (C - B) = ((1 - t) * (1 - t)) * G)
    (e3 : Gf B (A - B) (C - B) = -(t * (1 - t)) * G) :
    cs A C = cs A B * cs B C - sn A B * sn B C := by
  have hr : rt G * rt G = G := rt_mul_self hG
  have hcos : -(t * (1 - t)) * G = W B * Sf A C - Sf B A * Sf B C := by
    rw [← e3, Gf_cos]
  have s1 : sn B A = t * rt G / (w B * w A) := by
    unfold sn; rw [e1, rt_mul (mul_self_nonneg t) hG, rt_mul_self_eq ht0]
  have s2 : sn B C = (1 - t) * rt G / (w B * w C) := by
    unfold sn; rw [e2, rt_mul (mul_self_nonneg _) hG, rt_mul_self_eq ht1]
  have num : Sf B A * Sf B C - (t * rt G) * ((1 - t) * rt G) = W B * Sf A C := by
    linear_combination (-(t * (1 - t))) * hr + hcos
  rw [cs_comm A B, sn_comm A B, s1, s2]
  unfold cs
  have e4 : Sf B A / (w B * w A) * (Sf B C / (w B * w C)) -
      t * rt G / (w B * w A) * ((1 - t) * rt G / (w B * w C)) =
      (Sf B A * Sf B C - (t * rt G) * ((1 - t) * rt G)) / ((w B * w B) * (w A * w C)) := by
    ring
  rw [e4, num, w_mul_self, mul_div_mul_left _ _ (W_pos B).ne']

/-- **Addition of segments**: the cosine of the sum. -/
theorem cs_add {A B C : Coord K 2} (h : Sbtw K A B C) :
    cs A C = cs A B * cs B C - sn A B * sn B C := by
  obtain ⟨hAC, t, ht0, ht1, rfl⟩ := AffPt.sbtw_iff_param.1 h
  exact cs_add_of (G := Gf (t • (C - A) + A) (C - A) (C - A)) ht0.le (by linarith)
    (Gf_self_nonneg _ _) (by cring) (by cring) (by cring)

theorem kc_eq_of_cs_eq {A B C A' B' C' : Coord K 2} (hB : B ≠ A) (hC : C ≠ A) (hB' : B' ≠ A')
    (hC' : C' ≠ A') (h1 : cs A B = cs A' B') (h2 : cs A C = cs A' C') (h3 : cs B C = cs B' C') :
    kc A (B - A) (C - A) = kc A' (B' - A') (C' - A') := by
  have l := kc_mul_sn hB hC
  have l' := kc_mul_sn hB' hC'
  have hP : 0 < sn A B * sn A C := mul_pos (sn_pos hB) (sn_pos hC)
  apply mul_right_cancel₀ hP.ne'
  rw [l, sn_eq_of_cs_eq h1, sn_eq_of_cs_eq h2, l', h1, h2, h3]

theorem cs_eq_of_kc_eq {A B C A' B' C' : Coord K 2} (hB : B ≠ A) (hC : C ≠ A) (hB' : B' ≠ A')
    (hC' : C' ≠ A') (h1 : cs A B = cs A' B') (h2 : cs A C = cs A' C')
    (hk : kc A (B - A) (C - A) = kc A' (B' - A') (C' - A')) : cs B C = cs B' C' := by
  have l := kc_mul_sn hB hC
  have l' := kc_mul_sn hB' hC'
  rw [hk, sn_eq_of_cs_eq h1, sn_eq_of_cs_eq h2, h1, h2] at l
  linarith

theorem kc_of_sameAngle {A O B C D : Coord K 2} (h : ¬Collinear (Line := CoordLine K 2) A O B)
    (hs : SameAngle (Line := CoordLine K 2) A O B C D) :
    kc O (C - O) (D - O) = kc O (A - O) (B - O) := by
  obtain ⟨c, d, hc, hd, hcd⟩ := AffPt.sameAngle_cases h hs
  rcases hcd with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2, kc_smul _ _ _ hc hd]
  · rw [e1, e2, kc_smul _ _ _ hc hd, kc_comm]

/-- **Laying off an angle** (existence), in co-ordinates: a direction `y` at `O'` on the side of
`dv` of the direction `u` making with `u` the angle of the directions `a`, `b` at `O`. -/
theorem ang_layoff {O a b : Coord K 2} (hab : crossProd2 a b ≠ 0) {O' u dv : Coord K 2}
    (hu : u ≠ 0) (hd : crossProd2 u dv ≠ 0) :
    ∃ y : Coord K 2, 0 < crossProd2 u y * crossProd2 u dv ∧ kc O' u y = kc O a b := by
  set p := Gf O a b with hp
  have hq : 0 < w O * |crossProd2 a b| := mul_pos (w_pos O) (abs_pos.2 hab)
  set q := w O * |crossProd2 a b| with hqdef
  have hpq : 0 < p ^ 2 + q ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg p) (pow_pos hq 2)
  have hk : kc O a b = p / rt (p ^ 2 + q ^ 2) := by
    refine kc_of_comp (k := 1) one_pos hpq (by rw [one_mul]) ?_
    rw [hqdef, mul_pow, sq_abs, sq (w O), w_mul_self]; ring
  have hGu := Gf_self_pos O' hu
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · refine ⟨(w O' * p) • u + (-q) • jv O' u, ?_, ?_⟩
    · rw [cr_rot]
      exact mul_pos_of_neg_of_neg (by nlinarith) hneg
    · have hpq' : 0 < p ^ 2 + (-q) ^ 2 := by rw [neg_sq]; exact hpq
      rw [kc_rot hu p (-q) hpq', neg_sq, hk]
  · refine ⟨(w O' * p) • u + q • jv O' u, ?_, ?_⟩
    · rw [cr_rot]
      exact mul_pos (mul_pos hq hGu) hpos
    · rw [kc_rot hu p q hpq, hk]

/-- **Laying off an angle** (uniqueness), in co-ordinates. -/
theorem ang_unique {P u v y : Coord K 2} (hu : u ≠ 0)
    (hs : 0 < crossProd2 u v * crossProd2 u y) (hk : kc P u v = kc P u y) :
    ∃ c : K, 0 < c ∧ v = c • y := by
  have h0 := cr_eq_zero_of_kc_eq hu hs hk
  have hy : y ≠ 0 := by
    rintro rfl
    have : crossProd2 u (0 : Coord K 2) = 0 := by cring
    rw [this, mul_zero] at hs; exact lt_irrefl _ hs
  have h0' : crossProd2 y v = 0 := by rw [cr_anticomm, h0, neg_zero]
  have hv := exists_smul_of_cr_eq_zero hy h0'
  refine ⟨ip y v / ip y y, ?_, hv⟩
  set c := ip y v / ip y y
  rw [hv, cr_smul_right] at hs
  by_contra hc
  push Not at hc
  nlinarith [mul_self_nonneg (crossProd2 u y)]

end Congruence

end Elliptic

end HilbertFoundations
