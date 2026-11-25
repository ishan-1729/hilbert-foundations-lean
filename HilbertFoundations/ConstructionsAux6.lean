import HilbertFoundations.ConstructionsAux5

/-!
# Helper module for `Constructions.lean`: the field `Ω`, conjugates, towers of square roots

This module contains no unit of Hilbert's text. It proves:

* `omega_conj`: an algebraic number conjugate to a number of `Ω` is a real number of `Ω`;
* `sqrt_two_sqrt_two_sub_two_not_mem`: `√(2√2 - 2) ∉ Ω`;
* `pythClosure_frame_iff`, `rt_frame_iff_omega`: over `ℝ`, the points constructible by
  straight-edge and transferer from the frame `(0,0)`, `(1,0)`, `(0,1)` are the points with
  coordinates in `Ω`; `theorem41_needs_frame`: without the unit segment the converse half of
  Theorem 41 fails;
* towers of square roots `towerField`, Hilbert's condition `RealTower` (every radicand is a
  nonnegative real number under every embedding into `ℂ`, i.e. for every choice of the signs of
  the square roots) and `theorem44_noParam`: the numbers of such a tower lie in `Ω` iff Hilbert's
  condition holds (Theorem 44 without parameters);
* the vertices of the regular `n`-gons for `n = 3, 4, 5, 6, 8, 10` have coordinates in `Ω`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

open Coord Polynomial
open scoped Real

/-! ## Conjugates of the numbers of `Ω` -/

/-- **The conjugates of a number of `Ω` are real numbers of `Ω`** (§ 37). -/
theorem omega_conj {x : ℝ} (hx : x ∈ Omega) {z : ℂ} (hz : aeval z (minpoly ℚ x) = 0) :
    ∃ r ∈ Omega, z = (r : ℂ) := by
  have hint : IsIntegral ℚ x := (Omega.isAlgebraic hx).isIntegral
  let pb := IntermediateField.adjoin.powerBasis hint
  have hz' : aeval z (minpoly ℚ pb.gen) = 0 := by
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen]; exact hz
  let φ := pb.lift z hz'
  have hφ : φ pb.gen = z := pb.lift_gen z hz'
  let F : Subfield ℝ := (IntermediateField.adjoin ℚ ({x} : Set ℝ)).toSubfield
  have hxF : x ∈ F := IntermediateField.mem_adjoin_simple_self ℚ x
  let σ : F →+* ℂ := φ.toRingHom
  obtain ⟨F', hle, hxF', σ', e, r, hr, hσ⟩ := omega_ext hx F σ
  refine ⟨r, hr, ?_⟩
  rw [← hσ, show (⟨x, hxF'⟩ : F') = ⟨(⟨x, hxF⟩ : F), hle hxF⟩ from rfl, e]
  rw [← hφ, IntermediateField.adjoin.powerBasis_gen]
  rfl

/-- The real numbers of `ℚ` inside `ℝ`. -/
noncomputable def ratField : Subfield ℝ := (Rat.castHom ℝ).fieldRange

theorem mem_ratField {x : ℝ} : x ∈ ratField ↔ ∃ q : ℚ, (q : ℝ) = x := by
  simp [ratField, RingHom.mem_fieldRange]

/-- Every embedding of `ℚ` into `ℂ` is the inclusion. -/
theorem ratField_hom (σ : ratField →+* ℂ) (x : ratField) : σ x = ((x : ℝ) : ℂ) := by
  obtain ⟨q, hq⟩ := mem_ratField.1 x.2
  have : x = (q : ratField) := Subtype.ext (by rw [← hq]; simp)
  rw [this, map_ratCast]; simp

/-- **Hilbert's example** (§ 37): `√(2√2 - 2) ∉ Ω`, since its conjugate `√(-2√2 - 2)` is
imaginary. -/
theorem sqrt_two_sqrt_two_sub_two_not_mem : Real.sqrt (2 * Real.sqrt 2 - 2) ∉ Omega := by
  intro hy
  set b := Real.sqrt 2 with hb
  have hb2 : b ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hb1 : 1 ≤ b := by rw [hb]; exact Real.one_le_sqrt.2 (by norm_num)
  have hb2F : b ^ 2 ∈ ratField := by rw [hb2]; exact two_mem_subfield _
  have hbF : b ∉ ratField := by
    intro h; obtain ⟨q, hq⟩ := mem_ratField.1 h
    exact irrational_sqrt_two ⟨q, hq⟩
  have hE := quadExt_closure hb2F
  let σ0 : ratField →+* ℂ := Complex.ofRealHom.comp ratField.subtype
  obtain ⟨σ1, -, hσ1⟩ := exists_ext hE hbF σ0 (-(b : ℂ)) (by
    simp [σ0])
  obtain ⟨F', hle, hyF, σ', e, r, -, hσ⟩ := omega_ext hy _ σ1
  set y := Real.sqrt (2 * b - 2) with hydef
  have hy2 : y ^ 2 = 2 * b - 2 := Real.sq_sqrt (by linarith)
  have hbF' : b ∈ F' := hle hE.mem
  have key : (⟨y, hyF⟩ : F') ^ 2 = ⟨b, hbF'⟩ + ⟨b, hbF'⟩ - 1 - 1 :=
    Subtype.ext (by simp [hy2]; ring)
  have h1 := congrArg σ' key
  rw [map_pow, hσ, map_sub, map_sub, map_add, map_one] at h1
  have hb' : σ' ⟨b, hbF'⟩ = -(b : ℂ) := by
    rw [← hσ1]; exact e ⟨b, hE.mem⟩
  rw [hb'] at h1
  have h2 : r ^ 2 = -2 * b - 2 := by
    have := congrArg Complex.re h1
    simp [← Complex.ofReal_pow] at this
    linarith
  nlinarith [sq_nonneg r]

/-! ## Theorem 41 over `ℝ` and Hilbert's field `Ω` -/

/-- The frame `(0,0)`, `(1,0)`, `(0,1)` of the coordinate plane. -/
def frameSet (K : Type*) [Field K] : Set (Coord K 2) := {pt2 0 0, pt2 1 0, pt2 0 1}

theorem omega_closed : PythClosed (fun x : ℝ => x ∈ Omega) where
  add := Omega.add_mem
  sub := Omega.sub_mem
  mul := Omega.mul_mem
  div hx hy _ := Omega.div_mem hx hy
  sqrt {x y z} hx hy hz hzz := by
    have : z = Real.sqrt (x ^ 2 + y ^ 2) := by rw [← hzz, Real.sqrt_sq hz]
    rw [this]; exact Omega.sqrt_sq_add_sq_mem hx hy

/-- **`Ω(ℚ) = Ω`**: the closure of the coordinates of the frame is Hilbert's field `Ω`. -/
theorem pythClosure_frame_iff {x : ℝ} :
    PythClosure (coordSet (frameSet ℝ)) x ↔ x ∈ Omega := by
  constructor
  · intro h
    refine PythClosure.le_of_closed omega_closed ?_ h
    rintro y ⟨X, hX, rfl | rfl⟩ <;>
      rcases hX with rfl | rfl | rfl <;> simp [Omega.one_mem, Omega.zero_mem]
  · intro h
    have h1 : PythClosure (coordSet (frameSet ℝ)) 1 :=
      .base ⟨pt2 1 0, by simp [frameSet], Or.inl rfl⟩
    induction h with
    | one => exact h1
    | add _ _ ha hb => exact .add ha hb
    | sub _ _ ha hb => exact .sub ha hb
    | mul _ _ ha hb => exact .mul ha hb
    | div _ _ hb0 ha hb => exact .div ha hb hb0
    | @sqrt w _ hw =>
      exact .sqrt h1 hw (Real.sqrt_nonneg _) (by rw [Real.sq_sqrt (by positivity)]; ring)

/-- Over `ℝ`, **the points constructible by straight-edge and transferer from the frame are the
points with coordinates in `Ω`**. -/
theorem rt_frame_iff_omega {X : Coord ℝ 2} :
    RulerTransferer (frameSet ℝ) X ↔ xc X ∈ Omega ∧ yc X ∈ Omega := by
  rw [theorem41_coord (by simp [frameSet]) (by simp [frameSet]) (by simp [frameSet]),
    pythClosure_frame_iff, pythClosure_frame_iff]

/-- **Without the unit segment, the converse half of Theorem 41 fails**: there are given points
`(0,0)`, `(c,0)`, `(0,c)` (a frame with another unit) and a point `(1,0)` whose coordinates lie in
`Ω(R)` but which is not constructible by straight-edge and transferer. -/
theorem theorem41_needs_frame :
    ∃ c : ℝ, c ≠ 0 ∧ PythClosure (coordSet ({pt2 0 0, pt2 c 0, pt2 0 c} : Set (Coord ℝ 2))) 1 ∧
      PythClosure (coordSet ({pt2 0 0, pt2 c 0, pt2 0 c} : Set (Coord ℝ 2))) 0 ∧
      ¬RulerTransferer ({pt2 0 0, pt2 c 0, pt2 0 c} : Set (Coord ℝ 2)) (pt2 1 0) := by
  have : ∃ b : ℝ, b ∉ Omega := by
    by_contra h; push Not at h
    exact Omega_ne_top (eq_top_iff.2 fun x _ => h x)
  obtain ⟨b, hb⟩ := this
  have hb0 : b ≠ 0 := by rintro rfl; exact hb Omega.zero_mem
  refine ⟨b⁻¹, inv_ne_zero hb0, ?_, ?_, ?_⟩
  · have hc : PythClosure (coordSet ({pt2 0 0, pt2 b⁻¹ 0, pt2 0 b⁻¹} : Set (Coord ℝ 2))) b⁻¹ :=
      .base ⟨pt2 b⁻¹ 0, by simp, Or.inl rfl⟩
    have := PythClosure.div hc hc (inv_ne_zero hb0)
    rwa [div_self (inv_ne_zero hb0)] at this
  · exact .base ⟨pt2 0 0, by simp, Or.inl rfl⟩
  · intro h
    have := rt_closed omega_closed (l := b) hb0 (by
      rintro X (rfl | rfl | rfl) <;> simp [hb0, Omega.zero_mem, Omega.one_mem]) h
    exact hb (by simpa using this.1)

/-! ## Towers of square roots (§ 39) -/

/-- `x` is **totally nonnegative** in `F`: every embedding of `F` into `ℂ` maps it to a
nonnegative real number. -/
def TotNonneg (F : Subfield ℝ) (x : ℝ) : Prop :=
  ∃ hx : x ∈ F, ∀ σ : F →+* ℂ, ∃ t : ℝ, 0 ≤ t ∧ σ ⟨x, hx⟩ = (t : ℂ)

/-- The field obtained from `ℚ` by adjoining the square roots of the radicands of the list, the
last radicand first. -/
noncomputable def towerField : List ℝ → Subfield ℝ
  | [] => ratField
  | a :: l => Subfield.closure ((towerField l : Set ℝ) ∪ {Real.sqrt a})

/-- A **tower of square roots**: each radicand is a nonnegative number of the field obtained
before. -/
def ValidTower : List ℝ → Prop
  | [] => True
  | a :: l => ValidTower l ∧ a ∈ towerField l ∧ 0 ≤ a

/-- **Hilbert's condition** (§ 39): every radicand is a nonnegative real number under every
embedding of the field obtained before, i.e. for either sign of each square root extracted
before. -/
def RealTower : List ℝ → Prop
  | [] => True
  | a :: l => RealTower l ∧ TotNonneg (towerField l) a

/-- Sums of squares of numbers of `F`. -/
inductive SOSIn (F : Subfield ℝ) : ℝ → Prop
  | zero : SOSIn F 0
  | cons {x u : ℝ} : x ∈ F → SOSIn F u → SOSIn F (x ^ 2 + u)

namespace SOSIn

variable {F G : Subfield ℝ}

theorem mem {u : ℝ} (h : SOSIn F u) : u ∈ F := by
  induction h with
  | zero => exact F.zero_mem
  | cons hx _ ih => exact F.add_mem (F.pow_mem hx 2) ih

theorem nonneg {u : ℝ} (h : SOSIn F u) : 0 ≤ u := by
  induction h with
  | zero => exact le_rfl
  | cons _ _ ih => positivity

theorem mono (hFG : F ≤ G) {u : ℝ} (h : SOSIn F u) : SOSIn G u := by
  induction h with
  | zero => exact .zero
  | cons hx _ ih => exact .cons (hFG hx) ih

theorem sq {x : ℝ} (hx : x ∈ F) : SOSIn F (x ^ 2) := by simpa using SOSIn.cons hx SOSIn.zero

theorem add {u v : ℝ} (hu : SOSIn F u) (hv : SOSIn F v) : SOSIn F (u + v) := by
  induction hu with
  | zero => simpa using hv
  | cons hx _ ih => rw [add_assoc]; exact .cons hx ih

theorem sq_mul {x u : ℝ} (hx : x ∈ F) (hu : SOSIn F u) : SOSIn F (x ^ 2 * u) := by
  induction hu with
  | zero => simpa using SOSIn.zero
  | @cons y v hy _ ih =>
    rw [mul_add, ← mul_pow]; exact .cons (F.mul_mem hx hy) ih

theorem mul {u v : ℝ} (hu : SOSIn F u) (hv : SOSIn F v) : SOSIn F (u * v) := by
  induction hu with
  | zero => simpa using SOSIn.zero
  | cons hx _ ih => rw [add_mul]; exact (sq_mul hx hv).add ih

/-- The square root of a sum of squares of numbers of `Ω` lies in `Ω` (§ 39: the square root of a
sum of any number of squares by repeated square roots of sums of two squares). -/
theorem sqrt_mem_omega (hF : F ≤ Omega) {u : ℝ} (h : SOSIn F u) : Real.sqrt u ∈ Omega := by
  induction h with
  | zero => simp
  | @cons x u hx hu ih =>
    have : Real.sqrt (x ^ 2 + u) = Real.sqrt (x ^ 2 + Real.sqrt u ^ 2) := by
      rw [Real.sq_sqrt hu.nonneg]
    rw [this]; exact Omega.sqrt_sq_add_sq_mem (hF hx) ih

end SOSIn

/-- `g` is a **quotient of two sums of squares** of numbers of `F`. -/
def QSOS (F : Subfield ℝ) (g : ℝ) : Prop :=
  ∃ u v : ℝ, SOSIn F u ∧ SOSIn F v ∧ v ≠ 0 ∧ g = u / v

theorem towerField_quadExt {a : ℝ} {l : List ℝ} (ha : a ∈ towerField l) (ha0 : 0 ≤ a) :
    IsQuadExt (towerField l) (towerField (a :: l)) (Real.sqrt a) :=
  quadExt_closure (by rw [Real.sq_sqrt ha0]; exact ha)

/-- A nonnegative rational number is a sum of four squares of rational numbers (from Lagrange's
theorem), hence a quotient of sums of squares in `ℚ`. -/
theorem qsos_rat {g : ℝ} (hg : g ∈ ratField) (hg0 : 0 ≤ g) : QSOS ratField g := by
  obtain ⟨q, rfl⟩ := mem_ratField.1 hg
  have hq0 : 0 ≤ q := by exact_mod_cast hg0
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = q.num := ⟨q.num.toNat, Int.toNat_of_nonneg (Rat.num_nonneg.2 hq0)⟩
  obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares (n * q.den)
  have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have mem : ∀ m : ℕ, (m : ℝ) ∈ ratField := fun m => mem_ratField.2 ⟨m, by simp⟩
  refine ⟨(a : ℝ) ^ 2 + ((b : ℝ) ^ 2 + ((c : ℝ) ^ 2 + ((d : ℝ) ^ 2 + 0))),
    (q.den : ℝ) ^ 2 + 0, .cons (mem a) (.cons (mem b) (.cons (mem c) (.cons (mem d) .zero))),
    .cons (mem _) .zero, by positivity, ?_⟩
  have h1 : ((a : ℝ) ^ 2 + ((b : ℝ) ^ 2 + ((c : ℝ) ^ 2 + ((d : ℝ) ^ 2 + 0)))) = n * q.den := by
    have := congrArg (fun m : ℕ => (m : ℝ)) habcd; push_cast at this; linarith
  rw [h1]
  have hq : (q : ℝ) = (q.num : ℝ) / q.den := by exact_mod_cast (Rat.num_div_den q).symm
  rw [hq, ← hn, add_zero]; push_cast
  rw [div_eq_div_iff hd (pow_ne_zero 2 hd)]; ring

/-- **Hilbert's lemma of § 39**: in a tower of square roots, every totally nonnegative number is
a quotient of two sums of squares of numbers of the tower. The step: for `g = r + s√a`, the trace
`φ = 2r` and the norm `ψ = r² - s² a` are totally nonnegative in the field below, `g` satisfies
`g² - φ g + ψ = 0`, and `g = (g² + ψ) / φ`. -/
theorem tower_qsos : ∀ l : List ℝ, ValidTower l → ∀ g : ℝ, TotNonneg (towerField l) g →
    QSOS (towerField l) g := by
  intro l
  induction l with
  | nil =>
    intro _ g ⟨hg, hσ⟩
    obtain ⟨t, ht, e⟩ := hσ (Complex.ofRealHom.comp ratField.subtype)
    have e' : ((g : ℝ) : ℂ) = (t : ℂ) := e
    have : g = t := by exact_mod_cast e'
    exact qsos_rat hg (this ▸ ht)
  | cons a l ih =>
    intro ⟨hv, ha, ha0⟩ g hg
    have hE := towerField_quadExt ha ha0
    set F := towerField l
    set b := Real.sqrt a with hbdef
    have hb2 : b ^ 2 = a := Real.sq_sqrt ha0
    by_cases hbF : b ∈ F
    · have e := hE.eq_of_mem hbF
      rw [e] at hg ⊢; exact ih hv g hg
    obtain ⟨hgE, hσg⟩ := hg
    obtain ⟨r, hr, s, hs, hgrs⟩ := hE.repr g hgE
    have hsq : b ^ 2 ∈ F := hE.sq_mem
    -- the two conjugates of `g` over `F`
    have conj : ∀ σ : F →+* ℂ, ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ 0 ≤ t₂ ∧
        σ ⟨r, hr⟩ * 2 = (t₁ : ℂ) + t₂ ∧
        σ ⟨r, hr⟩ ^ 2 - σ ⟨s, hs⟩ ^ 2 * σ ⟨b ^ 2, hsq⟩ = (t₁ : ℂ) * t₂ := by
      intro σ
      obtain ⟨τ, hτ⟩ := IsAlgClosed.exists_pow_nat_eq (σ ⟨b ^ 2, hsq⟩) two_pos
      obtain ⟨σ₁, e₁, h₁⟩ := exists_ext hE hbF σ τ hτ
      obtain ⟨σ₂, e₂, h₂⟩ := exists_ext hE hbF σ (-τ) (by rw [neg_sq]; exact hτ)
      obtain ⟨t₁, ht₁, et₁⟩ := hσg σ₁
      obtain ⟨t₂, ht₂, et₂⟩ := hσg σ₂
      have hgE' : (⟨g, hgE⟩ : towerField (a :: l)) =
          ⟨((⟨r, hr⟩ : F) : ℝ), hE.le hr⟩ + ⟨((⟨s, hs⟩ : F) : ℝ), hE.le hs⟩ * ⟨b, hE.mem⟩ :=
        Subtype.ext (by simp [hgrs])
      rw [hgE', map_add, map_mul, e₁ ⟨r, hr⟩, e₁ ⟨s, hs⟩, h₁] at et₁
      rw [hgE', map_add, map_mul, e₂ ⟨r, hr⟩, e₂ ⟨s, hs⟩, h₂] at et₂
      refine ⟨t₁, t₂, ht₁, ht₂, ?_, ?_⟩
      · rw [← et₁, ← et₂]; ring
      · rw [← hτ, ← et₁, ← et₂]; ring
    -- the trace `φ = 2r` and the norm `ψ = r² - s² b²`
    have hTm : 2 * r ∈ F := F.mul_mem (two_mem_subfield F) hr
    have hNm : r ^ 2 - s ^ 2 * b ^ 2 ∈ F := F.sub_mem (F.pow_mem hr 2) (F.mul_mem (F.pow_mem hs 2) hsq)
    have hT : TotNonneg F (2 * r) := by
      refine ⟨hTm, fun σ => ?_⟩
      obtain ⟨t₁, t₂, ht₁, ht₂, e1, -⟩ := conj σ
      refine ⟨t₁ + t₂, add_nonneg ht₁ ht₂, ?_⟩
      have : (⟨2 * r, hTm⟩ : F) = ⟨r, hr⟩ + ⟨r, hr⟩ := Subtype.ext (by simp; ring)
      rw [this, map_add, show σ ⟨r, hr⟩ + σ ⟨r, hr⟩ = σ ⟨r, hr⟩ * 2 by ring, e1]; simp
    have hN : TotNonneg F (r ^ 2 - s ^ 2 * b ^ 2) := by
      refine ⟨hNm, fun σ => ?_⟩
      obtain ⟨t₁, t₂, ht₁, ht₂, -, e2⟩ := conj σ
      refine ⟨t₁ * t₂, mul_nonneg ht₁ ht₂, ?_⟩
      have : (⟨r ^ 2 - s ^ 2 * b ^ 2, hNm⟩ : F) = ⟨r, hr⟩ ^ 2 - ⟨s, hs⟩ ^ 2 * ⟨b ^ 2, hsq⟩ :=
        Subtype.ext (by simp)
      rw [this, map_sub, map_mul, map_pow, map_pow, e2]; push_cast; ring
    have hgT : g * (2 * r) = g ^ 2 + (r ^ 2 - s ^ 2 * b ^ 2) := by rw [hgrs]; ring
    obtain ⟨u1, v1, hu1, hv1, hv10, hT1⟩ := ih hv _ hT
    obtain ⟨u2, v2, hu2, hv2, hv20, hN2⟩ := ih hv _ hN
    by_cases hr0 : 2 * r = 0
    · -- then `g = 0`
      have hN0 : 0 ≤ r ^ 2 - s ^ 2 * b ^ 2 := by
        obtain ⟨_, hσ⟩ := hN
        obtain ⟨t, ht, e⟩ := hσ (Complex.ofRealHom.comp F.subtype)
        have e' : ((r ^ 2 - s ^ 2 * b ^ 2 : ℝ) : ℂ) = (t : ℂ) := e
        have : r ^ 2 - s ^ 2 * b ^ 2 = t := by exact_mod_cast e'
        rw [this]; exact ht
      have hr' : r = 0 := by linarith
      have hg0 : g = 0 := by
        have : g ^ 2 = 0 := by
          rw [hgrs, hr']; rw [hr'] at hN0; nlinarith [sq_nonneg (s * b)]
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      have h1 : SOSIn (towerField (a :: l)) 1 := by
        have := SOSIn.sq (F := towerField (a :: l)) (Subfield.one_mem _)
        rwa [one_pow] at this
      exact ⟨0, 1, .zero, h1, one_ne_zero, by simp [hg0]⟩
    · have hu10 : u1 ≠ 0 := by rintro rfl; rw [zero_div] at hT1; exact hr0 hT1
      refine ⟨(g ^ 2 * v2 + u2) * v1, v2 * u1,
        ((SOSIn.sq_mul hgE (hv2.mono hE.le)).add (hu2.mono hE.le)).mul (hv1.mono hE.le),
        (hv2.mono hE.le).mul (hu1.mono hE.le), mul_ne_zero hv20 hu10, ?_⟩
      rw [hT1, hN2] at hgT
      have e1 : g * (u1 / v1) * (v1 * v2) = g * u1 * v2 := by field_simp
      have e2 : (g ^ 2 + u2 / v2) * (v1 * v2) = (g ^ 2 * v2 + u2) * v1 := by
        field_simp
      have key : g * u1 * v2 = (g ^ 2 * v2 + u2) * v1 := by rw [← e1, ← e2, hgT]
      rw [eq_div_iff (mul_ne_zero hv20 hu10)]; linear_combination key

/-- **Theorem 44 without parameters, sufficiency**: if Hilbert's condition holds, every number of
the tower lies in `Ω`, i.e. is constructible by straight-edge and transferer. -/
theorem tower_le_omega : ∀ l : List ℝ, ValidTower l → RealTower l → towerField l ≤ Omega
  | [], _, _ => fun x hx => by
    obtain ⟨q, rfl⟩ := mem_ratField.1 hx; exact SubfieldClass.ratCast_mem Omega q
  | a :: l, ⟨hv, ha, ha0⟩, ⟨hr, htn⟩ => by
    have ih := tower_le_omega l hv hr
    obtain ⟨u, v, hu, hv', hv0, hauv⟩ := tower_qsos l hv a htn
    have hvpos : 0 < v := lt_of_le_of_ne hv'.nonneg (Ne.symm hv0)
    have hsqrt : Real.sqrt a ∈ Omega := by
      have : Real.sqrt a = Real.sqrt (u * v) / v := by
        rw [hauv, show u / v = (u * v) / v ^ 2 by field_simp,
          Real.sqrt_div' _ (sq_nonneg v), Real.sqrt_sq hvpos.le]
      rw [this]; exact Omega.div_mem ((hu.mul hv').sqrt_mem_omega ih) (ih hv'.mem)
    show Subfield.closure _ ≤ Omega
    rw [Subfield.closure_le]
    rintro x (hx | hx)
    · exact ih hx
    · rw [Set.mem_singleton_iff.1 hx]; exact hsqrt

/-- **Theorem 44 without parameters, necessity**: if the numbers of the tower lie in `Ω`, every
radicand is a nonnegative real number under every embedding. -/
theorem realTower_of_le_omega : ∀ l : List ℝ, ValidTower l → towerField l ≤ Omega → RealTower l
  | [], _, _ => trivial
  | a :: l, ⟨hv, ha, ha0⟩, hle => by
    have hE := towerField_quadExt ha ha0
    refine ⟨realTower_of_le_omega l hv (hE.le.trans hle), ha, fun σ => ?_⟩
    obtain ⟨F', h1, hbF', σ', e, r, -, hσ⟩ := omega_ext (hle hE.mem) (towerField l) σ
    refine ⟨r ^ 2, sq_nonneg r, ?_⟩
    rw [← e ⟨a, ha⟩]
    rw [show (⟨((⟨a, ha⟩ : towerField l) : ℝ), h1 ha⟩ : F') = ⟨Real.sqrt a, hbF'⟩ ^ 2 from
      Subtype.ext (by simp [Real.sq_sqrt ha0]), map_pow, hσ]
    push_cast; ring

/-- **Theorem 44 without parameters**: the numbers of a tower of square roots are constructible by
straight-edge and transferer (lie in `Ω`) iff every radicand is a nonnegative real number for
every choice of the signs of the square roots extracted before. -/
theorem theorem44_noParam (l : List ℝ) (hv : ValidTower l) :
    RealTower l ↔ towerField l ≤ Omega :=
  ⟨tower_le_omega l hv, realTower_of_le_omega l hv⟩

/-! ## Regular polygons -/

theorem sqrt_two_mem : Real.sqrt 2 ∈ Omega := by
  have := Omega.sqrt_mem Omega.one_mem; norm_num at this; exact this

theorem sqrt_three_mem : Real.sqrt 3 ∈ Omega := by
  have := Omega.sqrt_mem sqrt_two_mem
  rw [Real.sq_sqrt (by norm_num)] at this; norm_num at this; exact this

theorem sqrt_five_mem : Real.sqrt 5 ∈ Omega := by
  have h2 : (2 : ℝ) ∈ Omega := two_mem_subfield _
  have := Omega.sqrt_mem h2; norm_num at this; exact this

theorem cos_sin_nat_mul_mem {θ : ℝ} (hc : Real.cos θ ∈ Omega) (hs : Real.sin θ ∈ Omega) :
    ∀ k : ℕ, Real.cos (k * θ) ∈ Omega ∧ Real.sin (k * θ) ∈ Omega
  | 0 => by simp [Omega.one_mem, Omega.zero_mem]
  | k + 1 => by
    obtain ⟨h1, h2⟩ := cos_sin_nat_mul_mem hc hs k
    push_cast
    rw [add_mul, one_mul, Real.cos_add, Real.sin_add]
    exact ⟨Omega.sub_mem (Omega.mul_mem h1 hc) (Omega.mul_mem h2 hs),
      Omega.add_mem (Omega.mul_mem h2 hc) (Omega.mul_mem h1 hs)⟩

theorem cos_sin_pi_div_five_mem : Real.cos (π / 5) ∈ Omega ∧ Real.sin (π / 5) ∈ Omega := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hc : Real.cos (π / 5) ∈ Omega := by
    rw [Real.cos_pi_div_five]
    exact Omega.div_mem (Omega.add_mem Omega.one_mem sqrt_five_mem) (by norm_num)
  refine ⟨hc, ?_⟩
  have hs0 : 0 ≤ Real.sin (π / 5) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  have : Real.sin (π / 5) =
      Real.sqrt (((Real.sqrt 5 - 1) / 4) ^ 2 + (1 / 2) ^ 2) := by
    rw [← Real.sqrt_sq hs0, Real.sin_sq, Real.cos_pi_div_five]
    congr 1; ring_nf; rw [h5]; ring
  rw [this]
  have h4 : (4 : ℝ) ∈ Omega := by norm_num
  exact Omega.sqrt_sq_add_sq_mem (Omega.div_mem (Omega.sub_mem sqrt_five_mem Omega.one_mem) h4)
    (Omega.div_mem Omega.one_mem (two_mem_subfield _))

/-- **The regular `n`-gons for `n = 3, 4, 5, 6, 8, 10`**: the vertices `(cos 2πk/n, sin 2πk/n)`
have coordinates in `Ω`, hence are constructible by straight-edge and transferer from the
frame. -/
theorem regular_polygon_mem (n : ℕ) (hn : n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 8 ∨ n = 10)
    (k : ℕ) : Real.cos (2 * π * k / n) ∈ Omega ∧ Real.sin (2 * π * k / n) ∈ Omega := by
  have h3 : Real.cos (π / 3) ∈ Omega ∧ Real.sin (π / 3) ∈ Omega := by
    rw [Real.cos_pi_div_three, Real.sin_pi_div_three]
    exact ⟨Omega.div_mem Omega.one_mem (two_mem_subfield _),
      Omega.div_mem sqrt_three_mem (two_mem_subfield _)⟩
  have h4 : Real.cos (π / 4) ∈ Omega ∧ Real.sin (π / 4) ∈ Omega := by
    rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
    exact ⟨Omega.div_mem sqrt_two_mem (two_mem_subfield _),
      Omega.div_mem sqrt_two_mem (two_mem_subfield _)⟩
  have h5 := cos_sin_pi_div_five_mem
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · have := cos_sin_nat_mul_mem h3.1 h3.2 (2 * k)
    convert this using 2 <;> push_cast <;> ring_nf
  · have := cos_sin_nat_mul_mem h4.1 h4.2 (2 * k)
    convert this using 2 <;> push_cast <;> ring_nf
  · have := cos_sin_nat_mul_mem h5.1 h5.2 (2 * k)
    convert this using 2 <;> push_cast <;> ring_nf
  · have := cos_sin_nat_mul_mem h3.1 h3.2 k
    convert this using 2 <;> push_cast <;> ring_nf
  · have := cos_sin_nat_mul_mem h4.1 h4.2 k
    convert this using 2 <;> push_cast <;> ring_nf
  · have := cos_sin_nat_mul_mem h5.1 h5.2 k
    convert this using 2 <;> push_cast <;> ring_nf

end HilbertFoundations
