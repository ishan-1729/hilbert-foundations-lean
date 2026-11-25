import HilbertFoundations.ConstructionsAux9

/-!
# Helper module for `Constructions.lean`: Hilbert's reduction of Theorem 44 to Theorem 43

This module contains no unit of Hilbert's text. For a subfield `R` of `ℝ` (the domain generated
by the coordinates of the given points, the arbitrary parameters included):

* `Theorem43For R`: every number of `R` that is nonnegative under every embedding real on `R`
  (for all real values of the parameters) is a quotient of two sums of squares of numbers of `R`
  — the generalization of Theorem 43 that Hilbert's proof of Theorem 44 uses (for `R = ℚ(p)` it
  is Theorem 43 for rational functions; for `R = ℚ` it is Lagrange's theorem, `theorem43For_rat`);
* `tower_qsos_over`: Hilbert's remark of § 39 over `R` — in a tower of square roots over `R`,
  every number nonnegative under every embedding real on `R` is a quotient of two sums of squares
  of numbers of the tower (induction with the trace and the norm, as in `tower_qsos`);
* `sqrt_qsos_mem`: the square root of such a quotient lies in `Ω(R)` when the field does;
* `theorem44For_of_theorem43For`: **Theorem 44 for the domain `R` follows from `Theorem43For R`**,
  for any number of parameters (Hilbert's reduction, the sufficiency by his argument and the
  necessity from `theorem44_necessary`).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

open Coord

/-- **Theorem 43 for the domain `R`**: every number of `R` that is nonnegative under every
embedding of `R` into `ℂ` that is real on `R` is a quotient of two sums of squares in `R`. -/
def Theorem43For (R : Subfield ℝ) : Prop := ∀ g : ℝ, TotNonnegOver R R g → QSOS R g

/-- `Ω(R)` is a field. -/
def pythSubfield (R : Subfield ℝ) : Subfield ℝ where
  carrier := {x | PythClosure (R : Set ℝ) x}
  one_mem' := .base R.one_mem
  mul_mem' := fun ha hb => .mul ha hb
  add_mem' := fun ha hb => .add ha hb
  zero_mem' := by
    have h := PythClosure.sub (B := (R : Set ℝ)) (.base R.one_mem) (.base R.one_mem)
    rwa [sub_self] at h
  neg_mem' := by
    intro x hx
    have h0 : PythClosure (R : Set ℝ) 0 := by
      have h := PythClosure.sub (B := (R : Set ℝ)) (.base R.one_mem) (.base R.one_mem)
      rwa [sub_self] at h
    have h := PythClosure.sub h0 hx
    rwa [zero_sub] at h
  inv_mem' := by
    intro x hx
    by_cases h0 : x = 0
    · subst h0
      have h := PythClosure.sub (B := (R : Set ℝ)) (.base R.one_mem) (.base R.one_mem)
      rw [sub_self] at h
      simpa using h
    · have h := PythClosure.div (.base R.one_mem) hx h0
      rwa [one_div] at h

theorem mem_pythSubfield {R : Subfield ℝ} {x : ℝ} :
    x ∈ pythSubfield R ↔ PythClosure (R : Set ℝ) x := Iff.rfl

theorem towerFieldOver_quadExt {R : Subfield ℝ} {a : ℝ} {l : List ℝ}
    (ha : a ∈ towerFieldOver R l) (ha0 : 0 ≤ a) :
    IsQuadExt (towerFieldOver R l) (towerFieldOver R (a :: l)) (Real.sqrt a) :=
  quadExt_closure (by rw [Real.sq_sqrt ha0]; exact ha)

/-- **Hilbert's remark of § 39 over a domain `R`**: if `Theorem43For R`, then in a tower of square
roots over `R` every number that is nonnegative under every embedding real on `R` (all real values
of the parameters, either sign of each square root) is a quotient of two sums of squares of
numbers of the tower. -/
theorem tower_qsos_over (R : Subfield ℝ) (hR : Theorem43For R) :
    ∀ l : List ℝ, ValidTowerOver R l → ∀ g : ℝ, TotNonnegOver R (towerFieldOver R l) g →
      QSOS (towerFieldOver R l) g := by
  intro l
  induction l with
  | nil => intro _ g hg; exact hR g hg
  | cons a l ih =>
    intro ⟨hv, ha, ha0⟩ g hg
    have hE := towerFieldOver_quadExt ha ha0
    have hRF : R ≤ towerFieldOver R l := le_towerFieldOver R l
    set F := towerFieldOver R l
    set b := Real.sqrt a with hbdef
    by_cases hbF : b ∈ F
    · have e := hE.eq_of_mem hbF
      rw [e] at hg ⊢; exact ih hv g hg
    obtain ⟨hgE, hσg⟩ := hg
    obtain ⟨r, hr, s, hs, hgrs⟩ := hE.repr g hgE
    have hsq : b ^ 2 ∈ F := hE.sq_mem
    -- an extension of an embedding real on `R` is real on `R`
    have real_ext : ∀ (σ : F →+* ℂ) (σ' : towerFieldOver R (a :: l) →+* ℂ),
        (∀ x : F, σ' ⟨x, hE.le x.2⟩ = σ x) →
        (∀ y : F, (y : ℝ) ∈ R → ∃ t : ℝ, σ y = (t : ℂ)) →
        ∀ y : towerFieldOver R (a :: l), (y : ℝ) ∈ R → ∃ t : ℝ, σ' y = (t : ℂ) := by
      intro σ σ' e hσ y hy
      obtain ⟨t, ht⟩ := hσ ⟨y, hRF hy⟩ hy
      exact ⟨t, by rw [← ht, ← e ⟨y, hRF hy⟩]⟩
    -- the two conjugates of `g` over `F`
    have conj : ∀ σ : F →+* ℂ, (∀ y : F, (y : ℝ) ∈ R → ∃ t : ℝ, σ y = (t : ℂ)) →
        ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ 0 ≤ t₂ ∧
        σ ⟨r, hr⟩ * 2 = (t₁ : ℂ) + t₂ ∧
        σ ⟨r, hr⟩ ^ 2 - σ ⟨s, hs⟩ ^ 2 * σ ⟨b ^ 2, hsq⟩ = (t₁ : ℂ) * t₂ := by
      intro σ hσ
      obtain ⟨τ, hτ⟩ := IsAlgClosed.exists_pow_nat_eq (σ ⟨b ^ 2, hsq⟩) two_pos
      obtain ⟨σ₁, e₁, h₁⟩ := exists_ext hE hbF σ τ hτ
      obtain ⟨σ₂, e₂, h₂⟩ := exists_ext hE hbF σ (-τ) (by rw [neg_sq]; exact hτ)
      obtain ⟨t₁, ht₁, et₁⟩ := hσg σ₁ (real_ext σ σ₁ e₁ hσ)
      obtain ⟨t₂, ht₂, et₂⟩ := hσg σ₂ (real_ext σ σ₂ e₂ hσ)
      have hgE' : (⟨g, hgE⟩ : towerFieldOver R (a :: l)) =
          ⟨((⟨r, hr⟩ : F) : ℝ), hE.le hr⟩ + ⟨((⟨s, hs⟩ : F) : ℝ), hE.le hs⟩ * ⟨b, hE.mem⟩ :=
        Subtype.ext (by simp [hgrs])
      rw [hgE', map_add, map_mul, e₁ ⟨r, hr⟩, e₁ ⟨s, hs⟩, h₁] at et₁
      rw [hgE', map_add, map_mul, e₂ ⟨r, hr⟩, e₂ ⟨s, hs⟩, h₂] at et₂
      refine ⟨t₁, t₂, ht₁, ht₂, ?_, ?_⟩
      · rw [← et₁, ← et₂]; ring
      · rw [← hτ, ← et₁, ← et₂]; ring
    -- the trace `φ = 2r` and the norm `ψ = r² - s² b²`
    have hTm : 2 * r ∈ F := F.mul_mem (two_mem_subfield F) hr
    have hNm : r ^ 2 - s ^ 2 * b ^ 2 ∈ F :=
      F.sub_mem (F.pow_mem hr 2) (F.mul_mem (F.pow_mem hs 2) hsq)
    have hT : TotNonnegOver R F (2 * r) := by
      refine ⟨hTm, fun σ hσ => ?_⟩
      obtain ⟨t₁, t₂, ht₁, ht₂, e1, -⟩ := conj σ hσ
      refine ⟨t₁ + t₂, add_nonneg ht₁ ht₂, ?_⟩
      have : (⟨2 * r, hTm⟩ : F) = ⟨r, hr⟩ + ⟨r, hr⟩ := Subtype.ext (by simp; ring)
      rw [this, map_add, show σ ⟨r, hr⟩ + σ ⟨r, hr⟩ = σ ⟨r, hr⟩ * 2 by ring, e1]; simp
    have hN : TotNonnegOver R F (r ^ 2 - s ^ 2 * b ^ 2) := by
      refine ⟨hNm, fun σ hσ => ?_⟩
      obtain ⟨t₁, t₂, ht₁, ht₂, -, e2⟩ := conj σ hσ
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
        obtain ⟨t, ht, e⟩ := hσ (Complex.ofRealHom.comp F.subtype) (fun y _ => ⟨y, rfl⟩)
        have e' : ((r ^ 2 - s ^ 2 * b ^ 2 : ℝ) : ℂ) = (t : ℂ) := e
        have : r ^ 2 - s ^ 2 * b ^ 2 = t := by exact_mod_cast e'
        rw [this]; exact ht
      have hr' : r = 0 := by linarith
      have hg0 : g = 0 := by
        have : g ^ 2 = 0 := by
          rw [hgrs, hr']; rw [hr'] at hN0; nlinarith [sq_nonneg (s * b)]
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      have h1 : SOSIn (towerFieldOver R (a :: l)) 1 := by
        have := SOSIn.sq (F := towerFieldOver R (a :: l)) (Subfield.one_mem _)
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

/-- The square root of a sum of squares of numbers of `Ω(R)` lies in `Ω(R)` (§ 39: by repeated
square roots of sums of two squares). -/
theorem SOSIn.sqrt_mem_pythClosure {R F : Subfield ℝ} (hF : F ≤ pythSubfield R) {u : ℝ}
    (h : SOSIn F u) : PythClosure (R : Set ℝ) (Real.sqrt u) := by
  induction h with
  | zero => rw [Real.sqrt_zero]; exact (pythSubfield R).zero_mem
  | @cons x u hx hu ih =>
    refine PythClosure.sqrt (hF hx) ih (Real.sqrt_nonneg _) ?_
    rw [Real.sq_sqrt (by have := hu.nonneg; positivity), Real.sq_sqrt hu.nonneg]

/-- **The square root of a nonnegative quotient of sums of squares** of numbers of `Ω(R)` lies in
`Ω(R)`: `√(u/v) = √(u v) / v`. -/
theorem sqrt_qsos_mem {R F : Subfield ℝ} (hF : F ≤ pythSubfield R) {g : ℝ} (hg : QSOS F g) :
    PythClosure (R : Set ℝ) (Real.sqrt g) := by
  obtain ⟨u, v, hu, hv, hv0, rfl⟩ := hg
  have hvpos : 0 < v := lt_of_le_of_ne hv.nonneg (Ne.symm hv0)
  have : Real.sqrt (u / v) = Real.sqrt (u * v) / v := by
    rw [show u / v = (u * v) / v ^ 2 by field_simp, Real.sqrt_div' _ (sq_nonneg v),
      Real.sqrt_sq hvpos.le]
  rw [this]
  exact PythClosure.div ((hu.mul hv).sqrt_mem_pythClosure hF) (hF hv.mem) hv0

/-- **Sufficiency in Theorem 44 over `R`, from `Theorem43For R`**: if every radicand is
nonnegative for all real values of the parameters and either sign of the square roots, every
number of the tower lies in `Ω(R)`. -/
theorem tower_le_pythClosure (R : Subfield ℝ) (hR : Theorem43For R) :
    ∀ l : List ℝ, ValidTowerOver R l → RealTowerOver R l → towerFieldOver R l ≤ pythSubfield R
  | [], _, _ => fun x hx => PythClosure.base hx
  | a :: l, ⟨hv, _, _⟩, ⟨hr, htn⟩ => by
    have ih := tower_le_pythClosure R hR l hv hr
    have hsqrt : Real.sqrt a ∈ pythSubfield R := sqrt_qsos_mem ih (tower_qsos_over R hR l hv a htn)
    show Subfield.closure _ ≤ pythSubfield R
    rw [Subfield.closure_le]
    rintro x (hx | hx)
    · exact ih hx
    · rw [Set.mem_singleton_iff.1 hx]; exact hsqrt

/-- **Hilbert's reduction** (§ 39): Theorem 44 for the domain `R` follows from Theorem 43 for
`R`. -/
theorem theorem44For_of_theorem43For (R : Subfield ℝ) (hR : Theorem43For R) : Theorem44For R :=
  fun l hv => ⟨fun h _ hx => tower_le_pythClosure R hR l hv h hx, theorem44_necessary R l hv⟩

/-- `Theorem43For ℚ` is Lagrange's theorem. -/
theorem theorem43For_rat : Theorem43For ratField := by
  intro g ⟨hg, hσ⟩
  obtain ⟨t, ht, e⟩ := hσ (Complex.ofRealHom.comp ratField.subtype) (fun y _ => ⟨y, rfl⟩)
  have e' : ((g : ℝ) : ℂ) = (t : ℂ) := e
  have : g = t := by exact_mod_cast e'
  exact qsos_rat hg (this ▸ ht)

/-- **Theorem 44 reduced to the generalization of Theorem 43**: Theorem 44 (for every domain
generated by finitely many real numbers, any number of parameters) holds as soon as Theorem 43
holds for each such domain. -/
theorem theorem44_of_theorem43For
    (h : ∀ S : Finset ℝ, Theorem43For (Subfield.closure (S : Set ℝ))) : Theorem44 :=
  fun S => theorem44For_of_theorem43For _ (h S)

end HilbertFoundations
