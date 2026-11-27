import HilbertFoundations.ConstructionsClose
import TauCeti.NumberTheory.QuadraticForm.Global.HigherRank
import TauCeti.NumberTheory.QuadraticForm.Global.Quaternary
import TauCeti.NumberTheory.QuadraticForm.Global.AnisotropicPlaces
import TauCeti.NumberTheory.QuadraticForm.Global.Localization
import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic

/-!
# Theorem 42: a totally positive number of a number field is a sum of four squares

This file closes the unit **`th.42`** of `Constructions.lean` (§ 38, Theorem 42):
`theorem42 : Theorem42` — in every number field `k`, every totally positive number `α` is a sum of
four squares of numbers of `k`.

## The Hasse–Minkowski theorem is taken from the Tau Ceti library

Hilbert derives the theorem from the solvability of quadratic diophantine equations in a number
field, that is, from what is now the Hasse–Minkowski theorem: a quadratic form over a number field
that has a nontrivial zero in every completion of the field has a nontrivial zero in the field.
That theorem is **not proved in this project**. It is taken from the Tau Ceti library

* repository: <https://github.com/TauCetiProject/TauCeti>
* licence: Apache License 2.0
* pinned commit: `aa3cfad1274c06cff25f2b58848498b3c3f68d0f` (see `lakefile.toml`)

which this project uses as a dependency, unchanged; none of its code is copied here. The
following definitions and statements of it are used (modules
`TauCeti.NumberTheory.QuadraticForm.Global.*` and `TauCeti.LinearAlgebra.QuadraticForm.*`):

* `QuadraticForm.not_anisotropic_of_isLocallyIsotropic_of_five_le_finrank` (`Global.HigherRank`):
  the step of the Hasse–Minkowski theorem from rank `n - 1` to rank `n ≥ 5`;
* `QuadraticForm.not_anisotropic_of_isLocallyIsotropic_quaternary` (`Global.Quaternary`): the
  Hasse–Minkowski theorem in rank four, which is the hypothesis of that step for `n = 5`;
* `QuadraticForm.not_anisotropic_atFinitePlace_of_five_le_finrank` (`Global.AnisotropicPlaces`):
  a form of rank at least five is isotropic at every finite place;
* `QuadraticForm.IsLocallyIsotropic`, `QuadraticForm.isLocallyIsotropic_iff`
  (`Global.Predicates`), `QuadraticForm.atFinitePlace` and `QuadraticForm.atRealPlace`
  (`Global.Localization`): the localizations of a form at the finite and at the real places, and
  the forms that are isotropic at all of them;
* `QuadraticForm.atRealPlaceWeightedSumSquares` (`Global.Localization`): the localization of a
  diagonal form at a real place is isometric to the diagonal form of the images of the
  coefficients;
* `QuadraticMap.Equivalent.anisotropic_iff` (`Representation`): isometric forms are isotropic
  together;
* `TauCeti.RegularFormPresentation`, `TauCeti.presentedForm`,
  `TauCeti.nondegenerate_presentedForm` and `TauCeti.presentedForm_eq_weightedSumSquares_coe`
  (`RegularFormClass.Basic`): the diagonal forms with nonzero coefficients, which are regular.

## What this file contributes

The application to Hilbert's theorem. For `α ≠ 0` the diagonal form
`x₁² + x₂² + x₃² + x₄² - α x₅²` over `k` is regular of rank five, so that

* it is isotropic at every finite place of `k` (rank at least five);
* it is isotropic at every real place of `k`: a real place is a real embedding `φ` of `k`, total
  positivity of `α` in Hilbert's sense (`TotallyPositive`) gives `φ α > 0`
  (`totallyPositive_ringHom_real_pos`), and `(√(φ α), 0, 0, 0, 1)` is a zero of
  `x₁² + x₂² + x₃² + x₄² - φ(α) x₅²` (`not_anisotropic_weightedSumSquares_real`);
* the complex places impose no condition.

By the Hasse–Minkowski theorem in rank five the form is isotropic over `k`
(`not_anisotropic_diagonalForm5`, `exists_isotropic_of_totallyPositive`), and a nontrivial zero of
it gives `α` as a sum of four squares (`four_squares_of_isotropic` of `ConstructionsClose.lean`,
which also treats the zeros with `x₅ = 0`). The number `α = 0` is the sum of four squares `0`.
-/

noncomputable section

namespace HilbertFoundations

/-! ## Diagonal forms in five variables -/

/-- The value of a diagonal form in five variables, written out. -/
theorem weightedSumSquares_fin_five {R : Type*} [Field R] (b x : Fin 5 → R) :
    QuadraticMap.weightedSumSquares R b x =
      b 0 * (x 0 * x 0) + b 1 * (x 1 * x 1) + b 2 * (x 2 * x 2) + b 3 * (x 3 * x 3)
        + b 4 * (x 4 * x 4) := by
  simp only [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_five, smul_eq_mul]

/-- A real diagonal form `x₁² + b₂ x₂² + b₃ x₃² + b₄ x₄² + b₅ x₅²` with `b₅ < 0` is isotropic:
`(√(-b₅), 0, 0, 0, 1)` is a zero of it. -/
theorem not_anisotropic_weightedSumSquares_real (b : Fin 5 → ℝ) (h0 : b 0 = 1) (h4 : b 4 < 0) :
    ¬QuadraticMap.Anisotropic (QuadraticMap.weightedSumSquares ℝ b) := by
  intro hA
  have hnn : 0 ≤ -b 4 := by linarith
  have hs : Real.sqrt (-b 4) * Real.sqrt (-b 4) = -b 4 := Real.mul_self_sqrt hnn
  have hval : QuadraticMap.weightedSumSquares ℝ b ![Real.sqrt (-b 4), 0, 0, 0, 1] = 0 := by
    refine (weightedSumSquares_fin_five b ![Real.sqrt (-b 4), 0, 0, 0, 1]).trans ?_
    show b 0 * (Real.sqrt (-b 4) * Real.sqrt (-b 4)) + b 1 * ((0 : ℝ) * 0)
      + b 2 * ((0 : ℝ) * 0) + b 3 * ((0 : ℝ) * 0) + b 4 * ((1 : ℝ) * 1) = 0
    rw [hs, h0]
    ring
  have hzero : (![Real.sqrt (-b 4), 0, 0, 0, 1] : Fin 5 → ℝ) = 0 :=
    hA ![Real.sqrt (-b 4), 0, 0, 0, 1] hval
  have h1 : (1 : ℝ) = 0 := congrFun hzero 4
  exact one_ne_zero h1

/-- The diagonal quadratic form `w₀ x₀² + w₁ x₁² + w₂ x₂² + w₃ x₃² + w₄ x₄²` over `k` with nonzero
coefficients `w`. -/
abbrev diagonalForm5 {k : Type*} [Field k] (w : Fin 5 → kˣ) : QuadraticForm k (Fin 5 → k) :=
  QuadraticMap.weightedSumSquares k fun i : Fin 5 => ((w i : kˣ) : k)

/-- **The Hasse–Minkowski theorem for the diagonal forms in five variables** (from the Tau Ceti
library): a diagonal form `⟨w₀, …, w₄⟩` with nonzero coefficients over a number field `k` that is
isotropic at every real place of `k` is isotropic over `k`. (At the finite places a form of rank
five is always isotropic.) -/
theorem not_anisotropic_diagonalForm5 {k : Type*} [Field k] [NumberField k] (w : Fin 5 → kˣ)
    (hreal : ∀ v : {v : NumberField.InfinitePlace k // v.IsReal},
      ¬QuadraticMap.Anisotropic (QuadraticMap.weightedSumSquares ℝ fun i : Fin 5 =>
        NumberField.InfinitePlace.embedding_of_isReal v.2 ((w i : kˣ) : k))) :
    ¬QuadraticMap.Anisotropic (diagonalForm5 w) := by
  -- the form is regular
  have hQ : (diagonalForm5 w).Nondegenerate := by
    let : Invertible (2 : k) := invertibleOfNonzero two_ne_zero
    have h : (TauCeti.presentedForm (⟨5, w⟩ : TauCeti.RegularFormPresentation k)).Nondegenerate :=
      TauCeti.nondegenerate_presentedForm (K := k) ⟨5, w⟩
    rw [TauCeti.presentedForm_eq_weightedSumSquares_coe w] at h
    exact h
  -- of rank five
  have h5 : Module.finrank k (Fin 5 → k) = 5 := Module.finrank_fin_fun k
  have hX : 5 ≤ Module.finrank k (Fin 5 → k) := h5.ge
  -- isotropic at the finite places
  have hfin : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k),
      ¬QuadraticMap.Anisotropic (QuadraticForm.atFinitePlace (diagonalForm5 w) v) :=
    fun v => QuadraticForm.not_anisotropic_atFinitePlace_of_five_le_finrank (diagonalForm5 w) hX v
  -- isotropic at the real places
  have hinf : ∀ v : {v : NumberField.InfinitePlace k // v.IsReal},
      ¬QuadraticMap.Anisotropic (QuadraticForm.atRealPlace (diagonalForm5 w) v) := by
    intro v hA
    have he : QuadraticMap.Equivalent (QuadraticForm.atRealPlace (diagonalForm5 w) v)
        (QuadraticMap.weightedSumSquares ℝ fun i : Fin 5 =>
          NumberField.InfinitePlace.embedding_of_isReal v.2 ((w i : kˣ) : k)) :=
      ⟨QuadraticForm.atRealPlaceWeightedSumSquares v fun i : Fin 5 => ((w i : kˣ) : k)⟩
    exact hreal v (he.anisotropic_iff.mp hA)
  have hloc : QuadraticForm.IsLocallyIsotropic (diagonalForm5 w) :=
    (QuadraticForm.isLocallyIsotropic_iff (diagonalForm5 w)).mpr ⟨hfin, hinf⟩
  -- the Hasse–Minkowski theorem in rank four
  have ih : ∀ p : TauCeti.RegularFormPresentation k,
      p.1 + 1 = Module.finrank k (Fin 5 → k) →
      QuadraticForm.IsLocallyIsotropic (TauCeti.presentedForm p) →
      ¬QuadraticMap.Anisotropic (TauCeti.presentedForm p) := by
    intro p hp hploc
    have hp5 : p.1 + 1 = 5 := hp.trans h5
    have hp1 : p.1 = 4 := by omega
    have hpp : Module.finrank k (Fin p.1 → k) = p.1 := Module.finrank_fin_fun k
    have hp4 : Module.finrank k (Fin p.1 → k) = 4 := hpp.trans hp1
    exact QuadraticForm.not_anisotropic_of_isLocallyIsotropic_quaternary hp4 hploc
  -- the step from rank four to rank five
  exact QuadraticForm.not_anisotropic_of_isLocallyIsotropic_of_five_le_finrank hQ hX hloc ih

/-! ## The form `x₁² + x₂² + x₃² + x₄² - α x₅²` -/

/-- A totally positive number is positive under every embedding of the field into `ℝ`. -/
theorem totallyPositive_ringHom_real_pos {k : Type*} [Field k] {α : k} (h : TotallyPositive α)
    (φ : k →+* ℝ) : 0 < φ α := by
  have hσ : ∀ x : k, ((Complex.ofRealHom.comp φ) x).im = 0 :=
    fun x => Complex.ofReal_im (φ x)
  have h1 : 0 < ((Complex.ofRealHom.comp φ) α).re := h (Complex.ofRealHom.comp φ) hσ
  have h2 : ((Complex.ofRealHom.comp φ) α).re = φ α := Complex.ofReal_re (φ α)
  exact lt_of_lt_of_eq h1 h2

/-- The coefficients `1, 1, 1, 1, -α` of the form `x₁² + x₂² + x₃² + x₄² - α x₅²`, for
`α ≠ 0`. -/
def fourSquaresWeights {k : Type*} [Field k] (α : k) (hα : α ≠ 0) : Fin 5 → kˣ :=
  ![1, 1, 1, 1, Units.mk0 (-α) (neg_ne_zero.mpr hα)]

theorem fourSquaresWeights_zero {k : Type*} [Field k] (α : k) (hα : α ≠ 0) :
    ((fourSquaresWeights α hα 0 : kˣ) : k) = 1 :=
  rfl

theorem fourSquaresWeights_one {k : Type*} [Field k] (α : k) (hα : α ≠ 0) :
    ((fourSquaresWeights α hα 1 : kˣ) : k) = 1 :=
  rfl

theorem fourSquaresWeights_two {k : Type*} [Field k] (α : k) (hα : α ≠ 0) :
    ((fourSquaresWeights α hα 2 : kˣ) : k) = 1 :=
  rfl

theorem fourSquaresWeights_three {k : Type*} [Field k] (α : k) (hα : α ≠ 0) :
    ((fourSquaresWeights α hα 3 : kˣ) : k) = 1 :=
  rfl

theorem fourSquaresWeights_four {k : Type*} [Field k] (α : k) (hα : α ≠ 0) :
    ((fourSquaresWeights α hα 4 : kˣ) : k) = -α :=
  rfl

/-- Under an embedding `φ` of `k` into `ℝ` with `φ α > 0`, the form
`x₁² + x₂² + x₃² + x₄² - φ(α) x₅²` is isotropic over `ℝ`. -/
theorem not_anisotropic_fourSquaresWeights_real {k : Type*} [Field k] {α : k} (hα : α ≠ 0)
    (φ : k →+* ℝ) (hpos : 0 < φ α) :
    ¬QuadraticMap.Anisotropic (QuadraticMap.weightedSumSquares ℝ fun i : Fin 5 =>
      φ ((fourSquaresWeights α hα i : kˣ) : k)) := by
  have h0 : φ ((fourSquaresWeights α hα 0 : kˣ) : k) = 1 := by
    rw [fourSquaresWeights_zero, map_one]
  have e4 : φ ((fourSquaresWeights α hα 4 : kˣ) : k) = -φ α := by
    rw [fourSquaresWeights_four, map_neg]
  have h4 : φ ((fourSquaresWeights α hα 4 : kˣ) : k) < 0 := by
    rw [e4]
    linarith
  exact not_anisotropic_weightedSumSquares_real
    (fun i : Fin 5 => φ ((fourSquaresWeights α hα i : kˣ) : k)) h0 h4

/-- **The form `x₁² + x₂² + x₃² + x₄² - α x₅²` is isotropic** over a number field `k`, for a
totally positive `α ≠ 0`: the instance of the Hasse–Minkowski theorem that Theorem 42 needs
(`theorem42_iff_isotropic`). -/
theorem exists_isotropic_of_totallyPositive {k : Type*} [Field k] [NumberField k] {α : k}
    (hα0 : α ≠ 0) (hα : TotallyPositive α) :
    ∃ x₁ x₂ x₃ x₄ x₅ : k, x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2 = α * x₅ ^ 2 ∧
      (x₁ ≠ 0 ∨ x₂ ≠ 0 ∨ x₃ ≠ 0 ∨ x₄ ≠ 0 ∨ x₅ ≠ 0) := by
  -- the form is isotropic at the real places of `k`
  have hreal : ∀ v : {v : NumberField.InfinitePlace k // v.IsReal},
      ¬QuadraticMap.Anisotropic (QuadraticMap.weightedSumSquares ℝ fun i : Fin 5 =>
        NumberField.InfinitePlace.embedding_of_isReal v.2
          ((fourSquaresWeights α hα0 i : kˣ) : k)) :=
    fun v => not_anisotropic_fourSquaresWeights_real hα0
      (NumberField.InfinitePlace.embedding_of_isReal v.2)
      (totallyPositive_ringHom_real_pos hα (NumberField.InfinitePlace.embedding_of_isReal v.2))
  -- hence over `k`
  have hiso : ¬QuadraticMap.Anisotropic (diagonalForm5 (fourSquaresWeights α hα0)) :=
    not_anisotropic_diagonalForm5 (fourSquaresWeights α hα0) hreal
  obtain ⟨x, hx0, hQx⟩ : ∃ x : Fin 5 → k, x ≠ 0 ∧
      diagonalForm5 (fourSquaresWeights α hα0) x = 0 :=
    (QuadraticMap.not_anisotropic_iff_exists (diagonalForm5 (fourSquaresWeights α hα0))).mp hiso
  -- the value of the form at the isotropic vector `x`
  have hsum : ((fourSquaresWeights α hα0 0 : kˣ) : k) * (x 0 * x 0)
      + ((fourSquaresWeights α hα0 1 : kˣ) : k) * (x 1 * x 1)
      + ((fourSquaresWeights α hα0 2 : kˣ) : k) * (x 2 * x 2)
      + ((fourSquaresWeights α hα0 3 : kˣ) : k) * (x 3 * x 3)
      + ((fourSquaresWeights α hα0 4 : kˣ) : k) * (x 4 * x 4) = 0 :=
    (weightedSumSquares_fin_five
      (fun i : Fin 5 => ((fourSquaresWeights α hα0 i : kˣ) : k)) x).symm.trans hQx
  rw [fourSquaresWeights_zero, fourSquaresWeights_one, fourSquaresWeights_two,
    fourSquaresWeights_three, fourSquaresWeights_four] at hsum
  have hsq : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 = α * x 4 ^ 2 := by
    linear_combination hsum
  -- one of the coordinates of `x` is not zero
  have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 ∨ x 3 ≠ 0 ∨ x 4 ≠ 0 := by
    by_contra hcon
    have h0 : x 0 = 0 := Classical.byContradiction fun h => hcon (Or.inl h)
    have h1 : x 1 = 0 := Classical.byContradiction fun h => hcon (Or.inr (Or.inl h))
    have h2 : x 2 = 0 := Classical.byContradiction fun h => hcon (Or.inr (Or.inr (Or.inl h)))
    have h3 : x 3 = 0 :=
      Classical.byContradiction fun h => hcon (Or.inr (Or.inr (Or.inr (Or.inl h))))
    have h4 : x 4 = 0 :=
      Classical.byContradiction fun h => hcon (Or.inr (Or.inr (Or.inr (Or.inr h))))
    have hall : ∀ i : Fin 5, x i = 0 := by
      intro i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    exact hx0 (funext hall)
  exact ⟨x 0, x 1, x 2, x 3, x 4, hsq, hne⟩

/-! ## Theorem 42 -/

/-- **Theorem 42** (unit `th.42`): in every number field, every totally positive number is a sum
of four squares of numbers of the field. The proof applies the Hasse–Minkowski theorem (of the
Tau Ceti library, see the header of this file) to the form `x₁² + x₂² + x₃² + x₄² - α x₅²`. -/
theorem theorem42 : Theorem42 := by
  intro k _ _ α hα
  by_cases hα0 : α = 0
  · exact ⟨0, 0, 0, 0, hα0.trans (by ring)⟩
  · obtain ⟨x₁, x₂, x₃, x₄, x₅, e, hne⟩ := exists_isotropic_of_totallyPositive hα0 hα
    exact four_squares_of_isotropic e hne

end HilbertFoundations
