import HilbertFoundations.DesarguesAlgebra

/-!
# Helper for §§ 31–35: skew Laurent series, Hilbert's number system `Ω(s, t)`, Theorem 38

Helper module of `NonPascal.lean` (the units are stated there). Contents:

* `SkewLaurent K σ`: the formal series `s^m T₀ + s^{m+1} T₁ + ⋯` (`m ∈ ℤ`, finitely or infinitely
  many terms) with coefficients `T_k` in a division ring `K`, written on the right of the powers of
  `s`, multiplied term by term with the rule `T s = s σ(T)` for a ring automorphism `σ` of `K`.
  The underlying additive group is mathlib's `HahnSeries ℤ K`; the multiplication is defined here
  (`coeff_mul`: the coefficient of `s^n` in `x y` is `∑_{i+j=n} σ^j(x_i) y_j`).
  It is a ring (`instRing`), a division ring (`instDivisionRing`: the right inverse is computed by
  "equating the like powers of `s`", `invSeq`, `mul_rinv`), and, for an ordered `K` and an
  order-preserving `σ`, an ordered division ring whose positive elements are those with positive
  first coefficient (`pos_iff`, `isStrictOrderedRing`).
* `TSeries = SkewLaurent ℚ 1`: Hilbert's expressions `T` (Laurent series in `t` over `ℚ`);
  `sigma2`: `T(t) ↦ T(2t)`; `OmegaST = SkewLaurent TSeries sigma2`: Hilbert's `Ω(s, t)`, with
  `t s = 2 s t` (`OmegaST.t_mul_s`), not commutative, not archimedean, not enumerable.
* Theorem 38: an archimedean ordered division ring is commutative (`mul_comm_of_archimedean`,
  Hilbert's proof), and its form with the laws of § 13 (`theorem38_laws`).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations
namespace NonPascal

open Finset
open scoped Pointwise

/-- **Skew Laurent series** `∑ s^k T_k` over a division ring `K`, with the coefficients written on
the right of the powers of `s`, multiplied with the rule `T s = s σ(T)`. -/
def SkewLaurent (K : Type*) [DivisionRing K] (_σ : RingAut K) : Type _ := HahnSeries ℤ K

namespace SkewLaurent

variable {K : Type*} [DivisionRing K] {σ : RingAut K}

instance : AddCommGroup (SkewLaurent K σ) := inferInstanceAs (AddCommGroup (HahnSeries ℤ K))

/-- The underlying Hahn series. -/
def toHahn (x : SkewLaurent K σ) : HahnSeries ℤ K := x

/-- A Hahn series as a skew Laurent series. -/
def ofHahn (x : HahnSeries ℤ K) : SkewLaurent K σ := x

@[simp] theorem toHahn_ofHahn (x : HahnSeries ℤ K) : toHahn (ofHahn (σ := σ) x) = x := rfl
@[simp] theorem ofHahn_toHahn (x : SkewLaurent K σ) : ofHahn (toHahn x) = x := rfl

theorem toHahn_injective : Function.Injective (toHahn : SkewLaurent K σ → HahnSeries ℤ K) :=
  fun _ _ h => h

/-- The coefficient `T_n` of `s^n`. -/
def coeff (x : SkewLaurent K σ) (n : ℤ) : K := (toHahn x).coeff n

theorem ext {x y : SkewLaurent K σ} (h : ∀ n, x.coeff n = y.coeff n) : x = y :=
  HahnSeries.ext (funext h)

@[simp] theorem coeff_ofHahn (x : HahnSeries ℤ K) (n : ℤ) :
    (ofHahn (σ := σ) x).coeff n = x.coeff n := rfl

@[simp] theorem coeff_add (x y : SkewLaurent K σ) (n : ℤ) :
    (x + y).coeff n = x.coeff n + y.coeff n :=
  HahnSeries.coeff_add (x := toHahn x) (y := toHahn y)

@[simp] theorem coeff_zero (n : ℤ) : (0 : SkewLaurent K σ).coeff n = 0 := rfl

@[simp] theorem coeff_neg (x : SkewLaurent K σ) (n : ℤ) : (-x).coeff n = -x.coeff n :=
  HahnSeries.coeff_neg (x := toHahn x)

@[simp] theorem coeff_sub (x y : SkewLaurent K σ) (n : ℤ) :
    (x - y).coeff n = x.coeff n - y.coeff n :=
  HahnSeries.coeff_sub (x := toHahn x) (y := toHahn y)

/-- The support (the exponents of `s` with non-zero coefficient). -/
def supp (x : SkewLaurent K σ) : Set ℤ := (toHahn x).support

theorem mem_supp {x : SkewLaurent K σ} {n : ℤ} : n ∈ supp x ↔ x.coeff n ≠ 0 := Iff.rfl

theorem isPWO_supp (x : SkewLaurent K σ) : (supp x).IsPWO := (toHahn x).isPWO_support

theorem supp_add_subset (x y : SkewLaurent K σ) : supp (x + y) ⊆ supp x ∪ supp y := by
  intro n hn
  rw [mem_supp, coeff_add] at hn
  by_contra h
  simp only [Set.mem_union, mem_supp, not_or, not_not] at h
  exact hn (by rw [h.1, h.2, add_zero])

/-- The single term `s^k a`. -/
noncomputable def single (k : ℤ) (a : K) : SkewLaurent K σ := ofHahn (HahnSeries.single k a)

theorem coeff_single (k : ℤ) (a : K) (n : ℤ) :
    (single (σ := σ) k a).coeff n = if n = k then a else 0 := by
  show (HahnSeries.single k a).coeff n = _
  rw [HahnSeries.coeff_single]
  split_ifs <;> rfl

theorem supp_single_subset (k : ℤ) (a : K) : supp (single (σ := σ) k a) ⊆ {k} :=
  HahnSeries.support_single_subset

/-! ### Multiplication -/

/-- The coefficient of `s^n` in the product: `∑_{i + j = n} σ^j (x_i) y_j`. -/
noncomputable def mulCoeff (x y : SkewLaurent K σ) (n : ℤ) : K :=
  ∑ ij ∈ Finset.antidiagonal (isPWO_supp x) (isPWO_supp y) n,
    (σ ^ ij.2) (x.coeff ij.1) * y.coeff ij.2

theorem mulCoeff_eq {x y : SkewLaurent K σ} {s t : Set ℤ} (hs : s.IsPWO) (ht : t.IsPWO)
    (hxs : supp x ⊆ s) (hyt : supp y ⊆ t) (n : ℤ) :
    mulCoeff x y n = ∑ ij ∈ Finset.antidiagonal hs ht n,
      (σ ^ ij.2) (x.coeff ij.1) * y.coeff ij.2 := by
  classical
  unfold mulCoeff
  have hsub : Finset.antidiagonal (isPWO_supp x) (isPWO_supp y) n ⊆
      Finset.antidiagonal hs ht n := by
    intro ij hij
    rw [Finset.mem_antidiagonal] at hij ⊢
    exact ⟨hxs hij.1, hyt hij.2.1, hij.2.2⟩
  apply sum_subset_zero_on_sdiff hsub _ (fun _ _ => rfl)
  intro ij hij
  rw [mem_sdiff, Finset.mem_antidiagonal, Finset.mem_antidiagonal] at hij
  by_cases hx : x.coeff ij.1 = 0
  · rw [hx, map_zero, zero_mul]
  by_cases hy : y.coeff ij.2 = 0
  · rw [hy, mul_zero]
  exact absurd ⟨hx, hy, hij.1.2.2⟩ hij.2

theorem supp_mulCoeff_subset (x y : SkewLaurent K σ) :
    Function.support (mulCoeff x y) ⊆ supp x + supp y := by
  intro n hn
  obtain ⟨ij, hij, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  rw [Finset.mem_antidiagonal] at hij
  exact ⟨ij.1, hij.1, ij.2, hij.2.1, hij.2.2⟩

noncomputable instance : Mul (SkewLaurent K σ) :=
  ⟨fun x y => ofHahn ⟨mulCoeff x y,
    ((isPWO_supp x).add (isPWO_supp y)).mono (supp_mulCoeff_subset x y)⟩⟩

theorem coeff_mul (x y : SkewLaurent K σ) (n : ℤ) : (x * y).coeff n = mulCoeff x y n := rfl

theorem supp_mul_subset (x y : SkewLaurent K σ) : supp (x * y) ⊆ supp x + supp y :=
  supp_mulCoeff_subset x y

theorem coeff_mul_eq {x y : SkewLaurent K σ} {s t : Set ℤ} (hs : s.IsPWO) (ht : t.IsPWO)
    (hxs : supp x ⊆ s) (hyt : supp y ⊆ t) (n : ℤ) :
    (x * y).coeff n = ∑ ij ∈ Finset.antidiagonal hs ht n,
      (σ ^ ij.2) (x.coeff ij.1) * y.coeff ij.2 :=
  mulCoeff_eq hs ht hxs hyt n

theorem coeff_single_mul (k : ℤ) (a : K) (y : SkewLaurent K σ) (n : ℤ) :
    (single k a * y).coeff n = (σ ^ (n - k)) a * y.coeff (n - k) := by
  classical
  rw [coeff_mul_eq (Set.isPWO_singleton k) (isPWO_supp y) (supp_single_subset k a) le_rfl]
  rw [Finset.sum_eq_single (k, n - k)]
  · simp [coeff_single]
  · intro ij hij hne
    rw [Finset.mem_antidiagonal, Set.mem_singleton_iff] at hij
    exact absurd (Prod.ext hij.1 (by omega)) hne
  · intro h
    rw [Finset.mem_antidiagonal] at h
    have : y.coeff (n - k) = 0 := by
      by_contra hy
      exact h ⟨rfl, hy, by omega⟩
    rw [this, mul_zero]

theorem coeff_mul_single (k : ℤ) (a : K) (x : SkewLaurent K σ) (n : ℤ) :
    (x * single k a).coeff n = (σ ^ k) (x.coeff (n - k)) * a := by
  classical
  rw [coeff_mul_eq (isPWO_supp x) (Set.isPWO_singleton k) le_rfl (supp_single_subset k a)]
  rw [Finset.sum_eq_single (n - k, k)]
  · simp [coeff_single]
  · intro ij hij hne
    rw [Finset.mem_antidiagonal, Set.mem_singleton_iff] at hij
    exact absurd (Prod.ext (by omega) hij.2.1) hne
  · intro h
    rw [Finset.mem_antidiagonal] at h
    have : x.coeff (n - k) = 0 := by
      by_contra hx
      exact h ⟨hx, rfl, by omega⟩
    rw [this, map_zero, zero_mul]

noncomputable instance : One (SkewLaurent K σ) := ⟨single 0 1⟩

theorem one_def : (1 : SkewLaurent K σ) = single 0 1 := rfl

theorem coeff_one (n : ℤ) : (1 : SkewLaurent K σ).coeff n = if n = 0 then 1 else 0 :=
  coeff_single 0 1 n

theorem one_mul' (x : SkewLaurent K σ) : 1 * x = x := ext fun n => by
  rw [one_def, coeff_single_mul]; simp

theorem mul_one' (x : SkewLaurent K σ) : x * 1 = x := ext fun n => by
  rw [one_def, coeff_mul_single]; simp

theorem zero_mul' (x : SkewLaurent K σ) : 0 * x = 0 := ext fun n => by
  rw [coeff_mul, mulCoeff]; simp

theorem mul_zero' (x : SkewLaurent K σ) : x * 0 = 0 := ext fun n => by
  rw [coeff_mul, mulCoeff]; simp

theorem mul_add' (x y z : SkewLaurent K σ) : x * (y + z) = x * y + x * z := ext fun n => by
  have hu := (isPWO_supp y).union (isPWO_supp z)
  rw [coeff_add, coeff_mul_eq (isPWO_supp x) hu le_rfl (supp_add_subset y z),
    coeff_mul_eq (isPWO_supp x) hu le_rfl Set.subset_union_left,
    coeff_mul_eq (isPWO_supp x) hu le_rfl Set.subset_union_right, ← sum_add_distrib]
  refine sum_congr rfl fun ij _ => ?_
  rw [coeff_add, mul_add]

theorem add_mul' (x y z : SkewLaurent K σ) : (x + y) * z = x * z + y * z := ext fun n => by
  have hu := (isPWO_supp x).union (isPWO_supp y)
  rw [coeff_add, coeff_mul_eq hu (isPWO_supp z) (supp_add_subset x y) le_rfl,
    coeff_mul_eq hu (isPWO_supp z) Set.subset_union_left le_rfl,
    coeff_mul_eq hu (isPWO_supp z) Set.subset_union_right le_rfl, ← sum_add_distrib]
  refine sum_congr rfl fun ij _ => ?_
  rw [coeff_add, map_add, add_mul]

theorem zpow_apply_apply (j l : ℤ) (a : K) : (σ ^ j) ((σ ^ l) a) = (σ ^ (l + j)) a := by
  rw [add_comm, zpow_add, RingAut.mul_apply]

theorem mul_assoc' (x y z : SkewLaurent K σ) : x * y * z = x * (y * z) := ext fun n => by
  rw [coeff_mul_eq ((isPWO_supp x).add (isPWO_supp y)) (isPWO_supp z) (supp_mul_subset x y) le_rfl,
    coeff_mul_eq (isPWO_supp x) ((isPWO_supp y).add (isPWO_supp z)) le_rfl (supp_mul_subset y z)]
  simp only [coeff_mul, mulCoeff, map_sum, map_mul, sum_mul, mul_sum, sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l + j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i + k, l), (i, k)⟩)
  · aesop (add safe Set.add_mem_add) (add simp [add_assoc])
  · aesop (add safe Set.add_mem_add) (add simp [add_assoc])
  · aesop (add simp [add_assoc])
  · aesop (add simp [add_assoc])
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ -
    simp only [zpow_apply_apply, mul_assoc]

noncomputable instance instRing : Ring (SkewLaurent K σ) :=
  { (inferInstance : AddCommGroup (SkewLaurent K σ)) with
    mul := (· * ·)
    one := 1
    mul_assoc := mul_assoc'
    one_mul := one_mul'
    mul_one := mul_one'
    left_distrib := mul_add'
    right_distrib := add_mul'
    zero_mul := zero_mul'
    mul_zero := mul_zero' }


/-! ### Coefficients of a product as sums over intervals -/

theorem isPWO_Ici (a : ℤ) : (Set.Ici a).IsPWO :=
  (BddBelow.isWF (bddBelow_Ici (a := a))).isPWO

theorem supp_subset_Ici {x : SkewLaurent K σ} {a : ℤ} (h : ∀ n < a, x.coeff n = 0) :
    supp x ⊆ Set.Ici a := fun n hn => by
  by_contra h'
  exact hn (h n (lt_of_not_ge h'))

/-- If `x` has no terms below `s^a` and `y` none below `s^b`, the coefficient of `s^n` in `x y` is
`∑_{a ≤ i ≤ n - b} σ^{n-i} (x_i) y_{n-i}`. -/
theorem coeff_mul_Icc {x y : SkewLaurent K σ} {a b : ℤ} (hx : ∀ n < a, x.coeff n = 0)
    (hy : ∀ n < b, y.coeff n = 0) (n : ℤ) :
    (x * y).coeff n = ∑ i ∈ Finset.Icc a (n - b), (σ ^ (n - i)) (x.coeff i) * y.coeff (n - i) := by
  rw [coeff_mul_eq (isPWO_Ici a) (isPWO_Ici b) (supp_subset_Ici hx) (supp_subset_Ici hy)]
  apply Finset.sum_nbij' (fun ij => ij.1) (fun i => (i, n - i))
  · intro ij h
    rw [Finset.mem_antidiagonal, Set.mem_Ici, Set.mem_Ici] at h
    rw [Finset.mem_Icc]
    omega
  · intro i h
    rw [Finset.mem_Icc] at h
    rw [Finset.mem_antidiagonal, Set.mem_Ici, Set.mem_Ici]
    omega
  · intro ij h
    rw [Finset.mem_antidiagonal] at h
    exact Prod.ext rfl (by simp only; omega)
  · intro i _
    rfl
  · intro ij h
    rw [Finset.mem_antidiagonal] at h
    have : ij.2 = n - ij.1 := by omega
    rw [this]

/-- Every non-zero series has a lowest term. -/
theorem exists_lowest {x : SkewLaurent K σ} (hx : x ≠ 0) :
    ∃ m, (∀ n < m, x.coeff n = 0) ∧ x.coeff m ≠ 0 := by
  have hne : (supp x).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hx (ext fun n => by
      have : n ∉ supp x := by rw [h]; exact Set.notMem_empty n
      rw [mem_supp, not_not] at this
      rw [this, coeff_zero])
  have hwf := (isPWO_supp x).isWF
  refine ⟨hwf.min hne, fun n hn => ?_, hwf.min_mem hne⟩
  by_contra h
  exact hwf.not_lt_min hne h hn

/-! ### The right inverse (Hilbert's "equating the like powers of `s`") -/

/-- The coefficients `y_{N - m}` of the right inverse `y` of a series `x` with lowest term
`s^m x_m`, determined successively from `x y = 1`. -/
noncomputable def invSeq (x : SkewLaurent K σ) (m : ℤ) : ℕ → K
  | N => ((σ ^ ((N : ℤ) - m)) (x.coeff m))⁻¹ *
      ((if N = 0 then 1 else 0) -
        ∑ l : Fin N, (σ ^ ((l : ℤ) - m)) (x.coeff (m + N - l)) * invSeq x m l)
decreasing_by exact l.isLt

theorem invSeq_spec (x : SkewLaurent K σ) {m : ℤ} (hm : x.coeff m ≠ 0) (N : ℕ) :
    (σ ^ ((N : ℤ) - m)) (x.coeff m) * invSeq x m N +
      ∑ l ∈ Finset.range N, (σ ^ ((l : ℤ) - m)) (x.coeff (m + N - l)) * invSeq x m l =
      if N = 0 then 1 else 0 := by
  have hc : (σ ^ ((N : ℤ) - m)) (x.coeff m) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (RingEquiv.injective _)]; exact hm
  rw [invSeq, mul_inv_cancel_left₀ hc,
    ← Fin.sum_univ_eq_sum_range (fun l => (σ ^ ((l : ℤ) - m)) (x.coeff (m + N - l)) *
      invSeq x m l) N]
  abel

/-- The right inverse as a series. -/
noncomputable def rinv (x : SkewLaurent K σ) (m : ℤ) : SkewLaurent K σ :=
  ofHahn ⟨fun n => if -m ≤ n then invSeq x m (n + m).toNat else 0,
    (isPWO_Ici (-m)).mono fun n hn => by
      by_contra h
      exact hn (ite_eq_right h)⟩

theorem coeff_rinv (x : SkewLaurent K σ) (m n : ℤ) :
    (rinv x m).coeff n = if -m ≤ n then invSeq x m (n + m).toNat else 0 := rfl

theorem mul_rinv {x : SkewLaurent K σ} {m : ℤ} (hlow : ∀ n < m, x.coeff n = 0)
    (hm : x.coeff m ≠ 0) : x * rinv x m = 1 := ext fun n => by
  have hy : ∀ n < -m, (rinv x m).coeff n = 0 := fun n hn => by
    rw [coeff_rinv, ite_eq_right (by omega)]
  rw [coeff_mul_Icc hlow hy, coeff_one, show n - -m = n + m by ring]
  rcases lt_or_ge n 0 with hn | hn
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, ite_eq_right (by omega)]
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = N := ⟨n.toNat, (Int.toNat_of_nonneg hn).symm⟩
  rw [show (if (N : ℤ) = 0 then (1 : K) else 0) = if N = 0 then 1 else 0 by simp,
    ← invSeq_spec x hm N]
  have key : (σ ^ ((N : ℤ) - m)) (x.coeff m) * invSeq x m N +
      ∑ l ∈ Finset.range N, (σ ^ ((l : ℤ) - m)) (x.coeff (m + N - l)) * invSeq x m l =
      ∑ l ∈ Finset.range (N + 1), (σ ^ ((l : ℤ) - m)) (x.coeff (m + N - l)) * invSeq x m l := by
    rw [Finset.sum_range_succ, add_comm, show m + (N : ℤ) - N = m by ring]
  rw [key]
  apply Finset.sum_nbij' (fun i => ((N : ℤ) + m - i).toNat) (fun l => m + N - l)
  · intro i h
    rw [Finset.mem_Icc] at h
    rw [Finset.mem_range]
    omega
  · intro l h
    rw [Finset.mem_range] at h
    rw [Finset.mem_Icc]
    omega
  · intro i h
    rw [Finset.mem_Icc] at h
    omega
  · intro l h
    omega
  · intro i h
    rw [Finset.mem_Icc] at h
    rw [coeff_rinv, ite_eq_left (by omega)]
    have e1 : ((((N : ℤ) + m - i).toNat : ℕ) : ℤ) = (N : ℤ) + m - i :=
      Int.toNat_of_nonneg (by omega)
    have e2 : ((N : ℤ) - i + m).toNat = ((N : ℤ) + m - i).toNat := by congr 1; ring
    rw [e1, e2, show (N : ℤ) + m - i - m = N - i by ring,
      show m + (N : ℤ) - (N + m - i) = i by ring]

/-! ### The division ring -/

instance : Nontrivial (SkewLaurent K σ) :=
  ⟨⟨0, 1, fun h => by
    have := congrArg (fun z : SkewLaurent K σ => z.coeff 0) h
    simp [coeff_one] at this⟩⟩

open Classical in
noncomputable instance instDivisionRing : DivisionRing (SkewLaurent K σ) :=
  { instRing with
    inv := fun x => if h : x = 0 then 0 else rinv x (exists_lowest h).choose
    mul_inv_cancel := fun x hx => by
      show x * (if h : x = 0 then 0 else rinv x (exists_lowest h).choose) = 1
      rw [dite_eq_right hx]
      exact mul_rinv (exists_lowest hx).choose_spec.1 (exists_lowest hx).choose_spec.2
    inv_zero := dite_eq_left rfl
    exists_pair_ne := ⟨0, 1, zero_ne_one⟩
    nnqsmul := _
    qsmul := _ }

/-! ### The order -/

section Order

variable [LinearOrder K]

noncomputable instance : LinearOrder (SkewLaurent K σ) :=
  LinearOrder.lift' (fun x : SkewLaurent K σ => toLex (toHahn x)) fun _ _ h => h

/-- `x < y` iff at the first exponent where they differ, the coefficient of `x` is smaller. -/
theorem lt_iff_coeff (x y : SkewLaurent K σ) :
    x < y ↔ ∃ i, (∀ j < i, x.coeff j = y.coeff j) ∧ x.coeff i < y.coeff i :=
  HahnSeries.lt_iff (toLex (toHahn x)) (toLex (toHahn y))

/-- **Hilbert's convention**: a number is positive iff its first coefficient is positive. -/
theorem pos_iff (x : SkewLaurent K σ) :
    0 < x ↔ ∃ i, (∀ j < i, x.coeff j = 0) ∧ 0 < x.coeff i := by
  rw [lt_iff_coeff]
  simp only [coeff_zero]
  exact exists_congr fun i => and_congr_left' (forall₂_congr fun j _ => eq_comm)

theorem le_iff_toLex (x y : SkewLaurent K σ) : x ≤ y ↔ toLex (toHahn x) ≤ toLex (toHahn y) :=
  Iff.rfl

variable [IsStrictOrderedRing K]

instance : IsOrderedAddMonoid (SkewLaurent K σ) where
  add_le_add_left a b h c := by
    rw [le_iff_toLex] at h ⊢
    exact add_le_add (α := Lex (HahnSeries ℤ K)) h le_rfl
  add_le_add_right a b h c := by
    rw [le_iff_toLex] at h ⊢
    exact add_le_add (α := Lex (HahnSeries ℤ K)) le_rfl h

theorem zpow_pos_iff (hσ : ∀ a : K, 0 < σ a ↔ 0 < a) (j : ℤ) (a : K) :
    0 < (σ ^ j) a ↔ 0 < a := by
  induction j using Int.induction_on generalizing a with
  | zero => rfl
  | succ k ih => rw [zpow_add_one, RingAut.mul_apply, ih, hσ]
  | pred k ih =>
    rw [zpow_sub_one, RingAut.mul_apply, ih, ← hσ]
    show 0 < σ (σ.symm a) ↔ _
    rw [RingEquiv.apply_symm_apply]

theorem zero_lt_one' : (0 : SkewLaurent K σ) < 1 := by
  rw [pos_iff]
  exact ⟨0, fun j hj => by rw [coeff_one, ite_eq_right hj.ne], by rw [coeff_one, ite_eq_left rfl]; exact one_pos⟩

theorem mul_pos' (hσ : ∀ a : K, 0 < σ a ↔ 0 < a) {x y : SkewLaurent K σ} (hx : 0 < x)
    (hy : 0 < y) : 0 < x * y := by
  rw [pos_iff] at hx hy ⊢
  obtain ⟨i, hi, hxi⟩ := hx
  obtain ⟨j, hj, hyj⟩ := hy
  refine ⟨i + j, fun n hn => ?_, ?_⟩
  · rw [coeff_mul_Icc hi hj, Finset.Icc_eq_empty (by omega), Finset.sum_empty]
  · rw [coeff_mul_Icc hi hj, show i + j - j = i by ring, Finset.Icc_self, Finset.sum_singleton,
      show i + j - i = j by ring]
    exact mul_pos ((zpow_pos_iff hσ j _).2 hxi) hyj

instance : ZeroLEOneClass (SkewLaurent K σ) := ⟨zero_lt_one'.le⟩

/-- **The skew Laurent series over an ordered division ring, with an order-preserving `σ`, form
an ordered division ring.** -/
theorem isStrictOrderedRing (hσ : ∀ a : K, 0 < σ a ↔ 0 < a) :
    IsStrictOrderedRing (SkewLaurent K σ) :=
  IsStrictOrderedRing.of_mul_pos fun _ _ => mul_pos' hσ

end Order

end SkewLaurent


namespace SkewLaurent

variable {K : Type*} [Field K]

/-- With `σ = 1` and commutative coefficients the multiplication is commutative. -/
theorem mul_comm_of_one (x y : SkewLaurent K 1) : x * y = y * x := ext fun n => by
  rw [coeff_mul, coeff_mul, mulCoeff, mulCoeff]
  refine Finset.sum_equiv (Equiv.prodComm _ _) (fun ij => ?_) (fun ij _ => ?_)
  · simp only [Finset.mem_antidiagonal, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, by rw [add_comm]; exact h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, by rw [add_comm]; exact h3⟩
  · simp only [one_zpow, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    exact mul_comm _ _

/-- Scaling the coefficient of `s^n` by `c^n`. -/
noncomputable def scale (c : K) (x : SkewLaurent K 1) : SkewLaurent K 1 :=
  ofHahn ⟨fun n => c ^ n * x.coeff n, (isPWO_supp x).mono fun n hn => by
    by_contra h
    rw [mem_supp, not_not] at h
    exact hn (by simp only [h, mul_zero])⟩

theorem coeff_scale (c : K) (x : SkewLaurent K 1) (n : ℤ) :
    (scale c x).coeff n = c ^ n * x.coeff n := rfl

theorem supp_scale_subset (c : K) (x : SkewLaurent K 1) : supp (scale c x) ⊆ supp x :=
  fun n hn h => hn (by
    change x.coeff n = 0 at h
    show c ^ n * x.coeff n = 0
    rw [h, mul_zero])

theorem scale_add (c : K) (x y : SkewLaurent K 1) : scale c (x + y) = scale c x + scale c y :=
  ext fun n => by simp only [coeff_scale, coeff_add, mul_add]

theorem scale_mul {c : K} (hc : c ≠ 0) (x y : SkewLaurent K 1) :
    scale c (x * y) = scale c x * scale c y := ext fun n => by
  rw [coeff_scale, coeff_mul, mulCoeff, coeff_mul_eq (isPWO_supp x) (isPWO_supp y)
    (supp_scale_subset c x) (supp_scale_subset c y), Finset.mul_sum]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  simp only [one_zpow, coeff_scale]
  show c ^ n * (x.coeff ij.1 * y.coeff ij.2) = c ^ ij.1 * x.coeff ij.1 * (c ^ ij.2 * y.coeff ij.2)
  rw [← hij.2.2, zpow_add₀ hc]
  ring

theorem scale_scale {c d : K} (x : SkewLaurent K 1) : scale c (scale d x) = scale (c * d) x :=
  ext fun n => by simp only [coeff_scale, mul_zpow]; ring

theorem scale_one (x : SkewLaurent K 1) : scale 1 x = x := ext fun n => by
  simp only [coeff_scale, one_zpow, one_mul]

/-- The ring automorphism `T(t) ↦ T(c t)` of the Laurent series. -/
noncomputable def scaleAut {c : K} (hc : c ≠ 0) : RingAut (SkewLaurent K 1) where
  toFun := scale c
  invFun := scale c⁻¹
  left_inv x := by rw [scale_scale, inv_mul_cancel₀ hc, scale_one]
  right_inv x := by rw [scale_scale, mul_inv_cancel₀ hc, scale_one]
  map_mul' := scale_mul hc
  map_add' := scale_add c

theorem scaleAut_apply {c : K} (hc : c ≠ 0) (x : SkewLaurent K 1) : scaleAut hc x = scale c x :=
  rfl

theorem scaleAut_pos_iff [LinearOrder K] [IsStrictOrderedRing K] {c : K} (hc : 0 < c)
    (x : SkewLaurent K 1) : 0 < scaleAut hc.ne' x ↔ 0 < x := by
  rw [scaleAut_apply, pos_iff, pos_iff]
  simp only [coeff_scale]
  refine exists_congr fun i => and_congr ?_ ?_
  · exact forall₂_congr fun j _ => by
      rw [mul_eq_zero, or_iff_right (zpow_ne_zero j hc.ne')]
  · exact mul_pos_iff_of_pos_left (zpow_pos hc i)

end SkewLaurent

/-! ## Hilbert's number system `Ω(s, t)` -/

/-- **Hilbert's expressions `T`** (§ 33): `T = r₀ tⁿ + r₁ tⁿ⁺¹ + ⋯`, finite or infinite, with rational
coefficients, i.e. the formal Laurent series in `t` over `ℚ`, the commutative case `σ = 1`. -/
abbrev TSeries : Type := SkewLaurent ℚ 1

noncomputable instance : LinearOrder TSeries := inferInstance

instance TSeries.isStrictOrderedRing : IsStrictOrderedRing TSeries :=
  SkewLaurent.isStrictOrderedRing fun _ => Iff.rfl

/-- `T(t) ↦ T(2t)`: the rule `T s = s T(2t)`, i.e. `t s = 2 s t`. -/
noncomputable def sigma2 : RingAut TSeries := SkewLaurent.scaleAut (two_ne_zero (α := ℚ))

theorem sigma2_pos_iff (x : TSeries) : 0 < sigma2 x ↔ 0 < x :=
  SkewLaurent.scaleAut_pos_iff (two_pos (α := ℚ)) x

/-- **Hilbert's complex number system `Ω(s, t)`** (§ 33): the expressions
`S = s^m T₀ + s^{m+1} T₁ + ⋯` with coefficients `T_k` of the form `T`, multiplied with `t s = 2 s t`. -/
abbrev OmegaST : Type := SkewLaurent TSeries sigma2

instance OmegaST.isStrictOrderedRing : IsStrictOrderedRing OmegaST :=
  SkewLaurent.isStrictOrderedRing sigma2_pos_iff

namespace OmegaST

/-- The parameter `s`. -/
noncomputable def s : OmegaST := SkewLaurent.single 1 1

/-- The parameter `t` (the series `t` of `TSeries`, as a term of degree `0` in `s`). -/
noncomputable def tT : TSeries := SkewLaurent.single 1 1

/-- The parameter `t`. -/
noncomputable def t : OmegaST := SkewLaurent.single 0 tT

theorem sigma2_tT : sigma2 tT = tT + tT := SkewLaurent.ext fun n => by
  show (2 : ℚ) ^ n * (SkewLaurent.single (σ := 1) 1 (1 : ℚ)).coeff n = _
  rw [SkewLaurent.coeff_add, tT, SkewLaurent.coeff_single]
  split_ifs with h
  · subst h; norm_num
  · simp

/-- **Formula (1) of § 33: `t s = 2 s t`.** -/
theorem t_mul_s : t * s = 2 * (s * t) := by
  rw [two_mul]
  refine SkewLaurent.ext fun n => ?_
  rw [s, SkewLaurent.coeff_mul_single, SkewLaurent.coeff_add, SkewLaurent.coeff_single_mul, t,
    SkewLaurent.coeff_single, zpow_one, mul_one, map_one, one_mul]
  split_ifs with h
  · rw [sigma2_tT]
  · simp

theorem s_ne_zero : s ≠ 0 := fun h => by
  have := congrArg (fun z : OmegaST => z.coeff 1) h
  simp [s, SkewLaurent.coeff_single] at this

theorem tT_ne_zero : tT ≠ 0 := fun h => by
  have := congrArg (fun z : TSeries => z.coeff 1) h
  simp [tT, SkewLaurent.coeff_single] at this

theorem t_ne_zero : t ≠ 0 := fun h => by
  have := congrArg (fun z : OmegaST => z.coeff 0) h
  simp [t, SkewLaurent.coeff_single] at this
  exact tT_ne_zero this

/-- **The commutative law of multiplication fails in `Ω(s, t)`.** -/
theorem t_mul_s_ne : t * s ≠ s * t := fun h => by
  rw [t_mul_s, two_mul] at h
  exact mul_ne_zero s_ne_zero t_ne_zero (add_eq_left.1 h)

theorem s_pos : 0 < s := by
  rw [SkewLaurent.pos_iff]
  refine ⟨1, fun j hj => ?_, ?_⟩
  · rw [s, SkewLaurent.coeff_single, ite_eq_right hj.ne]
  · rw [s, SkewLaurent.coeff_single, ite_eq_left rfl]; exact one_pos

/-- `n s < 1` for every natural number `n`: `s` is infinitely small. -/
theorem nsmul_s_lt_one (n : ℕ) : n • s < 1 := by
  rw [SkewLaurent.lt_iff_coeff]
  have hc : ∀ j ≤ 0, (n • s).coeff j = 0 := fun j hj => by
    induction n with
    | zero => rw [zero_smul]; rfl
    | succ k ih => rw [succ_nsmul, SkewLaurent.coeff_add, ih, s, SkewLaurent.coeff_single,
        ite_eq_right (by omega), add_zero]
  refine ⟨0, fun j hj => ?_, ?_⟩
  · rw [hc j hj.le, SkewLaurent.one_def, SkewLaurent.coeff_single, ite_eq_right hj.ne]
  · rw [hc 0 le_rfl, SkewLaurent.one_def, SkewLaurent.coeff_single, ite_eq_left rfl]; exact one_pos

end OmegaST


/-! ## The commutative law in an archimedean ordered division ring (Theorem 38) -/

section Archimedean

variable {D : Type*} [DivisionRing D] [LinearOrder D] [IsStrictOrderedRing D]

/-- Products of integers times `d` (integers commute with every number). -/
theorem intCast_mul_mul (p q : ℤ) (d : D) :
    ((p : D) * d) * ((q : D) * d) = ((p * q : ℤ) : D) * (d * d) := by
  rw [mul_assoc, ← mul_assoc d, ← Int.cast_comm q d, mul_assoc, ← mul_assoc, Int.cast_mul]

/-- Hilbert's `m`: for `a > 0`, `d > 0` an integer `m ≥ 0` with `m d < a ≤ (m + 1) d`. -/
theorem exists_floor_mul [Archimedean D] {a d : D} (ha : 0 < a) (hd : 0 < d) :
    ∃ m : ℤ, 0 ≤ m ∧ (m : D) * d < a ∧ a ≤ ((m + 1 : ℤ) : D) * d := by
  obtain ⟨m, hm, -⟩ := existsUnique_sub_zsmul_mem_Ioc hd a 0
  rw [Set.mem_Ioc, zero_add, zsmul_eq_mul] at hm
  have h1 : (m : D) * d < a := by
    have := hm.1; rwa [sub_pos] at this
  have h2 : a ≤ ((m + 1 : ℤ) : D) * d := by
    have := hm.2
    rw [Int.cast_add, Int.cast_one, add_mul, one_mul]
    rw [sub_le_iff_le_add] at this
    rwa [add_comm] at this
  refine ⟨m, ?_, h1, h2⟩
  have hpos : 0 < ((m + 1 : ℤ) : D) * d := ha.trans_le h2
  have : (0 : D) < ((m + 1 : ℤ) : D) := pos_of_mul_pos_left hpos hd.le
  have : (0 : ℤ) < m + 1 := Int.cast_pos.1 this
  omega

/-- **Hilbert's estimates** (§ 32): if `m d < a ≤ (m + 1) d` and `n d < b ≤ (n + 1) d` (with
`a, b, d > 0`, `n ≥ 0`), then `a b ≤ m n d² + (m + n + 1) d²`, `b a > m n d²`, hence
`a b - b a < (m + n + 1) d²`. -/
theorem hilbert_estimates {a b d : D} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) {m n : ℤ}
    (hn0 : 0 ≤ n) (hA1 : (m : D) * d < a) (hA2 : a ≤ ((m + 1 : ℤ) : D) * d)
    (hB1 : (n : D) * d < b) (hB2 : b ≤ ((n + 1 : ℤ) : D) * d) :
    a * b ≤ ((m * n : ℤ) : D) * (d * d) + ((m + n + 1 : ℤ) : D) * (d * d) ∧
      ((m * n : ℤ) : D) * (d * d) < b * a ∧
      a * b - b * a < ((m + n + 1 : ℤ) : D) * (d * d) := by
  -- `a b ≤ (m + 1) (n + 1) d²`
  have k1 : a * b ≤ (((m + 1) * (n + 1) : ℤ) : D) * (d * d) := by
    rw [← intCast_mul_mul]
    have hM : (0 : D) ≤ ((m + 1 : ℤ) : D) * d := ha.le.trans hA2
    calc a * b ≤ (((m + 1 : ℤ) : D) * d) * b := mul_le_mul_of_nonneg_right hA2 hb.le
      _ ≤ (((m + 1 : ℤ) : D) * d) * (((n + 1 : ℤ) : D) * d) := mul_le_mul_of_nonneg_left hB2 hM
  -- `b a > m n d²`
  have k2 : (((n * m) : ℤ) : D) * (d * d) < b * a := by
    rw [← intCast_mul_mul]
    have hN : (0 : D) ≤ (n : D) * d := mul_nonneg (Int.cast_nonneg hn0) hd.le
    calc ((n : D) * d) * ((m : D) * d) ≤ ((n : D) * d) * a := mul_le_mul_of_nonneg_left hA1.le hN
      _ < b * a := mul_lt_mul_of_pos_right hB1 ha
  have e1 : (((m + 1) * (n + 1) : ℤ) : D) * (d * d) =
      ((m * n : ℤ) : D) * (d * d) + ((m + n + 1 : ℤ) : D) * (d * d) := by
    rw [← add_mul, ← Int.cast_add]; congr 2; ring
  have e2 : ((n * m : ℤ) : D) = ((m * n : ℤ) : D) := by rw [mul_comm]
  refine ⟨by rw [← e1]; exact k1, by rw [← e2]; exact k2, ?_⟩
  have := lt_of_le_of_lt (sub_le_sub_right k1 _) (sub_lt_sub_left k2 _)
  rwa [← sub_mul, ← Int.cast_sub, show (m + 1) * (n + 1) - n * m = m + n + 1 by ring] at this

/-- **Hilbert's estimate** `(m + n + 1) d < a + b + 1` (from `m d < a`, `n d < b`, `d < 1`). -/
theorem hilbert_sum_estimate {a b d : D} {m n : ℤ} (hA1 : (m : D) * d < a)
    (hB1 : (n : D) * d < b) (hd1 : d < 1) : ((m + n + 1 : ℤ) : D) * d < a + b + 1 := by
  rw [Int.cast_add, Int.cast_add, Int.cast_one, add_mul, add_mul, one_mul]
  exact add_lt_add (add_lt_add hA1 hB1) hd1

/-- **The reduction of § 32**: if two numbers do not commute, there are `a > 0`, `b > 0` with
`a b - b a > 0`. -/
theorem exists_pos_comm_sub {a b : D} (h : a * b ≠ b * a) :
    ∃ a b : D, 0 < a ∧ 0 < b ∧ 0 < a * b - b * a := by
  have key : ∀ a b : D, 0 < a → 0 < b → a * b ≠ b * a →
      ∃ a b : D, 0 < a ∧ 0 < b ∧ 0 < a * b - b * a := fun a b ha hb h => by
    rcases lt_or_gt_of_ne (sub_ne_zero.2 h) with h' | h'
    · exact ⟨b, a, hb, ha, by rw [← neg_sub]; exact neg_pos.2 h'⟩
    · exact ⟨a, b, ha, hb, h'⟩
  have ha0 : a ≠ 0 := by rintro rfl; simp at h
  have hb0 : b ≠ 0 := by rintro rfl; simp at h
  rcases lt_or_gt_of_ne ha0 with ha | ha <;> rcases lt_or_gt_of_ne hb0 with hb | hb
  · exact key (-a) (-b) (neg_pos.2 ha) (neg_pos.2 hb) (by rw [neg_mul_neg, neg_mul_neg]; exact h)
  · exact key (-a) b (neg_pos.2 ha) hb (by rw [neg_mul, mul_neg]; exact fun e => h (neg_inj.1 e))
  · exact key a (-b) ha (neg_pos.2 hb) (by rw [mul_neg, neg_mul]; exact fun e => h (neg_inj.1 e))
  · exact key a b ha hb h

/-- **Hilbert's argument (§ 32)**: in an archimedean ordered division ring, for `a > 0`, `b > 0`
the difference `a b - b a` is not positive. -/
theorem not_pos_comm_sub [Archimedean D] {a b : D} (ha : 0 < a) (hb : 0 < b) :
    ¬0 < a * b - b * a := by
  intro hD
  have h1 : (0 : D) < a + b + 1 := add_pos (add_pos ha hb) one_pos
  -- the number `c` with `(a + b + 1) c = a b - b a` (law 6)
  set c := (a + b + 1)⁻¹ * (a * b - b * a) with hcdef
  have hc : (a + b + 1) * c = a * b - b * a := by
    rw [hcdef, ← mul_assoc, mul_inv_cancel₀ h1.ne', one_mul]
  have hc0 : 0 < c := mul_pos (inv_pos.2 h1) hD
  -- the number `d` with `0 < d < 1`, `d < c`
  have h2 : (0 : D) < 2 := two_pos
  have hhalf : (2 : D)⁻¹ < 1 := inv_lt_one_of_one_lt₀ one_lt_two
  set e := min c 1 with hedef
  have he : 0 < e := lt_min hc0 one_pos
  set d := e * (2 : D)⁻¹ with hddef
  have hd : 0 < d := mul_pos he (inv_pos.2 h2)
  have hde : d < e := by
    have := mul_lt_mul_of_pos_left hhalf he; rwa [mul_one] at this
  have hd1 : d < 1 := hde.trans_le (min_le_right _ _)
  have hdc : d < c := hde.trans_le (min_le_left _ _)
  -- Hilbert's `m`, `n` (Archimedes)
  obtain ⟨m, -, hA1, hA2⟩ := exists_floor_mul ha hd
  obtain ⟨n, hn0, hB1, hB2⟩ := exists_floor_mul hb hd
  have k3 := (hilbert_estimates ha hb hd hn0 hA1 hA2 hB1 hB2).2.2
  have k4 := hilbert_sum_estimate hA1 hB1 hd1
  -- `a b - b a < (a + b + 1) d < (a + b + 1) c = a b - b a`
  have k5 : (((m + n + 1) : ℤ) : D) * (d * d) < (a + b + 1) * d := by
    rw [← mul_assoc]; exact mul_lt_mul_of_pos_right k4 hd
  have k6 : (a + b + 1) * d < (a + b + 1) * c := mul_lt_mul_of_pos_left hdc h1
  have := (k3.trans k5).trans k6
  rw [hc] at this
  exact lt_irrefl _ this

/-- **Theorem 38** (in the language of ordered division rings): an archimedean ordered division
ring is commutative. -/
theorem mul_comm_of_archimedean [Archimedean D] (a b : D) : a * b = b * a := by
  have pos : ∀ a b : D, 0 < a → 0 < b → a * b = b * a := fun a b ha hb => by
    have h1 := not_pos_comm_sub ha hb
    have h2 := not_pos_comm_sub hb ha
    rw [not_lt, sub_nonpos] at h1 h2
    exact le_antisymm h1 h2
  have pos' : ∀ a b : D, 0 < a → a * b = b * a := fun a b ha => by
    rcases lt_trichotomy b 0 with hb | rfl | hb
    · have := pos a (-b) ha (neg_pos.2 hb)
      rw [mul_neg, neg_mul] at this
      exact neg_inj.1 this
    · rw [mul_zero, zero_mul]
    · exact pos a b ha hb
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have := pos' (-a) b (neg_pos.2 ha)
    rw [mul_neg, neg_mul] at this
    exact (neg_inj.1 this)
  · rw [mul_zero, zero_mul]
  · exact pos' a b ha

end Archimedean


/-! ## Theorem 38 in the language of the laws of § 13 -/

open DesAlg

section LawsDR

variable {D : Type*} [DivisionRing D] [LinearOrder D] [IsStrictOrderedRing D]

/-- `a + a + ⋯ + a` (`n + 1` terms) is `(n + 1) • a`. -/
theorem repeatAdd_eq_nsmul (a : D) (n : ℕ) : repeatAdd D a n = (n + 1) • a := by
  induction n with
  | zero => simp [repeatAdd]
  | succ n ih => rw [repeatAdd, ih]; exact (succ_nsmul a (n + 1)).symm

/-- **Law 17 is the archimedean property** of an ordered division ring. -/
theorem law17_iff_archimedean' : Law17 D ↔ Archimedean D := by
  constructor
  · intro h
    refine ⟨fun x y hy => ?_⟩
    rcases le_or_gt x 0 with hx | hx
    · exact ⟨0, by simpa using hx⟩
    · obtain ⟨n, hn⟩ := h y x hy hx
      rw [repeatAdd_eq_nsmul] at hn
      exact ⟨n + 1, hn.le⟩
  · intro h a b ha _
    obtain ⟨n, hn⟩ := Archimedean.arch b ha
    refine ⟨n, ?_⟩
    rw [repeatAdd_eq_nsmul, succ_nsmul]
    exact lt_of_le_of_lt hn (lt_add_of_pos_right _ ha)

end LawsDR

/-- **Theorem 38** (laws of § 13): a number system with the laws 1–11, 13–17 (law 13 with its
tacit asymmetry) satisfies law 12. -/
theorem theorem38_laws {α : Type*} [Add α] [Mul α] [Zero α] [One α] [LT α]
    (h : DesarguesianNumberSystem α) (ha : Law13Asymm α) (h17 : Law17 α) : Law12 α := by
  by_cases h01 : (0 : α) = 1
  · intro a b
    rw [dns_trivial_of_zero_eq_one h h01 a, dns_trivial_of_zero_eq_one h h01 b]
  let := h.toDivisionRing h01
  let := h.toLinearOrder ha
  have := h.isStrictOrderedRing ha h01
  have : Archimedean α := law17_iff_archimedean'.1 h17
  exact fun a b => mul_comm_of_archimedean a b

/-! ## The laws for `Ω(s, t)` -/

namespace OmegaST

/-- `Ω(s, t)` is a desarguesian number system (laws 1–11, 13–16, with the asymmetry of 13). -/
theorem dns : DesarguesianNumberSystem OmegaST ∧ Law13Asymm OmegaST ∧ (0 : OmegaST) ≠ 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h13, h13a, h14, h15, h16⟩ :=
    DesAlg.laws_of_divisionRing (D := OmegaST)
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h13, h14, h15, h16⟩, h13a, zero_ne_one⟩

/-- Law 12 fails in `Ω(s, t)`. -/
theorem not_law12 : ¬Law12 OmegaST := fun h => t_mul_s_ne (h t s)

/-- Law 17 (Archimedes) fails in `Ω(s, t)`: no multiple of `s` exceeds `1`. -/
theorem not_law17 : ¬Law17 OmegaST := fun h => by
  obtain ⟨n, hn⟩ := h s 1 s_pos one_pos
  rw [repeatAdd_eq_nsmul] at hn
  exact lt_asymm hn (nsmul_s_lt_one (n + 1))

/-- The laws hold for every ordered division ring. -/
theorem laws_of_sub (S : Subfield OmegaST) :
    DesarguesianNumberSystem S ∧ Law13Asymm S ∧ (0 : S) ≠ 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h13, h13a, h14, h15, h16⟩ :=
    DesAlg.laws_of_divisionRing (D := S)
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h13, h14, h15, h16⟩, h13a, zero_ne_one⟩

end OmegaST

/-! ## Cardinality -/

namespace SkewLaurent

/-- The series `∑_{n ∈ S} tⁿ` of a set `S` of natural numbers. -/
noncomputable def ofSet (S : Set ℕ) : TSeries := by
  classical
  exact ofHahn ⟨fun n => if 0 ≤ n ∧ n.toNat ∈ S then 1 else 0,
    (isPWO_Ici 0).mono fun n hn => by
      by_contra h
      exact hn (ite_eq_right fun h' => h h'.1)⟩

theorem ofSet_injective : Function.Injective ofSet := fun S T h => by
  classical
  ext k
  have := congrArg (fun z : TSeries => z.coeff k) h
  simp only [ofSet, coeff_ofHahn, Nat.cast_nonneg, Int.toNat_natCast, true_and] at this
  constructor
  · intro hk
    by_contra hk'
    rw [ite_eq_left hk, ite_eq_right hk'] at this
    exact one_ne_zero this
  · intro hk
    by_contra hk'
    rw [ite_eq_right hk', ite_eq_left hk] at this
    exact zero_ne_one this

end SkewLaurent

/-- **The expressions `T` are not enumerable.** -/
theorem tSeries_not_countable : ¬Countable TSeries := fun h => by
  obtain ⟨f, hf⟩ := h.exists_injective_nat
  exact Function.cantor_injective _ (hf.comp SkewLaurent.ofSet_injective)

/-- **`Ω(s, t)` is not enumerable**: it contains the expressions `T` (as the terms `s⁰ T`). -/
theorem omegaST_not_countable : ¬Countable OmegaST := fun h => by
  apply tSeries_not_countable
  have hinj : Function.Injective (fun T : TSeries => (SkewLaurent.single 0 T : OmegaST)) :=
    fun T T' e => by
      have := congrArg (fun z : OmegaST => z.coeff 0) e
      simpa [SkewLaurent.coeff_single] using this
  exact hinj.countable

/-- The sub-division ring of `Ω(s, t)` generated by `s` and `t`. -/
noncomputable def omegaST₀ : Subfield OmegaST := Subfield.closure {OmegaST.s, OmegaST.t}

/-- **It is enumerable.** -/
theorem omegaST₀_countable : Countable omegaST₀ := by
  rw [← Cardinal.mk_le_aleph0_iff]
  refine (Subfield.cardinalMk_closure_le_max _).trans (max_le ?_ le_rfl)
  have : ({OmegaST.s, OmegaST.t} : Set OmegaST).Countable := (Set.toFinite _).countable
  exact Cardinal.mk_le_aleph0_iff.2 this.to_subtype

/-- `s` and `t` as elements of the enumerable system. -/
noncomputable def s₀ : omegaST₀ := ⟨OmegaST.s, Subfield.subset_closure (by simp)⟩
noncomputable def t₀ : omegaST₀ := ⟨OmegaST.t, Subfield.subset_closure (by simp)⟩

theorem omegaST₀_not_law12 : ¬Law12 omegaST₀ := fun h => OmegaST.t_mul_s_ne (by
  have := congrArg Subtype.val (h t₀ s₀)
  exact this)

theorem omegaST₀_not_law17 : ¬Law17 omegaST₀ := fun h => by
  obtain ⟨n, hn⟩ := h s₀ 1 (show (0 : OmegaST) < OmegaST.s from OmegaST.s_pos) one_pos
  rw [repeatAdd_eq_nsmul] at hn
  have : ((n + 1) • s₀ : omegaST₀).val = (n + 1) • OmegaST.s := by
    simp [s₀]
  have hn' : (1 : OmegaST) < (n + 1) • OmegaST.s := by
    rw [← this]; exact hn
  exact lt_asymm hn' (OmegaST.nsmul_s_lt_one (n + 1))


/-! ## Terms and powers of `s` -/

namespace SkewLaurent

variable {K : Type*} [DivisionRing K] {σ : RingAut K}

/-- **The product of two terms**: `(s^i a)(s^j b) = s^{i+j} σ^j(a) b`. -/
theorem single_mul_single (i j : ℤ) (a b : K) :
    (single i a * single j b : SkewLaurent K σ) = single (i + j) ((σ ^ j) a * b) := ext fun n => by
  rw [coeff_single_mul, coeff_single, coeff_single]
  by_cases h : n - i = j
  · rw [ite_eq_left h, ite_eq_left (by omega), h]
  · rw [ite_eq_right h, ite_eq_right (by omega), mul_zero]

theorem single_one_pow (n : ℕ) : (single 1 1 : SkewLaurent K σ) ^ n = single n 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ih, single_mul_single, zpow_one, map_one, one_mul]
    push_cast; rfl

theorem single_one_zpow (k : ℤ) : (single 1 1 : SkewLaurent K σ) ^ k = single k 1 := by
  cases k with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, single_one_pow]
  | negSucc n =>
    rw [zpow_negSucc, single_one_pow]
    apply inv_eq_of_mul_eq_one_right
    rw [single_mul_single, map_one, one_mul, show ((n + 1 : ℕ) : ℤ) + Int.negSucc n = 0 by omega]
    rfl

end SkewLaurent

namespace OmegaST

/-- `s^k = s^k · 1` is the term with exponent `k`. -/
theorem s_zpow (k : ℤ) : s ^ k = SkewLaurent.single k 1 := SkewLaurent.single_one_zpow k

/-- **The term `s^k T` of an expression `S`** is the product of the power `s^k` and the number `T`
(the expression `T` regarded as an element of `Ω(s, t)`). -/
theorem single_eq (k : ℤ) (T : TSeries) :
    (SkewLaurent.single k T : OmegaST) = s ^ k * SkewLaurent.single 0 T := by
  rw [s_zpow, SkewLaurent.single_mul_single, add_zero, zpow_zero, map_one, one_mul]

end OmegaST

/-! ## Law 13 must include its asymmetry for Theorem 38 -/

section Laws111

variable {D : Type*} [DivisionRing D] [LT D]

/-- Laws 1–11 hold in every division ring (whatever the relation `<`). -/
theorem laws_1_11_of_divisionRing :
    Law1 D ∧ Law2 D ∧ Law3 D ∧ Law4 D ∧ Law5 D ∧ Law6 D ∧ Law7 D ∧ Law8 D ∧ Law9 D ∧ Law10 D ∧
      Law11 D := by
  refine ⟨law1_holds D, fun a => ⟨add_zero a, zero_add a⟩, fun a b => ⟨⟨-a + b, by abel,
    fun x hx => by rw [← hx]; abel⟩, ⟨b + -a, by abel, fun y hy => by rw [← hy]; abel⟩⟩,
    law4_holds D, fun a => ⟨mul_one a, one_mul a⟩, fun a b ha => ⟨⟨a⁻¹ * b, by
      show a * (a⁻¹ * b) = b
      rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul], fun x hx => by
      rw [← hx, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]⟩, ⟨b * a⁻¹, by
      show b * a⁻¹ * a = b
      rw [mul_assoc, inv_mul_cancel₀ ha, mul_one], fun y hy => by
      rw [← hy, mul_assoc, mul_inv_cancel₀ ha, mul_one]⟩⟩,
    fun a b c => (add_assoc a b c).symm, add_comm, fun a b c => (mul_assoc a b c).symm,
    mul_add, add_mul⟩

end Laws111

/-- The quaternions over `ℚ`, with the relation "`a < b` for all `a`, `b`". -/
def QuatTotal : Type := Quaternion ℚ

noncomputable instance : DivisionRing QuatTotal := inferInstanceAs (DivisionRing (Quaternion ℚ))

instance : LT QuatTotal := ⟨fun _ _ => True⟩

/-- **Without the asymmetry of law 13, Theorem 38 fails**: the quaternions with the relation `<`
always true satisfy laws 1–11 and 13–17 as printed, but not law 12. -/
theorem quatTotal_laws : DesarguesianNumberSystem QuatTotal ∧ Law17 QuatTotal ∧
    ¬Law13Asymm QuatTotal ∧ ¬Law12 QuatTotal := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    laws_1_11_of_divisionRing (D := QuatTotal)
  refine ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, fun _ _ _ => Or.inl trivial,
    fun _ _ _ _ _ => trivial, fun _ _ _ _ => ⟨trivial, trivial⟩,
    fun _ _ _ _ _ => ⟨trivial, trivial⟩⟩, fun _ _ _ _ => ⟨0, trivial⟩,
    fun h => h 0 0 trivial trivial, fun h => ?_⟩
  have e : (⟨0, 1, 0, 0⟩ : Quaternion ℚ) * ⟨0, 0, 1, 0⟩ = (⟨0, 0, 1, 0⟩ : Quaternion ℚ) * ⟨0, 1, 0, 0⟩ :=
    h (⟨0, 1, 0, 0⟩ : Quaternion ℚ) (⟨0, 0, 1, 0⟩ : Quaternion ℚ)
  have := congrArg QuaternionAlgebra.imK e
  rw [Quaternion.imK_mul, Quaternion.imK_mul] at this
  norm_num at this

end NonPascal
end HilbertFoundations
