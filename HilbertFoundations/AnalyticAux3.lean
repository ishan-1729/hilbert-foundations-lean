import HilbertFoundations.AnalyticAux2

/-!
# Hilbert's non-archimedean field `Ω(t)` (helper for § 13; constructed in § 12)

Helper module of `Analytic.lean` (unit `s13.omega_t`). Hilbert's `Ω(t)` (§ 12) is the domain of
the real functions of `t` obtained from `t` by the four operations and `ω ↦ √(1 + ω²)`, two
functions being compared "for sufficiently large values of `t`". Here:

* `OmegaT.IsGen f`: the function `f : ℝ → ℝ` is obtained from `t ↦ t` (and `1`) by the five
  operations (division only by functions that are not eventually zero, Hilbert's "division" by a
  nonzero number of the system);
* `OmegaT`: the germs at `+∞` (`Filter.Germ Filter.atTop ℝ`) of such functions, a subring of the
  ring of germs; two functions agreeing for large `t` are the same number.

The key fact, Hilbert's "it can in no case vanish for more than a finite number of values of `t`,
and, hence, for sufficiently large positive values of `t`, it must remain always positive or always
negative", is `OmegaT.IsGen.trichotomy`. Hilbert argues by algebraicity; the proof here uses that
`s ↦ f (1/s)` is (on a right neighbourhood of `0`) a meromorphic function of `s`
(`OmegaT.IsGen.rep`, the square root being the delicate case, `exists_meromorphic_sqrt`), and the
identity theorem for meromorphic functions together with the intermediate value theorem.

Results: `OmegaT` is a linearly ordered field (`OmegaT.instField`, `OmegaT.instLinearOrder`,
`OmegaT.instIsStrictOrderedRing`) whose order is Hilbert's (`OmegaT.lt_iff_eventually`), it is
Pythagorean (`OmegaT.instIsPythagorean`), and it is not archimedean
(`OmegaT.natCast_lt_t`, `OmegaT.not_archimedean`).
-/

namespace HilbertFoundations

open Filter Topology

/-! ### A square root of `1 + F²` for meromorphic `F` -/

theorem analyticAt_sqrt_comp {g : ℝ → ℝ} {x : ℝ} (hg : AnalyticAt ℝ g x) (hx : 0 < g x) :
    AnalyticAt ℝ (fun z => Real.sqrt (g z)) x :=
  ((Real.contDiffAt_sqrt (n := ⊤) hx.ne').analyticAt).comp hg

theorem nhdsGT_le_nhdsNE : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 :=
  nhdsWithin_mono _ (fun _ hx => ne_of_gt hx)

/-- If `F` is meromorphic at `0`, then `√(1 + F²)` agrees on a right neighbourhood of `0` with a
function meromorphic at `0`. -/
theorem exists_meromorphic_sqrt {F : ℝ → ℝ} (hF : MeromorphicAt F 0) :
    ∃ H : ℝ → ℝ, MeromorphicAt H 0 ∧ ∀ᶠ s in 𝓝[>] (0 : ℝ), Real.sqrt (1 + F s ^ 2) = H s := by
  cases h : meromorphicOrderAt F 0 with
  | top =>
    rw [meromorphicOrderAt_eq_top_iff] at h
    refine ⟨fun _ => 1, analyticAt_const.meromorphicAt, (h.filter_mono nhdsGT_le_nhdsNE).mono fun s hs => ?_⟩
    simp [hs]
  | coe n =>
    obtain ⟨g, hg, hg0, hFg⟩ := (meromorphicOrderAt_eq_int_iff hF).1 h
    rcases le_or_gt 0 n with hn | hn
    · lift n to ℕ using hn
      have hG : AnalyticAt ℝ (fun z => z ^ n * g z) 0 := (analyticAt_id.pow n).mul hg
      have hK : AnalyticAt ℝ (fun z => 1 + (z ^ n * g z) ^ 2) 0 := analyticAt_const.add (hG.pow 2)
      refine ⟨fun z => Real.sqrt (1 + (z ^ n * g z) ^ 2),
        (analyticAt_sqrt_comp hK (by positivity)).meromorphicAt, ?_⟩
      filter_upwards [hFg.filter_mono nhdsGT_le_nhdsNE] with s hs
      rw [hs, sub_zero, smul_eq_mul, zpow_natCast]
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨n.natAbs, by omega⟩
      have hm0 : 0 < m := by omega
      subst hm
      have hK : AnalyticAt ℝ (fun z => z ^ (2 * m) + g z ^ 2) 0 :=
        (analyticAt_id.pow _).add (hg.pow 2)
      have hK0 : 0 < (0 : ℝ) ^ (2 * m) + g 0 ^ 2 := by
        rw [zero_pow (by omega), zero_add]; positivity
      refine ⟨fun z => z ^ (-(m : ℤ)) * Real.sqrt (z ^ (2 * m) + g z ^ 2), ?_, ?_⟩
      · exact (analyticAt_id.meromorphicAt.zpow (-(m : ℤ))).mul
          (analyticAt_sqrt_comp hK hK0).meromorphicAt
      · filter_upwards [hFg.filter_mono nhdsGT_le_nhdsNE, self_mem_nhdsWithin] with s hs hpos
        have hs0 : (0 : ℝ) < s := hpos
        rw [hs, sub_zero, smul_eq_mul]
        have e : 1 + (s ^ (-(m : ℤ)) * g s) ^ 2 = (s ^ (-(m : ℤ))) ^ 2 * (s ^ (2 * m) + g s ^ 2) := by
          rw [zpow_neg, zpow_natCast]
          field_simp
          ring
        rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (zpow_pos hs0 _).le]

namespace OmegaT

/-- **The functions of Hilbert's `Ω(t)`**: obtained from `t` (and `1`) by the five operations. -/
inductive IsGen : (ℝ → ℝ) → Prop
  | t : IsGen id
  | one : IsGen 1
  | add {f g : ℝ → ℝ} : IsGen f → IsGen g → IsGen (f + g)
  | sub {f g : ℝ → ℝ} : IsGen f → IsGen g → IsGen (f - g)
  | mul {f g : ℝ → ℝ} : IsGen f → IsGen g → IsGen (f * g)
  | div {f g : ℝ → ℝ} : IsGen f → IsGen g → ¬(g =ᶠ[atTop] 0) → IsGen (f / g)
  | sqrt {f : ℝ → ℝ} : IsGen f → IsGen (fun x => Real.sqrt (1 + f x ^ 2))

theorem IsGen.zero : IsGen 0 := by simpa using IsGen.sub IsGen.one IsGen.one

/-- `f (t) = F (1/t)` for large `t`, with `F` meromorphic at `0`. -/
def Rep (f : ℝ → ℝ) : Prop :=
  ∃ F : ℝ → ℝ, MeromorphicAt F 0 ∧ ∀ᶠ t in atTop, f t = F t⁻¹

theorem IsGen.rep {f : ℝ → ℝ} (h : IsGen f) : Rep f := by
  induction h with
  | t =>
    refine ⟨fun s => s⁻¹, analyticAt_id.meromorphicAt.inv, Eventually.of_forall fun t => ?_⟩
    simp
  | one => exact ⟨fun _ => 1, analyticAt_const.meromorphicAt, Eventually.of_forall fun _ => rfl⟩
  | add _ _ hf hg =>
    obtain ⟨F, hF, hfF⟩ := hf; obtain ⟨G, hG, hgG⟩ := hg
    exact ⟨F + G, hF.add hG, by filter_upwards [hfF, hgG] with t h1 h2; simp [h1, h2]⟩
  | sub _ _ hf hg =>
    obtain ⟨F, hF, hfF⟩ := hf; obtain ⟨G, hG, hgG⟩ := hg
    exact ⟨F - G, hF.sub hG, by filter_upwards [hfF, hgG] with t h1 h2; simp [h1, h2]⟩
  | mul _ _ hf hg =>
    obtain ⟨F, hF, hfF⟩ := hf; obtain ⟨G, hG, hgG⟩ := hg
    exact ⟨F * G, hF.mul hG, by filter_upwards [hfF, hgG] with t h1 h2; simp [h1, h2]⟩
  | div _ _ _ hf hg =>
    obtain ⟨F, hF, hfF⟩ := hf; obtain ⟨G, hG, hgG⟩ := hg
    exact ⟨F / G, hF.div hG, by filter_upwards [hfF, hgG] with t h1 h2; simp [h1, h2]⟩
  | sqrt _ hf =>
    obtain ⟨F, hF, hfF⟩ := hf
    obtain ⟨H, hH, hFH⟩ := exists_meromorphic_sqrt hF
    refine ⟨H, hH, ?_⟩
    filter_upwards [hfF, tendsto_inv_atTop_nhdsGT_zero.eventually hFH] with t h1 h2
    rw [h1, h2]

/-- **Hilbert's key fact** (§ 12): every function of `Ω(t)` is, for all sufficiently large `t`,
identically zero, or always positive, or always negative. -/
theorem Rep.trichotomy {f : ℝ → ℝ} (h : Rep f) :
    (∀ᶠ t in atTop, f t = 0) ∨ (∀ᶠ t in atTop, 0 < f t) ∨ (∀ᶠ t in atTop, f t < 0) := by
  obtain ⟨F, hF, hfF⟩ := h
  have htend := tendsto_inv_atTop_nhdsGT_zero (𝕜 := ℝ)
  rcases hF.eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · left
    filter_upwards [hfF, htend.eventually (h0.filter_mono nhdsGT_le_nhdsNE)] with t h1 h2
    rw [h1, h2]
  · right
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), F s ≠ 0 ∧ AnalyticAt ℝ F s :=
      (hne.and hF.eventually_analyticAt).filter_mono nhdsGT_le_nhdsNE
    obtain ⟨ε, hε, hP⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 hev
    have hcont : ContinuousOn F (Set.Ioo 0 ε) :=
      fun s hs => (hP hs).2.continuousAt.continuousWithinAt
    have hs0 : ε / 2 ∈ Set.Ioo 0 ε := ⟨by linarith, by linarith⟩
    have hIoo : Set.Ioo (0 : ℝ) ε ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hε
    rcases lt_or_gt_of_ne (hP hs0).1 with hneg | hpos
    · right
      have hall : ∀ s ∈ Set.Ioo 0 ε, F s < 0 := by
        intro s hs
        rcases lt_or_gt_of_ne (hP hs).1 with h' | h'
        · exact h'
        · exfalso
          obtain ⟨x, hx, hx0⟩ := isPreconnected_Ioo.intermediate_value hs0 hs hcont
            ⟨hneg.le, h'.le⟩
          exact (hP hx).1 hx0
      filter_upwards [hfF, htend.eventually hIoo] with t h1 h2
      rw [h1]; exact hall _ h2
    · left
      have hall : ∀ s ∈ Set.Ioo 0 ε, 0 < F s := by
        intro s hs
        rcases lt_or_gt_of_ne (hP hs).1 with h' | h'
        · exfalso
          obtain ⟨x, hx, hx0⟩ := isPreconnected_Ioo.intermediate_value hs hs0 hcont
            ⟨h'.le, hpos.le⟩
          exact (hP hx).1 hx0
        · exact h'
      filter_upwards [hfF, htend.eventually hIoo] with t h1 h2
      rw [h1]; exact hall _ h2

theorem IsGen.trichotomy {f : ℝ → ℝ} (h : IsGen f) :
    (∀ᶠ t in atTop, f t = 0) ∨ (∀ᶠ t in atTop, 0 < f t) ∨ (∀ᶠ t in atTop, f t < 0) :=
  h.rep.trichotomy

/-! ### The field `Ω(t)` -/

end OmegaT

/-- Germs of real functions at `+∞`. -/
abbrev GermT : Type := Germ (atTop : Filter ℝ) ℝ

/-- The germs at `+∞` of the functions of `Ω(t)`. -/
def omegaTSubring : Subring GermT where
  carrier := {x | ∃ f : ℝ → ℝ, OmegaT.IsGen f ∧ (f : GermT) = x}
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩; exact ⟨f * g, hf.mul hg, Germ.coe_mul f g⟩
  one_mem' := ⟨1, OmegaT.IsGen.one, Germ.coe_one⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩; exact ⟨f + g, hf.add hg, Germ.coe_add f g⟩
  zero_mem' := ⟨0, OmegaT.IsGen.zero, Germ.coe_zero⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨0 - f, OmegaT.IsGen.zero.sub hf, by rw [zero_sub, Germ.coe_neg]⟩

/-- **Hilbert's number system `Ω(t)`** (§ 12). -/
abbrev OmegaT : Type := omegaTSubring

namespace OmegaT

theorem mem_omegaTSubring {x : GermT} : x ∈ omegaTSubring ↔ ∃ f, IsGen f ∧ (f : GermT) = x :=
  Iff.rfl

theorem exists_rep (x : HilbertFoundations.OmegaT) :
    ∃ f, IsGen f ∧ (f : GermT) = (x : GermT) := x.2

theorem eq_zero_or_eventually_ne {f : ℝ → ℝ} (hf : IsGen f) :
    (f =ᶠ[atTop] 0) ∨ ∀ᶠ t in atTop, f t ≠ 0 := by
  rcases hf.trichotomy with h | h | h
  · exact Or.inl h
  · exact Or.inr (h.mono fun _ h => h.ne')
  · exact Or.inr (h.mono fun _ h => h.ne)

theorem inv_mem {x : GermT} (hx : x ∈ omegaTSubring) : x⁻¹ ∈ omegaTSubring := by
  obtain ⟨f, hf, rfl⟩ := hx
  rcases eq_zero_or_eventually_ne hf with h | h
  · refine ⟨0, IsGen.zero, ?_⟩
    rw [← Germ.coe_inv, Germ.coe_eq]
    filter_upwards [h] with t ht; simp [ht]
  · refine ⟨1 / f, IsGen.one.div hf (fun h' => ?_), ?_⟩
    · obtain ⟨t, h1, h2⟩ := (h.and h').exists; exact h1 h2
    · rw [← Germ.coe_inv, one_div]


noncomputable instance instField : Field OmegaT :=
  { (inferInstance : CommRing OmegaT) with
    inv := fun x => ⟨(x : GermT)⁻¹, inv_mem x.2⟩
    exists_pair_ne := ⟨0, 1, fun h => by
      have : ((0 : OmegaT) : GermT) = ((1 : OmegaT) : GermT) := congrArg _ h
      simp only [ZeroMemClass.coe_zero, OneMemClass.coe_one] at this
      exact zero_ne_one (Germ.const_inj.1 this)⟩
    mul_inv_cancel := fun x hx => by
      apply Subtype.ext
      obtain ⟨f, hf, hfx⟩ := x.2
      show (x : GermT) * (x : GermT)⁻¹ = 1
      rw [← hfx, ← Germ.coe_inv, ← Germ.coe_mul, ← Germ.coe_one, Germ.coe_eq]
      rcases eq_zero_or_eventually_ne hf with h | h
      · exfalso; apply hx; apply Subtype.ext
        rw [ZeroMemClass.coe_zero, ← hfx, ← Germ.coe_zero, Germ.coe_eq]; exact h
      · filter_upwards [h] with t ht; simp [ht]
    inv_zero := by
      apply Subtype.ext
      show ((0 : OmegaT) : GermT)⁻¹ = ((0 : OmegaT) : GermT)
      rw [ZeroMemClass.coe_zero, ← Germ.coe_zero, ← Germ.coe_inv]
      congr 1; funext x; simp
    nnqsmul := _
    qsmul := _ }

theorem coe_le_coe {x y : OmegaT} : x ≤ y ↔ (x : GermT) ≤ y := Iff.rfl

/-- Comparison of two numbers of `Ω(t)` by their representing functions. -/
theorem le_iff_eventually {x y : OmegaT} {f g : ℝ → ℝ} (hf : (f : GermT) = x)
    (hg : (g : GermT) = y) : x ≤ y ↔ ∀ᶠ t in atTop, f t ≤ g t := by
  rw [coe_le_coe, ← hf, ← hg, Germ.coe_le]; rfl

theorem le_total' (x y : OmegaT) : x ≤ y ∨ y ≤ x := by
  obtain ⟨f, hf, hfx⟩ := x.2
  obtain ⟨g, hg, hgy⟩ := y.2
  rw [le_iff_eventually hfx hgy, le_iff_eventually hgy hfx]
  rcases (hg.sub hf).trichotomy with h | h | h
  · left; filter_upwards [h] with t ht; simp at ht; linarith
  · left; filter_upwards [h] with t ht; simp at ht; linarith
  · right; filter_upwards [h] with t ht; simp at ht; linarith

noncomputable instance instLinearOrder : LinearOrder OmegaT :=
  { (inferInstance : PartialOrder OmegaT) with
    le_total := le_total'
    toDecidableLE := Classical.decRel _ }

/-- **Hilbert's order on `Ω(t)`**: `x < y` iff `y - x` is positive for all sufficiently large `t`. -/
theorem lt_iff_eventually {x y : OmegaT} {f g : ℝ → ℝ} (hf : (f : GermT) = x)
    (hg : (g : GermT) = y) : x < y ↔ ∀ᶠ t in atTop, f t < g t := by
  rw [lt_iff_le_not_ge, le_iff_eventually hf hg, le_iff_eventually hg hf]
  obtain ⟨f', hf', hf'x⟩ := x.2
  obtain ⟨g', hg', hg'y⟩ := y.2
  have hff : f =ᶠ[atTop] f' := Germ.coe_eq.1 (hf.trans hf'x.symm)
  have hgg : g =ᶠ[atTop] g' := Germ.coe_eq.1 (hg.trans hg'y.symm)
  constructor
  · rintro ⟨h1, h2⟩
    rcases (hg'.sub hf').trichotomy with h | h | h
    · exfalso; apply h2
      filter_upwards [h, hff, hgg] with t ht h3 h4; simp at ht; rw [h3, h4]; linarith
    · filter_upwards [h, hff, hgg] with t ht h3 h4; simp at ht; rw [h3, h4]; linarith
    · exfalso
      obtain ⟨t, ht, h1t, h3, h4⟩ := (h.and (h1.and (hff.and hgg))).exists
      simp at ht; rw [h3, h4] at h1t; linarith
  · intro h
    refine ⟨h.mono fun _ ht => ht.le, fun h' => ?_⟩
    obtain ⟨t, h1, h2⟩ := (h.and h').exists
    linarith

theorem pos_iff_eventually {x : OmegaT} {f : ℝ → ℝ} (hf : (f : GermT) = x) :
    0 < x ↔ ∀ᶠ t in atTop, 0 < f t :=
  lt_iff_eventually (f := 0) (by rw [Germ.coe_zero]; rfl) hf

noncomputable instance instIsStrictOrderedRing : IsStrictOrderedRing OmegaT := by
  have hadd : IsOrderedAddMonoid OmegaT :=
    { add_le_add_left := fun a b hab c => by
        rw [coe_le_coe] at hab ⊢
        simpa using add_le_add_right hab (c : GermT)
      add_le_add_right := fun a b hab c => by
        rw [coe_le_coe] at hab ⊢
        simpa using add_le_add_left hab (c : GermT) }
  have hzo : ZeroLEOneClass OmegaT := ⟨by
    rw [coe_le_coe, ZeroMemClass.coe_zero, OneMemClass.coe_one, ← Germ.coe_zero, ← Germ.coe_one,
      Germ.coe_le]
    exact Eventually.of_forall fun _ => zero_le_one⟩
  exact IsStrictOrderedRing.of_mul_pos fun a b ha hb => by
    obtain ⟨f, hf, hfa⟩ := a.2
    obtain ⟨g, hg, hgb⟩ := b.2
    rw [pos_iff_eventually hfa] at ha
    rw [pos_iff_eventually hgb] at hb
    rw [pos_iff_eventually (f := f * g) (by rw [Germ.coe_mul, hfa, hgb]; rfl)]
    filter_upwards [ha, hb] with t h1 h2
    exact mul_pos h1 h2

/-- `Ω(t)` is Pythagorean: closed under `ω ↦ √(1 + ω²)`. -/
instance instIsPythagorean : IsPythagorean OmegaT := by
  constructor
  intro x
  obtain ⟨f, hf, hfx⟩ := x.2
  refine ⟨⟨((fun t => Real.sqrt (1 + f t ^ 2) : ℝ → ℝ) : GermT), _, hf.sqrt, rfl⟩, ?_, ?_⟩
  · rw [le_iff_eventually (f := 0) (by rw [Germ.coe_zero]; rfl) rfl]
    exact Eventually.of_forall fun _ => Real.sqrt_nonneg _
  · apply Subtype.ext
    show ((fun t => Real.sqrt (1 + f t ^ 2) : ℝ → ℝ) : GermT) ^ 2 =
      (1 : GermT) + (x : GermT) ^ 2
    rw [← hfx, ← Germ.coe_pow, ← Germ.coe_pow, ← Germ.coe_one, ← Germ.coe_add, Germ.coe_eq]
    exact Eventually.of_forall fun t => by
      simp only [Pi.pow_apply, Pi.add_apply, Pi.one_apply]
      exact Real.sq_sqrt (by positivity)

/-- The number `t` of `Ω(t)`. -/
def t : OmegaT := ⟨((id : ℝ → ℝ) : GermT), id, IsGen.t, rfl⟩

/-- **`n < t` for every natural number `n`** (§ 12). -/
theorem natCast_lt_t (n : ℕ) : (n : OmegaT) < t := by
  have hn : (((fun _ => (n : ℝ)) : ℝ → ℝ) : GermT) = ((n : OmegaT) : GermT) := by
    rw [Germ.natCast_def]; rfl
  rw [lt_iff_eventually hn rfl]
  filter_upwards [eventually_gt_atTop (n : ℝ)] with s hs
  exact hs

/-- **`Ω(t)` is not archimedean.** -/
theorem not_archimedean : ¬Archimedean OmegaT := by
  intro h
  obtain ⟨n, hn⟩ := (archimedean_iff_nat_lt.1 h) t
  exact lt_asymm hn (natCast_lt_t n)

end OmegaT

end HilbertFoundations
