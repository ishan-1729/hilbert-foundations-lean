import GaloisOeuvres.Basic

/-!
# The groups `AGL(1, F) ≀ C₂`

Auxiliary file for the unit `nombres.reciproque` of *Sur la théorie des nombres*
(`GaloisOeuvres/TheorieNombres.lean`).

For a field `F`, `couronne F` is the group of the substitutions
`(k₁, k₂) ↦ (a k₁ + n₁, b k₂ + n₂)` and `(k₁, k₂) ↦ (a k₂ + n₁, b k₁ + n₂)` (`a, b ≠ 0`) of the
points of `F × F`. It is solvable (`couronne_soluble`); it is primitive as soon as `F` has an
element other than `0` and `1` (`couronne_primitif`); and, `F` having `q` elements, its order is
divisible by `2 (q - 1)²` (`two_mul_dvd_card`). For `F = ℤ/p` this is the group
`EquationsPrimitives.couronne p`, and the proofs are the same, written for an arbitrary field.
`arith` is the arithmetic fact that makes these groups, for `q = ℓ²`, too large for Galois's
group of substitutions of `ℓ⁴` indices.
-/

namespace GaloisOeuvres.TheorieNombres.Couronne

open MulAction

variable {F : Type*} [Field F]

/-- `k ↦ (a k₁ + n₁, b k₂ + n₂)`. -/
def EstDroite (a b : F) (σ : Equiv.Perm (F × F)) : Prop :=
  ∃ n₁ n₂ : F, ∀ k, σ k = (a * k.1 + n₁, b * k.2 + n₂)

/-- `k ↦ (a k₂ + n₁, b k₁ + n₂)`. -/
def EstCroisee (a b : F) (σ : Equiv.Perm (F × F)) : Prop :=
  ∃ n₁ n₂ : F, ∀ k, σ k = (a * k.2 + n₁, b * k.1 + n₂)

section Lemmes

variable {a b a' b' : F} {σ τ : Equiv.Perm (F × F)}

theorem dd (h : EstDroite a b σ) (h' : EstDroite a' b' τ) :
    EstDroite (a * a') (b * b') (σ * τ) := by
  obtain ⟨n₁, n₂, h⟩ := h; obtain ⟨n₁', n₂', h'⟩ := h'
  exact ⟨a * n₁' + n₁, b * n₂' + n₂, fun k => by
    rw [Equiv.Perm.mul_apply, h', h]; ext <;> simp <;> ring⟩

theorem dc (h : EstDroite a b σ) (h' : EstCroisee a' b' τ) :
    EstCroisee (a * a') (b * b') (σ * τ) := by
  obtain ⟨n₁, n₂, h⟩ := h; obtain ⟨n₁', n₂', h'⟩ := h'
  exact ⟨a * n₁' + n₁, b * n₂' + n₂, fun k => by
    rw [Equiv.Perm.mul_apply, h', h]; ext <;> simp <;> ring⟩

theorem cd (h : EstCroisee a b σ) (h' : EstDroite a' b' τ) :
    EstCroisee (a * b') (b * a') (σ * τ) := by
  obtain ⟨n₁, n₂, h⟩ := h; obtain ⟨n₁', n₂', h'⟩ := h'
  exact ⟨a * n₂' + n₁, b * n₁' + n₂, fun k => by
    rw [Equiv.Perm.mul_apply, h', h]; ext <;> simp <;> ring⟩

theorem cc (h : EstCroisee a b σ) (h' : EstCroisee a' b' τ) :
    EstDroite (a * b') (b * a') (σ * τ) := by
  obtain ⟨n₁, n₂, h⟩ := h; obtain ⟨n₁', n₂', h'⟩ := h'
  exact ⟨a * n₂' + n₁, b * n₁' + n₂, fun k => by
    rw [Equiv.Perm.mul_apply, h', h]; ext <;> simp <;> ring⟩

theorem d_inv (ha : a ≠ 0) (hb : b ≠ 0) (h : EstDroite a b σ) : EstDroite a⁻¹ b⁻¹ σ⁻¹ := by
  obtain ⟨n₁, n₂, h⟩ := h
  refine ⟨-(a⁻¹ * n₁), -(b⁻¹ * n₂), fun k => ?_⟩
  rw [Equiv.Perm.inv_eq_iff_eq, h]
  ext <;> simp <;> field_simp <;> ring

theorem c_inv (ha : a ≠ 0) (hb : b ≠ 0) (h : EstCroisee a b σ) : EstCroisee b⁻¹ a⁻¹ σ⁻¹ := by
  obtain ⟨n₁, n₂, h⟩ := h
  refine ⟨-(b⁻¹ * n₂), -(a⁻¹ * n₁), fun k => ?_⟩
  rw [Equiv.Perm.inv_eq_iff_eq, h]
  ext <;> simp <;> field_simp <;> ring

theorem not_d_c (h : EstDroite a b σ) (h' : EstCroisee a' b' σ) (ha : a ≠ 0) : False := by
  obtain ⟨n₁, n₂, h⟩ := h; obtain ⟨n₁', n₂', h'⟩ := h'
  have e1 := h (1, 0); have e0 := h (0, 0); have f1 := h' (1, 0); have f0 := h' (0, 0)
  rw [e1] at f1; rw [e0] at f0
  simp only [Prod.mk.injEq, mul_one, mul_zero, zero_add] at f1 f0
  exact ha (by linear_combination f1.1 - f0.1)

end Lemmes

/-- An explicit permutation `k ↦ (a k₁ + n₁, b k₂ + n₂)`. -/
def droite (a b n₁ n₂ : F) (ha : a ≠ 0) (hb : b ≠ 0) : Equiv.Perm (F × F) where
  toFun k := (a * k.1 + n₁, b * k.2 + n₂)
  invFun k := (a⁻¹ * (k.1 - n₁), b⁻¹ * (k.2 - n₂))
  left_inv k := by ext <;> simp <;> field_simp
  right_inv k := by ext <;> simp <;> field_simp <;> ring

/-- The exchange of the two indices. -/
def echange : Equiv.Perm (F × F) := Equiv.prodComm _ _

theorem droite_est (a b n₁ n₂ : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    EstDroite a b (droite a b n₁ n₂ ha hb) := ⟨n₁, n₂, fun _ => rfl⟩

theorem echange_est : EstCroisee (1 : F) 1 echange :=
  ⟨0, 0, fun k => by simp [echange, Prod.swap]⟩

variable (F) in
/-- The group `AGL(1, F) ≀ C₂`. -/
def couronne : Subgroup (Equiv.Perm (F × F)) where
  carrier := {σ | ∃ a b : F, a ≠ 0 ∧ b ≠ 0 ∧ (EstDroite a b σ ∨ EstCroisee a b σ)}
  one_mem' := ⟨1, 1, one_ne_zero, one_ne_zero, Or.inl ⟨0, 0, fun k => by simp⟩⟩
  mul_mem' := by
    rintro σ τ ⟨a, b, ha, hb, hσ | hσ⟩ ⟨a', b', ha', hb', hτ | hτ⟩
    · exact ⟨_, _, mul_ne_zero ha ha', mul_ne_zero hb hb', Or.inl (dd hσ hτ)⟩
    · exact ⟨_, _, mul_ne_zero ha ha', mul_ne_zero hb hb', Or.inr (dc hσ hτ)⟩
    · exact ⟨_, _, mul_ne_zero ha hb', mul_ne_zero hb ha', Or.inr (cd hσ hτ)⟩
    · exact ⟨_, _, mul_ne_zero ha hb', mul_ne_zero hb ha', Or.inl (cc hσ hτ)⟩
  inv_mem' := by
    rintro σ ⟨a, b, ha, hb, hσ | hσ⟩
    · exact ⟨_, _, inv_ne_zero ha, inv_ne_zero hb, Or.inl (d_inv ha hb hσ)⟩
    · exact ⟨_, _, inv_ne_zero hb, inv_ne_zero ha, Or.inr (c_inv ha hb hσ)⟩

variable (F) in
/-- Its subgroup `AGL(1, F) × AGL(1, F)`. -/
def produit : Subgroup (Equiv.Perm (F × F)) where
  carrier := {σ | ∃ a b : F, a ≠ 0 ∧ b ≠ 0 ∧ EstDroite a b σ}
  one_mem' := ⟨1, 1, one_ne_zero, one_ne_zero, ⟨0, 0, fun k => by simp⟩⟩
  mul_mem' := by
    rintro σ τ ⟨a, b, ha, hb, hσ⟩ ⟨a', b', ha', hb', hτ⟩
    exact ⟨_, _, mul_ne_zero ha ha', mul_ne_zero hb hb', dd hσ hτ⟩
  inv_mem' := by
    rintro σ ⟨a, b, ha, hb, hσ⟩
    exact ⟨_, _, inv_ne_zero ha, inv_ne_zero hb, d_inv ha hb hσ⟩

theorem produit_le_couronne : produit F ≤ couronne F := fun _ ⟨a, b, ha, hb, h⟩ =>
  ⟨a, b, ha, hb, Or.inl h⟩

theorem index_produit : ((produit F).subgroupOf (couronne F)).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨echange, 1, 1, one_ne_zero, one_ne_zero, Or.inr echange_est⟩, ?_⟩
  rintro ⟨σ, a, b, ha, hb, hσ | hσ⟩
  · simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    exact Or.inr ⟨⟨a, b, ha, hb, hσ⟩, fun ⟨a', b', ha', hb', h'⟩ =>
      not_d_c h' (dc hσ (echange_est (F := F))) ha'⟩
  · simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    exact Or.inl ⟨⟨_, _, mul_ne_zero ha one_ne_zero, mul_ne_zero hb one_ne_zero,
      cc hσ (echange_est (F := F))⟩, fun ⟨a', b', ha', hb', h'⟩ => not_d_c h' hσ ha'⟩

omit [Field F] in
theorem smul_mem_of_block {G : Subgroup (Equiv.Perm (F × F))}
    {B : Set (F × F)} (hB : IsBlock G B) {σ : Equiv.Perm (F × F)} (hσ : σ ∈ G)
    {v : F × F} (hv : v ∈ B) (hσv : σ v ∈ B) {w : F × F} (hw : w ∈ B) :
    σ w ∈ B := by
  have h := hB.smul_eq_of_mem (g := ⟨σ, hσ⟩) hv hσv
  rw [← h]
  exact ⟨w, hw, rfl⟩

theorem ligne_sub {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) {B : Set (F × F)}
    (hB : IsBlock (couronne F) B) (h0 : (0, 0) ∈ B)
    {v : F × F} (hv : v ∈ B) (hv1 : v.1 ≠ 0) (x : F) : (x, 0) ∈ B := by
  have hm1 : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hdiag : ∀ (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) w, w ∈ B → (a * w.1, b * w.2) ∈ B :=
    fun a b ha hb w hw => by
      have := smul_mem_of_block hB
        (produit_le_couronne ⟨a, b, ha, hb, droite_est a b 0 0 ha hb⟩) h0
        (by simpa [droite] using h0) hw
      simpa [droite] using this
  have htrans : ∀ u w, u ∈ B → w ∈ B → (w.1 + u.1, w.2 + u.2) ∈ B := fun u w hu hw => by
    have := smul_mem_of_block hB (produit_le_couronne ⟨1, 1, one_ne_zero, one_ne_zero,
      droite_est 1 1 u.1 u.2 one_ne_zero one_ne_zero⟩) h0 (by simpa [droite] using hu) hw
    simpa [droite] using this
  have hv' : ((c - 1) * v.1, 0) ∈ B := by
    have h1 := hdiag c 1 hc0 one_ne_zero v hv
    have h3 := hdiag (-1) (-1) hm1 hm1 v hv
    have := htrans _ _ h3 h1
    convert this using 2 <;> ring
  by_cases hx : x = 0
  · rw [hx]; exact h0
  · have hc : (c - 1) * v.1 ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hc1) hv1
    have := hdiag (x / ((c - 1) * v.1)) 1 (div_ne_zero hx hc) one_ne_zero _ hv'
    convert this using 2
    · exact (div_mul_cancel₀ x hc).symm
    · simp

/-- **`AGL(1, F) ≀ C₂` is primitive** when `F` has at least three elements. -/
theorem couronne_primitif (h3 : ∃ c : F, c ≠ 0 ∧ c ≠ 1) :
    IsPreprimitive (couronne F) (F × F) := by
  obtain ⟨c, hc0, hc1⟩ := h3
  have htr : IsPretransitive (couronne F) (F × F) := by
    refine ⟨fun x y => ⟨⟨droite 1 1 (y.1 - x.1) (y.2 - x.2) one_ne_zero one_ne_zero,
      1, 1, one_ne_zero, one_ne_zero, Or.inl (droite_est _ _ _ _ _ _)⟩, ?_⟩⟩
    change droite 1 1 (y.1 - x.1) (y.2 - x.2) one_ne_zero one_ne_zero x = y
    ext <;> simp [droite]
  apply IsPreprimitive.of_isTrivialBlock_base (0, 0)
  intro B h0 hB
  by_cases hsub : B ⊆ {(0, 0)}
  · left; exact Set.subsingleton_singleton.anti hsub
  · right
    obtain ⟨v, hv, hv0⟩ := Set.not_subset.mp hsub
    have hsw : ∀ w, w ∈ B → (w.2, w.1) ∈ B := fun w hw => by
      have := smul_mem_of_block hB (σ := echange)
        ⟨1, 1, one_ne_zero, one_ne_zero, Or.inr echange_est⟩ h0 (by simpa [echange] using h0) hw
      simpa [echange, Prod.swap] using this
    have hrow : ∀ x : F, (x, 0) ∈ B := by
      by_cases hv1 : v.1 = 0
      · have hv2 : v.2 ≠ 0 := fun h => hv0 (Prod.ext hv1 h)
        exact ligne_sub hc0 hc1 hB h0 (hsw v hv) hv2
      · exact ligne_sub hc0 hc1 hB h0 hv hv1
    apply Set.eq_univ_of_forall
    intro w
    have h1 := hrow w.1
    have h2 := hsw _ (hrow w.2)
    have := smul_mem_of_block hB (σ := droite 1 1 w.1 0 one_ne_zero one_ne_zero)
      (produit_le_couronne ⟨1, 1, one_ne_zero, one_ne_zero, droite_est _ _ _ _ _ _⟩) h0
      (by simpa [droite] using h1) h2
    simpa [droite] using this

/-- **`AGL(1, F) ≀ C₂` is solvable.** -/
theorem couronne_soluble : Group.IsSolvable (couronne F) := by
  set W := couronne F
  let H : Subgroup W := (produit F).subgroupOf W
  let T : Subgroup W :=
    { carrier := {σ | EstDroite 1 1 (σ : Equiv.Perm (F × F))}
      one_mem' := ⟨0, 0, fun k => by simp⟩
      mul_mem' := fun ha hb => by simpa using dd ha hb
      inv_mem' := fun ha => by simpa using d_inv one_ne_zero one_ne_zero ha }
  have h1 : Subgroup.derivedSeries W 1 ≤ H := by
    rw [Subgroup.derivedSeries_one, commutator_def, Subgroup.commutator_le]
    rintro ⟨g, a, b, ha, hb, hg | hg⟩ - ⟨h, a', b', ha', hb', hh | hh⟩ -
    · exact Subgroup.mem_subgroupOf.mpr ⟨_, _, by simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]; tauto, by simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]; tauto,
        dd (dd (dd hg hh) (d_inv ha hb hg)) (d_inv ha' hb' hh)⟩
    · exact Subgroup.mem_subgroupOf.mpr ⟨_, _, by simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]; tauto, by simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]; tauto,
        cc (cd (dc hg hh) (d_inv ha hb hg)) (c_inv ha' hb' hh)⟩
    · exact Subgroup.mem_subgroupOf.mpr ⟨_, _, by simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]; tauto, by simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]; tauto,
        dd (cc (cd hg hh) (c_inv ha hb hg)) (d_inv ha' hb' hh)⟩
    · exact Subgroup.mem_subgroupOf.mpr ⟨_, _, by simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]; tauto, by simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]; tauto,
        cc (dc (cc hg hh) (c_inv ha hb hg)) (c_inv ha' hb' hh)⟩
  have h2 : Subgroup.derivedSeries W 2 ≤ T := by
    rw [Subgroup.derivedSeries_succ]
    refine (Subgroup.commutator_mono h1 h1).trans ?_
    rw [Subgroup.commutator_le]
    intro g hg h hh
    obtain ⟨a, b, ha, hb, hg⟩ := Subgroup.mem_subgroupOf.mp hg
    obtain ⟨a', b', ha', hb', hh⟩ := Subgroup.mem_subgroupOf.mp hh
    have := dd (dd (dd hg hh) (d_inv ha hb hg)) (d_inv ha' hb' hh)
    have e1 : a * a' * a⁻¹ * a'⁻¹ = 1 := by field_simp
    have e2 : b * b' * b⁻¹ * b'⁻¹ = 1 := by field_simp
    rw [e1, e2] at this
    exact this
  have h3 : Subgroup.derivedSeries W 3 = ⊥ := by
    rw [eq_bot_iff, Subgroup.derivedSeries_succ]
    refine (Subgroup.commutator_mono h2 h2).trans ?_
    rw [Subgroup.commutator_le]
    rintro g ⟨n₁, n₂, hg⟩ h ⟨n₁', n₂', hh⟩
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext; ext k
    · simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, hg, hh]; ring
    · simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, hg, hh]; ring
  exact ⟨⟨3, h3⟩⟩

/-- The diagonal substitutions `k ↦ (a k₁, b k₂)`. -/
def diag : Fˣ × Fˣ →* Equiv.Perm (F × F) where
  toFun u := droite (u.1 : F) (u.2 : F) 0 0 u.1.ne_zero u.2.ne_zero
  map_one' := by ext k <;> simp [droite]
  map_mul' u v := by ext k <;> simp [droite, mul_assoc]

theorem diag_injective : Function.Injective (diag (F := F)) := by
  intro u v h
  have h1 : diag u (1, 1) = diag v (1, 1) := by rw [h]
  have h2 : ((u.1 : F) * 1 + 0, (u.2 : F) * 1 + 0) = ((v.1 : F) * 1 + 0, (v.2 : F) * 1 + 0) := h1
  simp only [mul_one, add_zero, Prod.mk.injEq] at h2
  exact Prod.ext (Units.ext h2.1) (Units.ext h2.2)

theorem diag_mem (u : Fˣ × Fˣ) : diag u ∈ produit F :=
  ⟨_, _, u.1.ne_zero, u.2.ne_zero, droite_est _ _ _ _ u.1.ne_zero u.2.ne_zero⟩

/-- The order of `AGL(1, F) ≀ C₂` is divisible by `2 (q - 1)²`, `q` the number of elements of `F`. -/
theorem two_mul_dvd_card [Finite F] : 2 * (Nat.card F - 1) ^ 2 ∣ Nat.card (couronne F) := by
  have h1 : (Nat.card F - 1) ^ 2 ∣ Nat.card (produit F) := by
    have := Subgroup.card_dvd_of_injective ((diag (F := F)).codRestrict (produit F) diag_mem)
      (fun u v h => diag_injective (congrArg Subtype.val h))
    rwa [Nat.card_prod, Nat.card_units, ← pow_two] at this
  have h2 : Nat.card ((produit F).subgroupOf (couronne F)) = Nat.card (produit F) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe produit_le_couronne).toEquiv
  have h3 := ((produit F).subgroupOf (couronne F)).index_mul_card
  rw [index_produit, h2] at h3
  rw [← h3]
  exact Nat.mul_dvd_mul_left 2 h1

theorem exists_ne_zero_ne_one [Finite F] (h : 2 < Nat.card F) : ∃ c : F, c ≠ 0 ∧ c ≠ 1 := by
  have h1 : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨u, hu⟩ := exists_ne (1 : Fˣ)
  exact ⟨u, u.ne_zero, fun h => hu (Units.ext h)⟩

theorem arith (ℓ : ℕ) (hℓ : 2 ≤ ℓ) : ¬ (2 * (ℓ ^ 2 - 1) ^ 2 ∣ ℓ ^ 4 * (ℓ ^ 4 - 1) * 4) := by
  have h4le : 4 ≤ ℓ ^ 2 :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left hℓ 2
  obtain ⟨m, hm⟩ : ∃ m, ℓ ^ 2 = m + 1 := ⟨ℓ ^ 2 - 1, by omega⟩
  have hm3 : 3 ≤ m := by omega
  have e1 : ℓ ^ 4 = (m + 1) ^ 2 := by rw [← hm]; ring
  have e2 : ℓ ^ 4 - 1 = m * (m + 2) := by
    rw [e1]; apply Nat.sub_eq_of_eq_add; ring
  rw [e2, e1, hm, Nat.add_sub_cancel]
  intro h
  have h' : 2 * m * m ∣ 2 * m * (2 * (m + 1) ^ 2 * (m + 2)) := by
    convert h using 1 <;> ring
  have h2 : m ∣ 2 * (m + 1) ^ 2 * (m + 2) :=
    (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2 * m)).mp h'
  have h4 : m ∣ 4 := by
    have h3 : m ∣ m * (2 * m ^ 2 + 8 * m + 10) + 4 := by convert h2 using 1; ring
    exact (Nat.dvd_add_right (dvd_mul_right m _)).mp h3
  have h5 : m ≤ 4 := Nat.le_of_dvd (by norm_num) h4
  interval_cases m
  · omega
  · rcases hℓ.eq_or_lt with h2 | h2
    · rw [← h2] at hm; norm_num at hm
    · have h9 : 9 ≤ ℓ ^ 2 :=
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left h2 2
      omega

end GaloisOeuvres.TheorieNombres.Couronne
