import HilbertFoundations.OrderPolygonAux2

/-!
# Helper module for `OrderPolygon.lean` (Theorem 6), part 3: joining points off the polygon

This module contains no unit of Hilbert's text.

* `Step v X Y`: `X` and `Y` are off the polygon and the segment `XY` does not meet it;
  `Conn v X Y`: `X` and `Y` are joined by finitely many such segments (the reflexive transitive
  closure). `Conn.exists_brokenLine`: a broken line in Hilbert's sense; `Conn.par_eq`: the parity
  is constant.
* `Sees v X Z`: `X` is off the polygon and no point between `X` and `Z` is on it.
* `first_hit`: every point off the polygon sees a point of the polygon (the first point of the
  polygon on a segment from `X` to a vertex).
* `sweep` (the main tool): in a triangle `A B W₀`, if no side of the polygon that meets the two
  sides `AB`, `AW₀` issuing from `A` enters the triangle, then the points `W` of `AW₀` close to `A`
  are joined to `B` by segments free of points of the polygon.
* `local_conn`: two points seeing a point `Z` of the polygon from the same side of a line `k`
  through `Z`, the sides through `Z` having no point on that side of `k`, are joined.
* `good_side`: if all points seeing a point `B` of a closed side have a property `C` invariant
  under `Conn`, so have all points seeing a point within that side.
-/

namespace HilbertFoundations

namespace PolyJordan

universe u v

variable {P : Type u} {L : Type v}

/-- `X` and `Y` are off the polygon, and so are all points between them. -/
def Step [HasBetween P] {n : ℕ} (v : Fin (n + 1) → P) (X Y : P) : Prop :=
  ¬OnPoly v X ∧ ¬OnPoly v Y ∧ ∀ p, Between X p Y → ¬OnPoly v p

/-- `X` and `Y` are joined by a chain of segments that do not meet the polygon. -/
def Conn [HasBetween P] {n : ℕ} (v : Fin (n + 1) → P) (X Y : P) : Prop :=
  Relation.ReflTransGen (Step v) X Y

/-- `X` is off the polygon and no point between `X` and `Z` is on the polygon. -/
def Sees [HasBetween P] {n : ℕ} (v : Fin (n + 1) → P) (X Z : P) : Prop :=
  ¬OnPoly v X ∧ ∀ p, Between X p Z → ¬OnPoly v p

theorem Conn.trans [HasBetween P] {n : ℕ} {v : Fin (n + 1) → P} {X Y Z : P} (h1 : Conn v X Y)
    (h2 : Conn v Y Z) : Conn v X Z :=
  Relation.ReflTransGen.trans h1 h2

theorem Conn.of_step [HasBetween P] {n : ℕ} {v : Fin (n + 1) → P} {X Y : P} (h : Step v X Y) :
    Conn v X Y :=
  Relation.ReflTransGen.single h

theorem fin_add_two_ne {n : ℕ} (hn : 2 ≤ n) (i : Fin (n + 1)) : i + 1 + 1 ≠ i := by
  intro h
  have h1 := congrArg Fin.val h
  rw [Fin.val_add_one] at h1
  split_ifs at h1 with h'
  · have h2 := congrArg Fin.val h'
    rw [Fin.val_add_one, Fin.val_last] at h2
    split_ifs at h2 with h''
    · omega
    · omega
  · rw [Fin.val_add_one] at h1
    split_ifs at h1 with h''
    · rw [h'', Fin.val_last] at h1; omega
    · omega

variable [HasLines P L] [HasBetween P] [hO : PlaneOrder P L]
include hO

/-! ### Points of a line -/

/-- A point `Z` cannot lie between each two of three points. -/
theorem not_three_between {X Z A B : P} (h1 : Between X Z A) (h2 : Between X Z B)
    (h3 : Between A Z B) : False := by
  obtain ⟨a, hX, hZ, hA⟩ := collinear_of_between (Line := L) h1
  have hB : B ∈ a := OrderCore.mem_of_between' h2 hX hZ
  obtain ⟨f, -, hf⟩ := line_pos a ![X, A, B, Z]
    (by intro i; fin_cases i <;> first | exact hX | exact hA | exact hB | exact hZ)
  have e1 := (hf 0 3 1).1 h1
  have e2 := (hf 0 3 2).1 h2
  have e3 := (hf 1 3 2).1 h3
  omega

/-- Two distinct points beyond `V` (seen from `W`): one lies between `V` and the other. -/
theorem same_ray_cases {W V A B : P} (h1 : Between W V A) (h2 : Between W V B) (hAB : A ≠ B) :
    Between V A B ∨ Between V B A := by
  obtain ⟨a, hW, hV, hA⟩ := collinear_of_between (Line := L) h1
  have hB : B ∈ a := OrderCore.mem_of_between' h2 hW hV
  obtain ⟨f, he, hf⟩ := line_pos a ![W, V, A, B]
    (by intro i; fin_cases i <;> first | exact hW | exact hV | exact hA | exact hB)
  have e1 := (hf 0 1 2).1 h1
  have e2 := (hf 0 1 3).1 h2
  have e3 : f 2 ≠ f 3 := fun e => hAB ((he 2 3).1 e)
  by_cases h' : (f 1 < f 2 ∧ f 2 < f 3) ∨ (f 3 < f 2 ∧ f 2 < f 1)
  · exact Or.inl ((hf 1 2 3).2 h')
  · exact Or.inr ((hf 1 3 2).2 (by omega))

/-- A point between a point within the segment `UV` and a point of the closed segment `UV` lies
within `UV`. -/
theorem side_between {U V Z B r : P} (hZ : Between U Z V) (hB : CSeg U V B)
    (hr : Between Z r B) : Between U r V := by
  obtain ⟨a, hUa, hZa, hVa⟩ := collinear_of_between (Line := L) hZ
  have hBa : B ∈ a := hB.mem_line hUa hVa
  have hra : r ∈ a := OrderCore.mem_of_between hr hZa hBa
  obtain ⟨f, he, hf⟩ := line_pos a ![U, V, Z, B, r]
    (by intro i; fin_cases i <;>
      first | exact hUa | exact hVa | exact hZa | exact hBa | exact hra)
  have e1 := (hf 0 2 1).1 hZ
  have e2 := (hf 2 4 3).1 hr
  refine (hf 0 4 1).2 ?_
  rcases hB with e | e | e
  · have := (he 3 0).2 e; omega
  · have := (he 3 1).2 e; omega
  · have := (hf 0 3 1).1 e; omega

/-- Two distinct points of a half-open segment `(X, T]`. -/
theorem halfopen_cases {X T Z Z' : P} (hZ : Z = T ∨ Between X Z T)
    (hZ' : Z' = T ∨ Between X Z' T) (hne : Z ≠ Z') : Between X Z Z' ∨ Between X Z' Z := by
  rcases hZ with hZ | hZ <;> rcases hZ' with hZ' | hZ'
  · exact absurd (hZ.trans hZ'.symm) hne
  · rw [hZ]; exact Or.inr hZ'
  · rw [hZ']; exact Or.inl hZ
  · exact between_cases hZ hZ' hne

theorem halfopen_trans {X T Z p : P} (hZ : Z = T ∨ Between X Z T) (hp : Between X p Z) :
    Between X p T := by
  rcases hZ with hZ | hZ
  · rw [← hZ]; exact hp
  · exact (OrderLin.trans₂ hp hZ).1

/-! ### The first point of a closed segment on a half-open segment -/

theorem first_on_cseg_aux {a : L} {X T U V Z : P} (hXa : X ∈ a) (hTa : T ∈ a) (hUa : U ∈ a)
    (hVa : V ∈ a) (hX : ¬CSeg U V X) (hZ : Z = T ∨ Between X Z T) (hZc : CSeg U V Z)
    (hc : U = V ∨ Between X U V) :
    (U = T ∨ Between X U T) ∧ ∀ p, Between X p U → ¬CSeg U V p := by
  have hZa : Z ∈ a := hZc.mem_line hUa hVa
  constructor
  · obtain ⟨f, he, hf⟩ := line_pos a ![X, T, U, V, Z]
      (by intro i; fin_cases i <;>
        first | exact hXa | exact hTa | exact hUa | exact hVa | exact hZa)
    have n1 : f 0 ≠ f 2 := fun e => hX (Or.inl ((he 0 2).1 e))
    have n2 : f 0 ≠ f 3 := fun e => hX (Or.inr (Or.inl ((he 0 3).1 e)))
    have c1 : f 2 = f 3 ∨ (f 0 < f 2 ∧ f 2 < f 3) ∨ (f 3 < f 2 ∧ f 2 < f 0) := by
      rcases hc with e | e
      · exact Or.inl ((he 2 3).2 e)
      · exact Or.inr ((hf 0 2 3).1 e)
    have c2 : f 4 = f 1 ∨ (f 0 < f 4 ∧ f 4 < f 1) ∨ (f 1 < f 4 ∧ f 4 < f 0) := by
      rcases hZ with e | e
      · exact Or.inl ((he 4 1).2 e)
      · exact Or.inr ((hf 0 4 1).1 e)
    have c3 : f 4 = f 2 ∨ f 4 = f 3 ∨ (f 2 < f 4 ∧ f 4 < f 3) ∨ (f 3 < f 4 ∧ f 4 < f 2) := by
      rcases hZc with e | e | e
      · exact Or.inl ((he 4 2).2 e)
      · exact Or.inr (Or.inl ((he 4 3).2 e))
      · exact Or.inr (Or.inr ((hf 2 4 3).1 e))
    by_cases h : f 2 = f 1
    · exact Or.inl ((he 2 1).1 h)
    · exact Or.inr ((hf 0 2 1).2 (by omega))
  · intro p hp hpc
    have hpa : p ∈ a := OrderCore.mem_of_between hp hXa hUa
    obtain ⟨f, he, hf⟩ := line_pos a ![X, U, V, p]
      (by intro i; fin_cases i <;> first | exact hXa | exact hUa | exact hVa | exact hpa)
    have e0 := (hf 0 3 1).1 hp
    have c1 : f 1 = f 2 ∨ (f 0 < f 1 ∧ f 1 < f 2) ∨ (f 2 < f 1 ∧ f 1 < f 0) := by
      rcases hc with e | e
      · exact Or.inl ((he 1 2).2 e)
      · exact Or.inr ((hf 0 1 2).1 e)
    rcases hpc with e | e | e
    · have := (he 3 1).2 e; omega
    · have := (he 3 2).2 e; omega
    · have := (hf 1 3 2).1 e; omega

/-- **The first point of a closed segment `UV` on a half-open segment `(X, T]`**, if `UV` has a
point on it. -/
theorem first_on_cseg {X T U V : P} (hXT : X ≠ T) (hX : ¬CSeg U V X) :
    (∀ p, (p = T ∨ Between X p T) → ¬CSeg U V p) ∨
      ∃ Z, (Z = T ∨ Between X Z T) ∧ CSeg U V Z ∧ ∀ p, Between X p Z → ¬CSeg U V p := by
  by_cases hex : ∃ Z, (Z = T ∨ Between X Z T) ∧ CSeg U V Z
  swap
  · exact Or.inl fun p hp hc => hex ⟨p, hp, hc⟩
  right
  obtain ⟨Z, hZ, hZc⟩ := hex
  obtain ⟨a, hXa, hTa⟩ := exists_line (Line := L) hXT
  have hZa : Z ∈ a := by
    rcases hZ with h | h
    · rw [h]; exact hTa
    · exact OrderCore.mem_of_between h hXa hTa
  by_cases hUV : U ∈ a ∧ V ∈ a
  · obtain ⟨hUa, hVa⟩ := hUV
    by_cases hc : U = V ∨ Between X U V
    · have := first_on_cseg_aux hXa hTa hUa hVa hX hZ hZc hc
      exact ⟨U, this.1, Or.inl rfl, this.2⟩
    · have hne : U ≠ V := fun e => hc (Or.inl e)
      have hXU : X ≠ U := fun e => hX (Or.inl e)
      have hXV : X ≠ V := fun e => hX (Or.inr (Or.inl e))
      have hb : Between X V U := by
        rcases between_trichotomy (Line := L) (collinear_of_mem hXa hUa hVa) hXU hXV hne with
          h | h | h
        · exact absurd (Or.inr (Or.inr h)) hX
        · exact absurd (Or.inr h) hc
        · exact h
      have := first_on_cseg_aux hXa hTa hVa hUa (fun h => hX h.symm) hZ hZc.symm (Or.inr hb)
      exact ⟨V, this.1, Or.inr (Or.inl rfl), fun p hp hpc => this.2 p hp hpc.symm⟩
  · refine ⟨Z, hZ, hZc, fun p hp hpc => ?_⟩
    have hpa : p ∈ a := OrderCore.mem_of_between hp hXa hZa
    have hpZ : p ≠ Z := ne23_of_between (Line := L) hp
    apply hUV
    by_cases hne : U = V
    · exfalso
      have e1 : p = U := by
        rcases hpc with e | e | e
        · exact e
        · rw [hne]; exact e
        · rw [hne] at e; exact absurd rfl (ne13_of_between (Line := L) e)
      have e2 : Z = U := by
        rcases hZc with e | e | e
        · exact e
        · rw [hne]; exact e
        · rw [hne] at e; exact absurd rfl (ne13_of_between (Line := L) e)
      exact hpZ (e1.trans e2.symm)
    · obtain ⟨k, hUk, hVk⟩ := exists_line (Line := L) hne
      have e : k = a := line_unique hpZ (hpc.mem_line hUk hVk) (hZc.mem_line hUk hVk) hpa hZa
      exact ⟨by rw [← e]; exact hUk, by rw [← e]; exact hVk⟩

/-! ### Chains of segments off the polygon -/

section Chains

variable {n : ℕ} {v : Fin (n + 1) → P}

theorem Step.symm {X Y : P} (h : Step v X Y) : Step v Y X :=
  ⟨h.2.1, h.1, fun p hp => h.2.2 p (between_symm (Line := L) hp)⟩

theorem Conn.symm {X Y : P} (h : Conn v X Y) : Conn v Y X := by
  unfold Conn at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head (Step.symm (L := L) hstep) ih

/-- The parity is constant along a chain of segments off the polygon. -/
theorem Conn.par_eq {ℓ0 : L} {O : P} (hside : ∀ j, SameSide ℓ0 O (v j)) {X Y : P}
    (h : Conn v X Y) : par v ℓ0 X = par v ℓ0 Y := by
  unfold Conn at h
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (par_eq_of_step hside hstep.1 hstep.2.1 hstep.2.2)

omit [HasLines P L] hO in
/-- A chain of segments off the polygon is a broken line (in the sense of § 4) that has no point
in common with the polygon. -/
theorem Conn.exists_brokenLine {X Y : P} (h : Conn v X Y) (hX : ¬OnPoly v X) :
    ∃ (m : ℕ) (w : Fin (m + 1) → P), IsBrokenLine w ∧ w 0 = X ∧ w (Fin.last m) = Y ∧
      ∀ p, p ∈ BrokenLinePoints w → ¬OnPoly v p := by
  unfold Conn at h
  induction h with
  | refl =>
    refine ⟨0, fun _ => X, fun i => i.elim0, rfl, rfl, ?_⟩
    rintro p (⟨i, rfl⟩ | ⟨i, -⟩)
    · exact hX
    · exact i.elim0
  | @tail Y Z _ hstep ih =>
    obtain ⟨m, w, hw, h0, hl, hfree⟩ := ih
    by_cases hYZ : Y = Z
    · exact ⟨m, w, hw, h0, hl.trans hYZ, hfree⟩
    refine ⟨m + 1, Fin.snoc (α := fun _ => P) w Z, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, hl]
        exact hYZ
      · rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
        exact hw j
    · rw [← Fin.castSucc_zero, Fin.snoc_castSucc]
      exact h0
    · exact Fin.snoc_last _ _
    · rintro p (⟨i, hi⟩ | ⟨i, hi⟩)
      · revert hi
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [Fin.snoc_last]
          intro hi
          rw [hi]; exact hstep.2.1
        · rw [Fin.snoc_castSucc]
          intro hi
          exact hfree p (Or.inl ⟨j, hi⟩)
      · revert hi
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, hl]
          intro hi
          exact hstep.2.2 p hi
        · rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
          intro hi
          exact hfree p (Or.inr ⟨j, hi⟩)

/-! ### Seeing a point of the polygon -/

/-- A point seeing the point `A` of the polygon along a line that contains a segment `AU` of the
polygon lies beyond `A`. -/
theorem sees_between {X A U : P} (hX : Sees v X A) (hA : OnPoly v A) (hU : OnPoly v U)
    (hAU : A ≠ U) (hseg : ∀ p, Between A p U → OnPoly v p) (hcol : Collinear X A U) :
    Between X A U := by
  have hXA : X ≠ A := fun e => hX.1 (e ▸ hA)
  have hXU : X ≠ U := fun e => hX.1 (e ▸ hU)
  rcases between_trichotomy (Line := L) hcol hXA hXU hAU with h | h | h
  · exact absurd (hseg X h) hX.1
  · exact h
  · exact absurd hU (hX.2 U h)

/-- A point seeing a point within a side does not lie on the line of this side. -/
theorem sees_not_mem {k : Fin (n + 1)} {g : L} {Z X : P} (hZ : Between (v k) Z (v (k + 1)))
    (hkg : v k ∈ g) (hk1g : v (k + 1) ∈ g) (hX : Sees v X Z) : X ∉ g := by
  intro hXg
  have hZg : Z ∈ g := OrderCore.mem_of_between hZ hkg hk1g
  have hZS : OnPoly v Z := ⟨k, Or.inr (Or.inr hZ)⟩
  have h1 : Between X Z (v k) :=
    sees_between hX hZS ⟨k, Or.inl rfl⟩ (ne12_of_between (Line := L) hZ).symm
      (fun p hp => ⟨k, Or.inr (Or.inr (OrderLin.trans₂ (between_symm (Line := L) hp) hZ).1)⟩)
      (collinear_of_mem hXg hZg hkg)
  have h2 : Between X Z (v (k + 1)) :=
    sees_between hX hZS ⟨k, Or.inr (Or.inl rfl)⟩ (ne23_of_between (Line := L) hZ)
      (fun p hp => ⟨k, Or.inr (Or.inr (between_symm (Line := L)
        (OrderLin.trans₂ (between_symm (Line := L) hp) (between_symm (Line := L) hZ)).1))⟩)
      (collinear_of_mem hXg hZg hk1g)
  exact not_three_between h1 h2 hZ

/-- **Every point off the polygon sees a point of the polygon.** -/
theorem first_hit {X T : P} (hX : ¬OnPoly v X) (hT : OnPoly v T) :
    ∃ Z, OnPoly v Z ∧ ∀ p, Between X p Z → ¬OnPoly v p := by
  classical
  have hXT : X ≠ T := fun e => hX (e ▸ hT)
  have key : ∀ s : Finset (Fin (n + 1)),
      (∀ j ∈ s, ∀ p, (p = T ∨ Between X p T) → ¬CSeg (v j) (v (j + 1)) p) ∨
      ∃ Z, (Z = T ∨ Between X Z T) ∧ OnPoly v Z ∧
        ∀ p, Between X p Z → ∀ j ∈ s, ¬CSeg (v j) (v (j + 1)) p := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact Or.inl fun j hj => by simp at hj
    | insert j₀ s hj₀ ih =>
      have h0 := first_on_cseg (L := L) (U := v j₀) (V := v (j₀ + 1)) hXT (fun h => hX ⟨j₀, h⟩)
      rcases ih with ih | ⟨Z, hZ, hZS, hZfree⟩ <;>
        rcases h0 with h0 | ⟨Z₀, hZ₀, hZ₀c, hZ₀free⟩
      · left
        intro j hj p hp
        rcases Finset.mem_insert.1 hj with e | hj
        · rw [e]; exact h0 p hp
        · exact ih j hj p hp
      · right
        refine ⟨Z₀, hZ₀, ⟨j₀, hZ₀c⟩, fun p hp j hj => ?_⟩
        rcases Finset.mem_insert.1 hj with e | hj
        · rw [e]; exact hZ₀free p hp
        · exact ih j hj p (Or.inr (halfopen_trans hZ₀ hp))
      · right
        refine ⟨Z, hZ, hZS, fun p hp j hj => ?_⟩
        rcases Finset.mem_insert.1 hj with e | hj
        · rw [e]; exact h0 p (Or.inr (halfopen_trans hZ hp))
        · exact hZfree p hp j hj
      · right
        by_cases hZZ : Z = Z₀
        · refine ⟨Z, hZ, hZS, fun p hp j hj => ?_⟩
          rcases Finset.mem_insert.1 hj with e | hj
          · rw [e]; exact hZ₀free p (hZZ ▸ hp)
          · exact hZfree p hp j hj
        rcases halfopen_cases hZ hZ₀ hZZ with h | h
        · refine ⟨Z, hZ, hZS, fun p hp j hj => ?_⟩
          rcases Finset.mem_insert.1 hj with e | hj
          · rw [e]; exact hZ₀free p (OrderLin.trans₂ hp h).1
          · exact hZfree p hp j hj
        · refine ⟨Z₀, hZ₀, ⟨j₀, hZ₀c⟩, fun p hp j hj => ?_⟩
          rcases Finset.mem_insert.1 hj with e | hj
          · rw [e]; exact hZ₀free p hp
          · exact hZfree p (OrderLin.trans₂ hp h).1 j hj
  rcases key Finset.univ with h | ⟨Z, -, hZS, hfree⟩
  · obtain ⟨j, hj⟩ := hT
    exact absurd hj (h j (Finset.mem_univ j) T (Or.inl rfl))
  · exact ⟨Z, hZS, fun p hp ⟨j, hj⟩ => hfree p hp j (Finset.mem_univ j) hj⟩

/-! ### Sides through a point of the polygon -/

/-- A side that contains a point within the side `v k v (k+1)` is this side. -/
theorem Simple.side_unique (hs : Simple v) {k j : Fin (n + 1)} {Z : P}
    (hZ : Between (v k) Z (v (k + 1))) (hj : CSeg (v j) (v (j + 1)) Z) : j = k := by
  by_contra h
  rcases hs.sides_inter (fun e => h e.symm) (Or.inr (Or.inr hZ)) hj with ⟨e, -⟩ | ⟨e, -⟩
  · exact ne12_of_between (Line := L) hZ e.symm
  · exact ne23_of_between (Line := L) hZ e

omit [HasLines P L] hO in
/-- A side that contains the vertex `v (k+1)` is one of the two sides ending there. -/
theorem Simple.vertex_sides (hs : Simple v) {k j : Fin (n + 1)}
    (hj : CSeg (v j) (v (j + 1)) (v (k + 1))) : j = k ∨ j = k + 1 := by
  rcases hj with e | e | e
  · exact Or.inr (hs.inj e).symm
  · exact Or.inl (add_right_cancel (hs.inj e)).symm
  · exact absurd e (hs.h3 (k + 1) j)

/-- Points of a segment issuing from `Z` near `Z` are off the polygon, if the sides through `Z`
have no point within the segment. -/
theorem near_free {Z N : P} (hZN : Z ≠ N)
    (h : ∀ j, CSeg (v j) (v (j + 1)) Z → ∀ p, Between Z p N → ¬CSeg (v j) (v (j + 1)) p) :
    Near Z N (fun p => ¬OnPoly v p) := by
  have h1 : Near Z N (fun p => ∀ i, ¬CSeg (v i) (v (i + 1)) p) := by
    refine Near.forall_fin hZN fun i => ?_
    by_cases hi : CSeg (v i) (v (i + 1)) Z
    · exact (Near.self (L := L) hZN).mono fun p hp => h i hi p hp
    · exact near_not_cseg hZN hi
  exact h1.mono fun p hp ⟨i, hi⟩ => hp i hi

/-! ### The sweep lemma -/

/-- **Sweep lemma.** Let `A`, `B` be points of a line `a` and `W₀` a point off `a`. Suppose that no
side of the polygon contains both a point `r` of the half-open segments `[A, B)`, `[A, W₀)` and a
point `p` between `B` and a point of the segment `AW₀`. Then for all points `W` of `AW₀` close
enough to `A`, no point between `B` and `W` is on the polygon. -/
theorem sweep (hs : Simple v) {a : L} {A B W₀ : P} (hAa : A ∈ a) (hBa : B ∈ a) (hAB : A ≠ B)
    (hW₀ : W₀ ∉ a)
    (H : ∀ j r p W, CSeg (v j) (v (j + 1)) r → CSeg (v j) (v (j + 1)) p →
      (r = A ∨ Between A r B ∨ Between A r W₀) → Between A W W₀ → Between B p W → False) :
    Near A W₀ (fun W => ∀ p, Between B p W → ¬OnPoly v p) := by
  have hAW₀ : A ≠ W₀ := fun e => hW₀ (e ▸ hAa)
  obtain ⟨c, hAc, hWc⟩ := exists_line (Line := L) hAW₀
  have hca : c ≠ a := fun e => hW₀ (e ▸ hWc)
  have hBc : B ∉ c := fun h => hca (line_unique hAB hAc h hAa hBa)
  have hb : Near A W₀ (fun q => ∀ t, v t ∉ a → ¬Collinear B (v t) q) := by
    refine Near.forall_fin hAW₀ fun t => ?_
    by_cases ht : v t ∈ a
    · exact (Near.self (L := L) hAW₀).mono fun q _ h => absurd ht h
    · refine (Near.of_unique (φ := fun q => ¬Collinear B (v t) q) hAc hWc hAW₀
        fun q q' hq hq' h h' => ?_).mono fun q hq _ => hq
      by_contra hne
      have h := not_not.1 h
      have h' := not_not.1 h'
      have hBt : B ≠ v t := fun e => ht (e ▸ hBa)
      obtain ⟨d, hBd, htd, hqd⟩ := h
      have hq'd : q' ∈ d := mem_of_collinear h' hBt hBd htd
      have e : c = d := line_unique hne hq hq' hqd hq'd
      exact hBc (e ▸ hBd)
  obtain ⟨N', hN', hN⟩ := hb.and (Near.self (L := L) hAW₀)
  refine ⟨N', hN', fun W hW p hp hpS => ?_⟩
  have hWall : ∀ q, (q = W ∨ Between A q W) →
      (∀ t, v t ∉ a → ¬Collinear B (v t) q) ∧ Between A q W₀ := by
    intro q hq
    apply hN
    rcases hW with hW | hW
    · rw [← hW]; exact hq
    · rcases hq with hq | hq
      · rw [hq]; exact Or.inr hW
      · exact Or.inr (OrderLin.trans₂ hq hW).1
  have hAWW₀ : Between A W W₀ := (hWall W (Or.inl rfl)).2
  have hWc' : W ∈ c := OrderCore.mem_of_between hAWW₀ hAc hWc
  have hWa : W ∉ a := fun h =>
    hca (line_unique (ne12_of_between (Line := L) hAWW₀) hAc hWc' hAa h)
  have hBW : B ≠ W := fun e => hWa (e ▸ hBa)
  obtain ⟨m, hBm, hWm⟩ := exists_line (Line := L) hBW
  have hma : m ≠ a := fun e => hWa (e ▸ hWm)
  have hAm : A ∉ m := fun h => hma (line_unique hAB h hBm hAa hBa)
  have hpm : p ∈ m := OrderCore.mem_of_between hp hBm hWm
  have hpa : SameSide a p W := sameSide_of_between_mem hBa hWa hp
  have hvert : ∀ t, v t ∈ m → v t = B := by
    intro t ht
    by_contra hne
    have hta : v t ∉ a := fun h => hne (eq_of_mem_of_mem hma ht h hBm hBa)
    exact (hWall W (Or.inl rfl)).1 t hta ⟨m, hBm, ht, hWm⟩
  obtain ⟨j, hj⟩ := hpS
  have hpj : CSeg (v j) (v (j + 1)) p := hj
  -- the main case: an endpoint `v t` of the side on the side of `A` of the line `BW`
  have key : ∀ (t : Fin (n + 1)) (u' : P), Between (v t) p u' → SameSide m A (v t) →
      (∀ x, (x = v t ∨ Between p x (v t)) → CSeg (v j) (v (j + 1)) x) → False := by
    intro t u' hup hsu hx
    have hpu : p ≠ v t := (ne12_of_between (Line := L) hup).symm
    obtain ⟨h, hph, huh⟩ := exists_line (Line := L) hpu
    have hhm : h ≠ m := fun e => hsu.2.1 (e ▸ huh)
    have hBh : B ∉ h := fun hB =>
      hhm (line_unique (ne12_of_between (Line := L) hp).symm hph hB hpm hBm)
    have hWh : W ∉ h := fun hW' =>
      hhm (line_unique (ne23_of_between (Line := L) hp) hph hW' hpm hWm)
    have hr : ∃ r, r ∈ h ∧ (r = A ∨ Between A r B ∨ Between A r W) := by
      by_cases hAh : A ∈ h
      · exact ⟨A, hAh, Or.inl rfl⟩
      · have hnc : ¬Collinear B W A := not_collinear_of_not_mem hBm hWm hBW hAm
        rcases OrderCore.pasch hnc hBh hWh hAh hph hp with ⟨Y, hY, hYb⟩ | ⟨Y, hY, hYb⟩
        · exact ⟨Y, hY, Or.inr (Or.inr (between_symm (Line := L) hYb))⟩
        · exact ⟨Y, hY, Or.inr (Or.inl (between_symm (Line := L) hYb))⟩
    obtain ⟨r, hrh, hr⟩ := hr
    have hrm : SameSide m r A := by
      rcases hr with hr | hr | hr
      · rw [hr]; exact OrderCore.sameSide_refl hAm
      · exact sameSide_of_between_mem hBm hAm (between_symm (Line := L) hr)
      · exact sameSide_of_between_mem hWm hAm (between_symm (Line := L) hr)
    have hru : SameSide m r (v t) := OrderCore.sameSide_trans hrm hsu
    have hrp : r ≠ p := fun e => hru.1 (e ▸ hpm)
    have hr' : r = A ∨ Between A r B ∨ Between A r W₀ := by
      rcases hr with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (OrderLin.trans₂ h1 hAWW₀).1)
    by_cases hrt : r = v t
    · exact H j r p W (hx r (Or.inl hrt)) hpj hr' hAWW₀ hp
    rcases between_trichotomy (Line := L) (collinear_of_mem hph hrh huh) hrp.symm hpu hrt with
      h3 | h3 | h3
    · exact hru.2.2 ⟨p, hpm, h3⟩
    · exact H j r p W (hx r (Or.inr h3)) hpj hr' hAWW₀ hp
    · have hua : SameSide a (v t) W := by
        by_cases hra : r ∈ a
        · exact OrderCore.sameSide_trans
            (sameSide_of_between_mem hra hpa.1 (between_symm (Line := L) h3)) hpa
        · have hrW : SameSide a r W := by
            rcases hr with h1 | h1 | h1
            · exact absurd (h1 ▸ hAa) hra
            · exact absurd (OrderCore.mem_of_between h1 hAa hBa) hra
            · exact sameSide_of_between_mem hAa hWa h1
          have hpr : SameSide a p r :=
            OrderCore.sameSide_trans hpa (OrderCore.sameSide_symm hrW)
          exact OrderCore.sameSide_trans
            (OrderCore.sameSide_symm (sameSide_of_between hpr h3)) hpa
      have hBt : B ≠ v t := fun e => hua.1 (e ▸ hBa)
      obtain ⟨d, hBd, htd⟩ := exists_line (Line := L) hBt
      obtain ⟨-, -, q, hqd, hq⟩ := crossbar_opp hAa hBa hBm hWm hAB hWa hua
        (OrderCore.sameSide_symm hsu) hBd htd
      exact (hWall q (Or.inr hq)).1 t hua.1 ⟨d, hBd, htd, hqd⟩
  rcases hj with e | e | e
  · have e' := hvert j (e ▸ hpm)
    exact ne12_of_between (Line := L) hp (e.trans e').symm
  · have e' := hvert (j + 1) (e ▸ hpm)
    exact ne12_of_between (Line := L) hp (e.trans e').symm
  · have h1 : v j ∉ m := by
      intro h
      have e1 := hvert j h
      have h2 : v (j + 1) ∈ m := OrderCore.mem_of_between' e h hpm
      exact hs.ne j (e1.trans (hvert (j + 1) h2).symm)
    have h2 : v (j + 1) ∉ m := by
      intro h
      have e2 := hvert (j + 1) h
      have h1' : v j ∈ m := OrderCore.mem_of_between'' e hpm h
      exact hs.ne j ((hvert j h1').trans e2.symm)
    rcases OrderCore.sameSide_or_opp hAm h1 with hs1 | ho1
    · refine key j (v (j + 1)) e hs1 fun x hx => ?_
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (Or.inr (OrderLin.trans₂ (between_symm (Line := L) hx) e).1)
    · have hs2 : SameSide m A (v (j + 1)) :=
        OrderCore.sameSide_of_opp_opp ho1 ⟨h1, h2, p, hpm, e⟩
      refine key (j + 1) (v j) (between_symm (Line := L) e) hs2 fun x hx => ?_
      rcases hx with hx | hx
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr (between_symm (Line := L)
          (OrderLin.trans₂ (between_symm (Line := L) hx) (between_symm (Line := L) e)).1))

/-! ### Joining points that see the same point of the polygon -/

/-- **Local lemma.** Two points that see a point `Z` of the polygon and lie on the same side of a
line `k` through `Z`, such that the sides through `Z` have no point on this side of `k`, are joined
by a chain of segments off the polygon. -/
theorem local_conn (hs : Simple v) {k : L} {Z X Y : P} (hZk : Z ∈ k) (hX : Sees v X Z)
    (hY : Sees v Y Z) (hXY : SameSide k X Y)
    (hk : ∀ j, CSeg (v j) (v (j + 1)) Z → ∀ p, CSeg (v j) (v (j + 1)) p → ¬SameSide k X p) :
    Conn v X Y := by
  have hZX : Z ≠ X := fun e => hXY.1 (e ▸ hZk)
  have hZY : Z ≠ Y := fun e => hXY.2.1 (e ▸ hZk)
  obtain ⟨a, hZa, hYa⟩ := exists_line (Line := L) hZY
  by_cases hXa : X ∈ a
  · by_cases hXYe : X = Y
    · rw [hXYe]; exact Relation.ReflTransGen.refl
    rcases between_trichotomy (Line := L) (collinear_of_mem hZa hXa hYa) hZX hZY hXYe with
      h | h | h
    · exact absurd ⟨Z, hZk, h⟩ hXY.2.2
    · exact Conn.of_step ⟨hX.1, hY.1, fun p hp => hY.2 p
        (OrderLin.trans₂ (between_symm (Line := L) hp) (between_symm (Line := L) h)).1⟩
    · exact Conn.of_step ⟨hX.1, hY.1, fun p hp => hX.2 p
        (OrderLin.trans₂ hp (between_symm (Line := L) h)).1⟩
  · have hsw := sweep hs hZa hYa hZY hXa (by
      intro j r p W hr hp hr' hW hpW
      rcases hr' with hr' | hr' | hr'
      · rw [hr'] at hr
        have h1 : SameSide k W X := sameSide_of_between_mem hZk hXY.1 hW
        have h2 : SameSide k Y W :=
          OrderCore.sameSide_trans (OrderCore.sameSide_symm hXY) (OrderCore.sameSide_symm h1)
        exact hk j hr p hp (OrderCore.sameSide_trans hXY (sameSide_of_between h2 hpW))
      · exact hY.2 r (between_symm (Line := L) hr') ⟨j, hr⟩
      · exact hX.2 r (between_symm (Line := L) hr') ⟨j, hr⟩)
    obtain ⟨W, hWfree, hW⟩ := (hsw.and (Near.self (L := L) hZX)).exists
    have hWS : ¬OnPoly v W := hX.2 W (between_symm (Line := L) hW)
    have h1 : Step v X W :=
      ⟨hX.1, hWS, fun p hp => hX.2 p (OrderLin.trans₂ hp (between_symm (Line := L) hW)).1⟩
    have h2 : Step v W Y :=
      ⟨hWS, hY.1, fun p hp => hWfree p (between_symm (Line := L) hp)⟩
    exact (Conn.of_step h1).trans (Conn.of_step h2)

/-- **Along a side.** If all points seeing a point `B` of the closed side `v k v (k+1)` have a
property `C` that is invariant under `Conn`, then so have all points seeing a point `Z` within
this side. -/
theorem good_side (hs : Simple v) {C : P → Prop} (hC : ∀ X Y, Conn v X Y → C Y → C X)
    {k : Fin (n + 1)} {B : P} (hB : CSeg (v k) (v (k + 1)) B) (hgood : ∀ X, Sees v X B → C X)
    {Z : P} (hZ : Between (v k) Z (v (k + 1))) {X : P} (hX : Sees v X Z) : C X := by
  by_cases hZB : Z = B
  · exact hgood X (hZB ▸ hX)
  obtain ⟨g, hkg, hk1g⟩ := exists_line (Line := L) (hs.ne k)
  have hZg : Z ∈ g := OrderCore.mem_of_between hZ hkg hk1g
  have hBg : B ∈ g := hB.mem_line hkg hk1g
  have hXg : X ∉ g := sees_not_mem hZ hkg hk1g hX
  have hZX : Z ≠ X := fun e => hXg (e ▸ hZg)
  have hside : ∀ j r p W, CSeg (v j) (v (j + 1)) r → CSeg (v j) (v (j + 1)) p →
      Between (v k) r (v (k + 1)) → Between Z W X → Between B p W → False := by
    intro j r p W hr hp hrk hW hpW
    have hj : j = k := hs.side_unique hrk hr
    rw [hj] at hp
    have hWg : W ∉ g := (sameSide_of_between_mem hZg hXg hW).1
    exact (sameSide_of_between_mem hBg hWg hpW).1 (hp.mem_line hkg hk1g)
  have hsw := sweep hs hZg hBg hZB hXg (by
    intro j r p W hr hp hr' hW hpW
    rcases hr' with hr' | hr' | hr'
    · exact hside j r p W hr hp (hr' ▸ hZ) hW hpW
    · exact hside j r p W hr hp (side_between hZ hB hr') hW hpW
    · exact hX.2 r (between_symm (Line := L) hr') ⟨j, hr⟩)
  obtain ⟨W, hWfree, hW⟩ := (hsw.and (Near.self (L := L) hZX)).exists
  have hWS : ¬OnPoly v W := hX.2 W (between_symm (Line := L) hW)
  have hstep : Step v X W :=
    ⟨hX.1, hWS, fun p hp => hX.2 p (OrderLin.trans₂ hp (between_symm (Line := L) hW)).1⟩
  exact hC X W (Conn.of_step hstep)
    (hgood W ⟨hWS, fun p hp => hWfree p (between_symm (Line := L) hp)⟩)

end Chains

end PolyJordan

end HilbertFoundations
