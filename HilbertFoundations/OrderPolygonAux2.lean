import HilbertFoundations.OrderPolygonAux

/-!
# Helper module for `OrderPolygon.lean` (Theorem 6), part 2: the parity of a point

This module contains no unit of Hilbert's text. For a simple polygon `v 0, …, v n` (indices mod
`n + 1`) all of whose vertices lie on one side of a line `ℓ0`, it defines the **parity** `par v ℓ0 X`
of a point `X` (an element of `ZMod 2`): the number, mod 2, of sides of the polygon crossed by a
segment from `X` to a point `Q` of `ℓ0` in general position (`Gen`: no vertex lies on the segment).

* `seg_tri_parity`, `tri_parity`: a segment whose extremities are not on a triangle crosses an even
  number of its sides iff both or none of its extremities are inside; hence a closed polygon crosses
  the sides of a triangle in general position an even number of times.
* `cr_indep`, `par_eq`: the parity does not depend on the point `Q`.
* `par_eq_of_step`: the parity is the same at the two extremities of a segment that does not meet
  the polygon.
* `exists_jump`: the parity changes across the side `v n v 0`.
* `par_zero_of_line`: the parity is `0` on every line that does not meet the polygon.
-/

namespace HilbertFoundations

namespace PolyJordan

universe u v

variable {P : Type u} {L : Type v}

/-! ### Indicators in `ZMod 2` -/

/-- The indicator of a proposition, in `ZMod 2`. -/
noncomputable def ind (p : Prop) : ZMod 2 := by
  classical exact if p then 1 else 0

theorem ind_true {p : Prop} (h : p) : ind p = 1 := by simp [ind, h]

theorem ind_false {p : Prop} (h : ¬p) : ind p = 0 := by simp [ind, h]

theorem ind_congr {p q : Prop} (h : p ↔ q) : ind p = ind q := by rw [propext h]

theorem ind_or {p q : Prop} (h : ¬(p ∧ q)) : ind (p ∨ q) = ind p + ind q := by
  by_cases hp : p <;> by_cases hq : q
  · exact absurd ⟨hp, hq⟩ h
  · rw [ind_true (Or.inl hp), ind_true hp, ind_false hq]; decide
  · rw [ind_true (Or.inr hq), ind_false hp, ind_true hq]; decide
  · rw [ind_false (fun h' => h'.elim hp hq), ind_false hp, ind_false hq]; decide

theorem zmod2_eq_of_add : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide

theorem zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem fin3_tri : ∀ t : Fin 3, t = 0 ∨ t = 1 ∨ t = 2 := by decide

/-- Three propositions, not all true, none of them the only true one: an even number is true. -/
theorem ind_sum_three (X : Fin 3 → Prop) (H1 : ∀ t, X t → ∃ t', t' ≠ t ∧ X t')
    (H3 : ¬(X 0 ∧ X 1 ∧ X 2)) : ∑ t, ind (X t) = 0 := by
  rw [Fin.sum_univ_three]
  by_cases h0 : X 0 <;> by_cases h1 : X 1 <;> by_cases h2 : X 2
  · exact absurd ⟨h0, h1, h2⟩ H3
  · rw [ind_true h0, ind_true h1, ind_false h2]; decide
  · rw [ind_true h0, ind_false h1, ind_true h2]; decide
  · exfalso
    obtain ⟨t', ht', hX⟩ := H1 0 h0
    rcases fin3_tri t' with e | e | e
    · exact ht' e
    · exact h1 (e ▸ hX)
    · exact h2 (e ▸ hX)
  · rw [ind_false h0, ind_true h1, ind_true h2]; decide
  · exfalso
    obtain ⟨t', ht', hX⟩ := H1 1 h1
    rcases fin3_tri t' with e | e | e
    · exact h0 (e ▸ hX)
    · exact ht' e
    · exact h2 (e ▸ hX)
  · exfalso
    obtain ⟨t', ht', hX⟩ := H1 2 h2
    rcases fin3_tri t' with e | e | e
    · exact h0 (e ▸ hX)
    · exact h1 (e ▸ hX)
    · exact ht' e
  · rw [ind_false h0, ind_false h1, ind_false h2]; decide

theorem sum_shift {n : ℕ} (f : Fin (n + 1) → ZMod 2) : ∑ i, f (i + 1) = ∑ i, f i :=
  Equiv.sum_comp (Equiv.addRight (1 : Fin (n + 1))) f

/-- A cyclic sum of `f i + f (i + 1)` vanishes in `ZMod 2`. -/
theorem sum_pair_shift {n : ℕ} (f : Fin (n + 1) → ZMod 2) : ∑ i, (f i + f (i + 1)) = 0 := by
  rw [Finset.sum_add_distrib, sum_shift]
  exact CharTwo.add_self_eq_zero _

theorem fin_add_one_ne {n : ℕ} (hn : 1 ≤ n) (i : Fin (n + 1)) : i + 1 ≠ i := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_add_one] at this
  split_ifs at this with h'
  · rw [h', Fin.val_last] at this; omega
  · omega

/-! ### Polygons with vertices `v 0, …, v n` -/

/-- `X` is a point of the polygon `v` (a point of one of its closed sides `v i v (i+1)`). -/
def OnPoly [HasBetween P] {n : ℕ} (v : Fin (n + 1) → P) (X : P) : Prop :=
  ∃ i, CSeg (v i) (v (i + 1)) X

/-- The side `v i v (i+1)` crosses the segment `XY` (a point within both). -/
def Crosses [HasBetween P] {n : ℕ} (v : Fin (n + 1) → P) (X Y : P) (i : Fin (n + 1)) : Prop :=
  ∃ p, Between X p Y ∧ Between (v i) p (v (i + 1))

/-- The number of sides of the polygon crossing the segment `XY`, mod 2. -/
noncomputable def cr [HasBetween P] {n : ℕ} (v : Fin (n + 1) → P) (X Y : P) : ZMod 2 :=
  ∑ i, ind (Crosses v X Y i)

/-- A simple polygon with `n + 1` vertices, the sides being `v i v (i + 1)`. -/
structure Simple [HasBetween P] {n : ℕ} (v : Fin (n + 1) → P) : Prop where
  two_le : 2 ≤ n
  inj : Function.Injective v
  h3 : ∀ i j, ¬Between (v j) (v i) (v (j + 1))
  h4 : ∀ i j, i ≠ j → ∀ X, Between (v i) X (v (i + 1)) → ¬Between (v j) X (v (j + 1))

theorem rot_eq {n : ℕ} (i : Fin (n + 1)) : finRotate (n + 1) i = i + 1 := finRotate_apply i

theorem simple_of [HasBetween P] {n : ℕ} {v : Fin (n + 1) → P} (hv : IsSimplePolygon v) :
    Simple v := by
  refine ⟨by have := hv.1; omega, hv.2.1, fun i j => ?_, fun i j hij X => ?_⟩
  · have := hv.2.2.1 i j
    rwa [rot_eq] at this
  · have := hv.2.2.2 i j hij X
    rwa [rot_eq, rot_eq] at this

/-- The point `Q` of `ℓ0` is in general position for `X`: no vertex lies between `X` and `Q`. -/
def Gen [HasLines P L] [HasBetween P] {n : ℕ} (v : Fin (n + 1) → P) (ℓ0 : L) (X Q : P) : Prop :=
  Q ∈ ℓ0 ∧ ∀ j, ¬Between X (v j) Q

/-- The **parity** of the point `X` with respect to the polygon `v` and the line `ℓ0`. -/
noncomputable def par [HasLines P L] [HasBetween P] {n : ℕ} (v : Fin (n + 1) → P) (ℓ0 : L)
    (X : P) : ZMod 2 := by
  classical exact if h : ∃ Q, Gen v ℓ0 X Q then cr v X h.choose else 0

variable [HasLines P L] [HasBetween P] [hO : PlaneOrder P L]
include hO

omit [HasLines P L] hO in
theorem Near.exists {M N : P} {φ : P → Prop} (h : Near M N φ) : ∃ p, φ p := by
  obtain ⟨N', -, h'⟩ := h
  exact ⟨N', h' N' (Or.inl rfl)⟩

/-! ### A segment and a triangle -/

section Triangle

variable {V : Fin 3 → P} {ℓ : Fin 3 → L}

/-- A point within the side opposite to `V s` lies on the side of `V j` of the side line `ℓ j`,
for `j ≠ s`. -/
theorem side_sameSide (hT : TriangleLines V ℓ) {s j : Fin 3} (hjs : j ≠ s) {q : P}
    (hq : Between (V (s + 1)) q (V (s + 2))) : SameSide (ℓ j) q (V j) := by
  rcases fin3_cases s j with e | e | e
  · exact absurd e hjs
  · subst e
    exact sameSide_of_between_mem (hT.mem_of_ne (fin3_ne12 s).symm) (hT.not_mem (s + 1))
      (between_symm (Line := L) hq)
  · subst e
    exact sameSide_of_between_mem (hT.mem_of_ne (fin3_ne12 s)) (hT.not_mem (s + 2)) hq

theorem side_not_vertex (hT : TriangleLines V ℓ) {s : Fin 3} {q : P}
    (hq : Between (V (s + 1)) q (V (s + 2))) (k : Fin 3) : q ≠ V k := by
  rcases fin3_cases s k with e | e | e
  · intro h
    have := hT.mem_line_of_side hq
    rw [h, e] at this
    exact hT.not_mem s this
  · rw [e]; exact (ne12_of_between (Line := L) hq).symm
  · rw [e]; exact ne23_of_between (Line := L) hq

/-- A point between points within two different sides of a triangle is inside. -/
theorem inside_of_between_sides (hT : TriangleLines V ℓ) {s s' : Fin 3} (hss : s ≠ s')
    {p q Z : P} (hp : Between (V (s + 1)) p (V (s + 2)))
    (hq : Between (V (s' + 1)) q (V (s' + 2))) (hZ : Between p Z q) : Z ∈ TriInside V ℓ := by
  intro j
  by_cases hjs : j = s
  · have hqj : SameSide (ℓ j) q (V j) := side_sameSide hT (hjs ▸ hss) hq
    have hpj : p ∈ ℓ j := hjs ▸ hT.mem_line_of_side hp
    exact OrderCore.sameSide_trans (sameSide_of_between_mem hpj hqj.1 hZ) hqj
  by_cases hjs' : j = s'
  · have hpj : SameSide (ℓ j) p (V j) := side_sameSide hT hjs hp
    have hqj : q ∈ ℓ j := hjs' ▸ hT.mem_line_of_side hq
    exact OrderCore.sameSide_trans
      (sameSide_of_between_mem hqj hpj.1 (between_symm (Line := L) hZ)) hpj
  · have hpj := side_sameSide hT hjs hp
    have hqj := side_sameSide hT hjs' hq
    have hpq := OrderCore.sameSide_trans hpj (OrderCore.sameSide_symm hqj)
    exact OrderCore.sameSide_trans (OrderCore.sameSide_symm (sameSide_of_between hpq hZ)) hpj

/-- A point between a vertex and a point within the opposite side is inside. -/
theorem inside_of_between_vertex (hT : TriangleLines V ℓ) {s : Fin 3} {p Y : P}
    (hp : Between (V (s + 1)) p (V (s + 2))) (hY : Between (V s) Y p) : Y ∈ TriInside V ℓ := by
  intro j
  by_cases hjs : j = s
  · rw [hjs]
    exact sameSide_of_between_mem (hT.mem_line_of_side hp) (hT.not_mem s)
      (between_symm (Line := L) hY)
  · have hpj := side_sameSide hT hjs hp
    exact OrderCore.sameSide_trans
      (sameSide_of_between_mem (hT.mem_of_ne (Ne.symm hjs)) hpj.1 hY) hpj

/-- A segment from an interior point to a point that is neither interior nor on the triangle
crosses exactly one side. -/
theorem cross_in_out (hT : TriangleLines V ℓ) {U W : P} (hU : U ∈ TriInside V ℓ)
    (hW : W ∉ TriInside V ℓ) (hW' : W ∉ TriPts V) (hVUW : ∀ t, ¬Between U (V t) W) :
    ∑ t : Fin 3, ind (∃ p, Between (V (t + 1)) p (V (t + 2)) ∧ Between U p W) = 1 := by
  obtain ⟨Z, hZ, hZW⟩ := hT.exit hU W hW
  have hUZW : Between U Z W := by
    rcases hZW with e | e
    · rw [e] at hZ; exact absurd hZ hW'
    · exact e
  obtain ⟨t0, ht0⟩ : ∃ t0, Between (V (t0 + 1)) Z (V (t0 + 2)) := by
    rcases hZ with ⟨j, e⟩ | h
    · rw [e] at hUZW; exact absurd hUZW (hVUW j)
    · exact h
  have key : ∀ t p p', Between (V (t + 1)) p (V (t + 2)) → ∀ t', t ≠ t' →
      Between (V (t' + 1)) p' (V (t' + 2)) → Between U p p' → False := by
    intro t p p' hp t' htt' hp' hb
    have hp't : SameSide (ℓ t) p' (V t) := side_sameSide hT htt' hp'
    have hopp : OppositeSides (ℓ t) U p' :=
      ⟨(hU t).1, hp't.1, p, hT.mem_line_of_side hp, hb⟩
    exact OrderCore.not_sameSide_of_opp hopp
      (OrderCore.sameSide_trans (hU t) (OrderCore.sameSide_symm hp't))
  refine (Finset.sum_eq_single t0 ?_ ?_).trans (ind_true ⟨Z, ht0, hUZW⟩)
  · intro t _ ht
    refine ind_false ?_
    rintro ⟨p, hp, hUpW⟩
    have hpZ : p ≠ Z := by
      intro e
      rw [e] at hp
      obtain ⟨k, hk⟩ := hT.eq_vertex ht (hT.mem_line_of_side hp) (hT.mem_line_of_side ht0)
      exact side_not_vertex hT ht0 k hk
    rcases between_cases hUpW hUZW hpZ with h | h
    · exact key t p Z hp t0 ht ht0 h
    · exact key t0 Z p ht0 t (Ne.symm ht) hp h
  · intro h; exact absurd (Finset.mem_univ _) h

/-- A segment between two points that are neither interior nor on the triangle, and that does not
pass through a vertex, crosses no side or two sides. -/
theorem cross_out_out (hT : TriangleLines V ℓ) {U W : P} (hU : U ∉ TriInside V ℓ)
    (hU' : U ∉ TriPts V) (hW : W ∉ TriInside V ℓ) (hW' : W ∉ TriPts V)
    (hVUW : ∀ t, ¬Between U (V t) W) :
    ∑ t : Fin 3, ind (∃ p, Between (V (t + 1)) p (V (t + 2)) ∧ Between U p W) = 0 := by
  refine ind_sum_three _ ?_ ?_
  · rintro t ⟨p, hp, hUpW⟩
    obtain ⟨a, hUa, hpa, hWa⟩ := collinear_of_between (Line := L) hUpW
    have hpl : p ∈ ℓ t := hT.mem_line_of_side hp
    have hUne : ∀ k, U ≠ V k := fun k e => hU' (Or.inl ⟨k, e⟩)
    have hWne : ∀ k, W ≠ V k := fun k e => hW' (Or.inl ⟨k, e⟩)
    have hUside : ∀ s, ¬Between (V (s + 1)) U (V (s + 2)) := fun s h => hU' (Or.inr ⟨s, h⟩)
    have hWside : ∀ s, ¬Between (V (s + 1)) W (V (s + 2)) := fun s h => hW' (Or.inr ⟨s, h⟩)
    have hat : a ≠ ℓ t := by
      intro e
      rw [e] at hUa
      exact online_cross (hT.mem₁ t) (hT.mem₂ t) hUa hp hUpW (hUne _) (hUne _) (hWne _)
        (hWne _) (hUside t) (hWside t) (hVUW _) (hVUW _)
    have h1 : V (t + 1) ∉ a := fun h =>
      hat (line_unique (side_not_vertex hT hp (t + 1)) hpa h hpl (hT.mem₁ t))
    have h2 : V (t + 2) ∉ a := fun h =>
      hat (line_unique (side_not_vertex hT hp (t + 2)) hpa h hpl (hT.mem₂ t))
    have h0 : V t ∉ a := by
      intro h
      rcases online_beyond hUa hWa h hUpW (hUne t).symm (hWne t).symm (hVUW t) with h' | h'
      · exact hU (inside_of_between_vertex hT hp h')
      · exact hW (inside_of_between_vertex hT hp h')
    have hnc : ¬Collinear (V (t + 1)) (V (t + 2)) (V t) :=
      not_collinear_of_not_mem (hT.mem₁ t) (hT.mem₂ t) (hT.vertex_ne (fin3_ne12 t))
        (hT.not_mem t)
    have second : ∀ (t' : Fin 3) (Y : P), t' ≠ t → Y ∈ a →
        Between (V (t' + 1)) Y (V (t' + 2)) →
        ∃ t', t' ≠ t ∧ ∃ p, Between (V (t' + 1)) p (V (t' + 2)) ∧ Between U p W := by
      intro t' Y ht' hYa hY
      refine ⟨t', ht', Y, hY, ?_⟩
      have hYT : Y ∈ TriPts V := Or.inr ⟨t', hY⟩
      have hYU : Y ≠ U := fun e => hU' (by rw [← e]; exact hYT)
      have hYW : Y ≠ W := fun e => hW' (by rw [← e]; exact hYT)
      by_contra hn
      rcases online_beyond hUa hWa hYa hUpW hYU hYW hn with h' | h'
      · exact hU (inside_of_between_sides hT ht' hY hp h')
      · exact hW (inside_of_between_sides hT ht' hY hp h')
    rcases OrderCore.pasch hnc h1 h2 h0 hpa hp with ⟨Y, hYa, hY⟩ | ⟨Y, hYa, hY⟩
    · refine second (t + 1) Y (fin3_ne1 t) hYa ?_
      rw [fin3_add11, fin3_add12]; exact hY
    · refine second (t + 2) Y (fin3_ne2 t) hYa ?_
      rw [fin3_add21, fin3_add22]; exact between_symm (Line := L) hY
  · rintro ⟨⟨p0, hp0, hb0⟩, ⟨p1, hp1, hb1⟩, ⟨p2, hp2, hb2⟩⟩
    obtain ⟨a, hUa, hp0a, hWa⟩ := collinear_of_between (Line := L) hb0
    have hp1a : p1 ∈ a := OrderCore.mem_of_between hb1 hUa hWa
    have hp2a : p2 ∈ a := OrderCore.mem_of_between hb2 hUa hWa
    have hnc : ¬Collinear (V 0) (V 1) (V 2) :=
      OrderCore.not_collinear_left (hT.mem₁ 0) (hT.mem₂ 0) (hT.vertex_ne (by decide))
        (hT.not_mem 0)
    exact OrderCore.pasch_excl hnc hp2a hp2 hp0a hp0 hp1a (between_symm (Line := L) hp1)

/-- **A segment and a triangle**: the number of sides of the triangle crossed by a segment `UW`
(with `U`, `W` not on the triangle, no vertex on the segment) is odd iff exactly one of `U`, `W` is
inside. -/
theorem seg_tri_parity (hT : TriangleLines V ℓ) {U W : P} (hU : U ∉ TriPts V)
    (hW : W ∉ TriPts V) (hVUW : ∀ t, ¬Between U (V t) W) :
    ∑ t : Fin 3, ind (∃ p, Between (V (t + 1)) p (V (t + 2)) ∧ Between U p W) =
      ind (U ∈ TriInside V ℓ) + ind (W ∈ TriInside V ℓ) := by
  by_cases hUi : U ∈ TriInside V ℓ <;> by_cases hWi : W ∈ TriInside V ℓ
  · have h0 : ∑ t : Fin 3, ind (∃ p, Between (V (t + 1)) p (V (t + 2)) ∧ Between U p W) = 0 :=
      Finset.sum_eq_zero fun t _ => ind_false (by
        rintro ⟨p, hp, hb⟩
        exact hT.not_mem_inside (Or.inr ⟨t, hp⟩) (TriangleLines.inside_convex hUi hWi hb))
    rw [h0, ind_true hUi, ind_true hWi]; decide
  · rw [ind_true hUi, ind_false hWi, cross_in_out hT hUi hWi hW hVUW]; decide
  · have h1 := cross_in_out hT hWi hUi hU (fun t h => hVUW t (between_symm (Line := L) h))
    have h2 : ∑ t : Fin 3, ind (∃ p, Between (V (t + 1)) p (V (t + 2)) ∧ Between U p W) =
        ∑ t : Fin 3, ind (∃ p, Between (V (t + 1)) p (V (t + 2)) ∧ Between W p U) :=
      Finset.sum_congr rfl fun t _ => ind_congr
        ⟨fun ⟨p, h1, h2⟩ => ⟨p, h1, between_symm (Line := L) h2⟩,
          fun ⟨p, h1, h2⟩ => ⟨p, h1, between_symm (Line := L) h2⟩⟩
    rw [h2, h1, ind_false hUi, ind_true hWi]; decide
  · rw [ind_false hUi, ind_false hWi, cross_out_out hT hUi hU hWi hW hVUW]; decide

/-- **A closed polygon and a triangle** in general position (no vertex of one on the other): the
total number of crossings of their sides is even. -/
theorem tri_parity (hT : TriangleLines V ℓ) {n : ℕ} (v : Fin (n + 1) → P)
    (hv : ∀ j, v j ∉ TriPts V) (hVS : ∀ t i, ¬Between (v i) (V t) (v (i + 1))) :
    ∑ t : Fin 3, cr v (V (t + 1)) (V (t + 2)) = 0 := by
  unfold cr
  rw [Finset.sum_comm]
  have h1 : ∀ i : Fin (n + 1), ∑ t : Fin 3, ind (Crosses v (V (t + 1)) (V (t + 2)) i) =
      ind (v i ∈ TriInside V ℓ) + ind (v (i + 1) ∈ TriInside V ℓ) := fun i =>
    seg_tri_parity hT (hv i) (hv (i + 1)) (fun t => hVS t i)
  rw [Finset.sum_congr rfl fun i _ => h1 i]
  exact sum_pair_shift fun i => ind (v i ∈ TriInside V ℓ)

/-- Side lines of a triangle given by three non-collinear points. -/
theorem triangleLines_of {A B C : P} (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A)
    (h : ¬Collinear A B C) : ∃ ℓ : Fin 3 → L, TriangleLines ![A, B, C] ℓ := by
  refine ⟨![line B C hBC, line C A hCA, line A B hAB], ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩⟩
  · fin_cases i
    · exact mem_line_left hBC
    · exact mem_line_left hCA
    · exact mem_line_left hAB
  · fin_cases i
    · exact mem_line_right hBC
    · exact mem_line_right hCA
    · exact mem_line_right hAB
  · fin_cases i
    · exact fun hA => h ⟨_, hA, mem_line_left hBC, mem_line_right hBC⟩
    · exact fun hB => h ⟨_, mem_line_right hCA, hB, mem_line_left hCA⟩
    · exact fun hC => h ⟨_, mem_line_left hAB, mem_line_right hAB, hC⟩

end Triangle

/-! ### The parity -/

section Parity

variable {n : ℕ} {v : Fin (n + 1) → P}

omit [HasLines P L] hO in
theorem onPoly_vertex (v : Fin (n + 1) → P) (j : Fin (n + 1)) : OnPoly v (v j) :=
  ⟨j, Or.inl rfl⟩

/-- If all vertices lie on one side of a line, so do all points of the polygon. -/
theorem onPoly_side {m : L} {O' p : P} (hside : ∀ j, SameSide m O' (v j)) (hp : OnPoly v p) :
    SameSide m O' p := by
  obtain ⟨i, e | e | e⟩ := hp
  · rw [e]; exact hside i
  · rw [e]; exact hside (i + 1)
  · have h1 : SameSide m (v i) (v (i + 1)) :=
      OrderCore.sameSide_trans (OrderCore.sameSide_symm (hside i)) (hside (i + 1))
    exact OrderCore.sameSide_trans (hside i) (sameSide_of_between h1 e)

theorem cr_comm (v : Fin (n + 1) → P) (X Y : P) : cr v X Y = cr v Y X :=
  Finset.sum_congr rfl fun _ _ => ind_congr
    ⟨fun ⟨p, h1, h2⟩ => ⟨p, between_symm (Line := L) h1, h2⟩,
      fun ⟨p, h1, h2⟩ => ⟨p, between_symm (Line := L) h1, h2⟩⟩

omit [HasLines P L] hO in
theorem cr_zero_free {X Y : P} (h : ∀ p, Between X p Y → ¬OnPoly v p) : cr v X Y = 0 :=
  Finset.sum_eq_zero fun i _ => ind_false fun ⟨p, hp, hpi⟩ => h p hp ⟨i, Or.inr (Or.inr hpi)⟩

/-- A segment from a point `Q` of a line `m` to a point not on the side of `m` containing the
polygon crosses no side. -/
theorem cr_zero_of_side {m : L} {O' X Q : P} (hS : ∀ p, OnPoly v p → SameSide m O' p)
    (hQ : Q ∈ m) (hX : ¬SameSide m O' X) : cr v X Q = 0 := by
  refine cr_zero_free fun p hp hpS => ?_
  have hps : SameSide m O' p := hS p hpS
  by_cases hXm : X ∈ m
  · exact hps.2.1 (OrderCore.mem_of_between hp hXm hQ)
  · exact hX (OrderCore.sameSide_trans hps
      (sameSide_of_between_mem hQ hXm (between_symm (Line := L) hp)))

variable {ℓ0 : L} {O : P}

/-- Points in general position exist near any point of `ℓ0`. -/
theorem near_gen (hside : ∀ j, SameSide ℓ0 O (v j)) {Q0 Q1 : P} (h0 : Q0 ∈ ℓ0) (h1 : Q1 ∈ ℓ0)
    (h01 : Q0 ≠ Q1) (X : P) : Near Q0 Q1 (fun Q => Gen v ℓ0 X Q) := by
  have hA : Near Q0 Q1 (fun Q => ∀ j, ¬Between X (v j) Q) := by
    refine Near.forall_fin h01 fun j => Near.of_unique h0 h1 h01 fun p q hp hq hp' hq' => ?_
    have hp' : Between X (v j) p := not_not.1 hp'
    have hq' : Between X (v j) q := not_not.1 hq'
    by_contra hpq
    obtain ⟨a, hXa, hja, hpa⟩ := collinear_of_between (Line := L) hp'
    have hqa : q ∈ a := OrderCore.mem_of_between' hq' hXa hja
    have e : a = ℓ0 := line_unique hpq hpa hqa hp hq
    rw [e] at hja
    exact (hside j).2.1 hja
  exact (hA.and (Near.self (L := L) h01)).mono fun Q hQ =>
    ⟨OrderCore.mem_of_between hQ.2 h0 h1, hQ.1⟩

theorem exists_gen (hside : ∀ j, SameSide ℓ0 O (v j)) (X : P) : ∃ Q, Gen v ℓ0 X Q := by
  obtain ⟨Q0, Q1, h01, h0, h1⟩ := exists_two_points (Point := P) ℓ0
  exact (near_gen hside h0 h1 h01 X).exists

/-- **The number of crossings mod 2 does not depend on the point in general position.** -/
theorem cr_indep (hside : ∀ j, SameSide ℓ0 O (v j)) {X Q Q' : P} (hX : ¬OnPoly v X)
    (hQ : Gen v ℓ0 X Q) (hQ' : Gen v ℓ0 X Q') : cr v X Q = cr v X Q' := by
  have hS : ∀ p, OnPoly v p → SameSide ℓ0 O p := fun p hp => onPoly_side hside hp
  by_cases hXs : SameSide ℓ0 O X
  swap
  · rw [cr_zero_of_side hS hQ.1 hXs, cr_zero_of_side hS hQ'.1 hXs]
  by_cases hQQ : Q = Q'
  · rw [hQQ]
  have hXℓ : X ∉ ℓ0 := hXs.2.1
  have hXQ : X ≠ Q := fun e => hXℓ (by rw [e]; exact hQ.1)
  have hQ'X : Q' ≠ X := fun e => hXℓ (by rw [← e]; exact hQ'.1)
  have hnc : ¬Collinear X Q Q' := OrderCore.not_collinear_left hQ.1 hQ'.1 hQQ hXℓ
  obtain ⟨ℓ, hT⟩ := triangleLines_of (L := L) hXQ hQQ hQ'X hnc
  have hnotS : ∀ p, p ∈ ℓ0 → ¬OnPoly v p := fun p hp h => (hS p h).2.1 hp
  have h3 : cr v Q Q' + cr v Q' X + cr v X Q = 0 := by
    have := tri_parity hT v (by
      intro j hj
      rcases hj with ⟨t, e⟩ | ⟨t, hb⟩
      · rcases fin3_tri t with rfl | rfl | rfl
        · have e' : v j = X := e
          exact hX (by rw [← e']; exact onPoly_vertex v j)
        · have e' : v j = Q := e
          exact hnotS Q hQ.1 (by rw [← e']; exact onPoly_vertex v j)
        · have e' : v j = Q' := e
          exact hnotS Q' hQ'.1 (by rw [← e']; exact onPoly_vertex v j)
      · rcases fin3_tri t with rfl | rfl | rfl
        · have hb' : Between Q (v j) Q' := hb
          exact (hside j).2.1 (OrderCore.mem_of_between hb' hQ.1 hQ'.1)
        · have hb' : Between Q' (v j) X := hb
          exact hQ'.2 j (between_symm (Line := L) hb')
        · have hb' : Between X (v j) Q := hb
          exact hQ.2 j hb') (by
      intro t i hb
      rcases fin3_tri t with rfl | rfl | rfl
      · have hb' : Between (v i) X (v (i + 1)) := hb
        exact hX ⟨i, Or.inr (Or.inr hb')⟩
      · have hb' : Between (v i) Q (v (i + 1)) := hb
        exact hnotS Q hQ.1 ⟨i, Or.inr (Or.inr hb')⟩
      · have hb' : Between (v i) Q' (v (i + 1)) := hb
        exact hnotS Q' hQ'.1 ⟨i, Or.inr (Or.inr hb')⟩)
    rw [Fin.sum_univ_three] at this
    exact this
  have h0 : cr v Q Q' = 0 := cr_zero_free fun p hp hp' =>
    hnotS p (OrderCore.mem_of_between hp hQ.1 hQ'.1) hp'
  rw [h0, zero_add, cr_comm v Q' X] at h3
  exact (zmod2_eq_of_add _ _ h3).symm

theorem par_eq (hside : ∀ j, SameSide ℓ0 O (v j)) {X Q : P} (hX : ¬OnPoly v X)
    (hQ : Gen v ℓ0 X Q) : par v ℓ0 X = cr v X Q := by
  have hex : ∃ Q, Gen v ℓ0 X Q := ⟨Q, hQ⟩
  unfold par
  rw [dite_eq_left hex]
  exact cr_indep hside hX hex.choose_spec hQ

/-- The points of `ℓ0` are not on the polygon and have parity `0`. -/
theorem par_zero_of_mem (hside : ∀ j, SameSide ℓ0 O (v j)) {X : P} (hX : X ∈ ℓ0) :
    ¬OnPoly v X ∧ par v ℓ0 X = 0 := by
  have hS : ∀ p, OnPoly v p → SameSide ℓ0 O p := fun p hp => onPoly_side hside hp
  have hXS : ¬OnPoly v X := fun h => (hS X h).2.1 hX
  obtain ⟨Q, hQ⟩ := exists_gen hside X
  exact ⟨hXS, by rw [par_eq hside hXS hQ]; exact cr_zero_of_side hS hQ.1 fun h => h.2.1 hX⟩

/-- **The parity is constant along a segment that does not meet the polygon.** -/
theorem par_eq_of_step (hside : ∀ j, SameSide ℓ0 O (v j)) {X Y : P} (hX : ¬OnPoly v X)
    (hY : ¬OnPoly v Y) (hXY : ∀ p, Between X p Y → ¬OnPoly v p) : par v ℓ0 X = par v ℓ0 Y := by
  by_cases hXYe : X = Y
  · rw [hXYe]
  have hS : ∀ p, OnPoly v p → SameSide ℓ0 O p := fun p hp => onPoly_side hside hp
  have hnotS : ∀ p, p ∈ ℓ0 → ¬OnPoly v p := fun p hp h => (hS p h).2.1 hp
  obtain ⟨Q0, Q1, h01, h0, h1⟩ := exists_two_points (Point := P) ℓ0
  by_cases hl : X ∈ ℓ0 ∧ Y ∈ ℓ0
  · rw [(par_zero_of_mem hside hl.1).2, (par_zero_of_mem hside hl.2).2]
  have hcol : Near Q0 Q1 (fun Q => ¬Collinear X Y Q) := by
    refine Near.of_unique h0 h1 h01 fun p q hp hq hp' hq' => ?_
    have hp' : Collinear X Y p := not_not.1 hp'
    have hq' : Collinear X Y q := not_not.1 hq'
    by_contra hpq
    obtain ⟨a, hXa, hYa, hpa⟩ := hp'
    have hqa : q ∈ a := mem_of_collinear hq' hXYe hXa hYa
    have e : a = ℓ0 := line_unique hpq hpa hqa hp hq
    rw [e] at hXa hYa
    exact hl ⟨hXa, hYa⟩
  obtain ⟨Q, hQX, hQY, hnc⟩ :=
    ((near_gen hside h0 h1 h01 X).and ((near_gen hside h0 h1 h01 Y).and hcol)).exists
  obtain ⟨a, hXa, hYa⟩ := exists_line (Line := L) hXYe
  have hYQ : Y ≠ Q := fun e => hnc ⟨a, hXa, hYa, by rw [← e]; exact hYa⟩
  have hQXne : Q ≠ X := fun e => hnc ⟨a, hXa, hYa, by rw [e]; exact hXa⟩
  obtain ⟨ℓ, hT⟩ := triangleLines_of (L := L) hXYe hYQ hQXne hnc
  have h3 : cr v Y Q + cr v Q X + cr v X Y = 0 := by
    have := tri_parity hT v (by
      intro j hj
      rcases hj with ⟨t, e⟩ | ⟨t, hb⟩
      · rcases fin3_tri t with rfl | rfl | rfl
        · have e' : v j = X := e
          exact hX (by rw [← e']; exact onPoly_vertex v j)
        · have e' : v j = Y := e
          exact hY (by rw [← e']; exact onPoly_vertex v j)
        · have e' : v j = Q := e
          exact hnotS Q hQX.1 (by rw [← e']; exact onPoly_vertex v j)
      · rcases fin3_tri t with rfl | rfl | rfl
        · have hb' : Between Y (v j) Q := hb
          exact hQY.2 j hb'
        · have hb' : Between Q (v j) X := hb
          exact hQX.2 j (between_symm (Line := L) hb')
        · have hb' : Between X (v j) Y := hb
          exact hXY _ hb' (onPoly_vertex v j)) (by
      intro t i hb
      rcases fin3_tri t with rfl | rfl | rfl
      · have hb' : Between (v i) X (v (i + 1)) := hb
        exact hX ⟨i, Or.inr (Or.inr hb')⟩
      · have hb' : Between (v i) Y (v (i + 1)) := hb
        exact hY ⟨i, Or.inr (Or.inr hb')⟩
      · have hb' : Between (v i) Q (v (i + 1)) := hb
        exact hnotS Q hQX.1 ⟨i, Or.inr (Or.inr hb')⟩)
    rw [Fin.sum_univ_three] at this
    exact this
  rw [cr_zero_free hXY, add_zero, cr_comm v Q X] at h3
  rw [par_eq hside hX hQX, par_eq hside hY hQY]
  exact (zmod2_eq_of_add _ _ h3).symm

/-- Six points of a line, for `exists_jump`. -/
theorem online_jump {a : L} {M N₁ Q Q'' N₂ p : P} (hM : M ∈ a) (hQ : Q ∈ a) (hp : p ∈ a)
    (h1 : Between M N₁ Q) (h2 : Between Q M Q'') (h3 : Between M N₂ Q'') :
    Between N₁ M N₂ ∧ Between N₂ M Q ∧ ¬Between N₁ M Q ∧ (Between N₁ p Q → Between N₂ p Q) ∧
      (Between N₂ p Q →
        Between N₂ p M ∨ p = M ∨ p = N₁ ∨ Between M p N₁ ∨ Between N₁ p Q) := by
  have hN₁ : N₁ ∈ a := OrderCore.mem_of_between h1 hM hQ
  have hQ'' : Q'' ∈ a := OrderCore.mem_of_between' h2 hQ hM
  have hN₂ : N₂ ∈ a := OrderCore.mem_of_between h3 hM hQ''
  obtain ⟨f, he, hf⟩ := line_pos a ![M, N₁, Q, Q'', N₂, p]
    (by intro i; fin_cases i <;>
      first | exact hM | exact hN₁ | exact hQ | exact hQ'' | exact hN₂ | exact hp)
  have e1 := (hf 0 1 2).1 h1
  have e2 := (hf 2 0 3).1 h2
  have e3 := (hf 0 4 3).1 h3
  refine ⟨(hf 1 0 4).2 (by omega), (hf 4 0 2).2 (by omega), fun h => ?_, fun h => ?_,
    fun h => ?_⟩
  · have := (hf 1 0 2).1 h
    omega
  · have := (hf 1 5 2).1 h
    exact (hf 4 5 2).2 (by omega)
  · have e := (hf 4 5 2).1 h
    by_cases c1 : (f 4 < f 5 ∧ f 5 < f 0) ∨ (f 0 < f 5 ∧ f 5 < f 4)
    · exact Or.inl ((hf 4 5 0).2 c1)
    by_cases c2 : f 5 = f 0
    · exact Or.inr (Or.inl ((he 5 0).1 c2))
    by_cases c3 : f 5 = f 1
    · exact Or.inr (Or.inr (Or.inl ((he 5 1).1 c3)))
    by_cases c4 : (f 0 < f 5 ∧ f 5 < f 1) ∨ (f 1 < f 5 ∧ f 5 < f 0)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((hf 0 5 1).2 c4))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ((hf 1 5 2).2 (by omega)))))

omit [HasLines P L] hO in
theorem Simple.ne (hs : Simple v) (i : Fin (n + 1)) : v i ≠ v (i + 1) := fun e =>
  fin_add_one_ne (by have := hs.two_le; omega) i (hs.inj e).symm

omit [HasLines P L] hO in
/-- Two different closed sides meet at most in a common vertex. -/
theorem Simple.sides_inter (hs : Simple v) {i j : Fin (n + 1)} (hij : i ≠ j) {X : P}
    (h1 : CSeg (v i) (v (i + 1)) X) (h2 : CSeg (v j) (v (j + 1)) X) :
    (X = v i ∧ i = j + 1) ∨ (X = v (i + 1) ∧ i + 1 = j) := by
  rcases h1 with e1 | e1 | e1 <;> rcases h2 with e2 | e2 | e2
  · exact absurd (hs.inj (e1.symm.trans e2)) hij
  · exact Or.inl ⟨e1, hs.inj (e1.symm.trans e2)⟩
  · rw [e1] at e2; exact absurd e2 (hs.h3 i j)
  · exact Or.inr ⟨e1, hs.inj (e1.symm.trans e2)⟩
  · exact absurd (add_right_cancel (hs.inj (e1.symm.trans e2))) hij
  · rw [e1] at e2; exact absurd e2 (hs.h3 (i + 1) j)
  · rw [e2] at e1; exact absurd e1 (hs.h3 j i)
  · rw [e2] at e1; exact absurd e1 (hs.h3 (j + 1) i)
  · exact absurd e2 (hs.h4 i j hij X e1)

/-- **The parity changes across the side `v n v 0`**: there are a point `M` within this side and
two points `N₁`, `N₂` off the polygon on a line through `M`, on different sides of `M`, joined to `M`
by segments that do not meet the polygon, whose parities differ. -/
theorem exists_jump (hs : Simple v) (hside : ∀ j, SameSide ℓ0 O (v j)) :
    ∃ M N₁ N₂ : P, Between (v (Fin.last n)) M (v 0) ∧ Between N₁ M N₂ ∧
      ¬Collinear (v (Fin.last n)) (v 0) N₁ ∧ ¬OnPoly v N₁ ∧ ¬OnPoly v N₂ ∧
      (∀ p, Between N₁ p M → ¬OnPoly v p) ∧ (∀ p, Between N₂ p M → ¬OnPoly v p) ∧
      par v ℓ0 N₂ = par v ℓ0 N₁ + 1 := by
  have hS : ∀ p, OnPoly v p → SameSide ℓ0 O p := fun p hp => onPoly_side hside hp
  have hne : v (Fin.last n) ≠ v 0 := by
    have := hs.ne (Fin.last n)
    rwa [Fin.last_add_one] at this
  obtain ⟨M, hM⟩ := exists_between (Line := L) hne
  have hM' : Between (v (Fin.last n)) M (v (Fin.last n + 1)) := by
    rw [Fin.last_add_one]; exact hM
  obtain ⟨g, hag, h0g⟩ := exists_line (Line := L) hne
  have hMg : M ∈ g := OrderCore.mem_of_between hM hag h0g
  have hMS : OnPoly v M := ⟨Fin.last n, Or.inr (Or.inr hM')⟩
  obtain ⟨Q0, Q1, h01, h0, h1⟩ := exists_two_points (Point := P) ℓ0
  have hQg : Near Q0 Q1 (fun Q => Q ∉ g) := by
    refine Near.of_unique h0 h1 h01 fun p q hp hq hp' hq' => ?_
    by_contra hpq
    have e : g = ℓ0 := line_unique hpq (not_not.1 hp') (not_not.1 hq') hp hq
    rw [e] at h0g
    exact (hside 0).2.1 h0g
  obtain ⟨Q, hQ, hQg⟩ := ((near_gen hside h0 h1 h01 M).and hQg).exists
  have hQM : Q ≠ M := fun e => hQg (by rw [e]; exact hMg)
  obtain ⟨h, hMh, hQh⟩ := exists_line (Line := L) hQM.symm
  have hhg : h ≠ g := fun e => hQg (by rw [← e]; exact hQh)
  have key : ∀ p, p ∈ h → p ∈ g → p = M := fun p hph hpg =>
    eq_of_mem_of_mem hhg hph hpg hMh hMg
  have free : ∀ N, N ≠ M → N ∈ h → Near M N (fun p => ¬OnPoly v p) := by
    intro N hN hNh
    have h1 : Near M N (fun p => ∀ i, ¬CSeg (v i) (v (i + 1)) p) := by
      refine Near.forall_fin hN.symm fun i => ?_
      by_cases hi : i = Fin.last n
      · refine (Near.self (L := L) hN.symm).mono fun p hp hc => ?_
        rw [hi] at hc
        have hpg : p ∈ g := hc.mem_line hag (by rw [Fin.last_add_one]; exact h0g)
        have hph : p ∈ h := OrderCore.mem_of_between hp hMh hNh
        exact ne12_of_between (Line := L) hp (key p hph hpg).symm
      · refine near_not_cseg hN.symm fun hc => ?_
        rcases hs.sides_inter (Ne.symm hi) (Or.inr (Or.inr hM')) hc with ⟨e, -⟩ | ⟨e, -⟩
        · exact ne12_of_between (Line := L) hM' e.symm
        · exact ne23_of_between (Line := L) hM' e
    exact h1.mono fun p hp ⟨i, hi⟩ => hp i hi
  obtain ⟨N₁, hN₁, hfree₁⟩ := free Q hQM hQh
  obtain ⟨Q'', hQ''⟩ := exists_beyond (Line := L) hQM
  have hQ''h : Q'' ∈ h := OrderCore.mem_of_between' hQ'' hQh hMh
  obtain ⟨N₂, hN₂, hfree₂⟩ := free Q'' (ne23_of_between (Line := L) hQ'').symm hQ''h
  have hN₁h : N₁ ∈ h := OrderCore.mem_of_between hN₁ hMh hQh
  have hN₂h : N₂ ∈ h := OrderCore.mem_of_between hN₂ hMh hQ''h
  obtain ⟨hN1MN2, hN2MQ, hnN1MQ, -, -⟩ := online_jump hMh hQh hMh hN₁ hQ'' hN₂
  have hN₁g : N₁ ∉ g := fun hg =>
    ne12_of_between (Line := L) hN₁ (key N₁ hN₁h hg).symm
  have hN₁S : ¬OnPoly v N₁ := hfree₁ N₁ (Or.inl rfl)
  have hN₂S : ¬OnPoly v N₂ := hfree₂ N₂ (Or.inl rfl)
  have hgen₁ : Gen v ℓ0 N₁ Q := ⟨hQ.1, fun j hj => hQ.2 j (between_symm (Line := L)
    (OrderLin.trans₂ (between_symm (Line := L) hj) (between_symm (Line := L) hN₁)).1)⟩
  have hgen₂ : Gen v ℓ0 N₂ Q := by
    refine ⟨hQ.1, fun j hj => ?_⟩
    have hjh : v j ∈ h := OrderCore.mem_of_between hj hN₂h hQh
    rcases (online_jump hMh hQh hjh hN₁ hQ'' hN₂).2.2.2.2 hj with c | c | c | c | c
    · exact hfree₂ _ (Or.inr (between_symm (Line := L) c)) (onPoly_vertex v j)
    · rw [← c] at hM'; exact hs.h3 j (Fin.last n) hM'
    · exact hN₁S (by rw [← c]; exact onPoly_vertex v j)
    · exact hfree₁ _ (Or.inr c) (onPoly_vertex v j)
    · exact hgen₁.2 j c
  have hexcl : ∀ i, ¬(Crosses v N₁ Q i ∧ i = Fin.last n) := by
    rintro i ⟨⟨p, hp, hpi⟩, rfl⟩
    have hpg : p ∈ g := OrderCore.mem_of_between hpi hag (by rw [Fin.last_add_one]; exact h0g)
    have hph : p ∈ h := OrderCore.mem_of_between hp hN₁h hQh
    rw [key p hph hpg] at hp
    exact hnN1MQ hp
  have hiff : ∀ i, Crosses v N₂ Q i ↔ (Crosses v N₁ Q i ∨ i = Fin.last n) := by
    intro i
    constructor
    · rintro ⟨p, hp, hpi⟩
      have hph : p ∈ h := OrderCore.mem_of_between hp hN₂h hQh
      have hpS : OnPoly v p := ⟨i, Or.inr (Or.inr hpi)⟩
      rcases (online_jump hMh hQh hph hN₁ hQ'' hN₂).2.2.2.2 hp with c | c | c | c | c
      · exact absurd hpS (hfree₂ _ (Or.inr (between_symm (Line := L) c)))
      · right
        by_contra hi
        rw [c] at hpi
        exact hs.h4 i (Fin.last n) hi M hpi hM'
      · rw [c] at hpS; exact absurd hpS hN₁S
      · exact absurd hpS (hfree₁ _ (Or.inr c))
      · exact Or.inl ⟨p, c, hpi⟩
    · rintro (⟨p, hp, hpi⟩ | rfl)
      · have hph : p ∈ h := OrderCore.mem_of_between hp hN₁h hQh
        exact ⟨p, (online_jump hMh hQh hph hN₁ hQ'' hN₂).2.2.2.1 hp, hpi⟩
      · exact ⟨M, hN2MQ, hM'⟩
  have hsum : ∑ i : Fin (n + 1), ind (i = Fin.last n) = 1 :=
    (Finset.sum_eq_single (Fin.last n) (fun b _ hb => ind_false hb)
      (fun h => absurd (Finset.mem_univ _) h)).trans (ind_true rfl)
  have hcr : cr v N₂ Q = cr v N₁ Q + 1 := by
    unfold cr
    rw [Finset.sum_congr rfl fun i _ => (ind_congr (hiff i)).trans (ind_or (hexcl i)),
      Finset.sum_add_distrib, hsum]
  refine ⟨M, N₁, N₂, hM, hN1MN2, not_collinear_of_not_mem hag h0g hne hN₁g, hN₁S, hN₂S,
    fun p hp => hfree₁ p (Or.inr (between_symm (Line := L) hp)),
    fun p hp => hfree₂ p (Or.inr (between_symm (Line := L) hp)), ?_⟩
  rw [par_eq hside hN₂S hgen₂, par_eq hside hN₁S hgen₁, hcr]

/-- Opposite sides of a line in terms of the side of a third point. -/
theorem ind_opp {a : L} {A B C : P} (hA : A ∉ a) (hB : B ∉ a) (hC : C ∉ a) :
    ind (OppositeSides a A B) = ind (SameSide a C A) + ind (SameSide a C B) := by
  rcases OrderCore.sameSide_or_opp hC hA with sA | oA <;>
    rcases OrderCore.sameSide_or_opp hC hB with sB | oB
  · rw [ind_true sA, ind_true sB, ind_false (fun h => OrderCore.not_sameSide_of_opp h
      (OrderCore.sameSide_trans (OrderCore.sameSide_symm sA) sB))]
    decide
  · rw [ind_true sA, ind_false (OrderCore.not_sameSide_of_opp oB),
      ind_true (OrderCore.opp_of_sameSide_opp (OrderCore.sameSide_symm sA) oB)]
    decide
  · rw [ind_false (OrderCore.not_sameSide_of_opp oA), ind_true sB,
      ind_true (OrderCore.opp_symm
        (OrderCore.opp_of_sameSide_opp (OrderCore.sameSide_symm sB) oA))]
    decide
  · rw [ind_false (OrderCore.not_sameSide_of_opp oA),
      ind_false (OrderCore.not_sameSide_of_opp oB),
      ind_false (fun h => OrderCore.not_sameSide_of_opp h
        (OrderCore.sameSide_of_opp_opp (OrderCore.opp_symm oA) oB))]
    decide

/-- **The parity is `0` on every line that does not meet the polygon.** -/
theorem par_zero_of_line (hside : ∀ j, SameSide ℓ0 O (v j)) (m : L)
    (hm : ∀ X, X ∈ m → ¬OnPoly v X) {X : P} (hX : X ∈ m) : par v ℓ0 X = 0 := by
  have hS : ∀ p, OnPoly v p → SameSide ℓ0 O p := fun p hp => onPoly_side hside hp
  have hXS : ¬OnPoly v X := hm X hX
  obtain ⟨Q, hQ⟩ := exists_gen hside X
  rw [par_eq hside hXS hQ]
  have hvm : ∀ j, v j ∉ m := fun j h => hm _ h (onPoly_vertex v j)
  have hstep : ∀ i, SameSide m (v i) (v (i + 1)) := fun i =>
    ⟨hvm i, hvm (i + 1), fun ⟨Z, hZ, hb⟩ => hm Z hZ ⟨i, Or.inr (Or.inr hb)⟩⟩
  have hall : ∀ j, SameSide m (v 0) (v j) := by
    intro j
    induction j using Fin.induction with
    | zero => exact OrderCore.sameSide_refl (hvm 0)
    | succ i ih =>
      have := hstep i.castSucc
      rw [Fin.coeSucc_eq_succ] at this
      exact OrderCore.sameSide_trans ih this
  have hSm : ∀ p, OnPoly v p → SameSide m (v 0) p := fun p hp => onPoly_side hall hp
  by_cases hQm : SameSide m (v 0) Q
  swap
  · rw [cr_comm]; exact cr_zero_of_side hSm hX hQm
  by_cases hXs : SameSide ℓ0 O X
  swap
  · exact cr_zero_of_side hS hQ.1 hXs
  have hXQ : X ≠ Q := fun e => hQm.2.1 (by rw [← e]; exact hX)
  obtain ⟨a, hXa, hQa⟩ := exists_line (Line := L) hXQ
  have hin : ∀ p, p ∈ a → OnPoly v p → Between X p Q := by
    intro p hpa hp
    have hpX : p ≠ X := fun e => hXS (by rw [← e]; exact hp)
    have hpQ : p ≠ Q := fun e => (hS p hp).2.1 (by rw [e]; exact hQ.1)
    rcases between_trichotomy (Line := L) (collinear_of_mem hXa hpa hQa) hpX.symm hXQ hpQ with
      h | h | h
    · exact absurd ⟨X, hX, h⟩
        (OrderCore.sameSide_trans (OrderCore.sameSide_symm (hSm p hp)) hQm).2.2
    · exact h
    · exact absurd ⟨Q, hQ.1, h⟩
        (OrderCore.sameSide_trans (OrderCore.sameSide_symm hXs) (hS p hp)).2.2
  have hva : ∀ j, v j ∉ a := fun j h => hQ.2 j (hin _ h (onPoly_vertex v j))
  have hiff : ∀ i, Crosses v X Q i ↔ OppositeSides a (v i) (v (i + 1)) := by
    intro i
    constructor
    · rintro ⟨p, hp, hpi⟩
      exact ⟨hva i, hva (i + 1), p, OrderCore.mem_of_between hp hXa hQa, hpi⟩
    · rintro ⟨-, -, Z, hZa, hZ⟩
      exact ⟨Z, hin Z hZa ⟨i, Or.inr (Or.inr hZ)⟩, hZ⟩
  unfold cr
  rw [Finset.sum_congr rfl fun i _ =>
    (ind_congr (hiff i)).trans (ind_opp (hva i) (hva (i + 1)) (hva 0))]
  exact sum_pair_shift fun i => ind (SameSide a (v 0) (v i))

end Parity

end PolyJordan

end HilbertFoundations
