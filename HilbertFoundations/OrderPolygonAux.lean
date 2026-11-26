import HilbertFoundations.Order

/-!
# Helper module for `OrderPolygon.lean` (Theorem 6), part 1: order tools

This module contains no unit of Hilbert's text; its results are used in `OrderPolygon.lean` to prove
Theorem 6 (unit `th.6`, the polygonal Jordan theorem) from the axioms of groups I and II.

* `line_pos`: finitely many points of a line have integer positions describing betweenness
  (from the order of sequence of `OrderAux.lean`), and a few consequences for points of a line.
* `Near M N φ`: the property `φ` holds for all points of the segment `MN` close enough to `M`
  (for all points of some half-open segment `(M, N']`); such properties are closed under finite
  conjunctions (`Near.and`, `Near.forall_fin`), and a property that fails for at most one point of a
  line holds near `M` (`Near.of_unique`).
* `CSeg A B X`: `X` is a point of the closed segment `AB`; `near_not_cseg`: a point off a closed
  segment has a neighbourhood on each segment issuing from it that misses the closed segment.
* Lemmas on the sides of a line: `opp_of_between_mem`, `not_sameSide_of_between`, the crossbar
  theorem `crossbar_opp`.
* `exists_line_sameSide`: every finite set of points lies on one side of some line
  (`exists_bounds`, `cone_sameSide`).
-/

namespace HilbertFoundations

namespace PolyJordan

universe u v

variable {P : Type u} {L : Type v}

/-- `φ` holds for all points of the segment `MN` sufficiently close to `M`: for all points of a
half-open segment `(M, N']` with `N'` between `M` and `N`. -/
def Near [HasBetween P] (M N : P) (φ : P → Prop) : Prop :=
  ∃ N', Between M N' N ∧ ∀ p, (p = N' ∨ Between M p N') → φ p

/-- `X` is a point of the closed segment `AB` (an extremity or a point between them). -/
def CSeg [HasBetween P] (A B X : P) : Prop := X = A ∨ X = B ∨ Between A X B

theorem Near.mono [HasBetween P] {M N : P} {φ ψ : P → Prop} (h : Near M N φ)
    (hφ : ∀ p, φ p → ψ p) : Near M N ψ := by
  obtain ⟨N', hN', h'⟩ := h
  exact ⟨N', hN', fun p hp => hφ p (h' p hp)⟩

variable [HasLines P L] [HasBetween P] [hO : PlaneOrder P L]
include hO

/-! ### Integer positions of finitely many points of a line -/

/-- **Finitely many points of a line have integer positions** describing their betweenness and
their coincidences (II 1–4, through the order of sequence of the points of a line). -/
theorem line_pos {n : ℕ} (a : L) (R : Fin n → P) (hR : ∀ i, R i ∈ a) :
    ∃ p : Fin n → ℤ, (∀ i j, p i = p j ↔ R i = R j) ∧
      ∀ i j k, (Between (R i) (R j) (R k) ↔
        (p i < p j ∧ p j < p k) ∨ (p k < p j ∧ p j < p i)) := by
  classical
  obtain ⟨O, U, hOU, hOa, hUa⟩ := exists_two_points (Point := P) a
  obtain ⟨p, hp⟩ : ∃ p : Fin n → ℤ, ∀ i, p i =
      ((Finset.univ.filter (fun j => OrderLin.lineLt O U (R j) (R i))).card : ℤ) :=
    ⟨_, fun _ => rfl⟩
  have mono : ∀ i j, OrderLin.lineLt O U (R i) (R j) → p i < p j := by
    intro i j h
    have hsub : (Finset.univ.filter (fun m => OrderLin.lineLt O U (R m) (R i))) ⊂
        (Finset.univ.filter (fun m => OrderLin.lineLt O U (R m) (R j))) := by
      refine (Finset.ssubset_iff_of_subset ?_).2 ⟨i, ?_, ?_⟩
      · intro m hm
        rw [Finset.mem_filter] at hm ⊢
        exact ⟨hm.1, OrderLin.lineLt_trans (L := L) hm.2 h⟩
      · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩
      · rw [Finset.mem_filter]
        exact fun h' => OrderLin.lineLt_irrefl (L := L) O U (R i) h'.2
    rw [hp i, hp j]
    exact_mod_cast Finset.card_lt_card hsub
  have eq_of : ∀ i j, R i = R j → p i = p j := by
    intro i j h; rw [hp i, hp j, h]
  have lt_or : ∀ i j, R i ≠ R j →
      OrderLin.lineLt O U (R i) (R j) ∨ OrderLin.lineLt O U (R j) (R i) := fun i j h =>
    OrderLin.lineLt_trichotomous hOa hUa hOU (hR i) (hR j) h
  have hpe : ∀ i j, p i = p j ↔ R i = R j := by
    intro i j
    constructor
    · intro h
      by_contra hne
      rcases lt_or i j hne with h' | h'
      · exact absurd h (ne_of_lt (mono i j h'))
      · exact absurd h.symm (ne_of_lt (mono j i h'))
    · exact eq_of i j
  have hlt : ∀ i j, OrderLin.lineLt O U (R i) (R j) ↔ p i < p j := by
    intro i j
    constructor
    · exact mono i j
    · intro h
      have hne : R i ≠ R j := fun e => absurd (eq_of i j e) (ne_of_lt h)
      rcases lt_or i j hne with h' | h'
      · exact h'
      · exact absurd (mono j i h') (not_lt.2 h.le)
  refine ⟨p, hpe, fun i j k => ?_⟩
  by_cases hij : R i = R j
  · have e := eq_of i j hij
    exact ⟨fun h => absurd hij (ne12_of_between (Line := L) h), fun h => by omega⟩
  by_cases hik : R i = R k
  · have e := eq_of i k hik
    exact ⟨fun h => absurd hik (ne13_of_between (Line := L) h), fun h => by omega⟩
  by_cases hjk : R j = R k
  · have e := eq_of j k hjk
    exact ⟨fun h => absurd hjk (ne23_of_between (Line := L) h), fun h => by omega⟩
  rw [OrderLin.between_iff_lineLt hOa hUa hOU (hR i) (hR j) (hR k) hij hik hjk,
    hlt i j, hlt j k, hlt k j, hlt j i]

/-- Two distinct points between `M` and `N`: one of them lies between `M` and the other. -/
theorem between_cases {M N p q : P} (h1 : Between M p N) (h2 : Between M q N) (hpq : p ≠ q) :
    Between M p q ∨ Between M q p := by
  obtain ⟨a, hM, hp, hN⟩ := collinear_of_between (Line := L) h1
  have hq : q ∈ a := OrderCore.mem_of_between h2 hM hN
  obtain ⟨f, he, hf⟩ := line_pos a ![M, N, p, q]
    (by intro i; fin_cases i <;> first | exact hM | exact hN | exact hp | exact hq)
  have e1 := (hf 0 2 1).1 h1
  have e2 := (hf 0 3 1).1 h2
  have e3 : f 2 ≠ f 3 := fun e => hpq ((he 2 3).1 e)
  by_cases h' : (f 0 < f 2 ∧ f 2 < f 3) ∨ (f 3 < f 2 ∧ f 2 < f 0)
  · exact Or.inl ((hf 0 2 3).2 h')
  · exact Or.inr ((hf 0 3 2).2 (by omega))

/-- Two segments of a line with a common inner point, none containing an extremity of the other
(as a point of the closed segment): impossible. -/
theorem online_cross {a : L} {B C U W p : P} (hB : B ∈ a) (hC : C ∈ a) (hU : U ∈ a)
    (h1 : Between B p C) (h2 : Between U p W) (hUB : U ≠ B) (hUC : U ≠ C) (hWB : W ≠ B)
    (hWC : W ≠ C) (hU' : ¬Between B U C) (hW' : ¬Between B W C) (hB' : ¬Between U B W)
    (hC' : ¬Between U C W) : False := by
  have hp : p ∈ a := OrderCore.mem_of_between h1 hB hC
  have hW : W ∈ a := OrderCore.mem_of_between' h2 hU hp
  obtain ⟨f, he, hf⟩ := line_pos a ![B, C, U, W, p]
    (by intro i; fin_cases i <;> first | exact hB | exact hC | exact hU | exact hW | exact hp)
  have e1 := (hf 0 4 1).1 h1
  have e2 := (hf 2 4 3).1 h2
  have n1 : f 2 ≠ f 0 := fun e => hUB ((he 2 0).1 e)
  have n2 : f 2 ≠ f 1 := fun e => hUC ((he 2 1).1 e)
  have n3 : f 3 ≠ f 0 := fun e => hWB ((he 3 0).1 e)
  have n4 : f 3 ≠ f 1 := fun e => hWC ((he 3 1).1 e)
  have m1 := mt (hf 0 2 1).2 hU'
  have m2 := mt (hf 0 3 1).2 hW'
  have m3 := mt (hf 2 0 3).2 hB'
  have m4 := mt (hf 2 1 3).2 hC'
  omega

/-- A point `A` of the line `UW` outside the closed segment `UW` lies beyond `U` or beyond `W`,
seen from a point `p` between `U` and `W`. -/
theorem online_beyond {a : L} {U W p A : P} (hU : U ∈ a) (hW : W ∈ a) (hA : A ∈ a)
    (h : Between U p W) (hAU : A ≠ U) (hAW : A ≠ W) (hn : ¬Between U A W) :
    Between A U p ∨ Between A W p := by
  have hp : p ∈ a := OrderCore.mem_of_between h hU hW
  obtain ⟨f, he, hf⟩ := line_pos a ![U, W, p, A]
    (by intro i; fin_cases i <;> first | exact hU | exact hW | exact hp | exact hA)
  have e1 := (hf 0 2 1).1 h
  have n1 : f 3 ≠ f 0 := fun e => hAU ((he 3 0).1 e)
  have n2 : f 3 ≠ f 1 := fun e => hAW ((he 3 1).1 e)
  have m1 := mt (hf 0 3 1).2 hn
  by_cases h' : (f 3 < f 0 ∧ f 0 < f 2) ∨ (f 2 < f 0 ∧ f 0 < f 3)
  · exact Or.inl ((hf 3 0 2).2 h')
  · exact Or.inr ((hf 3 1 2).2 (by omega))

/-! ### Properties holding near a point on a segment -/

theorem Near.and {M N : P} {φ ψ : P → Prop} (h1 : Near M N φ) (h2 : Near M N ψ) :
    Near M N (fun p => φ p ∧ ψ p) := by
  obtain ⟨N1, hN1, h1⟩ := h1
  obtain ⟨N2, hN2, h2⟩ := h2
  by_cases he : N1 = N2
  · subst he
    exact ⟨N1, hN1, fun p hp => ⟨h1 p hp, h2 p hp⟩⟩
  rcases between_cases hN1 hN2 he with h | h
  · refine ⟨N1, hN1, fun p hp => ⟨h1 p hp, h2 p ?_⟩⟩
    rcases hp with hp | hp
    · rw [hp]; exact Or.inr h
    · exact Or.inr (OrderLin.trans₂ hp h).1
  · refine ⟨N2, hN2, fun p hp => ⟨h1 p ?_, h2 p hp⟩⟩
    rcases hp with hp | hp
    · rw [hp]; exact Or.inr h
    · exact Or.inr (OrderLin.trans₂ hp h).1

/-- All points near `M` on the segment `MN` lie between `M` and `N`. -/
theorem Near.self {M N : P} (h : M ≠ N) : Near M N (fun p => Between M p N) := by
  obtain ⟨N', hN'⟩ := exists_between (Line := L) h
  refine ⟨N', hN', fun p hp => ?_⟩
  rcases hp with hp | hp
  · rw [hp]; exact hN'
  · exact (OrderLin.trans₂ hp hN').1

theorem Near.forall_fin {ι : Type*} [Fintype ι] {M N : P} (hMN : M ≠ N) {φ : ι → P → Prop}
    (h : ∀ i, Near M N (φ i)) : Near M N (fun p => ∀ i, φ i p) := by
  classical
  have key : ∀ s : Finset ι, Near M N (fun p => ∀ i ∈ s, φ i p) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact (Near.self (L := L) hMN).mono fun p _ i hi => by simp at hi
    | insert a s ha ih =>
      refine ((h a).and ih).mono fun p hp i hi => ?_
      rcases Finset.mem_insert.1 hi with hi | hi
      · rw [hi]; exact hp.1
      · exact hp.2 i hi
  exact (key Finset.univ).mono fun p hp i => hp i (Finset.mem_univ i)

/-- A property failing for at most one point of the line `MN` holds near `M`. -/
theorem Near.of_unique {a : L} {M N : P} {φ : P → Prop} (hM : M ∈ a) (hN : N ∈ a) (hMN : M ≠ N)
    (h : ∀ p q, p ∈ a → q ∈ a → ¬φ p → ¬φ q → p = q) : Near M N φ := by
  by_cases hex : ∃ B, Between M B N ∧ ¬φ B
  · obtain ⟨B, hB, hφB⟩ := hex
    have hBa : B ∈ a := OrderCore.mem_of_between hB hM hN
    obtain ⟨N', hN'⟩ := exists_between (Line := L) (ne12_of_between (Line := L) hB)
    refine ⟨N', (OrderLin.trans₂ hN' hB).1, fun p hp => ?_⟩
    have hpB : Between M p B := by
      rcases hp with hp | hp
      · rw [hp]; exact hN'
      · exact (OrderLin.trans₂ hp hN').1
    by_contra hφp
    exact ne23_of_between (Line := L) hpB
      (h p B (OrderCore.mem_of_between hpB hM hBa) hBa hφp hφB)
  · obtain ⟨N', hN'⟩ := exists_between (Line := L) hMN
    refine ⟨N', hN', fun p hp => ?_⟩
    have hpN : Between M p N := by
      rcases hp with hp | hp
      · rw [hp]; exact hN'
      · exact (OrderLin.trans₂ hp hN').1
    by_contra hφp
    exact hex ⟨p, hpN, hφp⟩

/-! ### Closed segments -/

theorem CSeg.symm {A B X : P} (h : CSeg A B X) : CSeg B A X := by
  rcases h with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (between_symm (Line := L) h))

theorem CSeg.mem_line {a : L} {A B X : P} (h : CSeg A B X) (hA : A ∈ a) (hB : B ∈ a) : X ∈ a := by
  rcases h with h | h | h
  · rw [h]; exact hA
  · rw [h]; exact hB
  · exact OrderCore.mem_of_between h hA hB

omit hO in
theorem not_cseg_of_sameSide {t : L} {U V p : P} (h : SameSide t U V) (hp : p ∈ t) :
    ¬CSeg U V p := by
  rintro (e | e | e)
  · exact h.1 (e ▸ hp)
  · exact h.2.1 (e ▸ hp)
  · exact h.2.2 ⟨p, hp, e⟩

/-- A point off a closed segment `UV` has, on every segment `MN` issuing from it, a neighbourhood
free of points of `UV`. -/
theorem near_not_cseg {M N U V : P} (hMN : M ≠ N) (hM : ¬CSeg U V M) :
    Near M N (fun p => ¬CSeg U V p) := by
  obtain ⟨h, hMh, hNh⟩ := exists_line (Line := L) hMN
  by_cases hc : U ∈ h ∧ V ∈ h
  · obtain ⟨hUh, hVh⟩ := hc
    have hU1 : Near M N (fun p => p ≠ U) :=
      Near.of_unique hMh hNh hMN fun p q _ _ hp hq => (not_not.1 hp).trans (not_not.1 hq).symm
    have hV1 : Near M N (fun p => p ≠ V) :=
      Near.of_unique hMh hNh hMN fun p q _ _ hp hq => (not_not.1 hp).trans (not_not.1 hq).symm
    obtain ⟨N', hN', hN'p⟩ := hU1.and hV1
    refine ⟨N', hN', fun p hp => ?_⟩
    have hN'h : N' ∈ h := OrderCore.mem_of_between hN' hMh hNh
    have hph : p ∈ h := by
      rcases hp with hp | hp
      · rw [hp]; exact hN'h
      · exact OrderCore.mem_of_between hp hMh hN'h
    rintro (e | e | e)
    · exact (hN'p p hp).1 e
    · exact (hN'p p hp).2 e
    · obtain ⟨f, he, hf⟩ := line_pos h ![M, N', U, V, p]
        (by intro i; fin_cases i <;>
          first | exact hMh | exact hN'h | exact hUh | exact hVh | exact hph)
      have e1 := (hf 2 4 3).1 e
      have n1 : f 2 ≠ f 1 := fun e' => (hN'p N' (Or.inl rfl)).1 ((he 2 1).1 e').symm
      have n2 : f 3 ≠ f 1 := fun e' => (hN'p N' (Or.inl rfl)).2 ((he 3 1).1 e').symm
      have n3 : f 2 ≠ f 0 := fun e' => hM (Or.inl ((he 2 0).1 e').symm)
      have n4 : f 3 ≠ f 0 := fun e' => hM (Or.inr (Or.inl ((he 3 0).1 e').symm))
      have m1 : ¬((f 0 < f 2 ∧ f 2 < f 1) ∨ (f 1 < f 2 ∧ f 2 < f 0)) := fun h' =>
        (hN'p U (Or.inr ((hf 0 2 1).2 h'))).1 rfl
      have m2 : ¬((f 0 < f 3 ∧ f 3 < f 1) ∨ (f 1 < f 3 ∧ f 3 < f 0)) := fun h' =>
        (hN'p V (Or.inr ((hf 0 3 1).2 h'))).2 rfl
      have m3 := mt (hf 2 0 3).2 (fun h' => hM (Or.inr (Or.inr h')))
      have e0 := (hf 0 1 0).1
      have hMN' : f 0 ≠ f 1 := fun e' => ne12_of_between (Line := L) hN' ((he 0 1).1 e')
      rcases hp with hp | hp
      · have e4 : f 4 = f 1 := (he 4 1).2 hp
        omega
      · have e4 := (hf 0 4 1).1 hp
        omega
  · refine Near.of_unique hMh hNh hMN fun p q hp hq hp' hq' => ?_
    by_contra hpq
    have hp' := not_not.1 hp'
    have hq' := not_not.1 hq'
    have hUV : U ≠ V := by
      rintro rfl
      have e1 : p = U := by
        rcases hp' with e | e | e
        · exact e
        · exact e
        · exact absurd rfl (ne13_of_between (Line := L) e)
      have e2 : q = U := by
        rcases hq' with e | e | e
        · exact e
        · exact e
        · exact absurd rfl (ne13_of_between (Line := L) e)
      exact hpq (e1.trans e2.symm)
    obtain ⟨k, hUk, hVk⟩ := exists_line (Line := L) hUV
    have hkh : k = h := line_unique hpq (hp'.mem_line hUk hVk) (hq'.mem_line hUk hVk) hp hq
    exact hc ⟨hkh ▸ hUk, hkh ▸ hVk⟩

/-! ### Sides of a line -/

/-- Two points with a point of `l` between them, one of them off `l`, lie on opposite sides. -/
theorem opp_of_between_mem {l : L} {A X B : P} (hX : X ∈ l) (hA : A ∉ l) (h : Between A X B) :
    OppositeSides l A B :=
  ⟨hA, fun hB => hA (OrderCore.mem_of_between'' h hX hB), X, hX, h⟩

/-- The complement of an open half-plane is convex. -/
theorem not_sameSide_of_between {g : L} {A U V p : P} (hU : ¬SameSide g A U)
    (hV : ¬SameSide g A V) (h : Between U p V) : ¬SameSide g A p := by
  intro hp
  have hpg : p ∉ g := hp.2.1
  have hAg : A ∉ g := hp.1
  by_cases hUg : U ∈ g
  · have hVg : V ∉ g := fun hVg => hpg (OrderCore.mem_of_between h hUg hVg)
    exact hV (OrderCore.sameSide_trans hp (sameSide_of_between_mem hUg hVg h))
  have hpU : OppositeSides g p U := by
    rcases OrderCore.sameSide_or_opp hAg hUg with h' | h'
    · exact absurd h' hU
    · exact OrderCore.opp_of_sameSide_opp (OrderCore.sameSide_symm hp) h'
  by_cases hVg : V ∈ g
  · exact OrderCore.not_sameSide_of_opp hpU
      (sameSide_of_between_mem hVg hUg (between_symm (Line := L) h))
  have hpV : OppositeSides g p V := by
    rcases OrderCore.sameSide_or_opp hAg hVg with h' | h'
    · exact absurd h' hV
    · exact OrderCore.opp_of_sameSide_opp (OrderCore.sameSide_symm hp) h'
  have hUV : SameSide g U V := OrderCore.sameSide_of_opp_opp (OrderCore.opp_symm hpU) hpV
  exact OrderCore.not_sameSide_of_opp (OrderCore.opp_symm hpU) (sameSide_of_between hUV h)

/-- **Crossbar theorem**: a line through the vertex `T` of the angle `ZTU` and a point `A₁` inside
the angle separates `Z` and `U`. -/
theorem crossbar_opp {Z T U A₁ : P} {g b t : L} (hZg : Z ∈ g) (hTg : T ∈ g) (hTb : T ∈ b)
    (hUb : U ∈ b) (hZT : Z ≠ T) (hU : U ∉ g) (h1 : SameSide g A₁ U) (h2 : SameSide b A₁ Z)
    (hTt : T ∈ t) (hAt : A₁ ∈ t) : OppositeSides t Z U := by
  have hZb : Z ∉ b := h2.2.1
  have hAg : A₁ ∉ g := h1.1
  have hAb : A₁ ∉ b := h2.1
  have htg : t ≠ g := fun e => hAg (e ▸ hAt)
  have htb : t ≠ b := fun e => hAb (e ▸ hAt)
  have hUT : U ≠ T := fun e => hU (e ▸ hTg)
  have hZt : Z ∉ t := fun hZt => htg (line_unique hZT hZt hTt hZg hTg)
  have hUt : U ∉ t := fun hUt => htb (line_unique hUT hUt hTt hUb hTb)
  obtain ⟨Z', hZ'⟩ := exists_beyond (Line := L) hZT
  have hZ'g : Z' ∈ g := OrderCore.mem_of_between' hZ' hZg hTg
  have hTZ' : T ≠ Z' := ne23_of_between (Line := L) hZ'
  have hZ't : Z' ∉ t := fun h => htg (line_unique hTZ' hTt h hTg hZ'g)
  have hbg : b ≠ g := fun e => hU (e ▸ hUb)
  have hZ'b : Z' ∉ b := fun h => hbg (line_unique hTZ' hTb h hTg hZ'g)
  have hnc : ¬Collinear Z Z' U :=
    not_collinear_of_not_mem hZg hZ'g (ne13_of_between (Line := L) hZ') hU
  rcases OrderCore.pasch hnc hZt hZ't hUt hTt hZ' with ⟨Y, hYt, hY⟩ | ⟨Y, hYt, hY⟩
  · exfalso
    have hYg : SameSide g Y U := sameSide_of_between_mem hZ'g hU hY
    have hYb : SameSide b Y Z' := sameSide_of_between_mem hUb hZ'b (between_symm (Line := L) hY)
    have hZZ' : OppositeSides b Z' Z := ⟨hZ'b, hZb, T, hTb, between_symm (Line := L) hZ'⟩
    have hYZ : OppositeSides b Y Z := OrderCore.opp_of_sameSide_opp hYb hZZ'
    have hAY : OppositeSides b A₁ Y := OrderCore.opp_of_sameSide_opp h2 (OrderCore.opp_symm hYZ)
    obtain ⟨-, -, W, hWb, hW⟩ := hAY
    have hWt : W ∈ t := OrderCore.mem_of_between hW hAt hYt
    have hWT : W = T := eq_of_mem_of_mem htb hWt hWb hTt hTb
    rw [hWT] at hW
    exact (OrderCore.sameSide_trans h1 (OrderCore.sameSide_symm hYg)).2.2 ⟨T, hTg, hW⟩
  · exact ⟨hZt, hUt, Y, hYt, hY⟩

/-! ### A line with a given finite set of points on one side -/

/-- A finite set of points of a line lies between two points of the line. -/
theorem exists_bounds (ℓ : L) (s : Finset P) (hs : ∀ x ∈ s, x ∈ ℓ) :
    ∃ A B : P, A ∈ ℓ ∧ B ∈ ℓ ∧ A ≠ B ∧ ∀ x ∈ s, Between A x B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨A, B, hAB, hA, hB⟩ := exists_two_points (Point := P) ℓ
    exact ⟨A, B, hA, hB, hAB, fun x hx => by simp at hx⟩
  | insert y s hy ih =>
    obtain ⟨A, B, hA, hB, hAB, hbet⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
    have hyl : y ∈ ℓ := hs y (Finset.mem_insert_self y s)
    -- the cases `y` beyond `A` and `y` beyond `B`
    have left : (y = A ∨ Between y A B) →
        ∃ A B : P, A ∈ ℓ ∧ B ∈ ℓ ∧ A ≠ B ∧ ∀ x ∈ insert y s, Between A x B := by
      intro hyA
      have hBy : B ≠ y := by
        rcases hyA with e | e
        · rw [e]; exact hAB.symm
        · exact (ne13_of_between (Line := L) e).symm
      obtain ⟨A', hA'⟩ := exists_beyond (Line := L) hBy
      have hA'l : A' ∈ ℓ := OrderCore.mem_of_between' hA' hB hyl
      refine ⟨A', B, hA'l, hB, (ne13_of_between (Line := L) hA').symm, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with e | hx
      · rw [e]; exact between_symm (Line := L) hA'
      · have hBxA : Between B x A := between_symm (Line := L) (hbet x hx)
        have hBxy : Between B x y := by
          rcases hyA with e | e
          · rw [e]; exact hBxA
          · exact (OrderLin.trans₂ hBxA (between_symm (Line := L) e)).1
        exact between_symm (Line := L) (OrderLin.trans₂ hBxy hA').1
    have right : (y = B ∨ Between A B y) →
        ∃ A B : P, A ∈ ℓ ∧ B ∈ ℓ ∧ A ≠ B ∧ ∀ x ∈ insert y s, Between A x B := by
      intro hyB
      have hAy : A ≠ y := by
        rcases hyB with e | e
        · rw [e]; exact hAB
        · exact ne13_of_between (Line := L) e
      obtain ⟨B', hB'⟩ := exists_beyond (Line := L) hAy
      have hB'l : B' ∈ ℓ := OrderCore.mem_of_between' hB' hA hyl
      refine ⟨A, B', hA, hB'l, ne13_of_between (Line := L) hB', fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with e | hx
      · rw [e]; exact hB'
      · have hAxB : Between A x B := hbet x hx
        have hAxy : Between A x y := by
          rcases hyB with e | e
          · rw [e]; exact hAxB
          · exact (OrderLin.trans₂ hAxB e).1
        exact (OrderLin.trans₂ hAxy hB').1
    by_cases hyA : y = A
    · exact left (Or.inl hyA)
    by_cases hyB : y = B
    · exact right (Or.inl hyB)
    rcases between_trichotomy (Line := L) (collinear_of_mem hyl hA hB) hyA hyB hAB with h | h | h
    · refine ⟨A, B, hA, hB, hAB, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with e | hx
      · rw [e]; exact h
      · exact hbet x hx
    · exact left (Or.inr h)
    · exact right (Or.inr (between_symm (Line := L) h))

/-- The points of the angle `AQB` (beyond the segment `AB`, seen from `Q`) lie on the side of `Q`
of a line joining a point beyond `Q` on `AQ` with a point beyond `Q` on `BQ`. -/
theorem cone_sameSide {ℓ n : L} {A B Q A' B' x p : P} (hA : A ∈ ℓ) (hB : B ∈ ℓ) (hAB : A ≠ B)
    (hQ : Q ∉ ℓ) (hA' : Between A Q A') (hB' : Between B Q B') (hA'n : A' ∈ n) (hB'n : B' ∈ n)
    (hAxB : Between A x B) (hQxp : Between Q x p) : SameSide n Q p := by
  have hQA : Q ≠ A := fun e => hQ (e ▸ hA)
  have hQB : Q ≠ B := fun e => hQ (e ▸ hB)
  obtain ⟨a, hQa, hAa⟩ := exists_line (Line := L) hQA
  obtain ⟨b, hQb, hBb⟩ := exists_line (Line := L) hQB
  have hA'a : A' ∈ a := OrderCore.mem_of_between' hA' hAa hQa
  have hB'b : B' ∈ b := OrderCore.mem_of_between' hB' hBb hQb
  have haℓ : a ≠ ℓ := fun e => hQ (e ▸ hQa)
  have hbℓ : b ≠ ℓ := fun e => hQ (e ▸ hQb)
  have hBa : B ∉ a := fun h => haℓ (line_unique hAB hAa h hA hB)
  have hAb : A ∉ b := fun h => hbℓ (line_unique hAB h hBb hA hB)
  have hab : a ≠ b := fun e => hBa (e ▸ hBb)
  have hQA' : Q ≠ A' := ne23_of_between (Line := L) hA'
  have hQB' : Q ≠ B' := ne23_of_between (Line := L) hB'
  have hA'b : A' ∉ b := fun h => hab (line_unique hQA' hQa hA'a hQb h)
  have hB'a : B' ∉ a := fun h => hab (line_unique hQB' hQa h hQb hB'b)
  have han : a ≠ n := fun e => hB'a (e ▸ hB'n)
  have hbn : b ≠ n := fun e => hA'b (e ▸ hA'n)
  have hQn : Q ∉ n := fun h => han (line_unique hQA' hQa hA'a h hA'n)
  have hxa : SameSide a x B := sameSide_of_between_mem hAa hBa hAxB
  have hxb : SameSide b x A := sameSide_of_between_mem hBb hAb (between_symm (Line := L) hAxB)
  have hpa' : p ∉ a := fun h => hxa.1 (OrderCore.mem_of_between hQxp hQa h)
  have hpb' : p ∉ b := fun h => hxb.1 (OrderCore.mem_of_between hQxp hQb h)
  have hpa : SameSide a p B :=
    OrderCore.sameSide_trans (OrderCore.sameSide_symm (sameSide_of_between_mem hQa hpa' hQxp)) hxa
  have hpb : SameSide b p A :=
    OrderCore.sameSide_trans (OrderCore.sameSide_symm (sameSide_of_between_mem hQb hpb' hQxp)) hxb
  have hBB' : OppositeSides a B B' := ⟨hBa, hB'a, Q, hQa, hB'⟩
  have hAA' : OppositeSides b A A' := ⟨hAb, hA'b, Q, hQb, hA'⟩
  have key : ∀ Z, Z ∈ n → (Z = p ∨ Between Q Z p) → False := by
    intro Z hZn hZ
    have hZa : SameSide a Z p := by
      rcases hZ with e | e
      · rw [e]; exact OrderCore.sameSide_refl hpa'
      · exact sameSide_of_between_mem hQa hpa' e
    have hZb : SameSide b Z p := by
      rcases hZ with e | e
      · rw [e]; exact OrderCore.sameSide_refl hpb'
      · exact sameSide_of_between_mem hQb hpb' e
    obtain ⟨-, -, W, hWa, hW⟩ :=
      OrderCore.opp_of_sameSide_opp (OrderCore.sameSide_trans hZa hpa) hBB'
    obtain ⟨-, -, W', hW'b, hW'⟩ :=
      OrderCore.opp_of_sameSide_opp (OrderCore.sameSide_trans hZb hpb) hAA'
    have e1 : W = A' :=
      eq_of_mem_of_mem han hWa (OrderCore.mem_of_between hW hZn hB'n) hA'a hA'n
    have e2 : W' = B' :=
      eq_of_mem_of_mem hbn hW'b (OrderCore.mem_of_between hW' hZn hA'n) hB'b hB'n
    rw [e1] at hW
    rw [e2] at hW'
    exact not_between_swap23 (Line := L) hW hW'
  exact ⟨hQn, fun h => key p h (Or.inl rfl), fun ⟨Z, hZn, hZ⟩ => key Z hZn (Or.inr hZ)⟩

/-- **Every finite set of points lies on one side of some line** (I, II): there are a line `ℓ` and a
point `O` off it such that all points of the set are on the side of `O`. (Two distinct points are
given, so that there is a line at all.) -/
theorem exists_line_sameSide {A₀ B₀ : P} (h₀ : A₀ ≠ B₀) (s : Finset P) :
    ∃ (ℓ : L) (O : P), O ∉ ℓ ∧ ∀ p ∈ s, SameSide ℓ O p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨ℓ, -, -⟩ := exists_line (Line := L) h₀
    obtain ⟨O, hO⟩ := exists_not_mem (P := P) ℓ
    exact ⟨ℓ, O, hO, fun p hp => by simp at hp⟩
  | insert q s hq ih =>
    obtain ⟨ℓ, O, hOℓ, hs⟩ := ih
    by_cases hqs : SameSide ℓ O q
    · refine ⟨ℓ, O, hOℓ, fun p hp => ?_⟩
      rcases Finset.mem_insert.1 hp with e | hp
      · rw [e]; exact hqs
      · exact hs p hp
    have hOq : O ≠ q := fun e => hqs (e ▸ OrderCore.sameSide_refl hOℓ)
    obtain ⟨Q, hOqQ⟩ := exists_beyond (Line := L) hOq
    have hOQ : OppositeSides ℓ O Q := by
      by_cases hqℓ : q ∈ ℓ
      · exact opp_of_between_mem hqℓ hOℓ hOqQ
      · rcases OrderCore.sameSide_or_opp hOℓ hqℓ with h | h
        · exact absurd h hqs
        · obtain ⟨-, -, x, hx, hOxq⟩ := h
          exact opp_of_between_mem hx hOℓ (OrderLin.trans₂ hOxq hOqQ).1
    have hQℓ : Q ∉ ℓ := hOQ.2.1
    have hex : ∀ p, p ∈ insert O s → ∃ x, x ∈ ℓ ∧ Between Q x p := by
      intro p hp
      have hpQ : OppositeSides ℓ p Q := by
        rcases Finset.mem_insert.1 hp with e | hp
        · rw [e]; exact hOQ
        · exact OrderCore.opp_of_sameSide_opp (OrderCore.sameSide_symm (hs p hp)) hOQ
      obtain ⟨-, -, x, hx, hpxQ⟩ := hpQ
      exact ⟨x, hx, between_symm (Line := L) hpxQ⟩
    have : Nonempty P := ⟨O⟩
    choose! x hxℓ hxb using hex
    obtain ⟨A, B, hA, hB, hAB, hbet⟩ := exists_bounds ℓ ((insert O s).image x) (by
      intro y hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hy
      exact hxℓ p hp)
    have hAQ : A ≠ Q := fun e => hQℓ (e ▸ hA)
    have hBQ : B ≠ Q := fun e => hQℓ (e ▸ hB)
    obtain ⟨A', hA'⟩ := exists_beyond (Line := L) hAQ
    obtain ⟨B', hB'⟩ := exists_beyond (Line := L) hBQ
    have hA'B' : A' ≠ B' := by
      intro e
      rw [← e] at hB'
      obtain ⟨a, hAa, hQa, hA'a⟩ := collinear_of_between (Line := L) hA'
      have hBa : B ∈ a := OrderCore.mem_of_between'' hB' hQa hA'a
      exact hQℓ ((line_unique hAB hAa hBa hA hB) ▸ hQa)
    obtain ⟨n, hA'n, hB'n⟩ := exists_line (Line := L) hA'B'
    have hcone : ∀ p, p ∈ insert O s → SameSide n Q p := fun p hp =>
      cone_sameSide hA hB hAB hQℓ hA' hB' hA'n hB'n
        (hbet (x p) (Finset.mem_image_of_mem x hp)) (hxb p hp)
    have hQO : SameSide n Q O := hcone O (Finset.mem_insert_self O s)
    refine ⟨n, Q, hQO.1, fun p hp => ?_⟩
    rcases Finset.mem_insert.1 hp with e | hp
    · rw [e]
      exact sameSide_of_between hQO (between_symm (Line := L) hOqQ)
    · exact hcone p (Finset.mem_insert_of_mem hp)

end PolyJordan

end HilbertFoundations
