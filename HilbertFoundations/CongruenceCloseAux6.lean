import HilbertFoundations.CongruenceCloseAux4

/-!
# Helper module for `CongruenceClose.lean`: Theorem 18 on a line

This module contains no unit of Hilbert's text. The existence clause of Theorem 18 in a space
geometry (groups I, II, IV) without planes, where all points lie on one line:

* `Frame.theorem17_line`: Theorem 17 for two figures on lines and a new point of the first line
  (the linear case of `Frame.theorem17_two`, which needs no plane);
* `theorem18_exists_noPlane`: the existence clause of Theorem 18 when there is no plane;
* `theorem18_exists_all`: the existence clause of Theorem 18 in every space geometry.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v w

namespace Frame

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hT : TriangleCongruence P L] (F : Frame P L)
include hT F

/-- **Theorem 17 on a line**: figures on the lines `l`, `l'` with congruent corresponding segments,
having at least two points, and a new point `Q` of `l`. -/
theorem theorem17_line {n : ℕ} {f g : Fin n → P} {l l' : L} (hfl : ∀ i, f i ∈ l)
    (hgl : ∀ i, g i ∈ l') (hfi : Function.Injective f) (hgi : Function.Injective g)
    (hseg : ∀ i j, i ≠ j → SegCong (f i) (f j) (g i) (g j)) {a0 b0 : Fin n} (hab : a0 ≠ b0)
    {Q : P} (hQl : Q ∈ l) (hQf : ∀ i, Q ≠ f i) :
    ∃ Q', Q' ∈ l' ∧ (∀ i, Q' ≠ g i) ∧ ∀ i, SegCong (f i) Q (g i) Q' := by
  have hAB : f a0 ≠ f b0 := hfi.ne hab
  have hA'B' : g a0 ≠ g b0 := hgi.ne hab
  have hAl := hfl a0
  have hBl := hfl b0
  have hA'l := hgl a0
  have hB'l := hgl b0
  have sym : ∀ i j, i ≠ j → SegCong (g i) (g j) (f i) (f j) := fun i j h =>
    segCong_symm (L := L) (hfi.ne h) (hgi.ne h) (hseg i j h)
  -- the half-ray from `A` is preserved
  have rayc : ∀ k, k ≠ a0 → (f k ∈ ray (f a0) (f b0) ↔ g k ∈ ray (g a0) (g b0)) := by
    intro k hka
    have hk := hfl k
    have hk' := hgl k
    by_cases hkb : k = b0
    · subst hkb
      exact ⟨fun _ => mem_ray_self' (L := L) hA'B'.symm, fun _ => mem_ray_self' (L := L) hAB.symm⟩
    have iff1 : ∀ {O A X : P} {m : L}, O ∈ m → A ∈ m → X ∈ m → A ≠ O → X ≠ O →
        (X ∈ ray O A ↔ ¬Between A O X) := fun hO hA hX hAO hXO =>
      ⟨fun h => h.2.2.2, fun h => (mem_ray_or_between (L := L) (collinear_of_mem hO hA hX) hAO
        hXO).resolve_right h⟩
    rw [iff1 hAl hBl hk hAB.symm (hfi.ne hka), iff1 hA'l hB'l hk' hA'B'.symm (hgi.ne hka)]
    constructor
    · intro h h'
      exact h (between_of_segCong h' (collinear_of_mem hBl hAl hk) hAB.symm (hfi.ne (Ne.symm hka))
        (hfi.ne (Ne.symm hkb)) (sym b0 a0 (Ne.symm hab)) (sym a0 k (Ne.symm hka))
        (sym b0 k (Ne.symm hkb)))
    · intro h h'
      exact h (between_of_segCong h' (collinear_of_mem hB'l hA'l hk') hA'B'.symm
        (hgi.ne (Ne.symm hka)) (hgi.ne (Ne.symm hkb)) (hseg b0 a0 (Ne.symm hab))
        (hseg a0 k (Ne.symm hka)) (hseg b0 k (Ne.symm hkb)))
  have hQA : Q ≠ f a0 := hQf a0
  -- lay off `AQ` on the corresponding half-ray of `A'B'`
  obtain ⟨Q', hQ'l, hQ'A, hQ'c, hQ'r⟩ : ∃ Q', Q' ∈ l' ∧ Q' ≠ g a0 ∧
      SegCong (f a0) Q (g a0) Q' ∧ (Q ∈ ray (f a0) (f b0) ↔ Q' ∈ ray (g a0) (g b0)) := by
    by_cases hr : Q ∈ ray (f a0) (f b0)
    · obtain ⟨Q', h1, h2⟩ := segCong_layoff (L := L) hQA.symm hA'B'
      exact ⟨Q', mem_of_collinear (collinear_of_mem_ray h1) hA'B' hA'l hB'l, ne_of_mem_ray h1,
        h2, ⟨fun _ => h1, fun _ => hr⟩⟩
    · obtain ⟨Bs, hBs⟩ := exists_beyond (Line := L) hA'B'.symm
      obtain ⟨Q', h1, h2⟩ := segCong_layoff (L := L) hQA.symm (ne23_of_between hBs)
      have hBsl : Bs ∈ l' := mem_right_of_between hBs hB'l hA'l
      have hnr : Q' ∉ ray (g a0) (g b0) := not_mem_ray_of_between
        (between_of_mem_rays hBs (mem_ray_self' (L := L) hA'B'.symm) h1)
      exact ⟨Q', mem_of_collinear (collinear_of_mem_ray h1) (ne23_of_between hBs) hA'l hBsl,
        ne_of_mem_ray h1, h2, ⟨fun h => absurd h hr, fun h => absurd h hnr⟩⟩
  have posc : ∀ i, i ≠ a0 → (f i ∈ ray (f a0) Q ↔ g i ∈ ray (g a0) Q') := by
    intro i hia
    have p1 := F.ray_iff_of_rays hAl hBl (hfl i) hQl hAB.symm (hfi.ne hia) hQA
    have p2 := F.ray_iff_of_rays hA'l hB'l (hgl i) hQ'l hA'B'.symm (hgi.ne hia) hQ'A
    exact p1.trans ((iff_congr (rayc i hia) hQ'r).trans p2.symm)
  refine ⟨Q', hQ'l, ?_, ?_⟩
  · intro i e
    by_cases hia : i = a0
    · subst hia; exact hQ'A e
    have hfr : f i ∈ ray (f a0) Q := (posc i hia).2 (by
      rw [← e]; exact mem_ray_self' (L := L) hQ'A)
    have hc := hQ'c
    rw [e] at hc
    have ee := eq_of_segCong_ray (L := L) (hgi.ne (Ne.symm hia)) hfr
      (mem_ray_self' (L := L) hQA) (sym a0 i (Ne.symm hia))
      (segCong_symm (L := L) hQA.symm (hgi.ne (Ne.symm hia)) hc)
    exact hQf i ee.symm
  · intro i
    by_cases hia : i = a0
    · subst hia; exact hQ'c
    exact seg_on_line (hseg a0 i (Ne.symm hia)) hQ'c (hfi.ne hia) hQA (hgi.ne hia) hQ'A
      (collinear_of_mem hAl hQl (hfl i)) (collinear_of_mem hA'l hQ'l (hgl i))
      (hQf i).symm (posc i hia)

end Frame

section NoPlane

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [HasSegCong P] [HasAngCong P] [hSC : SpaceCongruence P L Pl] {n : ℕ} {f g : Fin n → P}
include hSC

local notation "𝔽" => (spaceFrame (P := P) (L := L) (Pl := Pl))

/-- **Theorem 18, existence, in a space geometry without planes** (all points on a line). -/
theorem theorem18_exists_noPlane [IsEmpty Pl] (hc : CongruentFigures (L := L) f g) {Q : P}
    (hQ : Q ∉ Set.range f) :
    ∃ Q', CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q') := by
  have col : ∀ A B C : P, Collinear (Line := L) A B C := by
    intro A B C
    by_contra h
    obtain ⟨α, -⟩ := exists_plane (Plane := Pl) h
    exact isEmptyElim α
  obtain ⟨l, hl⟩ := line_of_collinear (Pl := Pl) (Fin.snoc f Q : Fin (n + 1) → P)
    (fun a b c => col _ _ _)
  obtain ⟨l', hl'⟩ := line_of_collinear (Pl := Pl) g (fun a b c => col _ _ _)
  have hfl : ∀ i, f i ∈ l := fun i => by
    have := hl (Fin.castSucc i); rwa [Fin.snoc_castSucc] at this
  have hQl : Q ∈ l := by
    have := hl (Fin.last n); rwa [Fin.snoc_last] at this
  have hQf : ∀ i, Q ≠ f i := fun i e => hQ ⟨i, e.symm⟩
  by_cases h2 : ∃ a0 b0 : Fin n, a0 ≠ b0
  · obtain ⟨a0, b0, hab⟩ := h2
    obtain ⟨Q', -, h1, h2⟩ := (𝔽).theorem17_line hfl hl' hc.1 hc.2.1 hc.2.2.1 hab hQl hQf
    exact ⟨Q', congruentFigures_snoc 𝔽 hc hQ (fun ⟨i, hi⟩ => h1 i hi.symm) h2⟩
  · push Not at h2
    rcases isEmpty_or_nonempty (Fin n) with he | ⟨⟨i₀⟩⟩
    · exact ⟨Q, congruentFigures_snoc 𝔽 hc hQ (fun ⟨i, _⟩ => he.elim i) (fun i => he.elim i)⟩
    · obtain ⟨m, hm⟩ := line_through_space (L := L) (Pl := Pl) (g i₀)
      obtain ⟨U, V, hUV, -, -⟩ := exists_two_points (Point := P) m
      obtain ⟨C', hC'⟩ : ∃ C' : P, g i₀ ≠ C' := by
        by_cases hU : g i₀ = U
        · exact ⟨V, fun e => hUV (hU.symm.trans e)⟩
        · exact ⟨U, hU⟩
      obtain ⟨Q', hQ'r, hQ's⟩ := segCong_layoff (L := L) (hQf i₀).symm hC'
      have hQ'g : Q' ∉ Set.range g := by
        rintro ⟨i, hi⟩
        rw [h2 i i₀] at hi
        exact ne_of_mem_ray hQ'r hi.symm
      exact ⟨Q', congruentFigures_snoc 𝔽 hc hQ hQ'g (fun i => by rw [h2 i i₀]; exact hQ's)⟩

/-- **Theorem 18, existence**, in every space geometry with groups I, II, IV. -/
theorem theorem18_exists_all (hc : CongruentFigures (L := L) f g) {Q : P}
    (hQ : Q ∉ Set.range f) :
    ∃ Q', CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q') := by
  rcases isEmpty_or_nonempty Pl with h | h
  · exact theorem18_exists_noPlane hc hQ
  · exact theorem18_exists hc hQ

end NoPlane

end HilbertFoundations
