import HilbertFoundations.OrderPolygonAux3

/-!
# Helper module for `OrderPolygon.lean` (Theorem 6), part 4: at most two regions

This module contains no unit of Hilbert's text.

* `vertex_good`: if all points seeing a point within the side `v k v (k+1)` have a property `C`
  invariant under `Conn`, so have all points seeing the vertex `v (k+1)` (walking round a vertex).
* `all_good`: hence, going round the polygon, all points off the polygon have the property, if the
  points seeing one point within the side `v n v 0` have it.
* `two_classes`: there are two points `N₁`, `N₂` off the polygon, of different parities, such that
  every point off the polygon is joined to `N₁` or to `N₂` by a chain of segments off the polygon.
-/

namespace HilbertFoundations

namespace PolyJordan

universe u v

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [hO : PlaneOrder P L]
  {n : ℕ} {v : Fin (n + 1) → P}
include hO

/-- **Round a vertex.** If all points seeing a point within the side `v k v (k+1)` have the
property `C` (invariant under `Conn`), then so have all points seeing the vertex `v (k+1)`. -/
theorem vertex_good (hs : Simple v) {C : P → Prop} (hC : ∀ X Y, Conn v X Y → C Y → C X)
    (k : Fin (n + 1))
    (hgood : ∀ Z, Between (v k) Z (v (k + 1)) → ∀ X, Sees v X Z → C X)
    {W : P} (hW : Sees v W (v (k + 1))) : C W := by
  obtain ⟨g₁, hA₁, hV₁⟩ := exists_line (Line := L) (hs.ne k)
  obtain ⟨g₂, hV₂, hB₂⟩ := exists_line (Line := L) (hs.ne (k + 1))
  have hAB : v k ≠ v (k + 1 + 1) := fun e => fin_add_two_ne hs.two_le k (hs.inj e).symm
  obtain ⟨M₁, hM₁⟩ := exists_between (Line := L) (hs.ne k)
  have hM₁g : M₁ ∈ g₁ := OrderCore.mem_of_between hM₁ hA₁ hV₁
  have hVM : v (k + 1) ≠ M₁ := (ne23_of_between (Line := L) hM₁).symm
  have hVS : OnPoly v (v (k + 1)) := onPoly_vertex v (k + 1)
  have hsides : ∀ j, CSeg (v j) (v (j + 1)) (v (k + 1)) → j = k ∨ j = k + 1 :=
    fun j hj => hs.vertex_sides hj
  -- Case A: `W` sees points of the side `v k v (k+1)` near the vertex
  have caseA : ∀ W, Sees v W (v (k + 1)) → W ∉ g₁ →
      (¬SameSide g₁ W (v (k + 1 + 1)) ∨ SameSide g₂ W (v k)) → C W := by
    intro W hW hWg₁ hcond
    have hVW : v (k + 1) ≠ W := fun e => hWg₁ (e ▸ hV₁)
    obtain ⟨a, hVa, hWa⟩ := exists_line (Line := L) hVW
    have hM₁a : M₁ ∉ a := fun h => by
      have e : a = g₁ := line_unique hVM hVa h hV₁ hM₁g
      exact hWg₁ (e ▸ hWa)
    have hsw := sweep hs hVa hWa hVW hM₁a (by
      intro j r p W' hr hp hr' hW' hpW
      have hW'g : W' ∈ g₁ := OrderCore.mem_of_between hW' hV₁ hM₁g
      have hpg₁ : SameSide g₁ p W :=
        sameSide_of_between_mem hW'g hWg₁ (between_symm (Line := L) hpW)
      have hjk : j = k → False := by
        intro e
        rw [e] at hp
        exact hpg₁.1 (hp.mem_line hA₁ hV₁)
      have hjk1 : j = k + 1 → False := by
        intro e
        rw [e] at hp
        rcases hcond with hc | hc
        · apply hc
          rcases hp with e | e | e
          · exact absurd (e ▸ hV₁) hpg₁.1
          · rw [← e]; exact OrderCore.sameSide_symm hpg₁
          · have hB₁ : v (k + 1 + 1) ∉ g₁ := fun h =>
              hpg₁.1 (OrderCore.mem_of_between e hV₁ h)
            exact OrderCore.sameSide_trans (OrderCore.sameSide_symm hpg₁)
              (sameSide_of_between_mem hV₁ hB₁ e)
        · have hpg₂ : p ∈ g₂ := hp.mem_line hV₂ hB₂
          have hW'2 : SameSide g₂ W' (v k) := sameSide_of_between_mem hV₂ hc.2.1
            (OrderLin.trans₂ hW' (between_symm (Line := L) hM₁)).1
          exact (OrderCore.sameSide_trans hc (OrderCore.sameSide_symm hW'2)).2.2 ⟨p, hpg₂, hpW⟩
      rcases hr' with hr' | hr' | hr'
      · rw [hr'] at hr
        rcases hsides j hr with e | e
        · exact hjk e
        · exact hjk1 e
      · exact hW.2 r (between_symm (Line := L) hr') ⟨j, hr⟩
      · have hrk : Between (v k) r (v (k + 1)) := between_symm (Line := L)
          (OrderLin.trans₂ hr' (between_symm (Line := L) hM₁)).1
        exact hjk (hs.side_unique hrk hr))
    obtain ⟨W', hfree, hW'⟩ := (hsw.and (Near.self (L := L) hVM)).exists
    have hW'k : Between (v k) W' (v (k + 1)) := between_symm (Line := L)
      (OrderLin.trans₂ hW' (between_symm (Line := L) hM₁)).1
    exact hgood W' hW'k W ⟨hW.1, hfree⟩
  -- Case B: `W` is separated from `v k` by the line of the side `v (k+1) v (k+2)`
  have caseB : ∀ W, Sees v W (v (k + 1)) → v (k + 1 + 1) ∉ g₁ → OppositeSides g₂ W (v k) →
      C W := by
    intro W hW hB₁ hopp
    have hA₂ : v k ∉ g₂ := hopp.2.1
    obtain ⟨Y, hY⟩ := exists_between (Line := L) hAB
    have hY₂ : SameSide g₂ Y (v k) :=
      sameSide_of_between_mem hB₂ hA₂ (between_symm (Line := L) hY)
    have hY₁ : SameSide g₁ Y (v (k + 1 + 1)) := sameSide_of_between_mem hA₁ hB₁ hY
    have hYV : Y ≠ v (k + 1) := fun e => hY₁.1 (e ▸ hV₁)
    obtain ⟨T₀, hT₀⟩ := exists_beyond (Line := L) hYV
    have hT₀1 : OppositeSides g₁ Y T₀ := opp_of_between_mem hV₁ hY₁.1 hT₀
    have hT₀2 : OppositeSides g₂ Y T₀ := opp_of_between_mem hV₂ hY₂.1 hT₀
    have hVT₀ : v (k + 1) ≠ T₀ := ne23_of_between (Line := L) hT₀
    have hnf := near_free (v := v) hVT₀ (by
      intro j hj p hp hpc
      rcases hsides j hj with e | e
      · rw [e] at hpc
        exact (sameSide_of_between_mem hV₁ hT₀1.2.1 hp).1 (hpc.mem_line hA₁ hV₁)
      · rw [e] at hpc
        exact (sameSide_of_between_mem hV₂ hT₀2.2.1 hp).1 (hpc.mem_line hV₂ hB₂))
    obtain ⟨T, -, hTall⟩ := hnf.and (Near.self (L := L) hVT₀)
    have hTb : Between (v (k + 1)) T T₀ := (hTall T (Or.inl rfl)).2
    have hTS : Sees v T (v (k + 1)) := ⟨(hTall T (Or.inl rfl)).1, fun p hp =>
      (hTall p (Or.inr (between_symm (Line := L) hp))).1⟩
    have hT1 : SameSide g₁ T T₀ := sameSide_of_between_mem hV₁ hT₀1.2.1 hTb
    have hT2 : SameSide g₂ T T₀ := sameSide_of_between_mem hV₂ hT₀2.2.1 hTb
    have hTY1 : OppositeSides g₁ T Y :=
      OrderCore.opp_of_sameSide_opp hT1 (OrderCore.opp_symm hT₀1)
    have hTY2 : OppositeSides g₂ T Y :=
      OrderCore.opp_of_sameSide_opp hT2 (OrderCore.opp_symm hT₀2)
    have hTB : OppositeSides g₁ T (v (k + 1 + 1)) := OrderCore.opp_symm
      (OrderCore.opp_of_sameSide_opp (OrderCore.sameSide_symm hY₁) (OrderCore.opp_symm hTY1))
    have hTA : OppositeSides g₂ T (v k) := OrderCore.opp_symm
      (OrderCore.opp_of_sameSide_opp (OrderCore.sameSide_symm hY₂) (OrderCore.opp_symm hTY2))
    have hCT : C T := caseA T hTS hT1.1 (Or.inl (OrderCore.not_sameSide_of_opp hTB))
    have hWT : SameSide g₂ W T := OrderCore.sameSide_of_opp_opp hopp (OrderCore.opp_symm hTA)
    refine hC W T (local_conn hs hV₂ hW hTS hWT ?_) hCT
    intro j hj p hpc hsp
    rcases hsides j hj with e | e
    · rw [e] at hpc
      rcases hpc with e | e | e
      · exact OrderCore.not_sameSide_of_opp hopp (e ▸ hsp)
      · exact hsp.2.1 (e ▸ hV₂)
      · have h1 : SameSide g₂ p (v k) :=
          sameSide_of_between_mem hV₂ hA₂ (between_symm (Line := L) e)
        exact OrderCore.not_sameSide_of_opp hopp (OrderCore.sameSide_trans hsp h1)
    · rw [e] at hpc
      exact hsp.2.1 (hpc.mem_line hV₂ hB₂)
  have hseg2 : ∀ p, Between (v (k + 1)) p (v (k + 1 + 1)) → OnPoly v p := fun p hp =>
    ⟨k + 1, Or.inr (Or.inr hp)⟩
  by_cases hWg₁ : W ∈ g₁
  · have hb1 : Between W (v (k + 1)) (v k) :=
      sees_between hW hVS (onPoly_vertex v k) (hs.ne k).symm
        (fun p hp => ⟨k, Or.inr (Or.inr (between_symm (Line := L) hp))⟩)
        (collinear_of_mem hWg₁ hV₁ hA₁)
    have hB₁ : v (k + 1 + 1) ∉ g₁ := by
      intro hB₁
      have hb2 : Between W (v (k + 1)) (v (k + 1 + 1)) :=
        sees_between hW hVS (onPoly_vertex v (k + 1 + 1)) (hs.ne (k + 1)) hseg2
          (collinear_of_mem hWg₁ hV₁ hB₁)
      rcases same_ray_cases hb1 hb2 hAB with h | h
      · exact hs.h3 k (k + 1) h
      · exact hs.h3 (k + 1 + 1) k (between_symm (Line := L) h)
    have hg : g₁ ≠ g₂ := fun e => hB₁ (e ▸ hB₂)
    have hA₂ : v k ∉ g₂ := fun h => hg (line_unique (hs.ne k) hA₁ hV₁ h hV₂)
    have hWg₂ : W ∉ g₂ := fun h => by
      have e : W = v (k + 1) := eq_of_mem_of_mem hg hWg₁ h hV₁ hV₂
      exact hW.1 (e ▸ hVS)
    exact caseB W hW hB₁ ⟨hWg₂, hA₂, v (k + 1), hV₂, hb1⟩
  · by_cases hcond : ¬SameSide g₁ W (v (k + 1 + 1)) ∨ SameSide g₂ W (v k)
    · exact caseA W hW hWg₁ hcond
    · have hs1 : SameSide g₁ W (v (k + 1 + 1)) := not_not.1 fun h => hcond (Or.inl h)
      have ht : ¬SameSide g₂ W (v k) := fun h => hcond (Or.inr h)
      have hB₁ : v (k + 1 + 1) ∉ g₁ := hs1.2.1
      have hg : g₁ ≠ g₂ := fun e => hB₁ (e ▸ hB₂)
      have hA₂ : v k ∉ g₂ := fun h => hg (line_unique (hs.ne k) hA₁ hV₁ h hV₂)
      have hWg₂ : W ∉ g₂ := by
        intro h
        have hb2 : Between W (v (k + 1)) (v (k + 1 + 1)) :=
          sees_between hW hVS (onPoly_vertex v (k + 1 + 1)) (hs.ne (k + 1)) hseg2
            (collinear_of_mem h hV₂ hB₂)
        exact hs1.2.2 ⟨v (k + 1), hV₁, hb2⟩
      rcases OrderCore.sameSide_or_opp hWg₂ hA₂ with h | h
      · exact absurd h ht
      · exact caseB W hW hB₁ h

/-- **Round the polygon.** If all points seeing a point `M` within the side `v n v 0` have the
property `C` (invariant under `Conn`), then all points off the polygon have it. -/
theorem all_good (hs : Simple v) {C : P → Prop} (hC : ∀ X Y, Conn v X Y → C Y → C X)
    {M : P} (hM : Between (v (Fin.last n)) M (v 0)) (hMgood : ∀ X, Sees v X M → C X) :
    ∀ X, ¬OnPoly v X → C X := by
  have hM' : Between (v (Fin.last n)) M (v (Fin.last n + 1)) := by
    rw [Fin.last_add_one]; exact hM
  have side : ∀ k : Fin (n + 1), ∀ Z, Between (v k) Z (v (k + 1)) → ∀ X, Sees v X Z → C X := by
    have step : ∀ k : Fin (n + 1),
        (∀ Z, Between (v k) Z (v (k + 1)) → ∀ X, Sees v X Z → C X) →
        ∀ Z, Between (v (k + 1)) Z (v (k + 1 + 1)) → ∀ X, Sees v X Z → C X := by
      intro k hk Z hZ X hX
      exact good_side hs hC (Or.inl rfl) (fun X hX => vertex_good hs hC k hk hX) hZ hX
    have hlast : ∀ Z, Between (v (Fin.last n)) Z (v (Fin.last n + 1)) →
        ∀ X, Sees v X Z → C X :=
      fun Z hZ X hX => good_side hs hC (Or.inr (Or.inr hM')) hMgood hZ hX
    intro k
    induction k using Fin.induction with
    | zero =>
      have := step (Fin.last n) hlast
      rwa [Fin.last_add_one] at this
    | succ i ih =>
      have := step i.castSucc ih
      rwa [Fin.coeSucc_eq_succ] at this
  intro X hX
  obtain ⟨Z, hZS, hfree⟩ := first_hit hX (onPoly_vertex v 0)
  obtain ⟨i, e | e | e⟩ := hZS
  · have h := vertex_good hs hC (i - 1) (side (i - 1)) (W := X)
    rw [sub_add_cancel] at h
    exact h ⟨hX, by rw [← e]; exact hfree⟩
  · exact vertex_good hs hC i (side i) ⟨hX, by rw [← e]; exact hfree⟩
  · exact side i Z e X ⟨hX, hfree⟩

/-- **At most two regions.** There are two points `N₁`, `N₂` off the polygon, of different
parities, such that every point off the polygon is joined to one of them by a chain of segments
that do not meet the polygon. -/
theorem two_classes (hs : Simple v) {ℓ0 : L} {O : P} (hside : ∀ j, SameSide ℓ0 O (v j)) :
    ∃ N₁ N₂ : P, ¬OnPoly v N₁ ∧ ¬OnPoly v N₂ ∧ par v ℓ0 N₂ = par v ℓ0 N₁ + 1 ∧
      ∀ X, ¬OnPoly v X → Conn v X N₁ ∨ Conn v X N₂ := by
  obtain ⟨M, N₁, N₂, hM, hNMN, hnc, hN₁, hN₂, hf₁, hf₂, hpar⟩ := exists_jump hs hside
  refine ⟨N₁, N₂, hN₁, hN₂, hpar, ?_⟩
  have hM' : Between (v (Fin.last n)) M (v (Fin.last n + 1)) := by
    rw [Fin.last_add_one]; exact hM
  have hne : v (Fin.last n) ≠ v 0 := ne13_of_between (Line := L) hM
  obtain ⟨g, hag, h0g⟩ := exists_line (Line := L) hne
  have h0g' : v (Fin.last n + 1) ∈ g := by rw [Fin.last_add_one]; exact h0g
  have hMg : M ∈ g := OrderCore.mem_of_between hM hag h0g
  have hN₁g : N₁ ∉ g := fun h => hnc ⟨g, hag, h0g, h⟩
  have hopp : OppositeSides g N₁ N₂ := opp_of_between_mem hMg hN₁g hNMN
  refine all_good hs (C := fun X => Conn v X N₁ ∨ Conn v X N₂)
    (fun X Y hXY hY => hY.imp hXY.trans hXY.trans) hM ?_
  intro X hX
  have hXg : X ∉ g := sees_not_mem hM' hag h0g' hX
  have hk : ∀ j, CSeg (v j) (v (j + 1)) M → ∀ p, CSeg (v j) (v (j + 1)) p →
      ¬SameSide g X p := by
    intro j hj p hp hsp
    have e : j = Fin.last n := hs.side_unique hM' hj
    rw [e] at hp
    exact hsp.2.1 (hp.mem_line hag h0g')
  rcases OrderCore.sameSide_or_opp hXg hN₁g with h | h
  · exact Or.inl (local_conn hs hMg hX ⟨hN₁, hf₁⟩ h hk)
  · exact Or.inr (local_conn hs hMg hX ⟨hN₂, hf₂⟩ (OrderCore.sameSide_of_opp_opp h hopp) hk)

end PolyJordan

end HilbertFoundations
