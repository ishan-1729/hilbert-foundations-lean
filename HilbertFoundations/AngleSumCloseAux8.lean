import HilbertFoundations.AngleSumCloseAux7

/-!
# Helper module for the angle-sum theorem: the outside lemma, part 1

This module contains no unit of Hilbert's text. Plane geometry with groups I, II, IV.

Setting: a Saccheri quadrilateral `A B C D`, a point `P'` on the summit line beyond `D`, and the
foot `Q` of `P'` on the base line beyond `B`. The structure `OutConf` bundles the incidence facts
of this setting, with the five lines as fields of type `L`; `OutAux` bundles the two auxiliary
Saccheri quadrilaterals `B Q D E`, `A Q C E` built on a point `E` of the line `QP'`. The main
result here: if `BD < QP'`, then `∠ACD < ∠BDP'`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace AngSum

universe u v

section

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]

variable (L) in
/-- The setting of Stage E (Lemma E0): `l = AB`, `s = CD`, `q = QP'`, `a = AC`, `b = BD`. -/
structure OutConf (A B C D P' Q : P) (l s q a b : L) : Prop where
  /-- `A B C D` is a Saccheri quadrilateral. -/
  sac : Saccheri L A B C D
  /-- `P'` lies on the summit line beyond `D`. -/
  hP : Between C D P'
  /-- `Q` lies on the base line beyond `B`. -/
  hQ : Between A B Q
  /-- `Q` is the foot of `P'` on the base line. -/
  hr : RightAng (L := L) B Q P'
  /-- `A` lies on `l`. -/
  hAl : A ∈ l
  /-- `B` lies on `l`. -/
  hBl : B ∈ l
  /-- `Q` lies on `l`. -/
  hQl : Q ∈ l
  /-- `C` lies on `s`. -/
  hCs : C ∈ s
  /-- `D` lies on `s`. -/
  hDs : D ∈ s
  /-- `P'` lies on `s`. -/
  hPs : P' ∈ s
  /-- `Q` lies on `q`. -/
  hQq : Q ∈ q
  /-- `P'` lies on `q`. -/
  hPq : P' ∈ q
  /-- `A` lies on `a`. -/
  hAa : A ∈ a
  /-- `C` lies on `a`. -/
  hCa : C ∈ a
  /-- `B` lies on `b`. -/
  hBb : B ∈ b
  /-- `D` lies on `b`. -/
  hDb : D ∈ b
  /-- The base line and the summit line do not meet. -/
  nls : ¬Meets (Point := P) l s
  /-- The perpendicular `q` does not meet the side line `a`. -/
  nqa : ¬Meets (Point := P) q a
  /-- The perpendicular `q` does not meet the side line `b`. -/
  nqb : ¬Meets (Point := P) q b
  /-- The two side lines do not meet. -/
  nab : ¬Meets (Point := P) a b
  /-- `P'` is not on the base line. -/
  hPl : P' ∉ l
  /-- `Q` is not on the summit line. -/
  hQs : Q ∉ s
  /-- `A` is not on `q`. -/
  hAq : A ∉ q
  /-- `B` is not on `q`. -/
  hBq : B ∉ q
  /-- The summit line differs from `q`. -/
  hsq : s ≠ q

variable (L) in
/-- The auxiliary point `E ∈ q` of Lemma E1, with the lines `d = DE`, `c = CE`. -/
structure OutAux (A B C D P' Q E : P) (l s q a b d c : L) : Prop where
  /-- `E` lies on `q`. -/
  hEq : E ∈ q
  /-- `E` differs from `Q`. -/
  hEQ : E ≠ Q
  /-- `E` and `P'` lie on the same side of the base line. -/
  sideE : SameSide l E P'
  /-- `B Q D E` is a Saccheri quadrilateral. -/
  sac1 : Saccheri L B Q D E
  /-- `A Q C E` is a Saccheri quadrilateral. -/
  sac2 : Saccheri L A Q C E
  /-- The summit angles of `B Q D E` are congruent. -/
  ang1 : AngCong B D E Q E D
  /-- The summit angles of `A Q C E` are congruent. -/
  ang2 : AngCong A C E Q E C
  /-- `D` lies on `d`. -/
  hDd : D ∈ d
  /-- `E` lies on `d`. -/
  hEd : E ∈ d
  /-- `C` lies on `c`. -/
  hCc : C ∈ c
  /-- `E` lies on `c`. -/
  hEc : E ∈ c
  /-- The line `d = DE` does not meet the base line. -/
  ndl : ¬Meets (Point := P) d l
  /-- The line `c = CE` does not meet the base line. -/
  ncl : ¬Meets (Point := P) c l

end

section

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] (hl : ∀ X : P, ∃ l : L, X ∈ l)
  {A B C D E F G H K M N O Q X Y Z A' B' C' D' O' A₁ B₁ O₁ P' : P} {l m : L}
include hC hl

/-- E0: the setting of the outside lemma, with its five lines, exists. -/
theorem exists_outConf (h : Saccheri L A B C D) (hP : Between C D P') (hQ : Between A B Q)
    (hr : RightAng (L := L) B Q P') :
    ∃ l s q a b : L, OutConf L A B C D P' Q l s q a b := by
  sorry

/-- A point `E ≠ P'` of the line `q` is not on the summit line `s`. -/
theorem outConf_not_mem_s {l s q a b : L} (O : OutConf L A B C D P' Q l s q a b)
    (hEq : E ∈ q) (hEP : E ≠ P') : E ∉ s := by
  sorry

/-- E1: a point `E ≠ Q` of `q` on the side of `P'` with `BD ≡ QE` yields the auxiliary Saccheri
quadrilaterals `B Q D E`, `A Q C E`. -/
theorem outConf_aux {l s q a b : L} (O : OutConf L A B C D P' Q l s q a b)
    (hEq : E ∈ q) (hEQ : E ≠ Q) (hside : SameSide l E P') (hc : SegCong B D Q E) :
    ∃ d c : L, OutAux L A B C D P' Q E l s q a b d c := by
  sorry

/-- E2 (in the bundled setting): if `BD < QP'`, then `∠ACD < ∠BDP'`. -/
theorem outConf_lt {l s q a b : L} (O : OutConf L A B C D P' Q l s q a b)
    (hlt : SLt B D Q P') : AngLt (L := L) A C D B D P' := by
  sorry

/-- E2: in a Saccheri quadrilateral `A B C D`, with `P'` beyond `D` on the summit line and its
foot `Q` beyond `B` on the base line, `BD < QP'` implies `∠ACD < ∠BDP'`. -/
theorem saccheri_out_lt (h : Saccheri L A B C D) (hP : Between C D P') (hQ : Between A B Q)
    (hr : RightAng (L := L) B Q P') (hlt : SLt B D Q P') : AngLt (L := L) A C D B D P' := by
  obtain ⟨l, s, q, a, b, O⟩ := exists_outConf hl h hP hQ hr
  exact outConf_lt hl O hlt

end

end AngSum

end HilbertFoundations
