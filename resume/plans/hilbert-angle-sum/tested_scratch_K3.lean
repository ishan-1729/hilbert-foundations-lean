import HilbertFoundations.PascalAux2
import HilbertFoundations.Commentary

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace AngSum

universe u v

section Defs

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]

variable (L) in
def LtSupp (A O B : P) : Prop :=
  ¬Collinear (Line := L) A O B ∧ ∃ C, Between A O C ∧ AngLt (L := L) A O B C O B

variable (L) in
def EqSupp (A O B : P) : Prop :=
  ¬Collinear (Line := L) A O B ∧ ∃ C, Between A O C ∧ AngCong A O B C O B

variable (L) in
def GtSupp (A O B : P) : Prop :=
  ¬Collinear (Line := L) A O B ∧ ∃ C, Between A O C ∧ AngLt (L := L) C O B A O B

variable (L) in
def SameType (A O B A' O' B' : P) : Prop :=
  (LtSupp L A O B ↔ LtSupp L A' O' B') ∧ (EqSupp L A O B ↔ EqSupp L A' O' B') ∧
    (GtSupp L A O B ↔ GtSupp L A' O' B')

def SLt (A B C D : P) : Prop := ∃ X, Between C X D ∧ SegCong A B C X

def Foot (l : L) (X F : P) : Prop :=
  F ∈ l ∧ X ∉ l ∧ ∀ G : P, G ∈ l → G ≠ F → RightAng (L := L) G F X

variable (L) in
def BiRight (A B C D : P) : Prop :=
  A ≠ B ∧ RightAng (L := L) B A C ∧ RightAng (L := L) A B D ∧
    ∀ l : L, A ∈ l → B ∈ l → SameSide l C D

variable (L) in
def Saccheri (A B C D : P) : Prop := BiRight L A B C D ∧ SegCong A C B D

variable (L) in
def Lambert (M B D N : P) : Prop :=
  RightAng (L := L) B M N ∧ RightAng (L := L) M B D ∧ RightAng (L := L) M N D

end Defs

section Defs2

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]

variable (L) in
structure OutConf (A B C D P' Q : P) (l s q a b : L) : Prop where
  sac : Saccheri L A B C D
  hP : Between C D P'
  hQ : Between A B Q
  hr : RightAng (L := L) B Q P'
  hAl : A ∈ l
  hBl : B ∈ l
  hQl : Q ∈ l
  hCs : C ∈ s
  hDs : D ∈ s
  hPs : P' ∈ s
  hQq : Q ∈ q
  hPq : P' ∈ q
  hAa : A ∈ a
  hCa : C ∈ a
  hBb : B ∈ b
  hDb : D ∈ b
  nls : ¬Meets (Point := P) l s
  nqa : ¬Meets (Point := P) q a
  nqb : ¬Meets (Point := P) q b
  nab : ¬Meets (Point := P) a b
  hPl : P' ∉ l
  hQs : Q ∉ s
  hAq : A ∉ q
  hBq : B ∉ q
  hsq : s ≠ q

variable (L) in
structure OutAux (A B C D P' Q E : P) (l s q a b d c : L) : Prop where
  hEq : E ∈ q
  hEQ : E ≠ Q
  sideE : SameSide l E P'
  sac1 : Saccheri L B Q D E
  sac2 : Saccheri L A Q C E
  ang1 : AngCong B D E Q E D
  ang2 : AngCong A C E Q E C
  hDd : D ∈ d
  hEd : E ∈ d
  hCc : C ∈ c
  hEc : E ∈ c
  ndl : ¬Meets (Point := P) d l
  ncl : ¬Meets (Point := P) c l

variable (L) in
structure TriConf (A B C F G H X Y A₁ B₁ : P) : Prop where
  nc : ¬Collinear (Line := L) A B C
  sac : Saccheri L F G A B
  hX : Between A C X
  hY : Between B₁ C Y
  angA : AngCong C A B X C Y
  sideY : ∀ a : L, A ∈ a → C ∈ a → SameSide a Y B
  intY : Y ∈ Interior (Line := L) X C B
  angB : AngCong C B A B C A₁
  ncA : ¬Collinear (Line := L) A₁ C B
  sideA : ∀ a : L, C ∈ a → B ∈ a → SameSide a A₁ Y
  angS : AngCong F A B H C B₁
  ncH : ¬Collinear (Line := L) B₁ C H
  ncH' : ¬Collinear (Line := L) A₁ C H
  angH : AngCong B₁ C H A₁ C H
  sideH : ∀ a : L, C ∈ a → H ∈ a → SameSide a A₁ Y
  sideYH : ∀ a : L, C ∈ a → Y ∈ a → SameSide a H B

end Defs2

section Defs3

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [PlaneCongruence P L]

variable (L) in
structure MidConf (A B C D E F G H : P) (e : L) : Prop where
  htA : Pas.ht (L := L) D A = C
  htB : Pas.ht (L := L) E B = C
  bD : Between A D C
  bE : Between B E C
  hD : D ∈ e
  hE : E ∈ e
  hA : A ∉ e
  hB : B ∉ e
  hC : C ∉ e
  sideAB : SameSide e A B
  fA : Foot e A F
  fB : Foot e B G
  fC : Foot e C H
  htF : Pas.ht (L := L) D F = H
  htG : Pas.ht (L := L) E G = H
  sac : Saccheri L F G A B

end Defs3

section Thms

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] (hl : ∀ X : P, ∃ l : L, X ∈ l)
  {A B C D E F G H K M N O Q X Y Z A' B' C' D' O' A₁ B₁ O₁ P' : P} {l m e : L}
include hC hl

theorem gtSupp_of_copy (h : ¬Collinear (Line := L) A O B) (hC : Between A O C)
    (hc : AngCong A O B X O B) (hX' : ¬Collinear (Line := L) X O B)
    (hX : C ∈ Interior (Line := L) X O B) : GtSupp L A O B := by sorry

theorem tri_midline (h : ¬Collinear (Line := L) A B C) :
    ∃ (D E F G H : P) (e : L), MidConf L A B C D E F G H e := by sorry

theorem exists_outConf (h : Saccheri L A B C D) (hP : Between C D P') (hQ : Between A B Q)
    (hr : RightAng (L := L) B Q P') :
    ∃ l s q a b : L, OutConf L A B C D P' Q l s q a b := by sorry

theorem outConf_not_mem_s {l s q a b : L} (O : OutConf L A B C D P' Q l s q a b)
    (hEq : E ∈ q) (hEP : E ≠ P') : E ∉ s := by
  intro hEs
  exact hEP (eq_of_mem_of_mem O.hsq hEs hEq O.hPs O.hPq)

theorem outConf_aux {l s q a b : L} (O : OutConf L A B C D P' Q l s q a b)
    (hEq : E ∈ q) (hEQ : E ≠ Q) (hside : SameSide l E P') (hc : SegCong B D Q E) :
    ∃ d c : L, OutAux L A B C D P' Q E l s q a b d c := by sorry

theorem outConf_lt {l s q a b : L} (O : OutConf L A B C D P' Q l s q a b)
    (hlt : SLt B D Q P') : AngLt (L := L) A C D B D P' := by sorry

theorem outConf_gt {l s q a b : L} (O : OutConf L A B C D P' Q l s q a b)
    (hgt : SLt Q P' B D) : AngLt (L := L) B D P' A C D := by sorry

theorem saccheri_out_lt (h : Saccheri L A B C D) (hP : Between C D P') (hQ : Between A B Q)
    (hr : RightAng (L := L) B Q P') (hlt : SLt B D Q P') : AngLt (L := L) A C D B D P' := by
  obtain ⟨l, s, q, a, b, O⟩ := exists_outConf hl h hP hQ hr
  exact outConf_lt hl O hlt

theorem tri_B₁_ne (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hB₁ : Pas.ht (L := L) D B = B₁) : B₁ ≠ C ∧ Between B D B₁ ∧ B₁ ∉ e := by sorry
theorem tri_angA (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hB₁ : Pas.ht (L := L) D B = B₁) (hX : Between A C X) (hY : Between B₁ C Y) :
    AngCong C A B X C Y := by sorry
theorem tri_sideY (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hB₁ : Pas.ht (L := L) D B = B₁) (hY : Between B₁ C Y) :
    ∀ a : L, A ∈ a → C ∈ a → SameSide a Y B := by sorry
theorem tri_intY (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hB₁ : Pas.ht (L := L) D B = B₁) (hX : Between A C X) (hY : Between B₁ C Y) :
    Y ∈ Interior (Line := L) X C B := by sorry
theorem tri_angB (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hA₁ : Pas.ht (L := L) E A = A₁) :
    AngCong C B A B C A₁ ∧ ¬Collinear (Line := L) A₁ C B := by sorry
theorem tri_sideA (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hA₁ : Pas.ht (L := L) E A = A₁) (hB₁ : Pas.ht (L := L) D B = B₁) (hX : Between A C X)
    (hY : Between B₁ C Y) : ∀ a : L, C ∈ a → B ∈ a → SameSide a A₁ Y := by sorry
theorem tri_angS (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hA₁ : Pas.ht (L := L) E A = A₁) (hB₁ : Pas.ht (L := L) D B = B₁) :
    AngCong F A B H C B₁ ∧ ¬Collinear (Line := L) B₁ C H ∧
      AngCong G B A H C A₁ ∧ ¬Collinear (Line := L) A₁ C H := by sorry
theorem tri_angH (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hA₁ : Pas.ht (L := L) E A = A₁) (hB₁ : Pas.ht (L := L) D B = B₁) :
    AngCong B₁ C H A₁ C H := by sorry
theorem tri_sideH (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hA₁ : Pas.ht (L := L) E A = A₁) (hB₁ : Pas.ht (L := L) D B = B₁) (hY : Between B₁ C Y) :
    ∀ a : L, C ∈ a → H ∈ a → SameSide a A₁ Y := by sorry
theorem tri_sideYH (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hB₁ : Pas.ht (L := L) D B = B₁) (hY : Between B₁ C Y) :
    ∀ a : L, C ∈ a → Y ∈ a → SameSide a H B := by sorry

theorem exists_triConf (h : ¬Collinear (Line := L) A B C) :
    ∃ F G H X Y A₁ B₁ : P, TriConf L A B C F G H X Y A₁ B₁ := by
  obtain ⟨D, E, F, G, H, e, M⟩ := tri_midline hl h
  obtain ⟨A₁, hA₁⟩ : ∃ A₁, Pas.ht (L := L) E A = A₁ := ⟨_, rfl⟩
  obtain ⟨B₁, hB₁⟩ : ∃ B₁, Pas.ht (L := L) D B = B₁ := ⟨_, rfl⟩
  sorry

theorem triConf_canon {X' Y' : P} (T : TriConf L A B C F G H X Y A₁ B₁)
    (h : Conclusion.ExteriorConfig L A B C X' Y') :
    Interior (Line := L) X' C B = Interior (Line := L) X C B ∧
      Interior (Line := L) Y' C B = Interior (Line := L) Y C B ∧
      ¬Collinear (Line := L) Y' C B ∧ AngCong Y' C B Y C B := by sorry

end Thms

end AngSum

end HilbertFoundations
