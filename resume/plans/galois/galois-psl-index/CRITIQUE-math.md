# CRITIQUE (mathematics lens) — BLUEPRINT.md, unit `lettre.impossible_au_dela`

Verdict: **sound**. No false statement, missing case, circularity or arithmetic error found in §3.
Only cosmetic issues (listed at the end).

## Target, binder by binder
Repository `GaloisOeuvres/LettreChevalier.lean` l. 3155–3157:
`∀ p : ℕ, ∀ _ : Fact p.Prime, 11 < p → ∀ H : Subgroup (PSL (Fin 2) (ZMod p)), H.index ≠ p`.
§7.4 final proof: `intro p hp h11 H hH; haveI := hp; exact no_subgroup_index_p p h11 H hH`, with
`no_subgroup_index_p (p) [Fact p.Prime] (hp : 11 < p) (H) (hH : H.index = p) : False`. Matches
exactly (`≠` unfolds to `= → False`). `card_PSL` (l. 2370, `p` explicit, `[Fact p.Prime]`,
`p ≠ 2`) is as quoted. PSL is finite, so `index` is the genuine index.

Cross-check: every non-blank line of the four §7 code blocks occurs in
`.lake-local/scratch/psl-index/T9.lean` (only the three `import …Aux*` lines differ, expected);
`T9.out` ends with `[OK]` and axioms `[propext, Classical.choice, Quot.sound]`; T9 contains no
`sorry`. So the formal implication lemmas ⇒ target is machine-checked.

## Re-derivations (all confirmed)
* E1: p = 2m+1, (p+1)p(p−1) = 4m(m+1)(2m+1), /2 = p·2m(m+1), so h = 2m(m+1); m ≥ 6 ⇒ h ≥ 84;
  h − 4p = 2m² − 6m − 4 ≥ 32 > 0; p ∤ h since 2, m, m+1 < p.
* E2: index of preimage under surjection = p; |S| = |G||Zc| ⇒ |K| = hz.
* C1: three entry equations of xg = gx and the three cases (b≠0; b=0,c≠0; b=c=0,a≠d) check.
* C2: (α+βg)(α'+β'g) symmetric. C3 trivial.
* C4: det(αI+βA) = α² + αβt + β²; with 2α = t(1−β): 4·E1 = (1−β)(1+β)(t²−4). β=1 ⇒ α=0 (2≠0);
  β=−1 ⇒ α=t, B = tI − A = adj A = A⁻¹. Correct.
* C5: M² = tM − I, t = 2s, s² = 1 (needs 2 ≠ 0); induction M^{n+1} = s^n(n+1)M − s^{n+1}n I
  checked; at n+1 = p the M-coefficient is 0 in char p. Correct.
* C6/C7: injection cen(A) → Q, fibres ≤ 2 ⇒ |cen(A)| ≤ 2q. Correct (needs only NS(A)).
* D1–D6: D3 (commuting non-central ⇒ equal centralizers) follows from D2 applied at B and at A.
  D4 uses tr(nAn⁻¹) = tr A. Correct.
* E3: (tr x)² = 4 ⇒ x^p ∈ Zc ⇒ π(x)^p = 1; π(x)^h = 1; gcd(p,h)=1 ⇒ π(x)=1. Correct, and this
  is exactly where p ∤ h (i.e. index p, not some other index) enters.
* B3: n ∈ N∖D ⇒ nxn⁻¹ = x⁻¹; for two such n₀, n, m = n₀⁻¹n fixes x ⇒ m ∈ D; N ⊆ D ∪ n₀D;
  Lagrange ⇒ |N| ∈ {|D|, 2|D|}. Correct.
* B4: equivariance (Step 1 uses B4.5 with k⁻¹ — valid for all x, also central ones), weight w
  invariant, w(D(x₀)) = |D(x₀)| − |Z| (uses B4.1–B4.3), orbit–stabilizer with stabilizer =
  normalizer. Classes with w = 0 dropped. Correct; empty ι handled in A4 (|s| = 0 ⇒ h = 1).
* E4: hypotheses B4.1–B4.7 for Γ = K, Z = Zc∩K, D(x) = K ∩ cen(x) all verified; B4.7 uses n ∈ K.
* E5: c_i ≥ 2 because Zc < D(x_i) strictly (x_i ∈ D(x_i)∖Zc); c_i ≤ a_i ≤ 2p ⇒ 2c_i ≤ 4p < h;
  e_i z c_i ∣ hz ⇒ e_i c_i ∣ h; cancel z. Correct.
* Part A: A0 (T ≥ h/2 for e=1, T ≥ h/4 for e=2) ⇒ |s| ≤ 3. A1, A2 (cases (1,1),(2,2),(1,2) with
  sub-cases c₁ = 2, 3, ≥4), A3 (any e_i = 1 ⇒ sum ≥ h; all e = 2 and all c ≥ 3 ⇒ sum ≤ X; c₁ = 2
  ⇒ 2(q₂+q₃) = P+2, solutions only P ∈ {6, 12, 30}, i.e. h ∈ {12, 24, 60}) — all re-derived by
  hand; agrees with the exceptional list of the original sketch ((2,3,3),(2,3,4),(2,3,5), and (3;2) at h=12).
  The strict `60 < h` is what kills h = 60 (p = 11): correct and sharp.

## Comparison with the route of the original sketch
The blueprint replaces tori in PSL by centralizers in K ≤ SL(2,p) (avoids choosing lifts and
"commuting up to sign"), and replaces |A| ≤ (p+1)/2 by the crude |cen| ≤ 2p, used only as
2c_i < h. Both changes are valid and do not weaken the result; |Zc| = 2 is never needed (z cancels).

## Issues (all minor / cosmetic)
1. §3.2 Lemma B3 proof: the letter `m` is used both for `n₀⁻¹ n` and for the final multiplier
   `|N| = m|D|`. Fix: rename the latter (e.g. `|N| = e|D|`).
2. §3.0 item 4 and C7 remark ("bound 2q attained in the parabolic case") are true but unused;
   could be marked as remarks to avoid an implementer trying to prove attainment. No action needed.
3. §6.2 says "None known" for mathematical risks — agreed; no hidden step found.
