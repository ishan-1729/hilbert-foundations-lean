# Mathlib contributions: where everything is

Branches are on the fork `ishan-1729/mathlib4`. Each PR file has the open link, the title, a draft description and the review points. Each NOTES file explains every declaration and proof step.

| PR | State | Branch(es) | Files |
|---|---|---|---|
| 1. `Real.sqrt` is analytic | open: leanprover-community/mathlib4#46502 | `analyticAt-sqrt` | [PR1-sqrt.md](PR1-sqrt.md), [NOTES.md](NOTES.md) |
| 2. Order on opposites | open: leanprover-community/mathlib4#46504 | `mulOpposite-linearOrder` | [PR2-opposite-order.md](PR2-opposite-order.md), [NOTES.md](NOTES.md) |
| 3. Archimedean ordered rings are commutative | open: leanprover-community/mathlib4#46535 | `archimedean-commutative` | [PR3-archimedean.md](PR3-archimedean.md), [NOTES-archimedean.md](NOTES-archimedean.md) |
| 4. Converse of Abel–Ruffini | dropped (Tau Ceti has it) | none | [PR4-abel-ruffini.md](PR4-abel-ruffini.md) |
| 5. Irreducibility over extensions of coprime degree | open: leanprover-community/mathlib4#46616 | `irreducible-map-coprime` | [PR5-irreducible-coprime.md](PR5-irreducible-coprime.md), [NOTES-irreducible-coprime.md](NOTES-irreducible-coprime.md) |
| 6. Periodic continued fractions (7 stacked PRs) | branches pushed, not opened | `cf-*` | [PR6-continued-fractions-stack.md](PR6-continued-fractions-stack.md), [NOTES-continued-fractions-stack.md](NOTES-continued-fractions-stack.md) |
| 7. Galois's criterion in prime degree (3 PRs) | branches pushed, not opened | `galois-prime-degree-*` | [PR7-galois-prime-degree.md](PR7-galois-prime-degree.md), [NOTES-galois-prime-degree.md](NOTES-galois-prime-degree.md) |

Suggested order for the rest: 6.1, then 7.1. Open one at a time and wait for a first review before the next.

The Tau Ceti overlap check for all candidates is in [TAUCETI-CHECK.md](TAUCETI-CHECK.md).
