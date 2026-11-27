# Temporary branch: write-ups for the mathlib contributions

**Delete this branch once all the pull requests listed below are open.**

```
git push origin --delete mathlib-prs
```

This branch has no common history with `main` and is not part of the formalization. It only keeps
a copy of the working notes for the contributions to mathlib that came out of this repository and
of `galois-oeuvres-lean`, so that they are not tied to one machine. The code itself is on branches
of the fork `ishan-1729/mathlib4`.

## Contents of `mathlib-prs/`

- `README.md`: the table of contributions, with the branch and the state of each.
- `PR<N>-*.md`: for each contribution the link to open the pull request, its title, its
  description and the points a reviewer may raise.
- `NOTES*.md`: an explanation of every declaration and every proof step.
- `TAUCETI-CHECK.md` and `out/tauceti-check.json`: the comparison of every candidate with the
  Tau Ceti library.
- `tools/`: the scripts that cut the stacked branches and generated `PR6-*.md` and `PR7-*.md`.

Paths such as `D:\Projects\mathlib4` in the notes are those of the clone of mathlib in which the
branches were prepared.

## State on 27 November 2026

| Contribution | State |
|---|---|
| 1. `Real.sqrt` is analytic | open, leanprover-community/mathlib4#46502 |
| 2. Order on opposites | open, leanprover-community/mathlib4#46504 |
| 3. Archimedean ordered rings are commutative | open, leanprover-community/mathlib4#46535 |
| 4. Converse of Abel–Ruffini | dropped; its branch is not on the fork |
| 5. Irreducibility over extensions of coprime degree | open, leanprover-community/mathlib4#46616 |
| 6. Periodic continued fractions (7 stacked pull requests) | branches `cf-*` on the fork, none opened |
| 7. Galois's criterion in prime degree (3 pull requests) | branches `galois-prime-degree-*` on the fork, none opened |

Still to open: the seven pull requests of 6 and the three of 7. When the last of them is open,
delete this branch with the command above.
