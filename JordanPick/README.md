# JordanPick: the Jordan curve theorem (vendored)

The Lean files in this directory are not part of the formalization of Hilbert's *Foundations of
Geometry*. They are a copy of four files of another project and contain a complete proof of the
Jordan curve theorem, which Mathlib does not contain. They are used in one place:
`HilbertFoundations/JordanCurveClose.lean` derives from them the statement `JordanCurveTheorem` of
the unit `app.jordan_theorem` (Hilbert's appendix), where the theorem is quoted as "the theorem of
C. Jordan".

## Source

| | |
|---|---|
| Repository | <https://github.com/rkirov/jordan_pick> |
| Commit | `7905cd4c75038b823a8204e5474996905dd50800` (14 November 2026) |
| Author | Rado Kirov (named as author and maintainer in the upstream `formalization.yaml`; author of the commits) |
| Licence | Apache License 2.0 (upstream `LICENSE`; upstream `README.md`, section "License") |
| Upstream toolchain | Lean `v4.35.0`, Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679` |

The upstream files have no copyright or licence header of their own; none has been added. The
licence text is the file `LICENSE` at the root of this repository, which is the same Apache License
2.0 text as the upstream `LICENSE` (the upstream file only begins with one more empty line).

## Files

The paths and module names are those of the upstream repository.

| File | Lines | Contents |
|---|---|---|
| `JordanPick/JordanCurve.lean` | 2650 | The Jordan curve theorem by Maehara's method (R. Maehara, *The Jordan curve theorem via the Brouwer fixed point theorem*, Amer. Math. Monthly 91 (1984)): `JordanCurve.jordan_curve`, and the statements about the components of the complement listed below. |
| `JordanPick/JordanCurve/Arcs.lean` | 462 | The unit circle of `EuclideanSpace ℝ (Fin 2)`: the isometry `complexLIE` with `ℂ`, the homeomorphism `circleHomeoSphere` with Mathlib's `Circle`, the angle parametrization, the splitting of the circle into arcs. |
| `JordanPick/JordanCurve/Brouwer.lean` | 481 | The Brouwer fixed point theorem for compact convex sets of the plane, `JordanCurve.Brouwer.brouwerFPT`, from the lifting of paths along the covering `ℝ → AddCircle 1`. |
| `JordanPick/JordanCurve/Counting.lean` | 60 | From "two components covering the space" to `Nat.card (ConnectedComponents _) = 2`. |

The four files import only Mathlib and each other. The rest of the upstream repository (Pick's
theorem, the polygonal Jordan curve theorem, Radó's theorem, uniformization) is not copied.

For a continuous injective map `r : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2)`
the statements used by `HilbertFoundations/JordanCurveClose.lean` are:

* `JordanCurve.exists_unbounded_component`, `JordanCurve.unbounded_component_unique`: the complement
  of `range r` has exactly one unbounded connected component;
* `JordanCurve.step_A_exists_bounded`, `JordanCurve.step_B_bounded_unique`: it has exactly one
  bounded connected component;
* `JordanCurve.component_boundary_eq`: if there is more than one component, the frontier of each
  component is `range r`;
* `JordanCurve.Brouwer.brouwerFPT`: the Brouwer fixed point theorem, a hypothesis of the three
  preceding statements;
* `JordanCurve.Arcs.complexLIE`, `JordanCurve.Arcs.circleHomeoSphere`: the identifications of the
  plane with `ℂ` and of its unit circle with `Circle`.

`JordanCurve.jordan_curve` is the statement that the complement of `range r` has exactly two
connected components.

## Modifications

None. The four files are identical, byte for byte, to the files of the upstream commit (as stored
in the upstream repository, with Unix line ends). They compile without change, and without
warnings, with the toolchain of this repository (Lean `v4.36.0`, Mathlib `v4.36.0`).

SHA-256 of the files:

```
9f891c3f542c6b1ed7fbae362d77de8785a2d76bf8ef97014078988fa030c33a  JordanPick/JordanCurve.lean
2fe8d187ca6dee7337c42f5c0d399b2e486a72108ee3dd8ab8ea003a32ce3ea8  JordanPick/JordanCurve/Arcs.lean
822ad7c891b3715e2d0cce5dd019de1b2f90056f7a26969d0e9c9f97aadf42fb  JordanPick/JordanCurve/Brouwer.lean
cd269824adfdc8d21e3e27176493190722c3d22a96cca4e8aa56f4502ac39141  JordanPick/JordanCurve/Counting.lean
```

What differs from the upstream repository is outside the files:

* They are built as a second library of this package, `JordanPick`, declared in `lakefile.toml`
  with the options of the upstream `lakefile.toml` that are not already options of this package:
  `relaxedAutoImplicit = false` and `maxSynthPendingDepth = 3`. The options of this package,
  `pp.unicode.fun = true` (also set upstream) and `autoImplicit = false` (not set upstream), apply
  to the library as well.
* There is no root module `JordanPick.lean` here: the upstream one imports the whole upstream
  library. The library is declared with `globs = ["JordanPick.+"]`, so that its modules are the
  files of this directory, and it is reached through `import JordanPick.JordanCurve`.
