# Sources and copyright

## The text
- David Hilbert, *The Foundations of Geometry*. Authorized translation by **E. J. Townsend**. The Open Court Publishing Company, Chicago, 1902. Library record of the 1902 printing: <https://catalog.hathitrust.org/Record/000383241> (as linked from the Online Books Page entry for Hilbert).
- It translates Hilbert's *Grundlagen der Geometrie*, the first part of the *Festschrift zur Feier der Enthüllung des Gauss-Weber-Denkmals in Göttingen* (B. G. Teubner, Leipzig, 1899; 92 pages, followed in the same volume by E. Wiechert's *Grundlagen der Elektrodynamik*; collation as in the review in *Bulletin of the American Mathematical Society* 6 (1900), <https://www.ams.org/journals/bull/1900-06-07/S0002-9904-1900-00719-1>). Library record: <https://catalog.hathitrust.org/Record/008892590>.
- Between the two came the French edition: D. Hilbert, "Les principes fondamentaux de la géométrie", *Annales scientifiques de l'École Normale Supérieure* (3) 17 (1900), 103–209, DOI 10.24033/asens.479, translated by L. Laugel. Record: <https://www.numdam.org/item/ASENS_1900_3_17__103_0>; the translator is named in the bibliography of *Revue d'histoire des mathématiques* 6 (2000), <https://www.numdam.org/item/RHM_2000__6_2_219_0/>.

What the English text contains beyond the Festschrift is stated in the text itself:
- The translator's preface (key `preface` of `data/foundations.json`) says that the material was given as lectures on euclidean geometry at Göttingen in the winter semester of 1898–1899 and published for the unveiling of the Gauss-Weber monument in June 1899, that Hilbert made additions for the French edition, "particularly in the concluding remarks", where he reports on Dehn's investigation, and that these additions are incorporated in the translation.
- Three passages are marked as additions of the French edition: the Remark at the end of § 8 that introduces the Axiom of Completeness (translator's note; units `s8.completeness_remark`, `ax.completeness`), and two parts of the long footnote of § 18 (unit `s18.gerard`, which quotes that footnote with these parts elided).
- The Appendix is, by the translator's note at its head, a summary of a paper by Hilbert that was then about to appear in the *Mathematische Annalen*. The paper is "Ueber die Grundlagen der Geometrie", *Math. Ann.* 56, 381–422 (listed below).
- Six footnotes are signed "Tr." and are the translator's.

The later German editions (the second appeared with Teubner in 1903) and the translations made from them are not used. The axioms formalized are those of this edition; the header of `HilbertFoundations/Basic.lean` lists where they differ from the later ones.

### Digital edition
- **Project Gutenberg eBook #17384**, *The Foundations of Geometry*, by David Hilbert.
  - Catalogue page: <https://www.gutenberg.org/ebooks/17384>
  - Files, as named in the trailer of the TeX file: <https://www.gutenberg.org/1/7/3/8/17384/> (`17384-t.tex`, `17384-t.zip`, `17384-pdf.pdf`).
- The header of the TeX file gives the release date as 23 December 2005 and the most recent update as 14 July 2025, and credits the edition to Joshua Hutchinson, Roger Frank, David Starner and the Online Distributed Proofreading Team (<http://www.pgdp.net>), revised by Richard Tonsing.
- The e-text is a LaTeX transcription. Its title page is that of the "Reprint Edition", The Open Court Publishing Company, La Salle, Illinois, 1950, and the page after it carries the notice "Translation copyrighted by The Open Court Publishing Co. 1902."

**Source used here:** the LaTeX source, `17384-t.tex`. Mathematics is TeX; the 52 figures are separate image files and are not used. The file is not part of this repository; `scripts/extract_source.py` takes its path as argument.

## Copyright status
| Jurisdiction | Rule | Status |
|---|---|---|
| United States | published before 1931 | public domain (German original 1899, translation 1902) |
| India | author's life + 60 years | Hilbert d. 1943: public domain since 1 January 2004. Townsend d. 1955: the translation since 1 January 2016 |
| EU / UK | author's life + 70 years | Hilbert's text: public domain since 1 January 2014. Townsend's translation: since 1 January 2026 |

- **David Hilbert**, 1862–1943.
- **Edgar Jerome Townsend**, 1864–1955, of the University of Illinois; his doctorate (Göttingen, 1900) was supervised by Hilbert (Mathematics Genealogy Project, <https://mathgenealogy.org/id.php?id=7343>). The dates 1864–1955 are those of the library authority records (VIAF: "Townsend, Edgar Jerome, 1864-1955", <https://viaf.org/viaf/75270643>) and of the Online Books Page record of the eBook, which also gives Hilbert's (<https://onlinebooks.library.upenn.edu/webbin/gutbook/lookup?num=17384>). Wikidata (Q94837958) gives 8 July 1955 as the day of death and 22 February 1866 as the day of birth; the birth year differs from the authority records, the death year agrees.
- A translation has its own term, counted from the translator's death. Both terms have run out in the jurisdictions of the table; the later one, that of the translation under life + 70 years, ended with the year 2025.
- The 1950 reprint from which the e-text was transcribed reprints the 1902 translation.

The repository relies on the United States status, which is the one Project Gutenberg gives on the catalogue page. The other two rows are computed from the death years and the general term of each jurisdiction, and from nothing else.

## The Project Gutenberg licence
The eBook is distributed under the Project Gutenberg License (<https://www.gutenberg.org/policy/license.html>), printed in full at the end of `17384-t.tex`. In the copy used:
- For a work that is not protected by copyright in the United States, and a user located there, the Foundation claims no right to prevent copying, distribution or derivative works, "as long as all references to Project Gutenberg are removed" (paragraph 1.C).
- "Project Gutenberg" is a registered trademark (1.B). A copy that keeps the name has to carry the licence notice of paragraph 1.E.1 and to follow paragraphs 1.E.2–1.E.9, which concern the attached licence, the formats and fees.
- The copyright law of the place of use applies as well, and the Foundation makes no statement about the status of a work outside the United States (1.D).

**How the text is used here:**
- The repository does not contain the eBook: neither the TeX file, nor the PDF, nor the figures.
- `data/foundations.json` holds the text of the book only. The extraction keeps two ranges of the TeX file: the preface (up to the table of contents), and everything from the Introduction to the end-of-text marker `*** END OF THE PROJECT GUTENBERG` that follows the Appendix. The table of contents is read only for the chapter and section titles. The Project Gutenberg header, the production credits, the transcribed title page and the licence lie outside these ranges.
- The quotations in the Lean files are taken from `data/foundations.json`.
- The name Project Gutenberg occurs in the repository in citations of the source: the `source` field of `data/foundations.json`, the header of `HilbertFoundations/Basic.lean`, `scripts/extract_source.py`, the README and the files under `docs/`.

## How the quotations were produced
`scripts/extract_source.py` reads the TeX file (as Latin-1) and writes `data/foundations.json`. Usage:

```sh
python scripts/extract_source.py path/to/17384-t.tex
```

It records:
- `source`: a one-line citation of the edition;
- `preface`, `introduction`, `conclusion`, `appendix`: the translator's preface, Hilbert's Introduction, the Conclusion and the Appendix, as text;
- `chapters`: the seven chapters, each with its number, its title and the number of its first section;
- `sections`: the 39 sections, each with its number, its title (from the table of contents), its chapter and its text;
- `statements`: the 68 statements that Hilbert labels, each with its text and the section it occurs in. They are 24 axioms (I, 1–7; II, 1–5; III; IV, 1–6; V; the Axiom of Completeness; Axioms I–III of the Appendix) and Theorems 1–44.

Clean-up applied:
- The markers of the scanned pages (`%%-----File: NNN.png-----%%`) and the TeX comment lines are removed.
- Each figure is replaced by a marker `[Fig. N]`. There are 52, Fig. 1 to Fig. 52.
- Footnotes are inlined as `[Note: …]`. There are 27 in the running text.
- Emphasis becomes `*…*`. Small capitals and size commands are dropped.
- Mathematics stays as TeX, between `$ … $` or `\[ … \]` or in its display environment.
- Outside mathematics, TeX quotes and dashes become typographic ones. `\"u`, `\"a`, `\"o` and `\'e` become `ü`, `ä`, `ö` and `é`, and `\S` followed by a space, a tie or `\!` becomes `§` (as `$\S$` inside mathematics it is kept). Lines are joined into paragraphs.
- One slip of the e-text is repaired: the label of the first axiom of congruence, printed "IV, I." there, is recorded as "IV, 1.".

Some TeX is left in the text. The tables and displayed formulas keep their environments (`tabular`, `array`, `equation`, `eqnarray`, `align*`), the 19 page references `\pageref{…}` are not resolved, and each of the eight `\S\S` leaves one `\S` before the `§`. A few layout commands remain at the end of the preface and of the appendix, and the accent of "Th\`ese" in the footnote of § 18 is not converted. The chapter titles are lower-cased after their first letter, so that of Chapter VII ends "the axioms i--v".

`scripts/make_skeletons.py` turned the 68 statements into unit blocks, `ax.…`, `th.1`–`th.44` and `app.axiom1`–`app.axiom3`, each quoting its statement in full. Every further claim of the book is quoted from `data/foundations.json` in a unit of its own; there are 430 units in all (`docs/UNITS.md`). A quotation may be shortened, with `…` at the cut. Each quoted passage of the unit blocks, cut at these marks, occurs verbatim in `data/foundations.json`, with its footnotes in the form `[Note: …]`.

## Third-party code: the library `JordanPick`
The directory `JordanPick/` holds the only code in the repository that was not written for it: four Lean files copied from another project. The facts of this section are those of [`JordanPick/README.md`](../JordanPick/README.md), which also gives the checksums of the files.

| | |
|---|---|
| Repository | <https://github.com/rkirov/jordan_pick> |
| Commit | `7905cd4c75038b823a8204e5474996905dd50800` (14 November 2026) |
| Author | Rado Kirov |
| Licence | Apache License 2.0 |
| Files | `JordanPick/JordanCurve.lean`, `JordanPick/JordanCurve/Arcs.lean`, `JordanPick/JordanCurve/Brouwer.lean`, `JordanPick/JordanCurve/Counting.lean` |

- **Unmodified.** The four files are identical, byte for byte, to the files of the upstream commit, and keep the upstream paths and module names. The rest of the upstream repository is not copied. What differs is outside the files: they are built as a second library of this package, declared in `lakefile.toml`.
- **Licence and copyright.** The upstream repository is under the Apache License 2.0, the licence of this repository; the text is the file `LICENSE` at the root. The upstream files have no copyright or licence header, and none has been added. Their copyright belongs to their author, not to this project.
- **Contents.** A proof of the Jordan curve theorem for a continuous injective map of the unit circle of `EuclideanSpace ℝ (Fin 2)` into `EuclideanSpace ℝ (Fin 2)`: the complement of its range has exactly two connected components (`JordanCurve.jordan_curve`), one bounded and one unbounded, and the curve is the frontier of each. The method is that of R. Maehara, "The Jordan curve theorem via the Brouwer fixed point theorem", *American Mathematical Monthly* 91 (1984), no. 10, 641–643, DOI 10.2307/2323369, <https://www.jstor.org/stable/2323369>. The Brouwer fixed point theorem for the plane is proved in the copied files as well (`JordanCurve.Brouwer.brouwerFPT`), from the lifting of paths along the covering of the circle by the line.
- **Use.** `HilbertFoundations/JordanCurveClose.lean`, which is a file of this repository, derives from the copied files the statement of the unit `app.jordan_theorem` (`Appendix.jordanCurveTheorem : JordanCurveTheorem`, for a closed curve `γ : ℝ → ℂ` of period 1). Nothing else in the repository uses them. How the axiom audit covers them is said in [docs/FAITHFULNESS.md](FAITHFULNESS.md), "Third-party code".

## A dependency: the library Tau Ceti
The proof of Theorem 42 uses a second body of code that was not written for this repository. Unlike `JordanPick`, it is not copied: the library Tau Ceti is a dependency of the package, which Lake fetches from the library's own repository. No file of it is in this repository.

| | |
|---|---|
| Repository | <https://github.com/TauCetiProject/TauCeti> |
| Commit | `aa3cfad1274c06cff25f2b58848498b3c3f68d0f` (20 November 2026) |
| Copyright | "The Tau Ceti contributors", as the headers of its files say (with the exceptions noted below) |
| Licence | Apache License 2.0 |
| Pinned in | `lakefile.toml` and `lake-manifest.json` |
| Toolchain at that commit | Lean `v4.36.0`, mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (mathlib `v4.36.0`), as in this repository |

- **The commit.** It is the last commit of the library on Lean v4.36.0: the next commit of its main branch, `e0e414ce57522ba17560057ad0d7f2edab91bf0c`, moves the library to a later toolchain.
- **A dependency, not a copy.** The library is used unchanged, at the pinned commit. None of its code is copied into a file of this repository, and it is not redistributed here.
- **Licence and copyright.** The library is under the Apache License 2.0 (the file `LICENSE` of its repository). Of the 1,044 modules that `Theorem42Close.lean` needs, each has a header that refers to that licence and names the copyright holders: 1,042 name the Tau Ceti contributors (975 as "The Tau Ceti contributors", 67 without the article), and two, `TauCeti.RingTheory.LocalRing.Localization` and `TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing`, name Taylor Dupuy, Thomas Tucker and Zhuoran Wang. The 78 further modules that the dependency `hilbert17` needs (next section) have such headers as well: 36 name the Tau Ceti contributors, 41 name Lean FRO, LLC, and one names Chris Birkbeck. The copyright belongs to them, not to this project.
- **What is built.** Lake builds the modules of the library that `HilbertFoundations/Theorem42Close.lean` imports, directly or through other modules: 1,044 of the 34,759 Lean files under `TauCeti/` at that commit, about 255,000 lines. The dependency `hilbert17` (next section) imports 83 modules of the library, 78 of them not among these, so that 1,122 modules are built in all, about 270,000 lines. The five modules imported directly are `TauCeti.NumberTheory.QuadraticForm.Global.HigherRank`, `….Global.Quaternary`, `….Global.AnisotropicPlaces`, `….Global.Localization` and `TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic`.
- **What is used.** The Hasse–Minkowski theorem for quadratic forms over number fields, in two statements: the step from rank `n − 1` to rank `n ≥ 5` (`QuadraticForm.not_anisotropic_of_isLocallyIsotropic_of_five_le_finrank`) and the theorem in rank four (`QuadraticForm.not_anisotropic_of_isLocallyIsotropic_quaternary`). With them: the isotropy of a form of rank at least five at every finite place (`QuadraticForm.not_anisotropic_atFinitePlace_of_five_le_finrank`), the localizations of a form at the finite and the real places (`QuadraticForm.atFinitePlace`, `QuadraticForm.atRealPlace`, `QuadraticForm.atRealPlaceWeightedSumSquares`, `QuadraticForm.IsLocallyIsotropic`, `QuadraticForm.isLocallyIsotropic_iff`), `QuadraticMap.Equivalent.anisotropic_iff`, and the regular diagonal forms (`TauCeti.RegularFormPresentation`, `TauCeti.presentedForm`, `TauCeti.nondegenerate_presentedForm`, `TauCeti.presentedForm_eq_weightedSumSquares_coe`). The header of `HilbertFoundations/Theorem42Close.lean` says what each of them states.
- **Use.** `HilbertFoundations/Theorem42Close.lean`, which is a file of this repository, derives from them the statement of the unit `th.42` (`theorem42 : Theorem42`). No other file of the repository imports the library; the dependency `hilbert17` does (next section). What this repository proves and what it takes from the library is set out in [docs/FAITHFULNESS.md](FAITHFULNESS.md), "Proved with a dependency"; how the axiom audit covers the part used is said there under "Third-party code".

## A second dependency: the package `hilbert17`
The proof of the unit `s38.two_variables` uses a third body of code that was not written for this repository: a proof of Artin's theorem on definite polynomials. Like Tau Ceti it is a dependency, which Lake fetches. No file of it is in this repository.

| | |
|---|---|
| Upstream repository | <https://github.com/pd4st8hb95-hub/hilbert17-lean>, commit `19cd90e0a2c0f5c0e034ee54d06f5e129561ee59` (14 October 2026) |
| Author | The upstream `README.md` names no author; the commits are authored under the name `Haitao-Ji` |
| Dependency | <https://github.com/ishan-1729/hilbert17-lean>, a fork of the upstream repository: branch `lean-v4.36-tauceti`, commit `a1a089e7e5080a2a27f0e95bf7b0e760f62ed4e5` |
| Pinned in | `lakefile.toml` and `lake-manifest.json` |
| Toolchain | upstream: Lean `v4.32.1`, a copy of mathlib, copies of 71 files of Tau Ceti; the branch: Lean `v4.36.0`, mathlib `v4.36.0` and Tau Ceti at the commit above, as dependencies |

- **Why a fork.** The upstream repository does not build on the toolchain of this repository. The branch makes the changes that the newer mathlib requires in nine Lean files and replaces the copies of mathlib and Tau Ceti by dependencies; its file `PORT-NOTES.md` lists every change. No statement that is kept has changed. The proof is the work of the upstream author.
- **Licence and copyright.** The upstream repository contains the text of the Apache License 2.0 in its file `LICENSE`. Its file `THIRD_PARTY.md` says that this licence is kept for the attributed upstream material and that no project-wide licence is assigned to the original contributions, and its file `PROVENANCE.json` says the same. The attributed upstream material is the third-party code in the repository: mathlib and the other vendored packages, and the Tau Ceti files. The Lean files used here are the repository's own and carry no licence header; on these statements no licence is granted for them. They are therefore not copied into this repository, the licence of this repository does not apply to them, and the fork grants nothing beyond what the upstream repository grants. Their copyright belongs to the upstream author.
- **What is built.** The 18 modules of the library `Hilbert17` of the branch, 1,542 lines, and the 83 modules of Tau Ceti that they import.
- **What is used.** `Hilbert17Transfer.hilbert17RealCleared_candidate : Hilbert17Target.Hilbert17RealCleared`, Artin's theorem for polynomials with real coefficients in the form `q² f = ∑ pᵢ²` with `q ≠ 0`. The suffix `_candidate` is part of the upstream name; the theorem has no hypothesis other than that `f` takes no negative value.
- **Use.** `HilbertFoundations/TwoVariablesClose.lean`, which is a file of this repository, derives from it the statement of the unit `s38.two_variables` (`twoVariableClaim : TwoVariableClaim`). Nothing else in the repository imports the package. What this repository proves and what it takes from the package is set out in [docs/FAITHFULNESS.md](FAITHFULNESS.md), "Proved with the dependency `hilbert17`".

## Works cited in the Lean files
These are cited for an attribution or for a result that is not formalized. None is a source of quoted text. The bibliographic data were checked against the records linked; the data of Halsted's note, of Pourchet's paper and of Maehara's paper are taken from the works that cite them, named below. One entry, Hasse's paper, is not cited in the Lean files and is marked as such.

**Order and incidence**
- E. H. Moore, "On the projective axioms of geometry", *Transactions of the American Mathematical Society* 3 (1902), 142–158. Record (of the erratum, which gives the citation): <https://www.ams.org/journals/tran/1902-003-04/S0002-9947-1902-1500457-1/>. Cited for the redundancy of Axiom II, 4: units `ax.II4` (`Basic.lean`), `s3.II4_dependent` (`Order.lean`), `intro.independent` (`Commentary.lean`), `s10.mutual_independence` (`Independence.lean`). It is the paper named in the translator's note at the head of § 10; the translator's note on the heading of § 24 refers to a paper of Moore read before the Society in January 1902, without a title.
- `s3.II4_dependent` adds "also R. L. Moore", without a reference. According to R. L. Wilder's obituary of R. L. Moore ("Robert Lee Moore, 1882–1974", *Bulletin of the American Mathematical Society* 82 (1976), 417–427, DOI 10.1090/S0002-9904-1976-14029-3, <https://projecteuclid.org/download/pdf_1/euclid.bams/1183537897>), that proof was published by G. B. Halsted, "The betweenness assumptions", *American Mathematical Monthly* 9 (1902), 98–101.
- O. Veblen, "A system of axioms for geometry", *Transactions of the American Mathematical Society* 5 (1904), 343–384. DOI 10.1090/S0002-9947-1904-1500678-X, <https://www.ams.org/tran/1904-005-03/S0002-9947-1904-1500678-X/>. Cited in unit `th.6` (`Order.lean`) for a proof of the theorem on polygons.
- F. R. Moulton, "A simple non-desarguesian plane geometry", *Transactions of the American Mathematical Society* 3 (1902), 192–195. DOI 10.2307/1986419. The geometry of `HilbertFoundations/NonDesarguesAux.lean`, used for Theorem 33 (unit `th.33`); it is the paper of the translator's note at the head of § 23.
- E. Artin, *Geometric Algebra*, Interscience Publishers, New York, 1957 (Interscience Tracts in Pure and Applied Mathematics), Chapter II. Review with the collation: <https://www.ams.org/bull/1958-64-01/S0002-9904-1958-10142-1>. The method of dilatations and translations followed in `HilbertFoundations/DesarguesAlgebra.lean` and `HilbertFoundations/DesarguesAlgebraAux.lean` (§§ 24–30).

**Pascal's theorem and the Conclusion**
- F. Schur, "Ueber den Fundamentalsatz der projectiven Geometrie", *Mathematische Annalen* 51 (1899), 401–409. <https://eudml.org/doc/157921>. (EuDML also has a record of the same title in the same volume with pages 299–320, doc 157915; the citation here follows the record with pages 401–409, which a second bibliography confirms.) The book cites it as "*Math. Ann.*, Vol. 51" in § 14; unit `s14.schur` (`Pascal.lean`) describes its theorem and gives the year.
- M. Dehn, "Die Legendre'schen Sätze über die Winkelsumme im Dreieck", *Mathematische Annalen* 53 (1900), 404–439. DOI 10.1007/BF01448980, <https://eudml.org/doc/157984>. The book cites it in the Conclusion as "*Math. Annalen*, Vol. 53 (1900)"; unit `concl.pseudo_geometry` (`Commentary.lean`) cites it for the theorem that stays open there.

**The Appendix**
- D. Hilbert, "Ueber die Grundlagen der Geometrie", *Mathematische Annalen* 56, 381–422. <https://eudml.org/doc/158069>. Cited in unit `app.main_theorem` (`Commentary.lean`) and in the header of `HilbertFoundations/CommentaryClose.lean`. The year: the Lean file gives 1902, as does the table of contents of a later German edition of the *Grundlagen*, which reprints the paper; EuDML dates the volume 1903.
- R. Maehara, "The Jordan curve theorem via the Brouwer fixed point theorem", *American Mathematical Monthly* 91 (1984), no. 10, 641–643. DOI 10.2307/2323369. Citation as in the reference list of <https://en.wikipedia.org/wiki/Jordan_curve_theorem>, which gives the author's first name as Ryuji; volume, year and pages also as in <https://proofwiki.org/wiki/Component_of_Complement_of_Jordan_Curve_has_Curve_as_Boundary>. Cited for the method of the proof of the Jordan curve theorem in the copied library `JordanPick` (section above): in the header of `HilbertFoundations/JordanCurveClose.lean` and in `JordanPick/README.md`, without the issue and the pages; unit `app.jordan_theorem` (`Commentary.lean`) names the method.

**Sums of squares (§§ 38–39)**
- D. Hilbert, "Über ternäre definite Formen", *Acta Mathematica* 17 (1893), 169–197. DOI 10.1007/BF02391990. The book cites it in § 38; unit `s38.two_variables` (`Constructions.lean`).
- C. L. Siegel, "Darstellung total positiver Zahlen durch Quadrate", *Mathematische Zeitschrift* 11 (1921), 246–275. DOI 10.1007/BF01203627, <https://eudml.org/doc/167660>. Cited as "Siegel (1921)" for the proof of Theorem 42: unit `th.42` (`Constructions.lean`) and the docstring of `Theorem42` (`ConstructionsAux7.lean`). The paper is not formalized: `theorem42` (`Theorem42Close.lean`) is derived from the Hasse–Minkowski theorem.
- H. Hasse, "Darstellbarkeit von Zahlen durch quadratische Formen in einem beliebigen algebraischen Zahlkörper", *Journal für die reine und angewandte Mathematik* 153 (1924), 113–130. <https://eudml.org/doc/149539>. Not cited in the Lean files, which name the Hasse–Minkowski theorem without a reference (unit `th.42`, the headers of `Theorem42Close.lean` and `ConstructionsClose.lean`); given here as a reference for that theorem over number fields. The companion paper on the equivalence of forms is "Äquivalenz quadratischer Formen in einem beliebigen algebraischen Zahlkörper", in the same volume, 158–162, <https://eudml.org/doc/149542>. The formal proof used is that of the library Tau Ceti (section above), not a formalization made here.
- E. Landau, "Über die Darstellung definiter Funktionen durch Quadrate", *Mathematische Annalen* 62 (1906), 272–285. DOI 10.1007/BF01449981, <https://eudml.org/doc/158257>. Cited as "Landau 1906" in unit `th.43` (`Constructions.lean`) and in the header of `HilbertFoundations/ConstructionsClose.lean`.
- Y. Pourchet, "Sur la représentation en somme de carrés des polynômes à une indéterminée sur un corps de nombres algébriques", *Acta Arithmetica* 19 (1971), 89–104. Citation as in <https://arxiv.org/abs/2302.02202>. Named without year in unit `th.43`, for the bound of five squares.
- E. Artin, "Über die Zerlegung definiter Funktionen in Quadrate", *Abhandlungen aus dem Mathematischen Seminar der Universität Hamburg* 5 (1927), 100–115. DOI 10.1007/BF02952513. Cited as "Artin 1927" for Hilbert's seventeenth problem: units `th.44`, `s39.general_case` and `s38.two_variables` (`Constructions.lean`) and the headers of `HilbertFoundations/ConstructionsClose.lean` and `HilbertFoundations/TwoVariablesClose.lean`. The theorem for polynomials with real coefficients is taken from the package `hilbert17`, a dependency described above; it is not proved in this repository.

**Named theorems.** The Lean files also name results without citing a work: Lagrange's four-square theorem (with the year 1770, unit `s38.fermat`), Hölder's theorem, Lüroth's theorem, the Hasse–Minkowski theorem, the Artin–Schreier theory, the Artin–Lang theorem, the Saccheri–Legendre theorem, the model of Beltrami, Cayley and Klein and Poincaré's model. The first three are taken from mathlib: `Nat.sum_four_squares` (in `fermat_four_squares`, `Constructions.lean`), `Archimedean.exists_orderAddMonoidHom_real_injective` (`CompletenessCloseAux4.lean`) and `RatFunc.Luroth.eq_adjoin_generator` (`ConstructionsCloseAux7.lean`). The Hasse–Minkowski theorem is taken from the library Tau Ceti, a dependency described above, in the statements that `Theorem42Close.lean` uses for Theorem 42; it is not proved in this repository. Jordan's curve theorem, which Hilbert quotes in the Appendix as "the theorem of C. Jordan" without a reference, is not in this list: it is proved (unit `app.jordan_theorem`), by the copied library `JordanPick` described above.

**The book's own references.** Hilbert's and the translator's footnotes cite Veronese, Klein, Pasch, Schur, Killing, Stolz, Gérard, Moore, Moulton, Dehn, Lie and Engel, and papers of Hilbert. They are reproduced with the text, as transcribed in the e-text. The units that quote them as bibliographical notes (`s14.schur`, `s18.gerard`, `s21.schur_killing_stolz`) have status `remark` and say that the cited works are not checked.
