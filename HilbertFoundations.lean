import HilbertFoundations.Basic
import HilbertFoundations.Order
import HilbertFoundations.Congruence
import HilbertFoundations.Analytic
import HilbertFoundations.Independence
import HilbertFoundations.Pascal
import HilbertFoundations.Proportion
import HilbertFoundations.Areas
import HilbertFoundations.Desargues
import HilbertFoundations.NonDesargues
import HilbertFoundations.DesarguesAlgebra
import HilbertFoundations.NonPascal
import HilbertFoundations.Constructions
import HilbertFoundations.Commentary
import HilbertFoundations.OrderPolygon
import HilbertFoundations.CongruenceClose
import HilbertFoundations.CompletenessClose
import HilbertFoundations.CoordinatesClose
import HilbertFoundations.ConstructionsClose
import HilbertFoundations.CommentaryClose
import HilbertFoundations.JordanCurveClose
import HilbertFoundations.Theorem42Close

/-!
# Hilbert, *The Foundations of Geometry*, in Lean

Root module (built by `lake build`, imported by `scripts/AxiomsAudit.lean`): the axioms and every
chapter, in the order of the book, then the introduction, conclusion and appendix (`Commentary`).

The last eight imports are the proofs of statements that the chapter files only state: Theorem 6
(`OrderPolygon`), Theorem 18 and the properties of the circle (`CongruenceClose`), the consequences
of the axiom of completeness (`CompletenessClose`), co-ordinates in space (`CoordinatesClose`),
Theorem 43 and the constructions of § 39 (`ConstructionsClose`), Dehn's geometries of the
conclusion (`CommentaryClose`), Jordan's curve theorem (`JordanCurveClose`, from the proof in
the library `JordanPick`, a copy of files of another project: see `JordanPick/README.md`), and
Theorem 42 (`Theorem42Close`, from the Hasse–Minkowski theorem of the library Tau Ceti, a
dependency of this package).
-/
