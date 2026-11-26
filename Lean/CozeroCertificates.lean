import CozeroLimitTheorem
import GraphRootBridge
import GapExponents

open Filter Set Metric RootSetTopology CozeroSeries
open scoped Topology
noncomputable section
namespace CozeroCertificates

/-- Geometry alone has just one external input. -/
theorem graph_geometry {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hpair : ¬(p=2 ∧ q=3)) (fuchs : CozeroLimitTheorem.FuchsUnitCoefficients) :
    let E := exterior (limitFun p (q-p-1))
    let K := circle ∪ E
    let A := GraphRootBridge.graphRoots p q
    closure E = K ∧ IsCompact K ∧
      Tendsto (fun m => hausdorffDist (A m) K) atTop (𝓝 0) ∧
      (∀ z : ℂ, z ∈ K ↔ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : ℕ → ℂ,
        (∀ j, x j ∈ A (φ j)) ∧ Tendsto x atTop (𝓝 z)) ∧
      (∀ z : ℂ, AccPt z (𝓟 E) ↔ z ∈ circle) := by
  dsimp only
  rw [GraphRootBridge.roots_agree hp hq hpq]
  exact CozeroLimitTheorem.geometry hp.one_lt
    (GraphRootBridge.positive_gap hp hq hpq hpair) fuchs

/-- The paper's positive-index nonexceptional main theorem, starting with
actual independent dominating sets of the cozero-divisor graph of ZMod (p^m*q).
The sequence has been extended by the empty set at m=0. The two external
theorems are explicit arguments, not additional global axioms. -/
theorem graph_limit_theorem {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hpair : ¬(p=2 ∧ q=3)) (fuchs : CozeroLimitTheorem.FuchsUnitCoefficients)
    (mahler : MahlerValues p) :
    let E := exterior (limitFun p (q-p-1))
    let K := circle ∪ E
    let A := GraphRootBridge.graphRoots p q
    closure E = K ∧ IsCompact K ∧
      Tendsto (fun m => hausdorffDist (A m) K) atTop (𝓝 0) ∧
      (∀ z : ℂ, z ∈ K ↔ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : ℕ → ℂ,
        (∀ j, x j ∈ A (φ j)) ∧ Tendsto x atTop (𝓝 z)) ∧
      (∀ z : ℂ, AccPt z (𝓟 E) ↔ z ∈ circle) ∧ (∀ z ∈ E, Transcendental ℚ z) := by
  dsimp only
  rw [GraphRootBridge.roots_agree hp hq hpq]
  exact CozeroLimitTheorem.nonexceptional hp.one_lt
    (GraphRootBridge.positive_gap hp hq hpq hpair) fuchs mahler

#check CozeroGraph.exceptional_graph_roots
#check CozeroGraph.exceptional_graph_no_finite_limit
#print axioms graph_limit_theorem
#print axioms graph_geometry
#print axioms CozeroGraph.exceptional_graph_roots
#print axioms CozeroGraph.exceptional_graph_no_finite_limit
end CozeroCertificates
