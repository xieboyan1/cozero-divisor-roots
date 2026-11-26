import GraphDefinition
import CozeroSeries
import RootSetTopology

open Filter Set Metric Topology
noncomputable section
namespace GraphRootBridge

/-- At index zero the paper's sequence is undefined; the empty set extends it
to Nat. All assertions for the actual ring family use positive indices. -/
def graphRoots (p q : ℕ) : ℕ → Set ℂ
  | 0 => ∅
  | b+1 => {z | z ≠ 0 ∧ CozeroGraph.independentDominationPolynomial (p^(b+1)*q) z = 0}

theorem section_agrees (p c m : ℕ) (w : ℂ) :
    CozeroAlgebra.gapSection p c m w = CozeroSeries.sectionPoly p c m w := by
  unfold CozeroAlgebra.gapSection CozeroSeries.sectionPoly CozeroSeries.e
  congr 1

theorem roots_agree {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p<q) :
    graphRoots p q = RootSetTopology.roots (CozeroSeries.sectionPoly p (q-p-1)) := by
  funext m
  ext z
  cases m with
  | zero => simp [graphRoots, RootSetTopology.roots, CozeroSeries.sectionPoly]
  | succ b =>
    change (z ≠ 0 ∧ _) ↔ (z ≠ 0 ∧ _)
    exact and_congr_right fun hz => by
      rw [CozeroGraph.root_via_sections hp hq hpq b hz, section_agrees]

theorem positive_gap {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hpair : ¬(p=2 ∧ q=3)) : 0<q-p-1 := by
  have hp2 := hp.two_le
  rcases hp.eq_two_or_odd with h | h <;> rcases hq.eq_two_or_odd with k | k <;> omega

end GraphRootBridge
