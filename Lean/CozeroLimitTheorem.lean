import RootSetTopology
import CozeroLocalZeros
import CozeroRadial
import CozeroMahler

/-! The nonexceptional limit theorem for the reciprocal sections.
Two classical literature results are exposed as explicit propositions. -/

open Filter Set Metric CozeroSeries RootSetTopology
open scoped Topology
noncomputable section

namespace CozeroLimitTheorem

/-- Unit-coefficient, constant-offset case of the sector theorem of Fuchs
(Sons, Pacific J. Math. 43 (1972), p. 515). The fixed lower ratio 3/2 is
sufficient for every exponent sequence in this paper. The angular neighborhood
uses chordal distance between unit directions and a free positive radius. -/
def FuchsUnitCoefficients : Prop :=
  ∀ (n : ℕ → ℕ) (b : ℂ), 0 < n 0 → (∀ j, 3 * n j ≤ 2 * n (j+1)) →
    AnalyticOnNhd ℂ (fun w : ℂ => b + ∑' j : ℕ, w^(n j)) (ball 0 1) →
    ∀ ξ ∈ circle, ∀ δ : ℝ, 0 < δ →
      (sector (fun w : ℂ => b + ∑' j : ℕ, w^(n j)) ξ δ).Infinite

/-- Twice each new exponent is at least three times its predecessor. -/
theorem gap_three_halves {p c : ℕ} (hp : 1 < p) (hc : 0 < c) (j : ℕ) :
    3 * e p c j ≤ 2 * e p c (j+1) := by
  have hpow : 0 < p^j := Nat.pow_pos (by omega)
  have hpos : 0 < c*p^j := Nat.mul_pos hc hpow
  have hmul : (c*p^j)*2 ≤ (c*p^j)*p := Nat.mul_le_mul_left _ hp
  simp only [e, pow_succ, ← Nat.mul_assoc]
  omega

theorem geometry {p c : ℕ} (hp : 1 < p) (hc : 0 < c)
    (fuchs : FuchsUnitCoefficients) :
    let E := exterior (limitFun p c)
    let K := circle ∪ E
    let A := roots (sectionPoly p c)
    closure E = K ∧ IsCompact K ∧
      Tendsto (fun m => hausdorffDist (A m) K) atTop (𝓝 0) ∧
      (∀ z : ℂ, z ∈ K ↔ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : ℕ → ℂ,
        (∀ j, x j ∈ A (φ j)) ∧ Tendsto x atTop (𝓝 z)) ∧
      (∀ z : ℂ, AccPt z (𝓟 E) ↔ z ∈ circle) := by
  let S := sectionPoly p c
  let F := limitFun p c
  have hu (r : ℝ) (hr : 0 < r) (hr1 : r < 1) : TendstoUniformlyOn S F atTop (closedBall 0 r) := by
    have he : closedBall (0:ℂ) r = {w : ℂ | ‖w‖ ≤ r} := by ext w; simp
    rw [he]
    exact uniform_sections hp hc hr.le hr1
  have hLead (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
      ∀ᶠ m : ℕ in atTop, ∀ z ∈ roots S m, r < ‖z‖ := by
    filter_upwards [eventually_outside hp hc hr hr1] with m hm z hz
    exact hm z hz.1 hz.2
  have hSector : ∀ ξ ∈ circle, ∀ δ : ℝ, 0 < δ → (sector F ξ δ).Infinite :=
    fuchs (e p c) 1 (by simp [e]) (gap_three_halves hp hc) (limit_analytic hp hc)
  have hLocal : ∀ w ∈ diskZeros F, Persists (fun m => diskZeros (S m)) w :=
    fun _ hw _ hε => local_zeros hp hc hw.2.1 hw.2.2 _ hε
  obtain ⟨hcl, hcompact, hhaus, hsubseq⟩ := complex_root_limits hu
    (fun n => (section_diff p c n).continuous)
    (fun m _ hz h => reciprocal_bound hp hc m hz h)
    hLead hSector (finite_subdisk hp hc) hLocal
  exact ⟨hcl, hcompact, hhaus, hsubseq, exterior_accumulation hcl (finite_subdisk hp hc)⟩

theorem nonexceptional {p c : ℕ} (hp : 1 < p) (hc : 0 < c)
    (fuchs : FuchsUnitCoefficients) (mahler : MahlerValues p) :
    let E := exterior (limitFun p c)
    let K := circle ∪ E
    let A := roots (sectionPoly p c)
    closure E = K ∧ IsCompact K ∧
      Tendsto (fun m => hausdorffDist (A m) K) atTop (𝓝 0) ∧
      (∀ z : ℂ, z ∈ K ↔ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : ℕ → ℂ,
        (∀ j, x j ∈ A (φ j)) ∧ Tendsto x atTop (𝓝 z)) ∧
      (∀ z : ℂ, AccPt z (𝓟 E) ↔ z ∈ circle) ∧ (∀ z ∈ E, Transcendental ℚ z) := by
  obtain ⟨hcl, hcpt, hdist, hseq, hacc⟩ := geometry hp hc fuchs
  refine ⟨hcl, hcpt, hdist, hseq, hacc, ?_⟩
  intro z hz
  obtain ⟨w, hw, rfl⟩ := (exterior_eq_inv_image (limitFun p c)) ▸ hz
  exact exterior_transcendental hp hc mahler hw.2.1 hw.2.2

#print axioms geometry
#print axioms nonexceptional
end CozeroLimitTheorem
