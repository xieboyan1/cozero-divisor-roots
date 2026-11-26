import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith

/-! The section polynomials, their analytic limit and the Fredholm series. -/
open Filter Topology
open scoped BigOperators
noncomputable section
namespace CozeroSeries

def e (p c j : ℕ) := 1+c*p^j
def sectionPoly (p c m : ℕ) (w : ℂ) := 1+∑ j ∈ Finset.range m, w^(e p c j)
def limitFun (p c : ℕ) (w : ℂ) := 1+∑' j : ℕ, w^(e p c j)
def fredholm (p : ℕ) (s : ℂ) := ∑' j : ℕ, s^(p^j)

theorem index_le (p c j : ℕ) (hp : 1<p) (hc : 0<c) : j ≤ e p c j := by
  have h := Nat.lt_pow_self (n := j) hp
  have h' : 1*p^j ≤ c*p^j := Nat.mul_le_mul_right _ hc
  simp only [one_mul] at h'
  unfold e
  omega

theorem term_bound {p c : ℕ} (hp : 1<p) (hc : 0<c)
    {r : ℝ} (hr : 0≤r) (hr1 : r≤1) (j : ℕ) {w : ℂ} (hw : ‖w‖≤r) :
    ‖w ^ e p c j‖ ≤ r ^ j := by
  rw [norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _) hw _).trans
    (pow_le_pow_of_le_one hr hr1 (index_le p c j hp hc))

theorem uniform_sections {p c : ℕ} (hp : 1<p) (hc : 0<c)
    {r : ℝ} (hr : 0≤r) (hr1 : r<1) :
    TendstoUniformlyOn (sectionPoly p c) (limitFun p c) atTop {w : ℂ | ‖w‖ ≤ r} := by
  have h := tendstoUniformlyOn_tsum_nat (summable_geometric_of_lt_one hr hr1)
    (s := {w : ℂ | ‖w‖ ≤ r}) (f := fun j w => w ^ e p c j)
    (fun j _ hw => term_bound hp hc hr hr1.le j hw)
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  simpa only [sectionPoly, limitFun, dist_add_left] using h ε hε

theorem fredholm_summable {p : ℕ} (hp : 1 < p) {s : ℂ} (hs : ‖s‖<1) :
    Summable (fun j : ℕ => s^(p^j)) := by
  apply (summable_geometric_of_lt_one (norm_nonneg s) hs).of_norm_bounded
  intro j
  rw [norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) hs.le (Nat.lt_pow_self (n := j) hp).le

theorem fredholm_factor {p c : ℕ} (hp : 1<p) (hc : 0<c) {w : ℂ} (hw : ‖w‖<1) :
    limitFun p c w = 1 + w * fredholm p (w^c) := by
  have hnorm : ‖w^c‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hw hc.ne'
  have h := fredholm_summable hp hnorm
  unfold limitFun fredholm
  rw [← h.tsum_mul_left]
  simp only [e, pow_add, pow_one, pow_mul]

theorem limit_zero (p c : ℕ) : limitFun p c 0 = 1 := by
  simp [limitFun, e, Nat.add_comm 1]

end CozeroSeries
