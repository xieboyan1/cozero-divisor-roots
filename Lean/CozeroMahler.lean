import CozeroSeries
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace CozeroSeries

/-- Precisely the external value theorem required, at a fixed integer base.
Mahler (1929), equivalently the Fredholm-series statement on Becker (1994), p. 269. -/
def MahlerValues (p : ℕ) : Prop :=
  ∀ s : ℂ, s ≠ 0 → ‖s‖ < 1 → IsAlgebraic ℚ s → Transcendental ℚ (fredholm p s)

theorem exterior_transcendental {p c : ℕ} (hp : 1 < p) (hc : 0 < c)
    (mahler : MahlerValues p) {w : ℂ} (hw : ‖w‖ < 1) (hzero : limitFun p c w = 0) :
    Transcendental ℚ w⁻¹ := by
  have hn : w ≠ 0 := by
    rintro rfl
    rw [limit_zero] at hzero
    exact one_ne_zero hzero
  intro ha
  have hwalg : IsAlgebraic ℚ w := IsAlgebraic.inv_iff.mp ha
  have hsalg : IsAlgebraic ℚ (w^c) := isAlgebraic_iff_isIntegral.mpr (hwalg.isIntegral.pow _)
  have hs : ‖w^c‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hw hc.ne'
  have heq : fredholm p (w^c) = -(w⁻¹) := by
    rw [fredholm_factor hp hc hw] at hzero
    apply mul_left_cancel₀ hn
    rw [mul_neg, mul_inv_cancel₀ hn]
    exact (eq_neg_iff_add_eq_zero).2 (by simpa only [add_comm] using hzero)
  apply mahler _ (pow_ne_zero _ hn) hs hsalg
  rw [heq]
  exact isAlgebraic_iff_isIntegral.mpr ha.isIntegral.neg

#print axioms exterior_transcendental
end CozeroSeries
