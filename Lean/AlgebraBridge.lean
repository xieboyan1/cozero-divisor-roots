import CozeroChains
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.List

/-! Evaluate the chain-weight polynomial and its reciprocal on the actual complex field. -/
namespace CozeroAlgebra
open CozeroChains Filter
open scoped Topology

noncomputable def chainPolynomial (p q m : ℕ) (z : ℂ) : ℂ :=
  ((exponents p q m).map fun k => z^k).sum

noncomputable def gapSection (p c m : ℕ) (w : ℂ) : ℂ :=
  1 + ((List.range m).map fun j => w^(1+c*p^j)).sum

theorem reciprocal (p q b : ℕ) (hp : 0 < p) (hpq : p < q) (z : ℂ) (hz : z ≠ 0) :
    chainPolynomial p q (b+1) z = z^((q-1)*p^b) * gapSection p (q-p-1) (b+1) (z⁻¹) := by
  unfold chainPolynomial exponents gapSection
  rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.sum_cons, first_weight p q b hp,
    mul_add, mul_one, ← List.sum_map_mul_left]
  congr 1
  rw [List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j hj
  have hj' := List.mem_range.mp hj
  have h := reversed_exponent p q b j hp hpq (by omega)
  change z^(weight p q (b+1) (j+1)) = _
  rw [← h, pow_add, mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hz), mul_one]

theorem nonzero_root_iff (p q b : ℕ) (hp : 0 < p) (hpq : p < q) {z : ℂ} (hz : z ≠ 0) :
    chainPolynomial p q (b+1) z = 0 ↔ gapSection p (q-p-1) (b+1) z⁻¹ = 0 := by
  rw [reciprocal p q b hp hpq z hz]
  simp [pow_ne_zero _ hz]

theorem exceptional_factor (b : ℕ) (z : ℂ) :
    chainPolynomial 2 3 (b+1) z = z^(2^(b+1)-1) * (z + ((b+1 : ℕ) : ℂ)) := by
  simp only [chainPolynomial, exceptional_exponents, List.map_cons, List.sum_cons,
    List.map_replicate, List.sum_replicate, nsmul_eq_mul, mul_add]
  have h : 0 < 2^(b+1) := Nat.two_pow_pos _
  have heq : 2^(b+1) = (2^(b+1)-1)+1 := by omega
  calc
    _ = z^((2^(b+1)-1)+1) + (b+1 : ℕ) * z^(2^(b+1)-1) := by
      rw [← heq]
    _ = _ := by rw [pow_succ, mul_comm (↑(b+1) : ℂ)]

theorem exceptional_root_set (b : ℕ) :
    {z : ℂ | z ≠ 0 ∧ chainPolynomial 2 3 (b+1) z = 0} = {-((b+1 : ℕ) : ℂ)} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, exceptional_factor]
  constructor
  · rintro ⟨hz,h⟩
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hz))
  · rintro rfl
    constructor
    · exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero b))
    · rw [neg_add_cancel, mul_zero]

theorem exceptional_no_finite_limit {index : ℕ → ℕ} (hi : StrictMono index)
    {roots : ℕ → ℂ} (hr : ∀ i, roots i ≠ 0 ∧ chainPolynomial 2 3 (index i+1) (roots i) = 0)
    (z : ℂ) : ¬ Tendsto roots atTop (𝓝 z) := by
  intro hconv
  have hroot (i : ℕ) : roots i = -((index i + 1 : ℕ) : ℂ) := by
    have hh : roots i ∈ {w : ℂ | w ≠ 0 ∧ chainPolynomial 2 3 (index i+1) w = 0} := hr i
    rwa [exceptional_root_set, Set.mem_singleton_iff] at hh
  have hnorm (i : ℕ) : ‖roots i‖ = ((index i+1 : ℕ) : ℝ) := by rw [hroot, norm_neg, Complex.norm_natCast]
  have hidx : StrictMono (fun i => index i+1) := fun a b hab => Nat.add_lt_add_right (hi hab) 1
  have inf : Tendsto (fun i => ‖roots i‖) atTop atTop := by
    simpa only [hnorm] using (tendsto_natCast_atTop_atTop (R := ℝ)).comp hidx.tendsto_atTop
  exact not_tendsto_atTop_of_tendsto_nhds hconv.norm inf

#print axioms reciprocal
#print axioms exceptional_root_set
#print axioms exceptional_no_finite_limit
end CozeroAlgebra

