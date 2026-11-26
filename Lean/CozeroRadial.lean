import CozeroSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Filter Topology
open scoped BigOperators
noncomputable section
namespace CozeroSeries

theorem half_geom (m : ℕ) :
    (∑ j ∈ Finset.range m, (1/2 : ℝ)^(j+1)) + (1/2 : ℝ)^m = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ (1/2 : ℝ) m]
    linarith

theorem no_small_section_root {p c : ℕ} (hp : 1<p) (hc : 0<c) (m : ℕ)
    {w : ℂ} (hw : ‖w‖≤1/2) : sectionPoly p c m w ≠ 0 := by
  have hb (j : ℕ) : ‖w^(e p c j)‖ ≤ (1/2 : ℝ)^(j+1) := by
    have hj : j < p^j := Nat.lt_pow_self hp
    have hmul : 1*p^j ≤ c*p^j := Nat.mul_le_mul_right _ hc
    have he : j+1 ≤ e p c j := by simp only [one_mul] at hmul; unfold e; omega
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hw _).trans
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) he)
  intro h
  have he : (∑ j ∈ Finset.range m, w ^ e p c j) = -1 := by
    unfold sectionPoly at h
    exact (eq_neg_iff_add_eq_zero).2 (by simpa only [add_comm] using h)
  have hbound := (norm_sum_le (Finset.range m) (fun j => w^e p c j)).trans
    (Finset.sum_le_sum (fun j _ => hb j))
  rw [he, norm_neg, norm_one] at hbound
  have hs := half_geom m
  have hpos : (0:ℝ) < (1/2 : ℝ)^m := pow_pos (by norm_num) _
  linarith

theorem reciprocal_bound {p c : ℕ} (hp : 1<p) (hc : 0<c) (m : ℕ)
    {z : ℂ} (hz : z≠0) (hroot : sectionPoly p c m z⁻¹=0) : ‖z‖≤2 := by
  by_contra! h
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  apply no_small_section_root hp hc m (w := z⁻¹) _ hroot
  rw [norm_inv, inv_eq_one_div, div_le_div_iff₀ hn (by norm_num : (0:ℝ)<2)]
  linarith

theorem e_mono {p c : ℕ} (hp : 1<p) {j k : ℕ} (hj : j≤k) :
    e p c j ≤ e p c k := by
  unfold e
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hj)) _

theorem gap_ge {p c : ℕ} (hp : 1<p) (hc : 0<c) (m : ℕ) :
    e p c m + m ≤ e p c (m+1) := by
  have h1 : m < p^m := Nat.lt_pow_self hp
  have ha : 1*p^m ≤ c*p^m := Nat.mul_le_mul_right _ hc
  have hb : (c*p^m)*2 ≤ (c*p^m)*p := Nat.mul_le_mul_left _ hp
  simp only [one_mul] at ha
  simp only [e, pow_succ, ← Nat.mul_assoc]
  omega

theorem section_norm_large {p c : ℕ} (hp : 1<p) (m : ℕ) {w : ℂ} (hw : 1≤‖w‖) :
    ‖sectionPoly p c (m+1) w‖ ≤ ((m:ℝ)+2)*‖w‖^e p c m := by
  have hpow : 1 ≤ ‖w‖^e p c m := one_le_pow₀ hw
  have hb (j : ℕ) (hj : j∈Finset.range (m+1)) : ‖w^e p c j‖ ≤ ‖w‖^e p c m := by
    rw [norm_pow]
    exact pow_le_pow_right₀ hw (e_mono hp (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
  have hs := (norm_sum_le (Finset.range (m+1)) (fun j => w^e p c j)).trans (Finset.sum_le_sum hb)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hs
  unfold sectionPoly
  refine (norm_add_le _ _).trans ?_
  rw [norm_one]
  nlinarith

theorem root_forces_slow_decay {p c : ℕ} (hp : 1<p) (hc : 0<c) (m : ℕ)
    {z : ℂ} (hz : z≠0) (hzn : ‖z‖≤1)
    (hroot : sectionPoly p c (m+2) z⁻¹ = 0) : 1 ≤ ((m:ℝ)+2)*‖z‖^m := by
  let w := z⁻¹
  have hzpos := norm_pos_iff.mpr hz
  have hw : 1≤‖w‖ := by simpa [w, norm_inv, one_le_inv₀ hzpos] using hzn
  have hsum : sectionPoly p c (m+1) w + w^e p c (m+1) = 0 := by
    simpa only [sectionPoly, Finset.sum_range_succ (n := m+1), add_assoc, w] using hroot
  have heq : w^e p c (m+1) = - sectionPoly p c (m+1) w :=
    (eq_neg_iff_add_eq_zero).2 (by simpa only [add_comm] using hsum)
  have he := congrArg norm heq
  rw [norm_pow, norm_neg] at he
  have hpow := (pow_le_pow_right₀ hw (gap_ge hp hc m)).trans (he.le.trans (section_norm_large hp m hw))
  rw [pow_add, mul_comm (‖w‖^e p c m)] at hpow
  have hpow' : ‖w‖^m ≤ (m:ℝ)+2 :=
    le_of_mul_le_mul_right hpow (pow_pos (by linarith : 0<‖w‖) _)
  change ‖z⁻¹‖^m ≤ (m:ℝ)+2 at hpow'
  rw [norm_inv, inv_pow, inv_eq_one_div] at hpow'
  exact (div_le_iff₀ (pow_pos hzpos _)).mp hpow'

theorem eventually_outside {p c : ℕ} (hp : 1<p) (hc : 0<c) {r : ℝ}
    (hr : 0≤r) (hr1 : r<1) :
    ∀ᶠ m : ℕ in atTop, ∀ z : ℂ, z≠0 → sectionPoly p c m z⁻¹=0 → r<‖z‖ := by
  have h1 := tendsto_pow_const_mul_const_pow_of_abs_lt_one (r := r) 1 (by simpa [abs_of_nonneg hr] using hr1)
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).const_mul (2:ℝ)
  have hlim : Tendsto (fun m : ℕ => ((m:ℝ)+2)*r^m) atTop (𝓝 0) := by
    simpa only [pow_one, mul_zero, add_zero, add_mul] using h1.add h2
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const (by norm_num : (0:ℝ)<1))
  apply eventually_atTop.mpr
  refine ⟨N+2, ?_⟩
  intro n hn z hz hroot
  let m := n-2
  have hn' : n = m+2 := by dsimp [m]; omega
  rw [hn'] at hroot
  by_contra! hzsmall
  have hlow := root_forces_slow_decay hp hc m hz (hzsmall.trans hr1.le) hroot
  have hb := pow_le_pow_left₀ (norm_nonneg _) hzsmall m
  have hu := mul_le_mul_of_nonneg_left hb (by positivity : 0≤(m:ℝ)+2)
  exact (not_lt_of_ge (hlow.trans hu)) (hN m (by dsimp [m]; omega))

end CozeroSeries
