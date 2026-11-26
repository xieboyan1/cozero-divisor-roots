import CozeroSeries
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros

open Set Filter Metric Topology
open scoped BigOperators
noncomputable section
namespace CozeroSeries

theorem section_diff (p c m : ℕ) : Differentiable ℂ (sectionPoly p c m) := by
  unfold sectionPoly
  fun_prop

theorem limit_analytic {p c : ℕ} (hp : 1<p) (hc : 0<c) :
    AnalyticOnNhd ℂ (limitFun p c) (ball 0 1) := by
  intro w hw
  have hw' : ‖w‖<1 := by simpa using hw
  obtain ⟨r, hwr, hr⟩ := exists_between hw'
  have hr0 := (norm_nonneg w).trans hwr.le
  have hd := Complex.differentiableOn_tsum_of_summable_norm
    (summable_geometric_of_lt_one hr0 hr)
    (U := ball (0:ℂ) r) (F := fun j w => w^(e p c j))
    (fun j => (differentiable_id.pow _).differentiableOn) isOpen_ball
    (fun j z hz => term_bound hp hc hr0 hr.le j (by simpa using (mem_ball.mp hz).le))
  exact ((differentiableOn_const (1:ℂ)).add hd).analyticAt (isOpen_ball.mem_nhds (by simpa using hwr))

theorem isolated {p c : ℕ} (hp : 1<p) (hc : 0<c) {w : ℂ} (hw : ‖w‖<1) :
    ∀ᶠ y in 𝓝[≠] w, limitFun p c y ≠ 0 := by
  by_contra hf
  have hfreq : ∃ᶠ y in 𝓝[≠] w, limitFun p c y = 0 := hf
  have he := (limit_analytic hp hc).eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball (0:ℂ) (1:ℝ)).isPreconnected (by simpa using hw) hfreq
  have h0 := he (mem_ball_self (by norm_num : (0:ℝ)<1))
  simp [limit_zero] at h0

theorem finite_subdisk {p c : ℕ} (hp : 1<p) (hc : 0<c) (r : ℝ) (hr : r<1) :
    {w : ℂ | limitFun p c w = 0 ∧ ‖w‖≤r}.Finite := by
  by_contra hi
  obtain ⟨x,hx,hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hi
    (isCompact_closedBall (0:ℂ) r) (fun w hw => by simpa using hw.2)
  have hx' : ‖x‖ ≤ r := by simpa using hx
  have hn := eventually_nhdsWithin_iff.mp (isolated hp hc (hx'.trans_lt hr))
  exact (accPt_iff_frequently.mp hacc)
    (hn.mono fun y hy ⟨hne, hz⟩ => hy hne hz.1)

theorem local_zeros {p c : ℕ} (hp : 1<p) (hc : 0<c) {w : ℂ}
    (hw : ‖w‖<1) (hw0 : limitFun p c w=0) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ m : ℕ in atTop, ∃ y : ℂ, (y ≠ 0 ∧ ‖y‖<1 ∧ sectionPoly p c m y = 0) ∧ dist w y<ε := by
  have hiso := eventually_nhdsWithin_iff.mp (isolated hp hc hw)
  obtain ⟨ρ, hρ, hband⟩ := nhds_basis_closedBall.mem_iff.mp hiso
  let a := min (ε/2) (min ρ ((1-‖w‖)/2))
  have ha : 0<a := lt_min (by linarith) (lt_min hρ (by linarith))
  have haε : a<ε := (min_le_left _ _).trans_lt (by linarith)
  have haρ : a≤ρ := (min_le_right _ _).trans (min_le_left _ _)
  have haR : a≤(1-‖w‖)/2 := (min_le_right _ _).trans (min_le_right _ _)
  let R := a+‖w‖
  have hR : R<1 := by dsimp [R]; linarith
  have hR0 : 0≤R := add_nonneg ha.le (norm_nonneg _)
  have hnorm {y : ℂ} (hy : y∈closedBall w a) : ‖y‖≤R := by
    simpa [R,dist_zero_right] using (dist_triangle y w 0).trans
      (add_le_add_right (mem_closedBall.mp hy) (dist w 0))
  have hsp (y : ℂ) (hy : y∈sphere w a) : limitFun p c y ≠ 0 :=
    hband (closedBall_subset_closedBall haρ (sphere_subset_closedBall hy))
      (ne_of_mem_sphere hy ha.ne')
  have hcont := (limit_analytic hp hc).continuousOn
  obtain ⟨v,hv,hmin⟩ := (isCompact_sphere w a).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr ha.le) (hcont.norm.mono
      (fun y hy => by simpa using (hnorm (sphere_subset_closedBall hy)).trans_lt hR))
  let b := ‖limitFun p c v‖
  have hb : 0<b := norm_pos_iff.mpr (hsp v hv)
  have hU := (Metric.tendstoUniformlyOn_iff.mp (uniform_sections hp hc hR0 hR))
    (b/3) (by linarith)
  filter_upwards [hU] with m hm
  have hcenter : ‖sectionPoly p c m w‖ < b/3 := by
    simpa [hw0] using hm w (hnorm (mem_closedBall_self ha.le))
  have hboundary (y : ℂ) (hy : y∈sphere w a) : b/2 ≤ ‖sectionPoly p c m y‖ := by
    have hh := hm y (hnorm (sphere_subset_closedBall hy))
    have hl : b ≤ ‖limitFun p c y‖ := hmin hy
    have hn := norm_sub_norm_le (limitFun p c y) (sectionPoly p c m y)
    rw [dist_eq_norm] at hh
    linarith
  have hex : ∃ y ∈ closedBall w a, sectionPoly p c m y = 0 := by
    by_contra! hno
    have hd : DiffContOnCl ℂ (fun y => (sectionPoly p c m y)⁻¹) (ball w a) :=
      ⟨(section_diff p c m).differentiableOn.inv (fun y hy => hno y (ball_subset_closedBall hy)),
       (section_diff p c m).continuous.continuousOn.inv₀ (fun y hy =>
           hno y ((closure_ball w ha.ne').le hy))⟩
    have hh := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
      (C := (b/2)⁻¹) (fun y hy => by
        rw [frontier_ball w ha.ne'] at hy
        rw [norm_inv]
        exact inv_anti₀ (by linarith) (hboundary y hy))
      (z := w) (subset_closure (mem_ball_self ha))
    rw [norm_inv] at hh
    have hn := norm_pos_iff.mpr (hno w (mem_closedBall_self ha.le))
    have hge := (inv_le_inv₀ hn (by linarith : 0<b/2)).mp hh
    linarith
  obtain ⟨y,hy,hy0⟩ := hex
  refine ⟨y, ⟨?_, (hnorm hy).trans_lt hR, hy0⟩, ?_⟩
  · rintro rfl
    simp [sectionPoly, e, Nat.add_comm 1] at hy0
  · rw [dist_comm]
    exact (mem_closedBall.mp hy).trans_lt haε

end CozeroSeries
