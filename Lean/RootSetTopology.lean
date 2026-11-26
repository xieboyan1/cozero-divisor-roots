import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

/-! From local root persistence and exclusion to Hausdorff convergence. -/

open Filter Set Metric
open scoped Topology

namespace RootSetTopology

variable {X : Type*} [MetricSpace X]

/-- Every open ball at x meets every sufficiently late section. -/
def Persists (A : ℕ → Set X) (x : X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∃ y ∈ A m, dist x y < ε

theorem persists_of_mem_closure {A : ℕ → Set X} {E : Set X}
    (h : ∀ x ∈ E, Persists A x) {x : X} (hx : x ∈ closure E) :
    Persists A x := by
  intro ε hε
  obtain ⟨e, he, hxe⟩ := Metric.mem_closure_iff.mp hx (ε/2) (half_pos hε)
  filter_upwards [h e he (ε/2) (half_pos hε)] with m hm
  obtain ⟨a, ha, hea⟩ := hm
  exact ⟨a, ha, (dist_triangle x e a).trans_lt (by linarith)⟩

/-- Compact containment converts the classification of subsequential limits
into a uniform upper approximation of each entire finite root set. -/
theorem upper_approximation {A : ℕ → Set X} {C K : Set X}
    (hC : IsCompact C) (hAC : ∀ m, A m ⊆ C)
    (classify : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (x : ℕ → X) (z : X),
      (∀ j, x j ∈ A (φ j)) → Tendsto x atTop (𝓝 z) → z ∈ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ x ∈ A m, ∃ z ∈ K, dist x z < ε := by
  classical
  by_contra! hn
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop (not_eventually.mp hn)
  push_neg at hbad
  choose x hx hxsep using hbad
  obtain ⟨z, _, ψ, hψ, hz⟩ := hC.tendsto_subseq (fun i => hAC (φ i) (hx i))
  have hzK := classify (φ ∘ ψ) (hφ.comp hψ) (x ∘ ψ) z (fun i => hx (ψ i)) hz
  obtain ⟨i, hi⟩ := (Metric.tendsto_nhds.mp hz ε hε).exists
  exact (not_lt_of_ge (hxsep (ψ i) z hzK)) hi

/-- Compactness and pointwise eventual hits give uniform eventual hits. -/
theorem lower_approximation {A : ℕ → Set X} {K : Set X}
    (hK : IsCompact K) (hp : ∀ x ∈ K, Persists A x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ x ∈ K, ∃ y ∈ A m, dist x y < ε := by
  obtain ⟨s, hsK, hs, hcover⟩ := finite_cover_balls_of_compact hK (half_pos hε)
  have hall : ∀ᶠ m in atTop, ∀ x ∈ s, ∃ y ∈ A m, dist x y < ε/2 :=
    hs.eventually_all.mpr (fun x hx => hp x (hsK hx) _ (half_pos hε))
  filter_upwards [hall] with m hm x hx
  obtain ⟨a, ha⟩ := mem_iUnion.mp (hcover hx)
  obtain ⟨has, hxa⟩ := mem_iUnion.mp ha
  obtain ⟨y, hy, hay⟩ := hm a has
  exact ⟨y, hy, (dist_triangle x a y).trans_lt
    (add_lt_add_of_lt_of_le (Metric.mem_ball.mp hxa) hay.le |>.trans_eq (add_halves ε))⟩

theorem hausdorff_of_local_roots {A : ℕ → Set X} {C K E : Set X}
    (hC : IsCompact C) (hAC : ∀ m, A m ⊆ C) (hK : IsCompact K)
    (classify : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (x : ℕ → X) (z : X),
      (∀ j, x j ∈ A (φ j)) → Tendsto x atTop (𝓝 z) → z ∈ K)
    (hdense : K ⊆ closure E) (hp : ∀ z ∈ E, Persists A z) :
    Tendsto (fun m => hausdorffDist (A m) K) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [upper_approximation hC hAC classify (half_pos hε),
    lower_approximation hK (fun x hx => persists_of_mem_closure hp (hdense hx)) (half_pos hε)]
    with m upper lower
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg hausdorffDist_nonneg]
  exact (hausdorffDist_le_of_mem_dist (half_pos hε).le
    (fun x hx => (upper x hx).imp (fun y h => ⟨h.1, h.2.le⟩))
    (fun x hx => (lower x hx).imp (fun y h => ⟨h.1, h.2.le⟩))).trans_lt (half_lt_self hε)

/-- A persistent point admits roots on a strictly increasing sequence of
indices, not merely on arbitrary subsequences with repetitions. -/
theorem subsequence_of_persists {A : ℕ → Set X} {z : X} (hp : Persists A z) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : ℕ → X,
      (∀ j, x j ∈ A (φ j)) ∧ Tendsto x atTop (𝓝 z) := by
  classical
  have pick (n : ℕ) : ∃ m ≥ n, ∃ x ∈ A m, dist z x < 1 / ((n : ℝ) + 1) := by
    exact ((eventually_ge_atTop n).and (hp _ (by positivity))).exists
  choose m hm x hx hd using pick
  obtain ⟨ψ, hψ, hmψ⟩ := strictMono_subseq_of_id_le hm
  refine ⟨m ∘ ψ, hmψ, x ∘ ψ, fun j => hx (ψ j), ?_⟩
  apply Tendsto.comp _ hψ.tendsto_atTop
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const hε] with n hn
  rw [dist_comm]
  exact (hd n).trans hn

/-- Zero limits on a moving sequence inside the disk. Uses uniform
convergence on closed subdisks and continuity of the sections. -/
theorem moving_zero {S : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hU : ∀ r : ℝ, 0 < r → r < 1 → TendstoUniformlyOn S F atTop (closedBall 0 r))
    (hS : ∀ n, Continuous (S n)) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {w : ℕ → ℂ} {v : ℂ} (hv : ‖v‖ < 1) (hw : Tendsto w atTop (𝓝 v))
    (hz : ∀ n, S (φ n) (w n) = 0) : F v = 0 := by
  obtain ⟨r, hvr, hr⟩ := exists_between hv
  have hu := hU r ((norm_nonneg v).trans_lt hvr) hr
  have hnb : closedBall (0:ℂ) r ∈ 𝓝 v := closedBall_mem_nhds_of_mem (by simpa using hvr)
  have hc : ContinuousAt F v :=
    (hu.continuousOn (.of_forall (fun n => (hS n).continuousOn)) v (mem_of_mem_nhds hnb)).continuousAt hnb
  apply eq_of_forall_dist_le
  intro ε hε
  have hconv := hφ.tendsto_atTop.eventually ((Metric.tendstoUniformlyOn_iff.mp hu) (ε/2) (half_pos hε))
  obtain ⟨n, hclose, hcomp, hins⟩ := (((Metric.tendsto_nhds.mp (hc.tendsto.comp hw)) (ε/2)
    (half_pos hε)).and (hconv.and (hw.eventually hnb))).exists
  have hlast := hcomp (w n) hins
  rw [hz] at hlast
  have hh := dist_triangle (F v) (F (w n)) 0
  rw [dist_comm (F v) (F (w n))] at hh
  change dist (F (w n)) (F v) < ε/2 at hclose
  linarith

def diskZeros (F : ℂ → ℂ) : Set ℂ := {w | w ≠ 0 ∧ ‖w‖ < 1 ∧ F w = 0}
def exterior (F : ℂ → ℂ) : Set ℂ := {z | 1 < ‖z‖ ∧ F z⁻¹ = 0}
def circle : Set ℂ := {z | ‖z‖ = 1}
def roots (S : ℕ → ℂ → ℂ) (m : ℕ) : Set ℂ := {z | z ≠ 0 ∧ S m z⁻¹ = 0}

/-- Genuine angular sector: use the unit ray direction u, with w=|w|u. -/
def sector (F : ℂ → ℂ) (ξ : ℂ) (δ : ℝ) : Set ℂ :=
  {w | w ∈ diskZeros F ∧ ∃ u : ℂ, ‖u‖ = 1 ∧ dist ξ u < δ ∧ w = (‖w‖ : ℂ)*u}

/-- The sector input is Fuchs's theorem, and local finiteness follows
from isolated analytic zeros and compactness of closed subdisks. -/
theorem circle_subset_closure_diskZeros {F : ℂ → ℂ}
    (hSector : ∀ ξ ∈ circle, ∀ δ : ℝ, 0 < δ → (sector F ξ δ).Infinite)
    (hFinite : ∀ r : ℝ, r < 1 → {w : ℂ | F w = 0 ∧ ‖w‖ ≤ r}.Finite) :
    circle ⊆ closure (diskZeros F) := by
  intro ξ hξ
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨w, ⟨hw, u, hu, hξu, hwu⟩, hout⟩ := (hSector ξ hξ _ (half_pos hε)).exists_not_mem_finite
    (hFinite (1 - ε/2) (by linarith))
  have hr : 1 - ε/2 < ‖w‖ := lt_of_not_ge (fun h => hout ⟨hw.2.2, h⟩)
  have hdist : dist u w = 1 - ‖w‖ := by
    rw [dist_eq_norm, show u-w = (1-(‖w‖:ℂ))*u by rw [sub_mul, one_mul, ← hwu], norm_mul, hu, mul_one]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hw.2.1.le)]
  refine ⟨w, hw, (dist_triangle ξ u w).trans_lt ?_⟩
  rw [hdist]
  linarith

theorem exterior_eq_inv_image (F : ℂ → ℂ) :
    exterior F = (fun w : ℂ => w⁻¹) '' diskZeros F := by
  ext z
  constructor
  · rintro ⟨h, hz⟩
    have hn : z ≠ 0 := by intro hh; rw [hh, norm_zero] at h; linarith
    exact ⟨z⁻¹, ⟨inv_ne_zero hn, by simpa using inv_lt_one_of_one_lt₀ h, hz⟩, inv_inv _⟩
  · rintro ⟨w, ⟨hn, h, hw⟩, rfl⟩
    exact ⟨by simpa using (one_lt_inv₀ (norm_pos_iff.mpr hn)).mpr h, by simpa using hw⟩

theorem circle_subset_closure_exterior {F : ℂ → ℂ} (h : circle ⊆ closure (diskZeros F)) :
    circle ⊆ closure (exterior F) := by
  intro ξ hξ
  have hu : ‖ξ‖ = 1 := hξ
  have hn : ξ ≠ 0 := by intro hh; simp [hh] at hu
  have hi : ξ⁻¹ ∈ circle := by simp [circle, hu]
  rw [exterior_eq_inv_image]
  simpa using mem_closure_image (continuousAt_inv₀ (inv_ne_zero hn)) (h hi)

theorem reciprocal_persists {S : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hLocal : ∀ w ∈ diskZeros F, Persists (fun m => diskZeros (S m)) w) :
    ∀ z ∈ exterior F, Persists (roots S) z := by
  rw [exterior_eq_inv_image]
  rintro _ ⟨w, hw, rfl⟩ ε hε
  obtain ⟨δ, hd, hInv⟩ := Metric.continuousAt_iff.mp (continuousAt_inv₀ hw.1) ε hε
  filter_upwards [hLocal w hw δ hd] with m hm
  obtain ⟨v, hv, hvw⟩ := hm
  exact ⟨v⁻¹, ⟨inv_ne_zero hv.1, by simpa using hv.2.2⟩, by
    rw [dist_comm]; exact hInv (by simpa [dist_comm] using hvw)⟩

theorem classify_reciprocal {S : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hU : ∀ r : ℝ, 0 < r → r < 1 → TendstoUniformlyOn S F atTop (closedBall 0 r))
    (hS : ∀ n, Continuous (S n))
    (hLead : ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ᶠ m in atTop, ∀ z ∈ roots S m, r < ‖z‖)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (x : ℕ → ℂ) (z : ℂ)
    (hx : ∀ j, x j ∈ roots S (φ j)) (hz : Tendsto x atTop (𝓝 z)) :
    z ∈ circle ∪ exterior F := by
  have hge : 1 ≤ ‖z‖ := by
    by_contra! hsmall
    obtain ⟨r, hr, hr'⟩ := exists_between hsmall
    have h₁ := hφ.tendsto_atTop.eventually (hLead r ((norm_nonneg z).trans_lt hr).le hr')
    obtain ⟨j, hl, hh⟩ := (h₁.and (hz.norm.eventually_lt_const hr)).exists
    exact (not_lt_of_ge (hl _ (hx j)).le) hh
  rcases hge.eq_or_lt with he | he
  · exact Or.inl he.symm
  · have hn : z ≠ 0 := by intro h; rw [h, norm_zero] at he; linarith
    exact Or.inr ⟨he, moving_zero hU hS hφ (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ he)
      (hz.inv₀ hn) (fun n => (hx n).2)⟩

/-- The concrete reciprocal-root Hausdorff conclusion in the complex plane.
The index starts at 0; either the zeroth truncated section is 1 or all
sections may be indexed by m+1. -/
theorem complex_root_limits {S : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hU : ∀ r : ℝ, 0 < r → r < 1 → TendstoUniformlyOn S F atTop (closedBall 0 r))
    (hS : ∀ n, Continuous (S n))
    (hBound : ∀ m z, z ≠ 0 → S m z⁻¹ = 0 → ‖z‖ ≤ 2)
    (hLead : ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ᶠ m in atTop, ∀ z ∈ roots S m, r < ‖z‖)
    (hSector : ∀ ξ ∈ circle, ∀ δ : ℝ, 0 < δ → (sector F ξ δ).Infinite)
    (hFinite : ∀ r : ℝ, r < 1 → {w : ℂ | F w = 0 ∧ ‖w‖ ≤ r}.Finite)
    (hLocal : ∀ w ∈ diskZeros F, Persists (fun m => diskZeros (S m)) w) :
    closure (exterior F) = circle ∪ exterior F ∧ IsCompact (circle ∪ exterior F) ∧
    Tendsto (fun m => hausdorffDist (roots S m) (circle ∪ exterior F)) atTop (𝓝 0) ∧
    (∀ z : ℂ, z ∈ circle ∪ exterior F ↔ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ x : ℕ → ℂ, (∀ j, x j ∈ roots S (φ j)) ∧ Tendsto x atTop (𝓝 z)) := by
  let E := exterior F
  let K := circle ∪ E
  let C := closedBall (0:ℂ) 2
  have hc : IsCompact C := isCompact_closedBall _ _
  have hAC : ∀ m, roots S m ⊆ C := fun m x hx =>
    Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hBound m x hx.1 hx.2)
  have classify := classify_reciprocal hU hS hLead
  have hp := reciprocal_persists hLocal
  have hdense : K ⊆ closure E := union_subset
    (circle_subset_closure_exterior (circle_subset_closure_diskZeros hSector hFinite)) subset_closure
  have hEK : closure E ⊆ K := by
    intro z hz
    obtain ⟨φ, hm, x, hx, ht⟩ := subsequence_of_persists (persists_of_mem_closure hp hz)
    exact classify φ hm x z hx ht
  have hh : closure E = K := hEK.antisymm hdense
  have hKC : K ⊆ C := by
    intro z hz
    obtain ⟨φ, _, x, hx, ht⟩ := subsequence_of_persists (persists_of_mem_closure hp (hdense hz))
    exact hc.isClosed.mem_of_tendsto ht (.of_forall (fun j => hAC _ (hx j)))
  have hK : IsCompact K := hc.of_isClosed_subset (hh ▸ isClosed_closure) hKC
  refine ⟨hh, hK, hausdorff_of_local_roots hc hAC hK classify hdense hp, ?_⟩
  intro z
  exact ⟨fun hz => subsequence_of_persists (persists_of_mem_closure hp (hdense hz)),
    fun ⟨φ, hm, x, hx, ht⟩ => classify φ hm x z hx ht⟩

#print axioms complex_root_limits

/-- The set of accumulation points of the exterior limits, in mathlib's
`AccPt` sense (points distinct from the center), is exactly the circle. -/
theorem exterior_accumulation {F : ℂ → ℂ}
    (hClosure : closure (exterior F) = circle ∪ exterior F)
    (hFinite : ∀ r : ℝ, r < 1 → {w : ℂ | F w = 0 ∧ ‖w‖ ≤ r}.Finite) (z : ℂ) :
    AccPt z (𝓟 (exterior F)) ↔ z ∈ circle := by
  constructor
  · intro ha
    have hfreq := accPt_iff_frequently.mp ha
    have hcl : z ∈ closure (exterior F) := (hfreq.mono (fun _ h => h.2)).mem_closure
    rw [hClosure] at hcl
    rcases hcl with h | h
    · exact h
    exfalso
    have hz : 1 < ‖z‖ := h.1
    have hn : z ≠ 0 := by intro hh; rw [hh, norm_zero] at hz; linarith
    have hi : ‖z⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz
    obtain ⟨r, hzr, hr⟩ := exists_between hi
    let T := {w : ℂ | F w = 0 ∧ ‖w‖ ≤ r} \ {z⁻¹}
    have hf : T.Finite := (hFinite r hr).diff
    have hc : IsClosed T := hf.isClosed
    have hev := (tendsto_inv₀ hn).norm.eventually_lt_const hzr
    have hq : ∃ᶠ y in 𝓝 z, y⁻¹ ∈ T := (hfreq.and_eventually hev).mono (by
      rintro y ⟨⟨hy, he⟩, hyr⟩
      exact ⟨⟨he.2, hyr.le⟩, fun hh => hy (inv_injective hh)⟩)
    exact (hc.mem_of_frequently_of_tendsto hq (tendsto_inv₀ hn)).2 rfl
  · intro hz
    have hcl : z ∈ closure (exterior F) := hClosure ▸ Or.inl hz
    apply accPt_iff_frequently.mpr
    exact (mem_closure_iff_frequently.mp hcl).mono (fun y h => ⟨fun hh => by
      have hy : 1 < ‖y‖ := h.1
      have hn : ‖z‖ = 1 := hz
      rw [hh, hn] at hy
      exact (lt_irrefl _ hy), h⟩)

#print axioms exterior_accumulation

end RootSetTopology
