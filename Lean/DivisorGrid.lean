import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import CozeroChains

/-! The cozero graph is the incomparability graph of gcd labels with repeated
vertices. We prove the arithmetic adjacency bridge and classify all maximal
independent sets of arbitrary nonempty fibres over the two-row divisor grid. -/
namespace CozeroGrid

theorem principal_membership {N : ℕ} [NeZero N] (x y : ZMod N) :
    x ∣ y ↔ Nat.gcd x.val N ∣ Nat.gcd y.val N := by
  constructor
  · rintro ⟨v,rfl⟩
    apply Nat.dvd_gcd _ (Nat.gcd_dvd_right _ _)
    rw [ZMod.val_mul]
    exact (Nat.dvd_mod_iff (Nat.gcd_dvd_right x.val N)).mpr
      (dvd_mul_of_dvd_left (Nat.gcd_dvd_left x.val N) _)
  · intro h
    obtain ⟨a,ha⟩ := dvd_trans h (Nat.gcd_dvd_left y.val N)
    refine ⟨x⁻¹*(a : ZMod N), ?_⟩
    calc
      y = (y.val : ZMod N) := (ZMod.natCast_zmod_val y).symm
      _ = x*(x⁻¹*(a : ZMod N)) := by rw [ha, Nat.cast_mul, ← ZMod.mul_inv_eq_gcd, mul_assoc]

theorem exceptional_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hlt : p < q) :
    q-p-1 = 0 ↔ p = 2 ∧ q = 3 := by
  obtain hp2 := hp.two_le
  obtain hp' := hp.eq_two_or_odd
  obtain hq' := hq.eq_two_or_odd
  omega

inductive Cell where
  | lo (i : ℕ)
  | hi (i : ℕ)
deriving DecidableEq

def proper (m : ℕ) : Cell → Prop
  | .lo i => 0 < i ∧ i ≤ m
  | .hi i => i < m

/-- In the product of the exponent interval [0,m] with [0,1], a mixed
pair of cells is comparable exactly when the lower-row index is smaller or equal. -/
def comp : Cell → Cell → Prop
  | .lo i, .hi j => i ≤ j
  | .hi j, .lo i => i ≤ j
  | .lo _, .lo _ | .hi _, .hi _ => True

def cut (k : ℕ) : Cell → Prop
  | .lo i => i ≤ k
  | .hi j => k ≤ j

/-- Independent, and each outside vertex has a neighbor in the set. The
adjacency relation of this graph is the negation of label comparability. -/
def maximalIndependent {V : Type*} (label : V → Cell) (S : V → Prop) : Prop :=
  (∀ x y, S x → S y → comp (label x) (label y)) ∧
  (∀ x, (∀ y, S y → comp (label x) (label y)) → S x)

private theorem greatest {P : ℕ → Prop} (n : ℕ) (zero : P 0) :
    ∃ k, k ≤ n ∧ P k ∧ ∀ j, j ≤ n → P j → j ≤ k := by
  induction n with
  | zero => exact ⟨0, le_rfl, zero, fun _ h _ => h⟩
  | succ n ih =>
    by_cases h : P (n+1)
    · exact ⟨n+1, le_rfl, h, fun _ h' _ => h'⟩
    · obtain ⟨k,hk,hp,hmax⟩ := ih
      exact ⟨k, by omega, hp, fun j hj pj => hmax _ (by
        have hn : j ≠ n+1 := fun e => h (e ▸ pj)
        omega) pj⟩

theorem all_maximal_cuts {V : Type*} {m : ℕ} (label : V → Cell)
    (labels : ∀ c, proper m c ↔ ∃ x, label x = c) (S : V → Prop) :
    maximalIndependent label S ↔ ∃ k, k ≤ m ∧ ∀ x, S x ↔ cut k (label x) := by
  classical
  have valid (x : V) : proper m (label x) := (labels _).2 ⟨x,rfl⟩
  constructor
  · intro ⟨hind,hmax⟩
    let low (i : ℕ) := i = 0 ∨ ∃ x, S x ∧ label x = .lo i
    obtain ⟨k,hkm,hlk,largest⟩ := greatest (P := low) m (Or.inl rfl)
    have selectedLow {x : V} {i : ℕ} (hx : S x) (hi : label x = .lo i) : i ≤ k :=
      largest i (by have h := valid x; rw [hi] at h; exact h.2) (Or.inr ⟨x,hx,hi⟩)
    have selectedHigh {x : V} {j : ℕ} (hx : S x) (hj : label x = .hi j) : k ≤ j := by
      rcases hlk with h0 | ⟨y,hy,yl⟩
      · omega
      · have h := hind y x hy hx
        simpa [yl,hj,comp] using h
    have upperCut {x : V} {j : ℕ} (hj : label x = .hi j) (hj' : k ≤ j) : S x := by
      apply hmax
      intro y hy
      cases hl : label y with
      | hi i => simp [hj,hl,comp]
      | lo i => simpa [hj,hl,comp] using (selectedLow hy hl).trans hj'
    refine ⟨k,hkm,fun x => ?_⟩
    cases hx : label x with
    | lo i =>
      refine ⟨fun hh => selectedLow hh hx, fun hi => ?_⟩
      apply hmax
      intro y hy
      cases ly : label y with
      | lo j => simp [hx,ly,comp]
      | hi j => simpa [hx,ly,comp] using Nat.le_trans (show i ≤ k from hi) (selectedHigh hy ly)
    | hi j => exact ⟨fun hh => selectedHigh hh hx, fun hj => upperCut hx hj⟩
  · rintro ⟨k,hkm,rep⟩
    constructor
    · intro x y hx hy
      have xi := (rep x).mp hx
      have yi := (rep y).mp hy
      cases cx : label x <;> cases cy : label y <;> simp_all [comp,cut] <;> omega
    · intro x hcomp
      apply (rep x).mpr
      have vx := valid x
      cases cx : label x with
      | lo i =>
        change i ≤ k
        by_contra hg
        have hm : k < m := by rw [cx] at vx; exact Nat.lt_of_lt_of_le (by omega) vx.2
        obtain ⟨y,hy⟩ := (labels (.hi k)).mp hm
        have sy := (rep y).mpr (by simp [hy,cut])
        exact hg (by simpa [cx,hy,comp] using hcomp y sy)
      | hi j =>
        change k ≤ j
        by_contra hg
        have hk0 : 0 < k := by omega
        obtain ⟨y,hy⟩ := (labels (.lo k)).mp ⟨hk0,hkm⟩
        have sy := (rep y).mpr (by simp [hy,cut])
        exact hg (by simpa [cx,hy,comp] using hcomp y sy)

theorem cut_parameter_unique {V : Type*} {m : ℕ} (label : V → Cell)
    (labels : ∀ c, proper m c ↔ ∃ x, label x = c) {k l : ℕ} (hk : k≤m) (hl : l≤m)
    (same : ∀ x, cut k (label x) ↔ cut l (label x)) : k=l := by
  have le_of_cut (a b : ℕ) (ha : a≤m) (leq : ∀ x, cut a (label x) → cut b (label x)) :
      a≤b := by
    cases a with
    | zero => exact Nat.zero_le _
    | succ a =>
      obtain ⟨x,hx⟩ := (labels (.lo (a+1))).mp ⟨by omega,ha⟩
      have h := leq x (by simp [hx,cut])
      simpa [hx,cut] using h
  exact Nat.le_antisymm (le_of_cut k l hk fun x => (same x).1)
    (le_of_cut l k hl fun x => (same x).2)

def divisorValue (p q : ℕ) : Cell → ℕ
  | .lo i => p^i
  | .hi i => p^i*q

theorem divisor_rows {p q m d : ℕ} (hp : p.Prime) (hq : q.Prime) (hd : d ∣ p^m*q) :
    ∃ i ≤ m, d = p^i ∨ d = p^i*q := by
  by_cases hq' : q ∣ d
  · obtain ⟨a,rfl⟩ := hq'
    have h : a ∣ p^m := (Nat.mul_dvd_mul_iff_left hq.pos).mp (by simpa [Nat.mul_comm q] using hd)
    obtain ⟨i,hi,rfl⟩ := (Nat.dvd_prime_pow hp).mp h
    exact ⟨i,hi,Or.inr (Nat.mul_comm _ _)⟩
  · have h := (hq.coprime_iff_not_dvd.mpr hq').symm.dvd_of_dvd_mul_right hd
    obtain ⟨i,hi,e⟩ := (Nat.dvd_prime_pow hp).mp h
    exact ⟨i,hi,Or.inl e⟩

theorem mixed_comparability {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (i j : ℕ) : (p^i ∣ p^j*q ∨ p^j*q ∣ p^i) ↔ i ≤ j := by
  have cp : (p^i).Coprime q := by simpa using Nat.coprime_pow_primes i 1 hp hq hpq
  constructor
  · rintro (h | h)
    · exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp (cp.dvd_of_dvd_mul_right h)
    · have bad : q ∣ p^i := dvd_trans (dvd_mul_left q (p^j)) h
      exact (hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow bad)).symm).elim
  · exact fun h => Or.inl (dvd_mul_of_dvd_left (pow_dvd_pow p h) q)

theorem gcd_fibre_card {N d : ℕ} (hd : d ∣ N) :
    ((Finset.range N).filter (fun k => N.gcd k = d)).card = Nat.totient (N/d) :=
  (Nat.totient_div_of_dvd hd).symm

theorem prime_power_card {p : ℕ} (hp : p.Prime) (j : ℕ) :
    Nat.totient (p^j) = CozeroChains.primePowerWeight p j := by
  cases j with
  | zero => simp [CozeroChains.primePowerWeight]
  | succ j => exact Nat.totient_prime_pow_succ hp j

theorem mixed_card {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (j : ℕ) :
    Nat.totient (p^j*q) = (q-1)*CozeroChains.primePowerWeight p j := by
  have cp : (p^j).Coprime q := by simpa using Nat.coprime_pow_primes j 1 hp hq hpq
  rw [Nat.totient_mul cp, Nat.totient_prime hq, prime_power_card hp, Nat.mul_comm]

#print axioms principal_membership
#print axioms exceptional_primes
#print axioms all_maximal_cuts
#print axioms cut_parameter_unique
#print axioms divisor_rows
#print axioms mixed_comparability
#print axioms gcd_fibre_card
#print axioms mixed_card
end CozeroGrid
