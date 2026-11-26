import DivisorGrid

/-! Specialize the arbitrary-fibre grid classification to actual nonzero
nonunits of ZMod (p^m*q). All constructions work for arbitrary indices. -/
namespace CozeroResidues
open CozeroGrid

abbrev Vertex (N : ℕ) := {x : ZMod N // x ≠ 0 ∧ ¬IsUnit x}

theorem vertex_iff {N : ℕ} [NeZero N] (x : ZMod N) :
    (x ≠ 0 ∧ ¬IsUnit x) ↔ 1 < x.val.gcd N ∧ x.val.gcd N < N := by
  have hu : IsUnit x ↔ x.val.gcd N = 1 := by
    simpa only [ZMod.natCast_zmod_val, Nat.Coprime] using ZMod.isUnit_iff_coprime x.val N
  have hp : 0 < x.val.gcd N := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne N))
  rw [hu]
  constructor
  · rintro ⟨hx,hn⟩
    have hv : 0 < x.val := Nat.pos_of_ne_zero (fun h => hx (x.val_eq_zero.mp h))
    exact ⟨by omega, (Nat.gcd_le_left _ hv).trans_lt x.val_lt⟩
  · rintro ⟨h1,h2⟩
    refine ⟨?_, by omega⟩
    rintro rfl
    simp at h2

private theorem no_cross {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (i j : ℕ) : p^i ≠ p^j*q := by
  intro eq
  have bad : q ∣ p^i := eq ▸ dvd_mul_left q (p^j)
  exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow bad)).symm

theorem value_injective {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Function.Injective (divisorValue p q) := by
  intro a b
  cases a with
  | lo i =>
    cases b with
    | lo j =>
      intro h
      exact congrArg Cell.lo ((pow_right_injective₀ hp.pos hp.ne_one) h)
    | hi j => exact fun h => (no_cross hp hq hpq i j h).elim
  | hi i =>
    cases b with
    | lo j => exact fun h => (no_cross hp hq hpq j i h.symm).elim
    | hi j =>
      intro h
      have eq := Nat.eq_of_mul_eq_mul_right hq.pos h
      exact congrArg Cell.hi ((pow_right_injective₀ hp.pos hp.ne_one) eq)

theorem grid_value_iff {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (c : Cell) :
    proper m c ↔ 1 < divisorValue p q c ∧ divisorValue p q c ∣ p^m*q ∧
      divisorValue p q c < p^m*q := by
  cases c with
  | lo i =>
    change (0 < i ∧ i ≤ m) ↔ 1 < p^i ∧ p^i ∣ p^m*q ∧ p^i < p^m*q
    constructor
    · rintro ⟨h0,him⟩
      refine ⟨one_lt_pow₀ hp.one_lt h0.ne', dvd_mul_of_dvd_left (pow_dvd_pow p him) q, ?_⟩
      exact (pow_le_pow_right₀ hp.one_lt.le him).trans_lt
        (lt_mul_of_one_lt_right (pow_pos hp.pos m) hq.one_lt)
    · rintro ⟨h1,hd,_⟩
      refine ⟨Nat.pos_of_ne_zero (fun h => ?_), (mixed_comparability hp hq hpq i m).mp (Or.inl hd)⟩
      simp [h] at h1
  | hi i =>
    change i < m ↔ 1 < p^i*q ∧ p^i*q ∣ p^m*q ∧ p^i*q < p^m*q
    constructor
    · intro him
      refine ⟨?_, Nat.mul_dvd_mul_right (pow_dvd_pow p him.le) q, ?_⟩
      · exact (show 1 ≤ p^i from pow_pos hp.pos i).trans_lt
          (lt_mul_of_one_lt_right (pow_pos hp.pos i) hq.one_lt)
      · exact Nat.mul_lt_mul_of_pos_right ((pow_lt_pow_iff_right₀ hp.one_lt).2 him) hq.pos
    · rintro ⟨_,_,ht⟩
      exact (pow_lt_pow_iff_right₀ hp.one_lt).mp (Nat.lt_of_mul_lt_mul_right ht)

theorem comparable_iff {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (x y : Cell) : comp x y ↔ divisorValue p q x ∣ divisorValue p q y ∨
      divisorValue p q y ∣ divisorValue p q x := by
  cases x with
  | lo i =>
    cases y with
    | lo j =>
      refine ⟨fun _ => ?_, fun _ => trivial⟩
      exact (le_total i j).imp (pow_dvd_pow p) (pow_dvd_pow p)
    | hi j => exact (mixed_comparability hp hq hpq i j).symm
  | hi i =>
    cases y with
    | lo j => exact (mixed_comparability hp hq hpq j i).symm.trans or_comm
    | hi j =>
      refine ⟨fun _ => ?_, fun _ => trivial⟩
      exact (le_total i j).imp (fun h => Nat.mul_dvd_mul_right (pow_dvd_pow p h) q)
        (fun h => Nat.mul_dvd_mul_right (pow_dvd_pow p h) q)

theorem residue_grid {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∃ label : Vertex (p^m*q) → Cell,
      (∀ c, proper m c ↔ ∃ x, label x = c) ∧
      (∀ x, divisorValue p q (label x) = x.val.val.gcd (p^m*q)) ∧
      ∀ x y, comp (label x) (label y) ↔ x.val ∣ y.val ∨ y.val ∣ x.val := by
  haveI : NeZero (p^m*q) := ⟨Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) hq.ne_zero⟩
  have row (x : Vertex (p^m*q)) :
      ∃ c, divisorValue p q c = x.val.val.gcd (p^m*q) := by
    obtain ⟨i,_,h | h⟩ := divisor_rows hp hq (Nat.gcd_dvd_right x.val.val (p^m*q))
    · exact ⟨.lo i,h.symm⟩
    · exact ⟨.hi i,h.symm⟩
  choose label value using row
  refine ⟨label, ?_, value, ?_⟩
  · intro c
    constructor
    · intro h
      obtain ⟨h1,hd,hlt⟩ := (grid_value_iff hp hq hpq c).mp h
      let r : ZMod (p^m*q) := (divisorValue p q c : ℕ)
      have hg : r.val.gcd (p^m*q) = divisorValue p q c := by
        rw [show r.val = divisorValue p q c from ZMod.val_natCast_of_lt hlt, Nat.gcd_eq_left hd]
      let x : Vertex (p^m*q) := ⟨r, (vertex_iff r).mpr (hg ▸ ⟨h1,hlt⟩)⟩
      exact ⟨x, value_injective hp hq hpq ((value x).trans hg)⟩
    · rintro ⟨x,rfl⟩
      apply (grid_value_iff hp hq hpq _).mpr
      rw [value]
      have h := (vertex_iff x.val).mp x.property
      exact ⟨h.1,Nat.gcd_dvd_right ..,h.2⟩
  · intro x y
    rw [comparable_iff hp hq hpq, value, value, principal_membership, principal_membership]

def independentDominating {N : ℕ} (S : Vertex N → Prop) : Prop :=
  (∀ x y, S x → S y → x.val ∣ y.val ∨ y.val ∣ x.val) ∧
    ∀ x, (∀ y, S y → x.val ∣ y.val ∨ y.val ∣ x.val) → S x

theorem residue_cut_classification {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∃ label : Vertex (p^m*q) → Cell,
      (∀ x, divisorValue p q (label x) = x.val.val.gcd (p^m*q)) ∧
      ∀ S : Vertex (p^m*q) → Prop, independentDominating S ↔
        ∃! k, k ≤ m ∧ ∀ x, S x ↔ cut k (label x) := by
  obtain ⟨lab,hs,hv,hc⟩ := residue_grid (m := m) hp hq hpq
  refine ⟨lab,hv,fun S => ?_⟩
  have hbridge : independentDominating S ↔ maximalIndependent lab S := by
    unfold independentDominating maximalIndependent
    simp only [hc]
  rw [hbridge,all_maximal_cuts lab hs S]
  constructor
  · rintro ⟨k,hk,cutRep⟩
    refine ⟨k,⟨hk,cutRep⟩,?_⟩
    rintro l ⟨hl,other⟩
    exact cut_parameter_unique lab hs hl hk (fun x => (other x).symm.trans (cutRep x))
  · exact ExistsUnique.exists

#print axioms residue_cut_classification
end CozeroResidues

