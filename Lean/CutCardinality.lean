import ResidueModel
import AlgebraBridge

/-! Count the actual residue representatives on each classified cut. The
graph generating polynomial defined by these cardinalities is linked to
the sections and to the exceptional nonzero-root statement over ℂ. -/
namespace CozeroCardinality
open CozeroChains CozeroGrid CozeroResidues CozeroAlgebra Finset

def lowerCell (m t j : ℕ) : Cell := .lo (m-(t+j))
def upperCell (m j : ℕ) : Cell := .hi (m-(j+1))
def cells (m t : ℕ) : Finset Cell :=
  ((range (m-t)).image (lowerCell m t)) ∪ ((range t).image (upperCell m))

theorem mem_cells_iff {m t : ℕ} (ht : t ≤ m) (c : Cell) :
    c ∈ cells m t ↔ proper m c ∧ cut (m-t) c := by
  cases c with
  | lo i =>
    simp only [cells,mem_union,mem_image,mem_range,lowerCell,upperCell,Cell.lo.injEq,
      reduceCtorEq,and_false,exists_const,or_false,proper,cut]
    constructor
    · rintro ⟨j,hj,he⟩
      omega
    · rintro ⟨⟨h0,hm⟩,hi⟩
      exact ⟨m-t-i,by omega,by omega⟩
  | hi i =>
    simp only [cells,mem_union,mem_image,mem_range,lowerCell,upperCell,Cell.hi.injEq,
      reduceCtorEq,and_false,exists_const,false_or,proper,cut]
    constructor
    · rintro ⟨j,hj,he⟩
      omega
    · rintro ⟨hm,hi⟩
      exact ⟨m-1-i,by omega,by omega⟩

def divisorsOnCut (p q m t : ℕ) := (cells m t).image (divisorValue p q)

def cutResidues (p q m t : ℕ) :=
  (range (p^m*q)).filter fun x => (p^m*q).gcd x ∈ divisorsOnCut p q m t

theorem mem_cutResidues {p q m t : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ht : t ≤ m) {x : Vertex (p^m*q)} {c : Cell} (hc : proper m c)
    (hx : divisorValue p q c = x.val.val.gcd (p^m*q)) :
    x.val.val ∈ cutResidues p q m t ↔ cut (m-t) c := by
  haveI : NeZero (p^m*q) := ⟨mul_ne_zero (pow_ne_zero _ hp.ne_zero) hq.ne_zero⟩
  simp only [cutResidues,mem_filter,mem_range, x.val.val_lt,true_and,divisorsOnCut]
  rw [Nat.gcd_comm,← hx]
  constructor
  · rintro h
    obtain ⟨a,ha,eq⟩ := mem_image.mp h
    have e := value_injective hp hq hpq eq
    exact ((mem_cells_iff ht c).mp (e ▸ ha)).2
  · exact fun h => mem_image.mpr ⟨c,(mem_cells_iff ht c).mpr ⟨hc,h⟩,rfl⟩

theorem only_vertices_on_cut {p q m t n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (ht : t ≤ m) (hn : n ∈ cutResidues p q m t) :
    ∃ x : Vertex (p^m*q), x.val.val = n := by
  haveI : NeZero (p^m*q) := ⟨mul_ne_zero (pow_ne_zero _ hp.ne_zero) hq.ne_zero⟩
  obtain ⟨hn0,hin⟩ := mem_filter.mp hn
  have hr : (n : ZMod (p^m*q)).val = n := ZMod.val_natCast_of_lt (mem_range.mp hn0)
  obtain ⟨c,hcell,e⟩ := mem_image.mp hin
  have h := (grid_value_iff hp hq hpq c).mp ((mem_cells_iff ht c).mp hcell).1
  rw [e, Nat.gcd_comm] at h
  exact ⟨⟨n,(vertex_iff _).mpr (by rw [hr]; exact ⟨h.1,h.2.2⟩)⟩,hr⟩

/-- Every independent dominating set of the residue graph occurs exactly once
in the enumeration used below, and every listed set is independent dominating. -/
theorem residue_sets_enumerated {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (m : ℕ) (S : Vertex (p^m*q) → Prop) :
    independentDominating S ↔
    ∃! t, t ≤ m ∧ ∀ x, S x ↔ x.val.val ∈ cutResidues p q m t := by
  haveI : NeZero (p^m*q) := ⟨mul_ne_zero (pow_ne_zero _ hp.ne_zero) hq.ne_zero⟩
  obtain ⟨lab,hval,hclass⟩ := residue_cut_classification (m := m) hp hq hpq
  have fits (t : ℕ) (ht : t ≤ m) (x : Vertex (p^m*q)) :
      x.val.val ∈ cutResidues p q m t ↔ cut (m-t) (lab x) := by
    apply mem_cutResidues hp hq hpq ht _ (hval x)
    apply (grid_value_iff hp hq hpq _).mpr
    rw [hval]
    have h := (vertex_iff x.val).mp x.property
    exact ⟨h.1,Nat.gcd_dvd_right ..,h.2⟩
  rw [hclass S]
  constructor
  · rintro ⟨k,⟨hk,hS⟩,uniq⟩
    refine ⟨m-k,⟨by omega, fun x => ?_⟩,?_⟩
    · rw [fits (m-k) (by omega), Nat.sub_sub_self hk]
      exact hS x
    · rintro t ⟨ht,rep⟩
      have e := uniq (m-t) ⟨by omega, fun x => (rep x).trans (fits t ht x)⟩
      omega
  · rintro ⟨t,⟨ht,hS⟩,uniq⟩
    refine ⟨m-t,⟨by omega, fun x => (hS x).trans (fits t ht x)⟩,?_⟩
    rintro k ⟨hk,rep⟩
    have e := uniq (m-k) ⟨by omega, fun x => by
      rw [fits (m-k) (by omega),Nat.sub_sub_self hk]
      exact rep x⟩
    omega

private theorem gcd_card_lower {p q m u : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hu : u ≤ m) :
    ((range (p^m*q)).filter (fun i => (p^m*q).gcd i = p^(m-u))).card =
      (q-1)*primePowerWeight p u := by
  have e : p^m*q = p^(m-u)*(p^u*q) := by rw [← mul_assoc,← pow_add,Nat.sub_add_cancel hu]
  rw [gcd_fibre_card ⟨p^u*q,e⟩,Nat.div_eq_of_eq_mul_right (pow_pos hp.pos _) e,mixed_card hp hq hpq]

private theorem gcd_card_upper {p q m u : ℕ} (hp : p.Prime) (hq : q.Prime) (hu : u ≤ m) :
    ((range (p^m*q)).filter (fun i => (p^m*q).gcd i = p^(m-u)*q)).card =
      primePowerWeight p u := by
  have e : p^m*q = (p^(m-u)*q)*p^u := by rw [mul_right_comm,← pow_add,Nat.sub_add_cancel hu]
  rw [gcd_fibre_card ⟨p^u,e⟩,Nat.div_eq_of_eq_mul_right (mul_pos (pow_pos hp.pos _) hq.pos) e,
    prime_power_card hp]

private theorem sum_segment (p t n : ℕ) :
    ∑ i ∈ range n, primePowerWeight p (t+i) = segment p t n := by
  induction n with
  | zero => simp [segment]
  | succ n ih => rw [sum_range_succ,ih]; rfl

private theorem sum_prefix (p t : ℕ) :
    (∑ i ∈ range t, primePowerWeight p (i+1)) + 1 = prefixWeight p (t+1) := by
  induction t with
  | zero => simp [prefixWeight,primePowerWeight]
  | succ t ih =>
    rw [sum_range_succ]
    change _ = prefixWeight p (t+1) + primePowerWeight p (t+1)
    omega

theorem cut_card_eq_weight {p q m t : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (ht : t ≤ m) : (cutResidues p q m t).card = weight p q m t := by
  unfold cutResidues
  rw [←sum_card_fiberwise_eq_card_filter, divisorsOnCut, sum_image]
  swap
  · intro a _ b _ h
    exact value_injective hp hq hpq h
  rw [cells,sum_union]
  swap
  · apply disjoint_left.mpr
    intro c hc hd
    obtain ⟨i,_,rfl⟩ := mem_image.mp hc
    obtain ⟨j,_,h⟩ := mem_image.mp hd
    contradiction
  rw [sum_image, sum_image]
  swap
  · intro i hi j hj h
    have e : m-(i+1) = m-(j+1) := Cell.hi.inj h
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    omega
  swap
  · intro i hi j hj h
    have e : m-(t+i) = m-(t+j) := Cell.lo.inj h
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    omega
  have hL : (∑ i ∈ range (m-t), ((range (p^m*q)).filter
      (fun x => (p^m*q).gcd x = divisorValue p q (lowerCell m t i))).card) =
      (q-1)*segment p t (m-t) := by
    rw [←sum_segment, mul_sum]
    apply sum_congr rfl
    intro i hi
    exact gcd_card_lower hp hq hpq (by have h := mem_range.mp hi; omega)
  have hU : (∑ i ∈ range t, ((range (p^m*q)).filter
      (fun x => (p^m*q).gcd x = divisorValue p q (upperCell m i))).card) =
      ∑ i ∈ range t, primePowerWeight p (i+1) := by
    apply sum_congr rfl
    intro i hi
    exact gcd_card_upper hp hq (by have h := mem_range.mp hi; omega)
  rw [hL,hU]
  have h := sum_prefix p t
  unfold weight
  omega

noncomputable def graphPolynomial (p q m : ℕ) (z : ℂ) : ℂ :=
  ((List.range (m+1)).map fun t => z^(cutResidues p q m t).card).sum

theorem graph_eq_chain {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (m : ℕ) (z : ℂ) :
    graphPolynomial p q m z = chainPolynomial p q m z := by
  unfold graphPolynomial chainPolynomial exponents
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [cut_card_eq_weight hp hq hpq (by have h := List.mem_range.mp ht; omega)]
  rfl

theorem graph_reciprocal {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (b : ℕ) {z : ℂ} (hz : z ≠ 0) :
    graphPolynomial p q (b+1) z = z^((q-1)*p^b) * gapSection p (q-p-1) (b+1) z⁻¹ :=
  (graph_eq_chain hp hq hpq.ne _ z).trans (reciprocal p q b hp.pos hpq z hz)

theorem graph_nonzero_root_iff {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (b : ℕ) {z : ℂ} (hz : z ≠ 0) :
    graphPolynomial p q (b+1) z = 0 ↔ gapSection p (q-p-1) (b+1) z⁻¹ = 0 := by
  rw [graph_eq_chain hp hq hpq.ne]
  exact nonzero_root_iff p q b hp.pos hpq hz

theorem graph_exceptional_root_set (b : ℕ) :
    {z : ℂ | z ≠ 0 ∧ graphPolynomial 2 3 (b+1) z = 0} = {-((b+1 : ℕ) : ℂ)} := by
  simp only [graph_eq_chain Nat.prime_two Nat.prime_three (by decide : 2 ≠ 3)]
  exact exceptional_root_set b

theorem graph_exceptional_no_finite_limit {index : ℕ → ℕ} (hi : StrictMono index)
    {roots : ℕ → ℂ} (hr : ∀ i, roots i ≠ 0 ∧ graphPolynomial 2 3 (index i+1) (roots i) = 0)
    (z : ℂ) : ¬ Filter.Tendsto roots Filter.atTop (nhds z) := by
  simp only [graph_eq_chain Nat.prime_two Nat.prime_three (by decide : 2 ≠ 3)] at hr
  exact exceptional_no_finite_limit hi hr z

#print axioms mem_cutResidues
#print axioms cut_card_eq_weight
#print axioms graph_eq_chain
#print axioms residue_sets_enumerated
#print axioms graph_reciprocal
#print axioms graph_exceptional_no_finite_limit
end CozeroCardinality
