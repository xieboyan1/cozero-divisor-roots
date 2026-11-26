import CutCardinality
import Mathlib.Data.Finset.Powerset

/-! A definition by summing over the actual powerset. No divisor data or
cut parameter enters the definition of independentDominationPolynomial. -/
namespace CozeroGraph
open CozeroChains CozeroGrid CozeroResidues CozeroAlgebra CozeroCardinality Finset

def adjacent {N : ℕ} (x y : Vertex N) : Prop := ¬(x.val ∣ y.val ∨ y.val ∣ x.val)

def graphIndependentDominating {N : ℕ} (S : Vertex N → Prop) : Prop :=
  (∀ x y, S x → S y → ¬adjacent x y) ∧ (∀ x, ¬S x → ∃ y, S y ∧ adjacent x y)

theorem graph_predicate_iff {N : ℕ} (S : Vertex N → Prop) :
    graphIndependentDominating S ↔ independentDominating S := by
  classical
  constructor
  · rintro ⟨hi,hd⟩
    refine ⟨fun x y hx hy => Classical.byContradiction (hi x y hx hy),?_⟩
    intro x hc
    by_contra hx
    obtain ⟨y,hy,edge⟩ := hd x hx
    exact edge (hc y hy)
  · rintro ⟨hi,hm⟩
    refine ⟨fun x y hx hy edge => edge (hi x y hx hy),?_⟩
    intro x hx
    by_contra hn
    apply hx
    apply hm
    intro y hy
    exact Classical.byContradiction (fun edge => hn ⟨y,hy,edge⟩)

def admissible (N : ℕ) (A : Finset ℕ) : Prop :=
  (∀ n ∈ A, ∃ x : Vertex N, x.val.val = n) ∧
    graphIndependentDominating (fun x : Vertex N => x.val.val ∈ A)

noncomputable def allDominatingSets (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (range N).powerset.filter (admissible N)

noncomputable def independentDominationPolynomial (N : ℕ) (z : ℂ) : ℂ :=
  ∑ A ∈ allDominatingSets N, z^A.card

private theorem cut_injective_on_range {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {t u : ℕ} (ht : t ≤ m) (hu : u ≤ m)
    (h : ∀ x : Vertex (p^m*q), x.val.val ∈ cutResidues p q m t ↔
      x.val.val ∈ cutResidues p q m u) : t=u := by
  obtain ⟨lab,existsLab,values,_⟩ := residue_grid (m := m) hp hq hpq
  have eq := cut_parameter_unique lab existsLab (k := m-t) (l := m-u) (by omega) (by omega) (by
    intro x
    have hgood := (existsLab _).mpr ⟨x,rfl⟩
    exact (mem_cutResidues hp hq hpq ht hgood (values x)).symm.trans ((h x).trans
      (mem_cutResidues hp hq hpq hu hgood (values x))))
  omega

theorem all_sets_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (m : ℕ) :
    allDominatingSets (p^m*q) = (range (m+1)).image (cutResidues p q m) := by
  classical
  ext A
  constructor
  · intro mem
    have adm := (mem_filter.mp mem).2
    obtain ⟨valid,gd⟩ := adm
    obtain ⟨t,⟨ht,rep⟩,_⟩ :=
      (residue_sets_enumerated hp hq hpq m _).mp ((graph_predicate_iff _).mp gd)
    refine mem_image.mpr ⟨t,mem_range.mpr (by omega),?_⟩
    ext n
    constructor
    · intro hn
      obtain ⟨x,e⟩ := only_vertices_on_cut hp hq hpq ht hn
      rw [← e] at hn ⊢
      exact (rep x).mpr hn
    · intro hn
      obtain ⟨x,e⟩ := valid n hn
      rw [← e] at hn ⊢
      exact (rep x).mp hn
  · intro h
    obtain ⟨t,ht',rfl⟩ := mem_image.mp h
    have ht : t ≤ m := Nat.le_of_lt_succ (mem_range.mp ht')
    apply mem_filter.mpr
    constructor
    · apply mem_powerset.mpr
      exact fun _ hn => (mem_filter.mp hn).1
    refine ⟨fun _ hn => only_vertices_on_cut hp hq hpq ht hn,(graph_predicate_iff _).mpr ?_⟩
    apply (residue_sets_enumerated hp hq hpq m _).mpr
    refine ⟨t,⟨ht,fun _ => Iff.rfl⟩,?_⟩
    rintro u ⟨hu,rep⟩
    exact cut_injective_on_range hp hq hpq hu ht (fun x => (rep x).symm)

private theorem sum_list_range (f : ℕ → ℂ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,List.map_append,List.sum_append,ih,Finset.sum_range_succ]

theorem graph_sum_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (m : ℕ) (z : ℂ) : independentDominationPolynomial (p^m*q) z = graphPolynomial p q m z := by
  unfold independentDominationPolynomial graphPolynomial
  rw [all_sets_eq hp hq hpq, sum_image, sum_list_range]
  intro t ht u hu eq
  apply cut_injective_on_range hp hq hpq (Nat.le_of_lt_succ (mem_range.mp ht))
    (Nat.le_of_lt_succ (mem_range.mp hu))
  exact fun _ => eq ▸ Iff.rfl

theorem root_via_sections {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (b : ℕ) {z : ℂ} (hz : z ≠ 0) : independentDominationPolynomial (p^(b+1)*q) z = 0 ↔
      gapSection p (q-p-1) (b+1) z⁻¹ = 0 := by
  rw [graph_sum_eq hp hq hpq.ne]
  exact graph_nonzero_root_iff hp hq hpq b hz

theorem exceptional_graph_roots (b : ℕ) :
    {z : ℂ | z ≠ 0 ∧ independentDominationPolynomial (2^(b+1)*3) z = 0} = {-((b+1 : ℕ) : ℂ)} := by
  simp only [graph_sum_eq Nat.prime_two Nat.prime_three (by decide : 2 ≠ 3)]
  exact graph_exceptional_root_set b

theorem exceptional_graph_no_finite_limit {index : ℕ → ℕ} (hi : StrictMono index)
    {roots : ℕ → ℂ} (hr : ∀ i, roots i ≠ 0 ∧
      independentDominationPolynomial (2^(index i+1)*3) (roots i) = 0)
    (z : ℂ) : ¬ Filter.Tendsto roots Filter.atTop (nhds z) := by
  simp only [graph_sum_eq Nat.prime_two Nat.prime_three (by decide : 2 ≠ 3)] at hr
  exact graph_exceptional_no_finite_limit hi hr z

#print axioms all_sets_eq
#print axioms graph_sum_eq
#print axioms root_via_sections
#print axioms exceptional_graph_roots
#print axioms exceptional_graph_no_finite_limit
end CozeroGraph
