import Std

/- Finite chain-weight computation used in the cozero-divisor graph note.
   A saturated chain in the p^a q divisor grid is a word of p-steps
   and one q-step. Its two endpoints carry no vertices. -/
namespace CozeroChains

inductive Move where | p | q deriving DecidableEq

def chain (before after : Nat) : List Move :=
  List.replicate before .p ++ .q :: List.replicate after .p

theorem all_p (xs : List Move) (h : xs.count .q = 0) :
    xs = List.replicate xs.length .p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | p =>
      have ht : xs.count .q = 0 := by simpa [List.count_cons] using h
      exact congrArg (List.cons .p) (ih ht)
    | q => simp [List.count_cons] at h

theorem classify (xs : List Move) (h : xs.count .q = 1) :
    ∃ t s, xs = chain t s := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    cases x with
    | p =>
      have ht : xs.count .q = 1 := by simpa [List.count_cons] using h
      obtain ⟨t,s,hw⟩ := ih ht
      exact ⟨t+1,s,by simp [chain, List.replicate_succ, hw]⟩
    | q =>
      have ht : xs.count .q = 0 := by simpa [List.count_cons] using h
      exact ⟨0,xs.length,by simp [chain, ← all_p xs ht]⟩

theorem chain_injective {t s u v : Nat} (h : chain t s = chain u v) :
    t=u ∧ s=v := by
  induction t generalizing u with
  | zero =>
    cases u with
    | zero => simpa [chain] using congrArg List.length h
    | succ u => simp [chain, List.replicate_succ] at h
  | succ t ih =>
    cases u with
    | zero => simp [chain, List.replicate_succ] at h
    | succ u =>
      have h' : chain t s = chain u v := List.cons.inj h |>.2
      obtain ⟨h₁,h₂⟩ := ih h'
      exact ⟨congrArg Nat.succ h₁,h₂⟩

/-- For prime p these are the sizes φ(p^j) of the divisor classes. -/
def primePowerWeight (p : Nat) : Nat → Nat
  | 0 => 1
  | j+1 => p^j * (p-1)

def prefixWeight (p : Nat) : Nat → Nat
  | 0 => 0
  | t+1 => prefixWeight p t + primePowerWeight p t

theorem prefix_closed (p t : Nat) (hp : 0<p) : prefixWeight p (t+1) = p^t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change prefixWeight p (t+1) + p^t * (p-1) = p^(t+1)
    rw [ih, Nat.pow_succ]
    calc
      p^t + p^t * (p-1) = p^t * (1 + (p-1)) := by simp [Nat.mul_add]
      _ = p^t * p := congrArg _ (by omega)

def segment (p t : Nat) : Nat → Nat
  | 0 => 0
  | s+1 => segment p t s + primePowerWeight p (t+s)

theorem split_prefix (p t s : Nat) :
    prefixWeight p t + segment p t s = prefixWeight p (t+s) := by
  induction s with
  | zero => simp [segment]
  | succ s ih => simp [segment, prefixWeight, ← Nat.add_assoc, ih]

/-- Here t counts the p-steps AFTER the q-step, so the switch in the
    divisor ladder occurs at k = a - t. Before the switch the proper
    divisors are p,...,p^k; after it they are q*p^k,...,q*p^(a-1). -/
def weight (p q a t : Nat) : Nat :=
  (prefixWeight p (t+1)-1) + (q-1)*segment p t (a-t)

def exponents (p q a : Nat) : List Nat := (List.range (a+1)).map (weight p q a)

theorem first_weight (p q b : Nat) (hp : 0<p) :
    weight p q (b+1) 0 = (q-1)*p^b := by
  have h' : segment p 0 (b+1) = p^b := by
    have hz := split_prefix p 0 (b+1)
    simpa only [show prefixWeight p 0 = 0 from rfl, Nat.zero_add,
      prefix_closed p b hp] using hz
  simp [weight, prefixWeight, primePowerWeight, h']

/-- Reversing the polynomial at its degree A=(q-1)*p^b changes each
    non-leading exponent into 1+(q-p-1)*p^t, for every t=0,...,b. -/
theorem reversed_exponent (p q b t : Nat) (hp : 0<p) (hpq : p<q) (ht : t≤b) :
    weight p q (b+1) (t+1) + (1+(q-p-1)*p^t) = (q-1)*p^b := by
  have h := split_prefix p (t+1) ((b+1)-(t+1))
  have hadd : t+1+((b+1)-(t+1)) = b+1 := by omega
  rw [hadd, prefix_closed p t hp, prefix_closed p b hp] at h
  have hpos : 0 < p^(t+1) := Nat.pow_pos hp
  have hm := congrArg (fun k => (q-1)*k) h
  simp only [Nat.mul_add] at hm
  have decomp : q-1 = p + (q-p-1) := by omega
  have part : (q-1)*p^t = p^(t+1) + (q-p-1)*p^t := by
    conv => lhs; rw [decomp, Nat.add_mul]
    rw [Nat.pow_succ, Nat.mul_comm (p^t) p]
  unfold weight
  rw [prefix_closed p (t+1) hp]
  omega

theorem exceptional_exponents (a : Nat) :
    exponents 2 3 (a+1) = 2^(a+1) :: List.replicate (a+1) (2^(a+1)-1) := by
  unfold exponents
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · rw [first_weight 2 3 a (by decide), Nat.pow_succ, Nat.mul_comm]
  · have mapEq := List.map_congr_left (l := List.range (a+1))
      (f := weight 2 3 (a+1) ∘ Nat.succ) (g := fun _ => 2^(a+1)-1)
      (by
        intro t ht
        have ht' := List.mem_range.mp ht
        have h := reversed_exponent 2 3 a t (by decide) (by decide) (by omega)
        simp only [show 3-2-1=0 from rfl, Nat.zero_mul, Nat.add_zero,
          show 3-1=2 from rfl] at h
        change weight 2 3 (a+1) (t+1) = 2^(a+1)-1
        rw [Nat.pow_succ, Nat.mul_comm (2^a) 2]
        change weight 2 3 (a+1) (t+1) + 1 = 2 * 2^a at h
        omega)
    rw [mapEq, List.map_const', List.length_range]

#print axioms classify
#print axioms chain_injective
#print axioms reversed_exponent
#print axioms exceptional_exponents
end CozeroChains
