import Std

/-!
Arithmetic in the outer-radius proposition. Write p = b+1 (so p-1 = b)
and e_j = 1 + c*p^j. Exactly the divisors of c*(p-1) divide every
e_j-e_0. The proof is uniform in the base, the gap parameter, and j.
-/
namespace GapExponents

def geom (b : Nat) : Nat → Nat
  | 0 => 0
  | j+1 => geom b j + (b+1)^j

def exponent (b c j : Nat) : Nat := 1 + c*(b+1)^j

theorem geometricIdentity (b j : Nat) : (b+1)^j = 1 + b*geom b j := by
  induction j with
  | zero => simp [geom]
  | succ j ih =>
    calc
      (b+1)^(j+1) = b*(b+1)^j + (b+1)^j := by
        rw [Nat.pow_succ, Nat.mul_add, Nat.mul_one, Nat.mul_comm ((b+1)^j) b]
      _ = 1 + b*geom b (j+1) := by
        simp only [geom, Nat.mul_add]
        omega

theorem exponentDifference (b c j : Nat) :
    exponent b c j - exponent b c 0 = (c*b)*geom b j := by
  simp only [exponent, Nat.pow_zero, Nat.mul_one]
  rw [geometricIdentity b j, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc]
  omega

theorem commonDivisors (b c d : Nat) :
    (∀ j, d ∣ exponent b c j - exponent b c 0) ↔ d ∣ c*b := by
  constructor
  · intro h
    simpa [exponentDifference, geom] using h 1
  · intro h j
    rw [exponentDifference]
    exact Nat.dvd_trans h (Nat.dvd_mul_right _ _)

#print axioms commonDivisors
end GapExponents
