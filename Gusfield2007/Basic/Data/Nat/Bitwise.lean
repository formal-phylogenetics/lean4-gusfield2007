module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Bits of natural numbers

Facts about `Nat.land`, `Nat.xor` and `Nat.testBit`, for computations on sets of sites coded as bits, and a chain of powers.
-/

@[expose] public section

open scoped Classical

namespace Nat

theorem beq_eq_false_of_ne {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false := by
  rw [← Bool.not_eq_true]
  exact fun h' => h (Nat.eq_of_beq_eq_true h')

/-- A number's top bit. -/
theorem testBit_log2_self {d : ℕ} (hd : d ≠ 0) : d.testBit (Nat.log2 d) = true := by
  have hlo := Nat.log2_self_le hd
  have hhi := Nat.lt_log2_self (n := d)
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
  have hdiv : d / 2 ^ Nat.log2 d = 1 := by
    apply Nat.div_eq_of_lt_le
    · simpa using hlo
    · rw [Nat.pow_succ] at hhi
      omega
  rw [hdiv]

theorem testBit_land' (a b k : ℕ) : (Nat.land a b).testBit k = (a.testBit k && b.testBit k) := Nat.testBit_and a b k

theorem testBit_xor' (a b k : ℕ) : (Nat.xor a b).testBit k = (a.testBit k ^^ b.testBit k) := Nat.testBit_xor a b k

theorem land_eq_zero_iff {a b : ℕ} : Nat.land a b = 0 ↔ ∀ k, (a.testBit k && b.testBit k) = false := by
  constructor
  · intro h k
    rw [← testBit_land', h, Nat.zero_testBit]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    rw [testBit_land', h k, Nat.zero_testBit]

theorem xor_two_pow_lt_two_pow {m : ℕ} {p i : ℕ} (hp : p < 2 ^ m) (hi : i < m) : Nat.xor p (2 ^ i) < 2 ^ m :=
  Nat.xor_lt_two_pow hp (Nat.pow_lt_pow_right (by decide) hi)

theorem pow_chain_le_six {X : ℕ} (h : 1 ≤ X) : X ≤ X ^ 2 ∧ X ^ 2 ≤ X ^ 3 ∧ X ^ 3 ≤ X ^ 4 ∧ X ^ 4 ≤ X ^ 5 ∧ X ^ 5 ≤ X ^ 6 := by
  refine ⟨?_, Nat.pow_le_pow_right h (by omega), Nat.pow_le_pow_right h (by omega), Nat.pow_le_pow_right h (by omega), Nat.pow_le_pow_right h (by omega)⟩
  simpa using Nat.pow_le_pow_right h (show 1 ≤ 2 by omega)

end Nat
