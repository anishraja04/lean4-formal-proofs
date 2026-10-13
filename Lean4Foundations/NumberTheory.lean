/-
  Lean 4 Foundations: Module 2 - Arithmetic & Number Theory Induction
  This module formalizes mathematical induction over the natural numbers (Nat),
  parity properties (Even/Odd), and closed-form summation proofs using core Lean 4.
-/

namespace Lean4Foundations.NumberTheory

/-!
### 1. Parity Definitions: Even and Odd
A natural number `n` is even if `n = 2 * k` for some `k`.
It is odd if `n = 2 * k + 1` for some `k`.
-/

/-- Definition of an even natural number. -/
def IsEven (n : Nat) : Prop := ∃ k : Nat, n = 2 * k

/-- Definition of an odd natural number. -/
def IsOdd (n : Nat) : Prop := ∃ k : Nat, n = 2 * k + 1

/-- Zero is even. -/
theorem zero_is_even : IsEven 0 := by
  use 0

/-- One is odd. -/
theorem one_is_odd : IsOdd 1 := by
  use 0

/-- The sum of two even numbers is always even. -/
theorem even_add_even (a b : Nat) (ha : IsEven a) (hb : IsEven b) : IsEven (a + b) := by
  rcases ha with ⟨k₁, hk₁⟩
  rcases hb with ⟨k₂, hk₂⟩
  rw [hk₁, hk₂]
  use (k₁ + k₂)
  omega

/-- The sum of two odd numbers is always even. -/
theorem odd_add_odd (a b : Nat) (ha : IsOdd a) (hb : IsOdd b) : IsEven (a + b) := by
  rcases ha with ⟨k₁, hk₁⟩
  rcases hb with ⟨k₂, hk₂⟩
  rw [hk₁, hk₂]
  use (k₁ + k₂ + 1)
  omega

/-- The sum of an even number and an odd number is always odd. -/
theorem even_add_odd (a b : Nat) (ha : IsEven a) (hb : IsOdd b) : IsOdd (a + b) := by
  rcases ha with ⟨k₁, hk₁⟩
  rcases hb with ⟨k₂, hk₂⟩
  rw [hk₁, hk₂]
  use (k₁ + k₂)
  omega

/-!
### 2. Recursive Functions and Induction
Formal verification of recursive algorithms and closed-form mathematical identities.
-/

/-- Recursive summation of the first `n` natural numbers: 1 + 2 + ... + n. -/
def sumN : Nat → Nat
  | 0 => 0
  | n + 1 => sumN n + (n + 1)

/--
  Gauss's Identity: Formal proof that `2 * ∑_{i=1}^n i = n * (n + 1)`.
  Verified via induction on natural numbers using Lean's `omega` decision procedure.
-/
theorem sumN_closed_form (n : Nat) : 2 * sumN n = n * (n + 1) := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    dsimp [sumN]
    omega

/-- Recursive factorial definition. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- Factorial of any natural number is strictly positive (> 0). -/
theorem factorial_pos (n : Nat) : factorial n > 0 := by
  induction n with
  | zero =>
    decide
  | succ n ih =>
    dsimp [factorial]
    omega

/-- For all `n ≥ 1`, `factorial n ≥ 1`. -/
theorem factorial_ge_one (n : Nat) : factorial n ≥ 1 := by
  have h := factorial_pos n
  omega

end Lean4Foundations.NumberTheory
