/-
  Lean 4 Foundations: Module 1 - Propositional Logic & Constructive Proofs
  This module covers foundational theorems of propositional logic using
  Curry-Howard correspondence and standard Lean 4 tactics.
-/

namespace Lean4Foundations.BasicLogic

/-!
### 1. Conjunction (AND) Rules and Symmetries
In Lean, a proof of `p ∧ q` is a pair constructed with `⟨hp, hq⟩` or `And.intro hp hq`.
-/

/-- Conjunction is commutative: `p ∧ q` implies `q ∧ p`. -/
theorem and_comm_prop (p q : Prop) : p ∧ q ↔ q ∧ p := by
  constructor
  · intro ⟨hp, hq⟩
    exact ⟨hq, hp⟩
  · intro ⟨hq, hp⟩
    exact ⟨hp, hq⟩

/-- Conjunction is associative: `(p ∧ q) ∧ r` is logically equivalent to `p ∧ (q ∧ r)`. -/
theorem and_assoc_prop (p q r : Prop) : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  · intro ⟨⟨hp, hq⟩, hr⟩
    exact ⟨hp, ⟨hq, hr⟩⟩
  · intro ⟨hp, ⟨hq, hr⟩⟩
    exact ⟨⟨hp, hq⟩, hr⟩

/-!
### 2. Disjunction (OR) Rules
In Lean, a proof of `p ∨ q` is produced by either `Or.inl hp` (left injection) or `Or.inr hq` (right injection).
Elimination of `p ∨ q` is done via case analysis (`cases` or `rcases`).
-/

/-- Disjunction is commutative: `p ∨ q` implies `q ∨ p`. -/
theorem or_comm_prop (p q : Prop) : p ∨ q ↔ q ∨ p := by
  constructor
  · intro h
    cases h with
    | inl hp => exact Or.inr hp
    | inr hq => exact Or.inl hq
  · intro h
    cases h with
    | inl hq => exact Or.inr hq
    | inr hp => exact Or.inl hp

/-- Disjunction elimination (proof by cases). -/
theorem or_elim_prop (p q r : Prop) (h : p ∨ q) (hp : p → r) (hq : q → r) : r := by
  cases h with
  | inl p_true => exact hp p_true
  | inr q_true => exact hq q_true

/-!
### 3. Implications & Negation
Negation `¬ p` in constructive type theory is defined as `p → False`.
-/

/-- Modus Tollens (Proof by Contraposition): If `p → q` and `¬ q`, then `¬ p`. -/
theorem modus_tollens (p q : Prop) (hpq : p → q) (hnq : ¬ q) : ¬ p := by
  intro hp
  have hq : q := hpq hp
  exact hnq hq

/-- Transitivity of Implication: If `p → q` and `q → r`, then `p → r`. -/
theorem impl_trans (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by
  intro hp
  exact hqr (hpq hp)

/-- Double Negation Introduction: `p` implies `¬ ¬ p`. -/
theorem double_neg_intro (p : Prop) (hp : p) : ¬ ¬ p := by
  intro hnp
  exact hnp hp

/-!
### 4. De Morgan's Laws (Constructive Direction)
Constructively, `¬ (p ∨ q)` is fully equivalent to `¬ p ∧ ¬ q`.
-/

/-- De Morgan's First Law: `¬ (p ∨ q) ↔ ¬ p ∧ ¬ q`. -/
theorem de_morgan_not_or (p q : Prop) : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q := by
  constructor
  · intro h
    constructor
    · intro hp
      exact h (Or.inl hp)
    · intro hq
      exact h (Or.inr hq)
  · intro ⟨hnp, hnq⟩ h_or
    cases h_or with
    | inl hp => exact hnp hp
    | inr hq => exact hnq hq

/-- De Morgan's Second Law (Weak Constructive Form): `¬ p ∨ ¬ q → ¬ (p ∧ q)`. -/
theorem de_morgan_or_not (p q : Prop) : ¬ p ∨ ¬ q → ¬ (p ∧ q) := by
  intro h ⟨hp, hq⟩
  cases h with
  | inl hnp => exact hnp hp
  | inr hnq => exact hnq hq

/-!
### 5. Currying and Uncurrying
Demonstrating equivalence between taking a pair of hypotheses vs chained implications.
-/

/-- Currying equivalence: `(p ∧ q → r) ↔ (p → q → r)`. -/
theorem curry_equiv (p q r : Prop) : (p ∧ q → r) ↔ (p → q → r) := by
  constructor
  · intro h hp hq
    exact h ⟨hp, hq⟩
  · intro h ⟨hp, hq⟩
    exact h hp hq

end Lean4Foundations.BasicLogic
