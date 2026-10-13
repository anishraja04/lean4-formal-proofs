# Lean 4 Foundations: Theorem Proving & Formal Verification

[![Lean 4](https://img.shields.io/badge/Lean-4.14.0-blue.svg)](https://lean-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
[![Formal Verification](https://img.shields.io/badge/Type_Theory-Calculus_of_Inductive_Constructions-purple.svg)](https://leanprover.github.io/theorem_proving_in_lean4/)

A self-contained, educational repository of formal mathematical proofs and software verification in **[Lean 4](https://lean-lang.org/)**. Designed to serve as a practical learning reference for interactive theorem proving, constructive logic, and formal methods.

---

## 📚 Overview

Interactive theorem provers (ITPs) bridge pure mathematics and computer science by using the **Curry-Howard correspondence** (propositions as types, proofs as programs). This repository presents clean, fully mechanized proofs covering core computer science and mathematical foundations:

1. **Propositional Logic & Constructive Reasoning** (`Lean4Foundations.BasicLogic`)
   - Conjunction, disjunction, and implication properties.
   - Modus tollens and constructive De Morgan's laws.
   - Currying / uncurrying equivalence.

2. **Peano Arithmetic & Mathematical Induction** (`Lean4Foundations.NumberTheory`)
   - Even and odd parity definitions with existential quantifiers.
   - Closed-form sum of the first $n$ natural numbers (Gauss's identity): $\sum_{i=1}^n i = \frac{n(n+1)}{2}$.
   - Inductive bounds on factorial functions.

3. **Inductive Data Structures & Structural Verification** (`Lean4Foundations.DataStructures`)
   - Custom inductive list operations and length preservation theorems.
   - Polymorphic binary tree type definitions.
   - Formal verification of tree invariant: $\text{depth}(t) \le \text{size}(t)$.

---

## 📁 Repository Structure

```
lean4-formal-proofs/
├── lakefile.lean                  # Lake package manager build configuration
├── lean-toolchain                 # Lean 4 version pin (v4.14.0)
├── Lean4Foundations.lean          # Root library import file
├── Lean4Foundations/
│   ├── BasicLogic.lean            # Propositional logic and constructive proofs
│   ├── NumberTheory.lean          # Parity proofs and mathematical induction
│   └── DataStructures.lean        # Inductive lists and binary tree verification
└── README.md                      # Documentation and learning guide
```

---

## 🛠️ Getting Started with Lean 4

### 1. Install `elan` (The Lean Version Manager)

**Windows (PowerShell):**
```powershell
curl -O --location https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1
powershell -File .\elan-init.ps1
```

**Linux / macOS:**
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

After installation, reload your shell or verify:
```bash
elan --version
lean --version
lake --version
```

### 2. Recommended Editor Setup

* Install **[VS Code](https://code.visualstudio.com/)**.
* Install the official **[Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)**.
* When opening any `.lean` file, the Lean Infoview pane will automatically open on the right, providing interactive feedback and real-time proof state inspection.

### 3. Build and Verify

To compile and check all proofs in this project:

```bash
lake build
```

---

## 🧠 Key Lean 4 Tactics Quick Reference

| Tactic | Description | Example |
| :--- | :--- | :--- |
| `intro` | Introduces hypotheses or bound variables from the goal into the local context. | `intro hp` |
| `exact` | Provides an exact term or proof that matches the goal type. | `exact hp` |
| `apply` | Applies a function or theorem whose conclusion matches the goal, generating subgoals. | `apply And.intro` |
| `constructor` | Splits a conjunction (`∧`), iff (`↔`), or inductive product into subgoals. | `constructor` |
| `cases` / `rcases` | Deconstructs a hypothesis (e.g. proof by cases on `p ∨ q` or existential `∃ k`). | `rcases h with ⟨k, hk⟩` |
| `induction` | Performs induction on a natural number or inductive datatype. | `induction n with \| zero => ... \| succ n ih => ...` |
| `rw` | Rewrites terms in the goal using an equality hypothesis or lemma. | `rw [hk]` |
| `omega` | Automated Presburger arithmetic decision procedure for linear integer inequalities and equalities. | `omega` |
| `rfl` | Proves reflexive equality (`a = a`) by definition. | `rfl` |

---

## 📖 Sample Proof Highlight

### Closed-form Summation: $\sum_{i=1}^n i = \frac{n(n+1)}{2}$

```lean
/-- Recursive summation of the first n natural numbers -/
def sumN : Nat → Nat
  | 0 => 0
  | n + 1 => sumN n + (n + 1)

/-- Formal verification of Gauss's summation formula -/
theorem sumN_closed_form (n : Nat) : 2 * sumN n = n * (n + 1) := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    dsimp [sumN]
    omega
```

---

## 📜 References & Further Reading

* [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/) - Official interactive reference.
* [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) - University-level textbook by the Lean community.
* [Functional Programming in Lean 4](https://lean-lang.org/functional_programming_in_lean/) - Programming language perspective.
* [Mathlib 4](https://github.com/leanprover-community/mathlib4) - The comprehensive Lean 4 mathematics library.

---

## 📄 License

This repository is licensed under the [MIT License](LICENSE).
