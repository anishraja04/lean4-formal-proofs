/-
  Lean 4 Foundations: Module 3 - Inductive Data Structures & Structural Induction
  This module defines inductive datatypes (Lists and Binary Trees) and verifies
  structural invariants such as length preservation and depth-size inequalities.
-/

namespace Lean4Foundations.DataStructures

/-!
### 1. Verification of List Operations
We formalize functional list operations and prove correctness via structural induction.
-/

/-- Custom recursive length computation for lists. -/
def myLength {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => 1 + myLength xs

/-- Length of an empty list is 0. -/
theorem myLength_nil {α : Type} : myLength ([] : List α) = 0 := rfl

/-- Appending two lists preserves the sum of their individual lengths. -/
theorem myLength_append {α : Type} (xs ys : List α) :
    myLength (xs ++ ys) = myLength xs + myLength ys := by
  induction xs with
  | nil =>
    dsimp [myLength]
    omega
  | cons x xs ih =>
    dsimp [myLength]
    omega

/-- Custom naive list reversal function. -/
def myReverse {α : Type} : List α → List α
  | [] => []
  | x :: xs => myReverse xs ++ [x]

/-- Reversing an empty list returns an empty list. -/
theorem myReverse_nil {α : Type} : myReverse ([] : List α) = [] := rfl

/-- Single element list reversed is itself. -/
theorem myReverse_singleton {α : Type} (x : α) : myReverse [x] = [x] := by
  rfl

/-!
### 2. Inductive Binary Trees
We define a polymorphic binary tree and prove fundamental structural properties.
-/

/-- Polymorphic binary tree type. -/
inductive Tree (α : Type) where
  | leaf : Tree α
  | node (left : Tree α) (val : α) (right : Tree α) : Tree α

open Tree

/-- Total number of values stored in the tree. -/
def treeSize {α : Type} : Tree α → Nat
  | leaf => 0
  | node l _ r => 1 + treeSize l + treeSize r

/-- Maximum depth (height) of the tree. -/
def treeDepth {α : Type} : Tree α → Nat
  | leaf => 0
  | node l _ r => 1 + Nat.max (treeDepth l) (treeDepth r)

/-- A leaf has size 0. -/
theorem leaf_size {α : Type} : treeSize (leaf : Tree α) = 0 := rfl

/-- A leaf has depth 0. -/
theorem leaf_depth {α : Type} : treeDepth (leaf : Tree α) = 0 := rfl

/--
  Fundamental Tree Inequality:
  For any binary tree `t`, the depth of `t` is always bounded above by its size:
  `treeDepth t ≤ treeSize t`.
-/
theorem treeDepth_le_treeSize {α : Type} (t : Tree α) : treeDepth t ≤ treeSize t := by
  induction t with
  | leaf =>
    dsimp [treeDepth, treeSize]
    omega
  | node l val r ih_l ih_r =>
    dsimp [treeDepth, treeSize]
    omega

/-- A tree containing at least one node has strictly positive size. -/
theorem node_size_pos {α : Type} (l : Tree α) (x : α) (r : Tree α) :
    treeSize (node l x r) ≥ 1 := by
  dsimp [treeSize]
  omega

end Lean4Foundations.DataStructures
