import Mathlib.Logic.Basic
import Mathlib.Order.Monotone.Basic

import Mathlib.Tactic
import TFL.Tactic

import TFL.ToMathlib
import TFL.Time


/- The `Node` type only needs to have decidable equality. -/
variable {Node : Type} [DecidableEq Node]

/-- Non-genesis bc-block hashes are represented by `ℕ+`. -/
public abbrev BcNonGenesisHash := ℕ+

/-- bc-block hashes in general are represented by `ℕ`. -/
public abbrev BcHash := ℕ

/--
A `BcChain` is represented as a linked list of bc-block hashes, from the tip backward,
*not* including the genesis block hash.

This representation is opposite to the order in the book, sorry.
-/
public def BcChain := List BcNonGenesisHash deriving DecidableEq, BEq

/-- The hash of the tip of a bc-chain. -/
public def bc_tip (c : BcChain) : BcHash := match List.head? c with
  | none => 0
  | some h => ↑h

/-- Do two bc-chains have the same hash at the tip? -/
public def bc_same_tip (a b : BcChain) : Bool := bc_tip a == bc_tip b

/-- Collision-freedom of the block hash means that two bc-chains with the same tip hash are the same. -/
public def NoCollisions := (a b : BcChain) → (same : bc_same_tip a b) → a = b

/--
Trim the most recent `k` blocks.

Since chains are represented tip-first, this is implemented by dropping the first
`k` elements.
-/
public def bc_trim (c : BcChain) (k : ℕ) : BcChain := c.drop k
local infix:60 "⎾" => bc_trim

public def bc_rep_suffix (a b : BcChain) : Bool := a.isSuffixOf b

/--
Since chains are represented tip-first, `a ≼ b` if the `List` representing `a` is
a suffix of the `List` representing `b`.
-/
public def bc_prefix (a b : BcChain) : Bool := bc_rep_suffix a b

/-- Local notation for bc-chain prefix. -/
local infix:50 "≼" => bc_prefix

/-- There is a preorder on `BcChain`s. -/
public instance bc_chain_preorder : Preorder BcChain where
  le (a b : BcChain) := a ≼ b
  le_refl := by intro a; simp [bc_prefix, bc_rep_suffix]
  le_trans := by
    intro a b c hab hbc
    simp_all [bc_prefix, bc_rep_suffix]
    simp [List.IsSuffix.trans hab hbc]

/--
Since the hash is collision-free, we may also assume `a ≼ b` if their initial
elements are equal.
-/
public lemma same_tip_implies_prefix (nc : NoCollisions) (a b : BcChain)
    (same_tip : bc_same_tip a b) : a ≼ b := by
  apply nc at same_tip
  subst same_tip
  simp [bc_prefix, bc_rep_suffix]

/-- Two bc-chains agree iff one is a prefix of the other. -/
public def bc_agrees (a b : BcChain) := a ≼ b ∨ b ≼ a

/-- Local notation for bc-chain agreement. -/
local infix:50 "≼≽" => bc_agrees

/-- Two bc-chains conflict iff neither is a prefix of the other. -/
public def bc_conflicts (a b : BcChain) := ¬(a ≼≽ b)

/-- Local notation for bc-chain conflict. -/
local infix:50 "≼/≽" => bc_conflicts

/-- If a ≼ c ∧ b ≼ c then a ≼≽ b. -/
public lemma linear_prefix (a b c : BcChain) (hac : a ≼ c) (hbc : b ≼ c) : a ≼≽ b := by
  simp_all [bc_agrees, bc_prefix, bc_rep_suffix]
  exact List.suffix_or_suffix_of_suffix hac hbc

/--
An execution of Π_bc has Agreement on the view `V : Node → Time → BcChain` iff
for all times `t`, `u` and all Π-nodes `i`, `j` (potentially the same) such that
`i` is honest at time `t` and `j` is honest at time `u`, we have `V i t ≤≥ V j u`.

TODO: this definition works for any chain type; generalize it.
-/
public def BcAgreement (V : Node → Time → BcChain) (honest : Node → Time → Bool) :=
  ∀ (i j : Node) (t u : Time) (_honest_i : honest i t) (_honest_j : honest j u), V i t ≼≽ V j u

/--
An execution of Π_bc has Agreement on the view `V : Node × Time → U` composed with
`f : U → BcChain` iff it has Agreement on `fun i t => f (V i t)`.

TODO: this definition works for any chain type; generalize it.
-/
public def ComposedBcAgreement {U : Type} (V : Node → Time → U) (f : U → BcChain) :=
  BcAgreement (fun i t => f (V i t))

/--
An execution of Π_bc has Prefix Agreement at confirmation depth `μ` iff it has
Agreement on the view `i ↦ t ↦ ch i t ⎾ μ`.
-/
public def BcPrefixAgreement (μ : ℕ) (ch : Node → Time → BcChain) :=
  ComposedBcAgreement ch (· ⎾ μ)

/--
An execution of `Π_bc` has Prefix Consistency at confirmation depth `μ`, iff
for all times `t ≤ u` and all nodes `i`, `j` (potentially the same) such that
`i` is honest at time `t` and `j` is honest at time `u`, we have `ch i t ⎾ μ ≼ ch j u`​.
-/
public def BcPrefixConsistency (μ : ℕ) (ch : Node → Time → BcChain) (honest : Node → Time → Bool) :=
  ∀ (i j : Node) (t u : Time) (_t_leq_u : t ≤ u) (_honest_i : honest i t) (_honest_j : honest j u),
  ch i t ⎾ μ ≼ ch j u

/--
The restriction of a time series of bc-blocks up to time `t` inclusive.
-/
public def up_to (f : Time → BcChain) (t : Time) := {r : Time | r ≤ t}.restrict f

/--
`BcLinear f t` specifies that a time series of bc-blocks given by `f : Time → BcChain`
is bc-linear up to time `t` inclusive.
-/
public def BcLinear (f : Time → BcChain) (t : Time) := @Monotone _ _ _ bc_chain_preorder (up_to f t)
