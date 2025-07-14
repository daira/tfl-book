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

/-
Effectively assume that we are using a collision-free hash, by requiring a
proof of that as an argument to anything in this file that needs it.
-/
variable (NC : NoCollisions)

/--
Trim the most recent `k` blocks.

Since chains are represented tip-first, this is implemented by dropping the first
`k` elements.
-/
public def bc_trim (c : BcChain) (k : ℕ) : BcChain := c.drop k
local infix:60 "⎾" => bc_trim

public def bc_rep_suffix (a b : BcChain) : Bool := a.isSuffixOf b
--public def bc_rep_suffix (a b : BcChain) := a <:+ b

/--
Since chains are represented tip-first, `a ≼ b` if the `List` representing `a` is
a suffix of the `List` representing `b`. Since the hash is collision-free, we may
also assume `a ≼ b` if their initial elements are equal. Taking a proof of
`NoCollisions` as an argument tracks where we are depending on this.
-/
public def bc_prefix (_nc : NoCollisions) (a b : BcChain) : Bool := bc_rep_suffix a b || bc_same_tip a b
--public def bc_prefix (_nc : NoCollisions) (a b : BcChain) := bc_rep_suffix a b ∨ bc_same_tip a b

/-- Local notation for bc-chain prefix, making the dependency on `NC` implicit. -/
local infix:50 "≼" => bc_prefix NC

/-- There is a preorder on `BcChain`s assuming no hash collisions. -/
public instance bc_chain_preorder : Preorder BcChain where
  le (a b : BcChain) := a ≼ b
  le_refl := by intro a; simp [bc_prefix, bc_rep_suffix]
  le_trans := by
    intro a b c hab hbc
    simp_all [bc_prefix, bc_rep_suffix]
    cases hbc with
    | inl hbc_tr => cases hab with
                    | inl hab_tr => simp [List.IsSuffix.trans hab_tr hbc_tr]
                    | inr hab_eq => simp_all [NC a b hab_eq]
    | inr hbc_eq => simp_all [NC b c hbc_eq]

/-- Two bc-chains agree iff one is a prefix of the other. -/
public def bc_agrees (a b : BcChain) := a ≼ b ∨ b ≼ a

/-- Local notation for bc-chain agreement, making the dependency on `NC` implicit. -/
local infix:50 "≼≽" => bc_agrees NC

/-- Two bc-chains conflict iff neither is a prefix of the other. -/
public def bc_conflicts (a b : BcChain) := ¬(a ≼≽ b)

/-- Local notation for bc-chain conflict, making the dependency on `NC` implicit. -/
local infix:50 "≼/≽" => bc_conflicts NC

/-- If a ≼ c ∧ b ≼ c then a ≼≽ b. -/
public lemma linear_prefix (a b c : BcChain) (hac : a ≼ c) (hbc : b ≼ c) : a ≼≽ b := by
  simp_all [bc_agrees, bc_prefix, bc_rep_suffix]
  cases hbc with
  | inl hbc_pr => cases hac with
                  | inl hac_pr => cases List.suffix_or_suffix_of_suffix hac_pr hbc_pr with
                                  | inl | inr => simp_all only [true_or, or_true]
                  | inr hac_eq => simp_all only [true_or, or_true, NC a c <| show bc_same_tip a c by simp_all only]
  | inr hbc_eq => simp_all only [true_or, NC b c <| show bc_same_tip b c by simp_all only]

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
  BcAgreement NC (fun i t => f (V i t))

/--
An execution of Π_bc has Prefix Agreement at confirmation depth `μ` iff it has
Agreement on the view `i ↦ t ↦ ch i t ⎾ μ`.
-/
public def BcPrefixAgreement (μ : ℕ) (ch : Node → Time → BcChain) :=
  ComposedBcAgreement NC ch (· ⎾ μ)

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
public def BcLinear (f : Time → BcChain) (t : Time) := @Monotone _ _ _ (bc_chain_preorder NC) (up_to f t)
