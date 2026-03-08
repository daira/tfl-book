import Mathlib.Logic.Basic
import Mathlib.Order.Monotone.Basic

import Mathlib.Tactic

import TFL.LCA


/- The `Node` type only needs to have decidable equality. -/
variable {Node : Type} [DecidableEq Node]

/- A block in the BFT protocol. -/
public structure BftBlock where
  headers_bc : BcChain

/--
A `BftChain` is represented as a linked list of bft-blocks, from the tip backward,
*not* including the genesis bft-block.

This representation is opposite to the order in the book, sorry.
-/
public def BftChain := List BftBlock

/--
Trim the most recent `k` blocks.

Since chains are represented tip-first, this is implemented by dropping the first
`k` elements.
-/
public def bft_trim (ch : BftChain) (k : ℕ) : BftChain := ch.drop k
local infix:60 "⎾" => bft_trim

/--
Since chains are represented tip-first, `a ≼ b` if the `List` representing `a` is
a suffix of the `List` representing `b`.
-/
public def bft_prefix (a b : BftChain) := a <:+ b

/-- Local notation for bft-chain prefix. -/
local infix:50 "≼" => bft_prefix

/-- There is a preorder on `BftChain`s. -/
public instance bft_chain_preorder : Preorder BftChain where
  le (a b : BftChain) := a ≼ b
  le_refl := by intro a; simp [bft_prefix]
  le_trans := by intro a b c hab hbc; simp only [List.IsSuffix.trans hab hbc, bft_prefix]

/-- Two bft-chains agree iff one is a prefix of the other. -/
public def bft_agrees (a b : BftChain) := a ≼ b ∨ b ≼ a

/-- Local notation for bft-chain agreement. -/
local infix:50 "≼≽" => bft_agrees

/-- Two bft-chains conflict iff neither is a prefix of the other. -/
public def bft_conflicts (a b : BftChain) := ¬(a ≼≽ b)

/-- Local notation for bft-chain conflict. -/
local infix:50 "≼/≽" => bft_conflicts

def bft_last_final (b : BftChain) : BftChain :=
  b -- FIXME

/--
An execution of `Π_bft` has Agreement on the view `V : Node → Time → BftChain` iff
for all times `t`, `u` and all bft-nodes `i`, `j` (potentially the same) such that
`i` is honest at time `t` and `j` is honest at time `u`, we have `V i t ≼≽ V j u`.

TODO: this definition works for any chain type; generalize it.
-/
public def BftAgreement (V : Node → Time → BftChain) (honest : Node → Time → Bool) :=
  ∀ (i j : Node) (t u : Time) (_honest_i : honest i t) (_honest_j : honest j u), V i t ≼≽ V j u

/--
An execution of `Π_bft` has Agreement on the view `V : Node × Time → U` composed with
`f : U → BftChain` iff it has Agreement on `fun i t => f (V i t)`.

TODO: this definition works for any chain type; generalize it.
-/
public def ComposedBftAgreement {U : Type} (V : Node → Time → U) (f : U → BftChain) :=
  BftAgreement (fun i t => f (V i t))

/--
Final Agreement is Agreement on `V` composed with `bft_last_final`.
-/
public def BftFinalAgreement (V : Node → Time → BftChain) :=
  ComposedBftAgreement V bft_last_final
