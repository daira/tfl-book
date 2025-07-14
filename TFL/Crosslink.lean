import Mathlib.Logic.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

import TFL.BcChain
import TFL.BftChain
import TFL.LCA

/- The `Node` type only needs to have decidable equality. -/
variable {Node : Type} [DecidableEq Node]

/-
Effectively assume that we are using a collision-free hash, by requiring a
proof of that as an argument to anything in this file that needs it.
-/
variable (NC : NoCollisions)

local infix:60 "⎾_bc" => bc_trim
local infix:50 "≼_bc" => bc_prefix NC
local infix:50 "≼≽_bc" => bc_agrees NC
local infix:50 "≼/≽_bc" => bc_conflicts NC

local infix:60 "⎾_bft" => bft_trim
local infix:50 "≼_bft" => bft_prefix
local infix:50 "≼≽_bft" => bft_agrees
local infix:50 "≼/≽_bft" => bft_conflicts

/-- The parameters for an instance of Crosslink 2. -/
structure Crosslink where
  σ : ℕ+
  L : ℕ+

/- The global parameters. -/
variable (Params : Crosslink)

/-- The Last Final bft-block for a given bc-block. -/
def LF (c : BcChain) : BftChain :=
  sorry

/-- The snapshotted bc-block for a given bft-block. -/
def snapshot (b : BftChain) : BcChain :=
  match b.head? with
  | some B => B.headers_bc ⎾_bc Params.σ
  | none => []

def candidate (H : BcChain) : BcChain :=
  last_common_ancestor (snapshot Params (LF H)) (H ⎾_bc Params.σ)

def scan {A : Type} (update : ℕ → A → A) (initial : A) : ℕ → A
  | 0 => initial
  | s+1 => update (s+1) (scan update initial s)

/- This is too hard to prove anything about currently. -/
def scan_iterative {A : Type} (update : ℕ → A → A) (initial : A) (t : ℕ) : A := Id.run do
  let mut state : A := initial
  for s in [0:t] do state ← update (s+1) state
  state

/-- Given `fin i s`, transition to `fin i t` where `t = s+1`. -/
def update_fin (ch_i : Time → BcChain) (t : ℕ) (fin_i_s : BcChain) : BcChain :=
  let N := candidate Params (ch_i t)
  if fin_i_s ≼_bc N then N else fin_i_s

/- Extend `update_fin` to a time series. -/
def fin (ch_i : Time → BcChain) (t : Time) : BcChain :=
  scan (update_fin NC Params ch_i) [] t

lemma fin_step (ch_i : Time → BcChain) (s : Time) :
  fin NC Params ch_i (s+1) = update_fin NC Params ch_i (s+1) (fin NC Params ch_i s) := by rfl

lemma candidate_trim (ch_i : Time → BcChain) (u : Time)
    : candidate Params (ch_i u) ≼_bc ch_i u ⎾_bc Params.σ := by
  let bc_snapshot := snapshot Params (LF (ch_i u))
  let bc_confirmed := ch_i u ⎾_bc Params.σ
  exact (lca_prefix NC bc_snapshot bc_confirmed).right

lemma local_fin_depth (ch : Node → Time → BcChain) (honest : Node → Time → Bool)
    : ∀ (i : Node) (t : Time) (honest_i : honest i t), ∃ (r : Time), r ≤ t ∧ fin NC Params (ch i) t ≼_bc ch i r ⎾_bc Params.σ := by
  intro i t honest_i
  use t-1
  simp_all
  sorry

/--
Assured Finality is Agreement on `V` composed with `fin`.
-/
public def AssuredFinality (V : Node → Time → BcChain) :=
  BcAgreement NC (fun i t => fin NC Params (V i) t)

/--
Safety theorem: Assured Finality from BC Prefix Agreement.
-/
theorem assured_finality_from_bc_prefix_agreement (ch : Node → Time → BcChain) (honest : Node → Time → Bool)
    (prefix_agreement : BcPrefixAgreement NC Params.σ ch honest) : AssuredFinality NC Params ch honest := by
  sorry

/--
Safety theorem: Assured Finality from BFT Final Agreement.
-/
theorem assured_finality_from_bft_final_agreement (V : Node → Time → BftChain × BcChain) (honest : Node → Time → Bool)
    (final_agreement : BftFinalAgreement (fun i t => (V i t).1) honest)
    : AssuredFinality NC Params (fun i t => (V i t).2) honest := by
  sorry
