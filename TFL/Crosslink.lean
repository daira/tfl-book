import Mathlib.Logic.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

import TFL.BcChain
import TFL.BftChain
import TFL.LCA

/- The `Node` type only needs to have decidable equality. -/
variable {Node : Type} [DecidableEq Node]

/- In this file we want to be explicit about which chain we're talking about. -/
local infix:60 "⎾_bc" => bc_trim
local infix:50 "≼_bc" => bc_prefix
local infix:50 "≼≽_bc" => bc_agrees
local infix:50 "≼/≽_bc" => bc_conflicts

local infix:60 "⎾_bft" => bft_trim
local infix:50 "≼_bft" => bft_prefix
local infix:50 "≼≽_bft" => bft_agrees
local infix:50 "≼/≽_bft" => bft_conflicts

/-- The parameters for an instance of Crosslink 2. -/
structure Crosslink where
  /-- The bc‑confirmation‑depth. -/
  σ : ℕ+
  /-- The finalization gap bound. -/
  L : ℕ+
  /-- "In practice, `L` should be *at least* `2σ`." -/
  L_constraint : L ≥ 2*σ
  /-- Rely on there being no collisions. -/
  nc : NoCollisions

/-- The Last Final bft-block for a given bc-block. -/
def LF (params : Crosslink) (c : BcChain) : BftChain :=
  sorry

/-- The snapshotted bc-block for a given bft-block. -/
def snapshot (params : Crosslink) (b : BftChain) : BcChain :=
  match b.head? with
  | some B => B.headers_bc ⎾_bc params.σ
  | none => []

/--
The candidate bc-chain to update the finalization point to, given that the
bc-tip is at `H`. On each node the finalization point is subject to a local
ratchet that only allows it to move forward. This may cause the candidate to
be ignored (which should happen only rarely under certain difficult attacks).
-/
def candidate (params : Crosslink) (H : BcChain) : BcChain :=
  last_common_ancestor params.nc (snapshot params (LF params H)) (H ⎾_bc params.σ)

/-- Apply `update` to `initial` a specified number of times. -/
def scan {A : Type} (update : ℕ → A → A) (initial : A) : ℕ → A
  | 0 => initial
  | s+1 => update (s+1) (scan update initial s)

/--
Equivalent to `scan`. This could be more efficient than `scan`, but is too hard
to prove anything about currently.
-/
def scan_iterative {A : Type} (update : ℕ → A → A) (initial : A) (t : ℕ) : A := Id.run do
  let mut state : A := initial
  for s in [0:t] do state ← update (s+1) state
  state

/-- Given `fin i s`, transition to `fin i t` where `t = s+1`. -/
def update_fin (params : Crosslink)
    (ch_i : Time → BcChain) (t : ℕ) (fin_i_s : BcChain) : BcChain :=
  let N := candidate params (ch_i t)
  if fin_i_s ≼_bc N then N else fin_i_s

/- Extend `update_fin` to a time series. -/
def fin (params : Crosslink) (ch_i : Time → BcChain) (t : Time) : BcChain :=
  scan (update_fin params ch_i) [] t

lemma fin_step (params : Crosslink) (ch_i : Time → BcChain) (s : Time)
    : fin params ch_i (s+1) = update_fin params ch_i (s+1) (fin params ch_i s) := by rfl

lemma candidate_trim (params : Crosslink) (ch_i : Time → BcChain) (u : Time)
    : candidate params (ch_i u) ≼_bc ch_i u ⎾_bc params.σ := by
  let bc_snapshot := snapshot params (LF params (ch_i u))
  let bc_confirmed := ch_i u ⎾_bc params.σ
  exact (lca_prefix params.nc bc_snapshot bc_confirmed).right

lemma local_fin_depth (params : Crosslink) (ch : Node → Time → BcChain) (honest : Node → Time → Bool)
    : ∀ (i : Node) (t : Time) (honest_i : honest i t), ∃ (r : Time), r ≤ t ∧ fin params (ch i) t ≼_bc ch i r ⎾_bc params.σ := by
  intro i t honest_i
  use t-1
  simp_all
  sorry

/--
Assured Finality is Agreement on `V` composed with `fin`.
-/
public def AssuredFinality (params : Crosslink) (V : Node → Time → BcChain) :=
  BcAgreement (fun i t => fin params (V i) t)

/--
Safety theorem: Assured Finality from BC Prefix Agreement.
-/
theorem assured_finality_from_bc_prefix_agreement (params : Crosslink)
    (ch : Node → Time → BcChain) (honest : Node → Time → Bool)
    (prefix_agreement : BcPrefixAgreement params.σ ch honest) : AssuredFinality params ch honest := by
  sorry

/--
Safety theorem: Assured Finality from BFT Final Agreement.
-/
theorem assured_finality_from_bft_final_agreement (params : Crosslink)
    (V : Node → Time → BftChain × BcChain) (honest : Node → Time → Bool)
    (final_agreement : BftFinalAgreement (fun i t => (V i t).1) honest)
    : AssuredFinality params (fun i t => (V i t).2) honest := by
  sorry
