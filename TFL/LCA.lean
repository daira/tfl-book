import Mathlib.Logic.Basic

import TFL.Tactic
import TFL.BcChain


variable (NC : NoCollisions)
local infix:50 "≼" => bc_prefix NC


/-- Helper function that finds the least common ancestor for bc-chains of the same length. -/
def lca_same_length (as bs : BcChain) (len : ℕ) (ha : len = as.length) (hb : len = bs.length) : BcChain :=
  if len_z : len = 0 then [] else
    match h : (as, bs) with
    | (a::ar, b::br) => if a = b then ar else lca_same_length ar br (len-1) (by simp_all) (by simp_all)
    | (_, []) => by simp [hb] at len_z; simp_all -- can't happen
    | ([], _) => by simp [ha] at len_z; simp_all -- can't happen

/-
Find the last common ancestor of two `BcChain`s. We assume that if two blocks are equal, they will have the
same ancestors.
-/
public def last_common_ancestor (a b : BcChain) : BcChain :=
  if a_no_longer : a.length ≤ b.length then
    lca_same_length a (b.drop (b.length - a.length)) a.length (by rfl) (by simp [Nat.sub_sub_self, a_no_longer])
  else
    let b_no_longer := show b.length ≤ a.length by simp at a_no_longer; exact Nat.le_of_succ_le a_no_longer
    lca_same_length b (a.drop (a.length - b.length)) b.length (by rfl) (by simp [Nat.sub_sub_self, b_no_longer])

-- TODO: merge `lca_same_length_left` and `lca_same_length_right`.

private lemma lca_same_length_left (as bs : BcChain) (len : ℕ) (ha : len = as.length) (hb : len = bs.length)
  : lca_same_length as bs len ha hb ≼ as := by
  induction len generalizing as bs
  . unfold lca_same_length
    quiet simp_all only [bc_prefix, bc_rep_suffix, ↓reduceDIte, List.isSuffixOf_nil_left, List.nil_suffix, decide_true, true_or, Bool.true_or]
  . rename_i n induct
    unfold lca_same_length; simp_all only [bc_prefix, bc_rep_suffix]
    split <;> try quiet simp only [List.isSuffixOf_nil_left, List.nil_suffix, decide_true, true_or, Bool.true_or]
    rename_i as_ne
    split <;> try trivial
    rename_i a ar b br heq
    simp at heq
    split
    . quiet simp_all only [List.isSuffixOf_iff_suffix, List.suffix_cons, decide_true, true_or, Bool.true_or, Bool.or_eq_true,
                           NC as bs <| by simp_all only [bc_same_tip, bc_tip, beq_iff_eq, List.head?_cons]]
    . rename_i a_neq_b
      have brl_eq_arl   : br.length = ar.length := by simp_all only [List.length_cons, Nat.add_right_cancel_iff]
      have n_eq_arl     : n = ar.length := by simp_all only [List.length_cons, Nat.add_right_cancel_iff]
      have ar_suff_aar  : ar <:+ a::ar := by quiet simp_all [List.length_cons, decide_eq_true_eq]

      let ind := lca_same_length ar br ar.length rfl (by simp_all only [List.length_cons])
      suffices ind <:+ a::ar by quiet simp_all only [bc_rep_suffix, List.isSuffixOf_iff_suffix, List.length_cons, add_tsub_cancel_right,
                                                     decide_true, true_or, Bool.true_or, Bool.or_eq_true, ind]
      let ind_preceq_ar := induct ar br (by simp only [n_eq_arl]) (by simp only [brl_eq_arl])
      simp [brl_eq_arl] at ind_preceq_ar
      cases ind_preceq_ar with | inl lca_suff_ar => exact List.IsSuffix.trans lca_suff_ar ar_suff_aar
                               | inr lca_same_ar => simp_all only [NC ind ar lca_same_ar]

private lemma lca_same_length_right (as bs : BcChain) (len : ℕ) (ha : len = as.length) (hb : len = bs.length)
  : lca_same_length as bs len ha hb ≼ bs := by
  induction len generalizing as bs
  . unfold lca_same_length
    quiet simp_all only [bc_prefix, bc_rep_suffix, ↓reduceDIte, List.isSuffixOf_nil_left, List.nil_suffix, decide_true, true_or, Bool.true_or]
  . rename_i n induct
    unfold lca_same_length; simp_all only [bc_prefix, bc_rep_suffix]
    split <;> try quiet simp only [List.isSuffixOf_nil_left, List.nil_suffix, decide_true, true_or, Bool.true_or]
    rename_i as_ne
    split <;> try trivial
    rename_i a ar b br heq
    simp at heq
    split
    . quiet simp_all only [List.isSuffixOf_iff_suffix, List.suffix_cons, decide_true, true_or, Bool.true_or, Bool.or_eq_true,
                           NC as bs <| by simp_all only [bc_same_tip, bc_tip, beq_iff_eq, List.head?_cons]]
    . rename_i a_neq_b
      have brl_eq_arl   : br.length = ar.length := by simp_all only [List.length_cons, Nat.add_right_cancel_iff]
      have n_eq_arl     : n = ar.length := by simp_all only [List.length_cons, Nat.add_right_cancel_iff]
      have br_suff_bbr  : br <:+ b::br := by simp_all only [List.suffix_cons]

      let ind := lca_same_length ar br ar.length rfl (by simp_all only [List.length_cons])
      suffices ind <:+ b::br by quiet simp_all only [bc_rep_suffix, List.isSuffixOf_iff_suffix, List.length_cons, add_tsub_cancel_right,
                                                     decide_true, true_or, Bool.true_or, Bool.or_eq_true, ind]
      let ind_preceq_br := induct ar br (by simp only [n_eq_arl]) (by simp only [brl_eq_arl])
      simp [brl_eq_arl] at ind_preceq_br
      cases ind_preceq_br with | inl lca_suff_br => exact List.IsSuffix.trans lca_suff_br br_suff_bbr
                               | inr lca_same_br => simp_all only [NC ind br lca_same_br]

/-- The special case of `lca a b` when `a` is no longer than `b`. -/
private lemma lca_left_no_longer (a b : BcChain) (a_no_longer : a.length ≤ b.length)
  : last_common_ancestor a b ≼ a ∧ last_common_ancestor a b ≼ b := by
  unfold last_common_ancestor
  split <;> try trivial
  rename_i a_no_longer

  let btr := b.drop (b.length - a.length)
  have al_eq_btrl : a.length = btr.length := by simp_all only [List.length_drop, Nat.sub_sub_self, btr]
  have btr_suff_b : btr <:+ b := by exact List.drop_suffix _ b
  let lca := lca_same_length a btr a.length rfl al_eq_btrl
  let lca_slr := lca_same_length_right NC a btr a.length rfl al_eq_btrl
  let lca_slr' := lca_same_length_left NC a btr a.length rfl al_eq_btrl

  change lca ≼ a ∧ lca ≼ b
  apply And.intro
  . exact lca_slr'
  . simp [bc_prefix, bc_rep_suffix] at ⊢ lca_slr lca_slr'
    left
    cases lca_slr with | inl lca_suff_btr => exact List.IsSuffix.trans lca_suff_btr btr_suff_b
                       | inr lca_same_btr => quiet simp_all only [List.isSuffixOf_iff_suffix, NC lca btr lca_same_btr]

/-- `last_common_ancestor a b` is a prefix of both `a` and `b`. -/
public lemma lca_prefix (a b : BcChain) : last_common_ancestor a b ≼ a ∧ last_common_ancestor a b ≼ b := by
  unfold last_common_ancestor
  split
  . rename_i a_no_longer
    let lca_prec_ab := lca_left_no_longer NC a b a_no_longer
    simp only [a_no_longer, last_common_ancestor] at lca_prec_ab
    exact lca_prec_ab
  . rename_i b_no_longer
    apply Nat.le_of_not_ge at b_no_longer
    let lca_prec_ba := lca_left_no_longer NC b a b_no_longer
    simp only [b_no_longer, last_common_ancestor, ↓reduceDIte] at lca_prec_ba
    simp_all only [and_self]

/-
The last common ancestor of `a` and `b` is unique, i.e. there is no other `e : BcChain` with
`e ≼ a ∧ e ≼ b ∧ e ≠ last_common_ancestor a b`.
-/
--lemma lca_unique (a b e : BcChain) (e_preceq_a : e ≼ a) (e_preceq_b : e ≼ b) : e = last_common_ancestor a b := by
--  sorry
