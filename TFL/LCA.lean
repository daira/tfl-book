import Mathlib.Logic.Basic

import TFL.Tactic
import TFL.BcChain


local infix:50 "≼" => bc_prefix

/-- Helper function that finds the least common ancestor for bc-chains of the same length. -/
def lca_same_length (nc : NoCollisions) (as bs : BcChain) (len : ℕ) (ha : len = as.length) (hb : len = bs.length) : BcChain :=
  if len_z : len = 0 then [] else
    match h : (as, bs) with
    | (a::ar, b::br) => if a = b then a::ar else lca_same_length nc ar br (len-1) (by simp_all) (by simp_all)
    | (_, []) => by simp [hb] at len_z; simp_all -- can't happen
    | ([], _) => by simp [ha] at len_z; simp_all -- can't happen

/-
Find the last common ancestor of two `BcChain`s. We assume that if two blocks are equal, they will have the
same ancestors.
-/
public def last_common_ancestor (nc : NoCollisions) (a b : BcChain) : BcChain :=
  if a_no_longer : a.length ≤ b.length then
    lca_same_length nc a (b.drop (b.length - a.length)) a.length (by rfl) (by simp [Nat.sub_sub_self, a_no_longer])
  else
    have b_no_longer : b.length ≤ a.length := by simp at a_no_longer; exact Nat.le_of_succ_le a_no_longer
    lca_same_length nc b (a.drop (a.length - b.length)) b.length (by rfl) (by simp [Nat.sub_sub_self, b_no_longer])

private lemma lca_same_length_prefix (nc : NoCollisions) (as bs : BcChain) (len : ℕ) (ha : len = as.length) (hb : len = bs.length)
  : lca_same_length nc as bs len ha hb ≼ as ∧ lca_same_length nc as bs len ha hb ≼ bs := by
  induction len generalizing as bs
  . unfold lca_same_length
    simp_all only [bc_prefix, bc_rep_suffix, ↓reduceDIte, List.isSuffixOf_nil_left, and_self]
  . rename_i n induct
    unfold lca_same_length; simp_all only [bc_prefix, bc_rep_suffix]
    split <;> try simp only [List.isSuffixOf_nil_left, and_self]
    rename_i as_ne
    split <;> try trivial
    rename_i a ar b br heq
    simp at heq
    obtain ⟨has, hbs⟩ := heq
    split
    . simp_all only [List.isSuffixOf_iff_suffix, List.suffix_cons, and_self,
                     nc as bs <| by simp_all only [bc_same_tip, bc_tip, beq_iff_eq, List.head?_cons]]
    . have brl_eq_arl   : br.length = ar.length := by simp_all only [List.length_cons, Nat.add_right_cancel_iff]
      have n_eq_arl     : n = ar.length := by simp_all only [List.length_cons, Nat.add_right_cancel_iff]
      have ar_suff_aar  : ar <:+ a::ar := by simp_all [List.length_cons]
      have br_suff_bbr  : br <:+ b::br := by simp_all [List.length_cons]

      let ind := lca_same_length nc ar br ar.length rfl (by simp_all only [List.length_cons])
      suffices ind <:+ a::ar ∧ ind <:+ b::br by
        simp_all only [List.isSuffixOf_iff_suffix, List.length_cons, add_tsub_cancel_right, and_self, ind]
      let ind_preceq := induct ar br (by simp only [n_eq_arl]) (by simp only [brl_eq_arl])
      simp [brl_eq_arl] at ind_preceq
      apply And.intro
      . exact List.IsSuffix.trans ind_preceq.left ar_suff_aar
      . exact List.IsSuffix.trans ind_preceq.right br_suff_bbr

/-- The special case of `lca a b` when `a` is no longer than `b`. -/
private lemma lca_left_no_longer (nc : NoCollisions) (a b : BcChain) (a_no_longer : a.length ≤ b.length)
  : last_common_ancestor nc a b ≼ a ∧ last_common_ancestor nc a b ≼ b := by
  unfold last_common_ancestor
  split <;> try trivial
  rename_i a_no_longer

  let btr := b.drop (b.length - a.length)
  have al_eq_btrl : a.length = btr.length := by simp_all only [List.length_drop, Nat.sub_sub_self, btr]
  have btr_suff_b : btr <:+ b := by exact List.drop_suffix _ b
  let lca := lca_same_length nc a btr a.length rfl al_eq_btrl
  let lca_slr := lca_same_length_prefix nc a btr a.length rfl al_eq_btrl

  change lca ≼ a ∧ lca ≼ b
  apply And.intro
  . exact lca_slr.left
  . simp [bc_prefix, bc_rep_suffix] at ⊢ lca_slr
    exact List.IsSuffix.trans lca_slr.right btr_suff_b

/-- `last_common_ancestor a b` is a prefix of both `a` and `b`. -/
public lemma lca_prefix (nc : NoCollisions) (a b : BcChain)
    : last_common_ancestor nc a b ≼ a ∧ last_common_ancestor nc a b ≼ b := by
  unfold last_common_ancestor
  split
  . rename_i a_no_longer
    let lca_prec_ab := lca_left_no_longer nc a b a_no_longer
    simp only [a_no_longer, last_common_ancestor] at lca_prec_ab
    exact lca_prec_ab
  . rename_i b_no_longer
    apply Nat.le_of_not_ge at b_no_longer
    let lca_prec_ba := lca_left_no_longer nc b a b_no_longer
    simp only [b_no_longer, last_common_ancestor, ↓reduceDIte] at lca_prec_ba
    simp_all only [and_self]

/-
The last common ancestor of `a` and `b` is unique, i.e. there is no other `e : BcChain` with
`e ≼ a ∧ e ≼ b ∧ e ≠ last_common_ancestor a b`.
-/
--lemma lca_unique (a b e : BcChain) (e_preceq_a : e ≼ a) (e_preceq_b : e ≼ b) : e = last_common_ancestor a b := by
--  sorry
