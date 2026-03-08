import Mathlib.Logic.Basic

import TFL.Tactic
import TFL.BcChain


local infix:50 "≼" => bc_prefix

/--
Helper function that finds the least common ancestor for bc-chains of the same length.
We assume that if two blocks are equal, they will have the same ancestors.
-/
def lca_same_length (nc : NoCollisions) (as bs : BcChain) (len : ℕ) (ha : len = as.length) (hb : len = bs.length) : BcChain :=
  if len_z : len = 0 then [] else
    match h : (as, bs) with
    | (a::ar, b::br) => if a = b then a::ar else lca_same_length nc ar br (len-1) (by simp_all) (by simp_all)
    | (_, []) => by simp [hb, show bs = [] by simp_all] at len_z -- can't happen
    | ([], _) => by simp [ha, show as = [] by simp_all] at len_z -- can't happen

/--
Find the last common ancestor of two `BcChain`s.
We assume that if two blocks are equal, they will have the same ancestors.
-/
public def last_common_ancestor (nc : NoCollisions) (as bs : BcChain) : BcChain :=
  if as_no_longer : as.length ≤ bs.length then
    lca_same_length nc as (bs.drop (bs.length - as.length)) as.length (by rfl) (by simp [Nat.sub_sub_self, as_no_longer])
  else
    have bs_no_longer : bs.length ≤ as.length := by simp at as_no_longer; exact Nat.le_of_succ_le as_no_longer
    lca_same_length nc bs (as.drop (as.length - bs.length)) bs.length (by rfl) (by simp [Nat.sub_sub_self, bs_no_longer])

/-- The special case of `lca_prefix as bs` when `as` and `bs` are the same length. -/
private lemma lca_prefix_same_length (nc : NoCollisions) (as bs : BcChain)
    (len : ℕ) (ha : len = as.length) (hb : len = bs.length)
    : lca_same_length nc as bs len ha hb ≼ as ∧ lca_same_length nc as bs len ha hb ≼ bs := by
  induction len generalizing as bs <;> unfold lca_same_length <;> simp_all only [bc_prefix, bc_rep_suffix]
  . simp_all only [↓reduceDIte, List.isSuffixOf_nil_left, and_self]
  . rename_i n induct
    (split <;> try simp only [List.isSuffixOf_nil_left, and_self]); rename_i as_ne
    (split <;> try trivial); rename_i a ar b br heq
    simp at heq; obtain ⟨has, hbs⟩ := heq
    split <;> simp_all only [List.isSuffixOf_iff_suffix]
    . simp_all only [List.suffix_rfl, and_self,
                     nc as bs <| show bc_same_tip as bs by simp_all only [bc_same_tip, bc_tip, beq_iff_eq, List.head?_cons]]
    . have brl_eq_arl  : br.length = ar.length := by simp_all only [List.length_cons, Nat.add_right_cancel_iff]
      have n_eq_arl    : n = ar.length := by simp_all only [List.length_cons, Nat.add_right_cancel_iff]
      have ar_suff_aar : ar <:+ a::ar := by simp_all only [List.suffix_cons]
      have br_suff_bbr : br <:+ b::br := by simp_all only [List.suffix_cons]

      let ind := lca_same_length nc ar br ar.length rfl (by simp_all only [List.length_cons])
      suffices ind <:+ a::ar ∧ ind <:+ b::br by simp_all only [List.length_cons, add_tsub_cancel_right, and_self, ind]
      obtain ⟨lca_preceq_ar, lca_preceq_br⟩ := induct ar br (by simp only [n_eq_arl]) (by simp only [brl_eq_arl])
      simp [brl_eq_arl] at lca_preceq_ar lca_preceq_br
      exact And.intro (List.IsSuffix.trans lca_preceq_ar ar_suff_aar)
                      (List.IsSuffix.trans lca_preceq_br br_suff_bbr)

/-- The special case of `lca_prefix as bs` when `as` is no longer than `bs`. -/
private lemma lca_prefix_left_no_longer (nc : NoCollisions) (as bs : BcChain)
    (as_no_longer : as.length ≤ bs.length)
    : last_common_ancestor nc as bs ≼ as ∧ last_common_ancestor nc as bs ≼ bs := by
  unfold last_common_ancestor
  (split <;> try trivial); rename_i a_no_longer

  let btr := bs.drop (bs.length - as.length)
  have asl_eq_btrl : as.length = btr.length := by simp_all only [List.length_drop, Nat.sub_sub_self, btr]
  have btr_suff_bs : btr <:+ bs := List.drop_suffix _ bs
  let lca := lca_same_length nc as btr as.length rfl asl_eq_btrl
  obtain ⟨lca_preceq_as, lca_preceq_btr⟩ := lca_prefix_same_length nc as btr as.length rfl asl_eq_btrl
  have lca_preceq_bs : lca ≼ bs := by
    simp [bc_prefix, bc_rep_suffix] at ⊢ lca_preceq_btr; exact List.IsSuffix.trans lca_preceq_btr btr_suff_bs
  trivial

/-- `last_common_ancestor as bs` is a prefix of both `as` and `bs`. -/
public lemma lca_prefix (nc : NoCollisions) (as bs : BcChain)
    : last_common_ancestor nc as bs ≼ as ∧ last_common_ancestor nc as bs ≼ bs := by
  unfold last_common_ancestor
  split
  . rename_i as_no_longer
    let lca_prec_asbs := lca_prefix_left_no_longer nc as bs as_no_longer
    simp only [as_no_longer, last_common_ancestor] at lca_prec_asbs
    exact lca_prec_asbs
  . rename_i bs_no_longer
    apply Nat.le_of_not_ge at bs_no_longer
    let lca_prec_bsas := lca_prefix_left_no_longer nc bs as bs_no_longer
    simp only [bs_no_longer, last_common_ancestor, ↓reduceDIte] at lca_prec_bsas
    simp_all only [and_self]

/-- The special case of `lca_unique` when `as` and `bs` are the same length. -/
public lemma lca_unique_same_length (nc : NoCollisions) (as bs es : BcChain)
    (len : ℕ) (ha : len = as.length) (hb : len = bs.length)
    (es_preceq_as : es ≼ as) (es_preceq_bs : es ≼ bs)
    : es ≼ lca_same_length nc as bs len ha hb := by
  induction len generalizing as bs <;> unfold lca_same_length <;> split <;> try contradiction
  . simp_all only [show as = [] by exact List.length_eq_zero_iff.mp ha.symm]
  . rename_i len ind _
    (cases as <;> try contradiction); rename_i a ar; have es_preceq_aar : es ≼ a::ar := by trivial
    (cases bs <;> try contradiction); rename_i b br; have es_preceq_bbr : es ≼ b::br := by trivial
    (split <;> try contradiction); rename_i a' ar' b' br' heq
    (split <;> try simp_all); rename_i a'_neq_b'
    injections; rename_i len_eq_arl _ beq a_eq_a' ar_eq_ar'; subst a_eq_a' ar_eq_ar'
    injection beq; rename_i b_eq_b' br_eq_br'; subst b_eq_b' br_eq_br'
    have arl_eq_brl : ar.length = br.length := by simp_all only
    suffices es ≼ ar ∧ es ≼ br by simp_all only
    unfold bc_prefix bc_rep_suffix at ⊢ es_preceq_aar es_preceq_bbr
    simp_all only [List.isSuffixOf_iff_suffix]
    have haar : es = a::ar ∨ es <:+ ar := List.suffix_cons_iff.mp es_preceq_aar
    have hbbr : es = b::br ∨ es <:+ br := List.suffix_cons_iff.mp es_preceq_bbr
    have esl_neq_aarl : es.length ≠ (a::ar).length := by
      by_contra esl_eq_aarl
      have es_eq_aar : es = a::ar := es_preceq_aar.eq_of_length esl_eq_aarl
      have es_eq_bbr : es = b::br := es_preceq_bbr.eq_of_length <| show es.length = (b::br).length by simp_all only
      have a_eq_b : a = b := List.head_eq_of_cons_eq <| show a::ar = b::br by simp_all only
      contradiction
    cases haar <;> simp_all
    cases hbbr <;> simp_all

/-- The special case of `lca_unique` when `as` is no longer than `bs`. -/
public lemma lca_unique_left_no_longer (nc : NoCollisions) (as bs es : BcChain)
  (left_no_longer : as.length ≤ bs.length)
  (es_preceq_as : es ≼ as) (es_preceq_bs : es ≼ bs) : es ≼ last_common_ancestor nc as bs := by
  unfold last_common_ancestor
  simp [left_no_longer]
  let btr := bs.drop (bs.length - as.length)
  have asl_eq_btrl : as.length = btr.length := by simp_all only [List.length_drop, Nat.sub_sub_self, btr]
  have btr_suff_bs : btr <:+ bs := List.drop_suffix _ bs
  let lca := lca_same_length nc as btr as.length rfl asl_eq_btrl
  change es ≼ lca
  have es_preceq_btr : es ≼ btr := by
    unfold bc_prefix bc_rep_suffix at ⊢ es_preceq_as es_preceq_bs
    simp_all only [List.isSuffixOf_iff_suffix]
    have esl_leq_btrl : es.length ≤ btr.length := by rw [← asl_eq_btrl]; exact List.IsSuffix.length_le es_preceq_as
    exact List.suffix_of_suffix_length_le es_preceq_bs btr_suff_bs esl_leq_btrl
  exact lca_unique_same_length nc as btr es as.length rfl asl_eq_btrl es_preceq_as es_preceq_btr

/-
For any `es : BcChain` with `es ≼ as ∧ es ≼ bs` we have `es ≼ last_common_ancestor as bs`.
-/
public lemma lca_unique (nc : NoCollisions) (as bs es : BcChain)
  (es_preceq_as : es ≼ as) (es_preceq_bs : es ≼ bs) : es ≼ last_common_ancestor nc as bs := by
  unfold last_common_ancestor
  split
  . rename_i as_no_longer
    let lca_prec_asbs := lca_unique_left_no_longer nc as bs es as_no_longer
    simp only [as_no_longer, last_common_ancestor] at lca_prec_asbs
    exact lca_prec_asbs es_preceq_as es_preceq_bs
  . rename_i bs_no_longer
    apply Nat.le_of_not_ge at bs_no_longer
    let lca_prec_bsas := lca_unique_left_no_longer nc bs as es bs_no_longer
    simp only [bs_no_longer, last_common_ancestor] at lca_prec_bsas
    exact lca_prec_bsas es_preceq_bs es_preceq_as
