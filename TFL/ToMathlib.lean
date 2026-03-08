import Mathlib.Logic.Basic

lemma List_isSuffixOf_trans {T : Type} {a b c : List T} [BEq T] [LawfulBEq T]
    (a_suff_b : a.isSuffixOf b) (b_suff_c : b.isSuffixOf c) : a.isSuffixOf c := by
  simp_all
  simp [List.IsSuffix.trans a_suff_b b_suff_c]
