import Mathbin.Data.List.Range

/-! 
# Lemmas about list.*_with_index functions.

Some specification lemmas for `list.map_with_index`, `list.mmap_with_index`, `list.foldl_with_index`
and `list.foldr_with_index`.
-/


universe u v

open Function

namespace List

variable{α : Type u}{β : Type v}

section MapWithIndex

theorem map_with_index_core_eq (l : List α) (f : ℕ → α → β) (n : ℕ) :
  l.map_with_index_core f n = l.map_with_index fun i a => f (i+n) a :=
  by 
    induction' l with hd tl hl generalizing f n
    ·
      simp [map_with_index, map_with_index_core]
    ·
      rw [map_with_index]
      simp [map_with_index_core, hl, add_left_commₓ, add_assocₓ, add_commₓ]

theorem map_with_index_eq_enum_map (l : List α) (f : ℕ → α → β) :
  l.map_with_index f = l.enum.map (Function.uncurry f) :=
  by 
    induction' l with hd tl hl generalizing f
    ·
      simp [map_with_index, map_with_index_core, List.enum_eq_zip_range]
    ·
      rw [map_with_index, map_with_index_core, map_with_index_core_eq, hl]
      simp [enum_eq_zip_range, range_succ_eq_map, zip_with_map_left, map_uncurry_zip_eq_zip_with]

end MapWithIndex

section FoldrWithIndex

/-- Specification of `foldr_with_index_aux`. -/
def foldr_with_index_aux_spec (f : ℕ → α → β → β) (start : ℕ) (b : β) (as : List α) : β :=
  foldr (uncurry f) b$ enum_from start as

theorem foldr_with_index_aux_spec_cons (f : ℕ → α → β → β) start b a as :
  foldr_with_index_aux_spec f start b (a :: as) = f start a (foldr_with_index_aux_spec f (start+1) b as) :=
  rfl

theorem foldr_with_index_aux_eq_foldr_with_index_aux_spec (f : ℕ → α → β → β) start b as :
  foldr_with_index_aux f start b as = foldr_with_index_aux_spec f start b as :=
  by 
    induction as generalizing start
    ·
      rfl
    ·
      simp only [foldr_with_index_aux, foldr_with_index_aux_spec_cons]

theorem foldr_with_index_eq_foldr_enum (f : ℕ → α → β → β) (b : β) (as : List α) :
  foldr_with_index f b as = foldr (uncurry f) b (enum as) :=
  by 
    simp only [foldr_with_index, foldr_with_index_aux_spec, foldr_with_index_aux_eq_foldr_with_index_aux_spec, enum]

end FoldrWithIndex

theorem indexes_values_eq_filter_enum (p : α → Prop) [DecidablePred p] (as : List α) :
  indexes_values p as = filter (p ∘ Prod.snd) (enum as) :=
  by 
    simp [indexes_values, foldr_with_index_eq_foldr_enum, uncurry, filter_eq_foldr]

theorem find_indexes_eq_map_indexes_values (p : α → Prop) [DecidablePred p] (as : List α) :
  find_indexes p as = map Prod.fst (indexes_values p as) :=
  by 
    simp only [indexes_values_eq_filter_enum, map_filter_eq_foldr, find_indexes, foldr_with_index_eq_foldr_enum,
      uncurry]

section FoldlWithIndex

-- error in Data.List.Indexes: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Specification of `foldl_with_index_aux`. -/
def foldl_with_index_aux_spec (f : exprℕ() → α → β → α) (start : exprℕ()) (a : α) (bs : list β) : α :=
«expr $ »(foldl (λ (a) (p : «expr × »(exprℕ(), β)), f p.fst a p.snd) a, enum_from start bs)

theorem foldl_with_index_aux_spec_cons (f : ℕ → α → β → α) start a b bs :
  foldl_with_index_aux_spec f start a (b :: bs) = foldl_with_index_aux_spec f (start+1) (f start a b) bs :=
  rfl

theorem foldl_with_index_aux_eq_foldl_with_index_aux_spec (f : ℕ → α → β → α) start a bs :
  foldl_with_index_aux f start a bs = foldl_with_index_aux_spec f start a bs :=
  by 
    induction bs generalizing start a
    ·
      rfl
    ·
      simp [foldl_with_index_aux, foldl_with_index_aux_spec_cons]

-- error in Data.List.Indexes: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem foldl_with_index_eq_foldl_enum
(f : exprℕ() → α → β → α)
(a : α)
(bs : list β) : «expr = »(foldl_with_index f a bs, foldl (λ
  (a)
  (p : «expr × »(exprℕ(), β)), f p.fst a p.snd) a (enum bs)) :=
by simp [] [] ["only"] ["[", expr foldl_with_index, ",", expr foldl_with_index_aux_spec, ",", expr foldl_with_index_aux_eq_foldl_with_index_aux_spec, ",", expr enum, "]"] [] []

end FoldlWithIndex

section MfoldWithIndex

variable{m : Type u → Type v}[Monadₓ m]

theorem mfoldr_with_index_eq_mfoldr_enum {α β} (f : ℕ → α → β → m β) (b : β) (as : List α) :
  mfoldr_with_index f b as = mfoldr (uncurry f) b (enum as) :=
  by 
    simp only [mfoldr_with_index, mfoldr_eq_foldr, foldr_with_index_eq_foldr_enum, uncurry]

-- error in Data.List.Indexes: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem mfoldl_with_index_eq_mfoldl_enum
[is_lawful_monad m]
{α β}
(f : exprℕ() → β → α → m β)
(b : β)
(as : list α) : «expr = »(mfoldl_with_index f b as, mfoldl (λ
  (b)
  (p : «expr × »(exprℕ(), α)), f p.fst b p.snd) b (enum as)) :=
by rw ["[", expr mfoldl_with_index, ",", expr mfoldl_eq_foldl, ",", expr foldl_with_index_eq_foldl_enum, "]"] []

end MfoldWithIndex

section MmapWithIndex

variable{m : Type u → Type v}[Applicativeₓ m]

/-- Specification of `mmap_with_index_aux`. -/
def mmap_with_index_aux_spec {α β} (f : ℕ → α → m β) (start : ℕ) (as : List α) : m (List β) :=
  List.traverseₓ (uncurry f)$ enum_from start as

theorem mmap_with_index_aux_spec_cons {α β} (f : ℕ → α → m β) (start : ℕ) (a : α) (as : List α) :
  mmap_with_index_aux_spec f start (a :: as) = (List.cons <$> f start a)<*>mmap_with_index_aux_spec f (start+1) as :=
  rfl

theorem mmap_with_index_aux_eq_mmap_with_index_aux_spec {α β} (f : ℕ → α → m β) (start : ℕ) (as : List α) :
  mmap_with_index_aux f start as = mmap_with_index_aux_spec f start as :=
  by 
    induction as generalizing start
    ·
      rfl
    ·
      simp [mmap_with_index_aux, mmap_with_index_aux_spec_cons]

theorem mmap_with_index_eq_mmap_enum {α β} (f : ℕ → α → m β) (as : List α) :
  mmap_with_index f as = List.traverseₓ (uncurry f) (enum as) :=
  by 
    simp only [mmap_with_index, mmap_with_index_aux_spec, mmap_with_index_aux_eq_mmap_with_index_aux_spec, enum]

end MmapWithIndex

section MmapWithIndex'

variable{m : Type u → Type v}[Applicativeₓ m][IsLawfulApplicative m]

theorem mmap_with_index'_aux_eq_mmap_with_index_aux {α} (f : ℕ → α → m PUnit) (start : ℕ) (as : List α) :
  mmap_with_index'_aux f start as = mmap_with_index_aux f start as *> pure PUnit.unit :=
  by 
    induction as generalizing start <;>
      simp' [mmap_with_index'_aux, mmap_with_index_aux, seq_right_eq, const, -comp_const] with functor_norm

theorem mmap_with_index'_eq_mmap_with_index {α} (f : ℕ → α → m PUnit) (as : List α) :
  mmap_with_index' f as = mmap_with_index f as *> pure PUnit.unit :=
  by 
    apply mmap_with_index'_aux_eq_mmap_with_index_aux

end MmapWithIndex'

end List

