import Mathbin.GroupTheory.Perm.Sign 
import Mathbin.Data.Equiv.Option

/-!
# Permutations of `option α`
-/


open Equiv

theorem EquivFunctor.map_equiv_option_injective {α β : Type _} :
  Function.Injective (EquivFunctor.mapEquiv Option : α ≃ β → Option α ≃ Option β) :=
  EquivFunctor.mapEquiv.injective Option Option.some_injective

@[simp]
theorem EquivFunctor.Option.map_none {α β : Type _} (e : α ≃ β) : EquivFunctor.map e none = none :=
  by 
    simp [EquivFunctor.map]

@[simp]
theorem map_equiv_option_one {α : Type _} : EquivFunctor.mapEquiv Option (1 : perm α) = 1 :=
  by 
    ext 
    simp [EquivFunctor.mapEquiv, EquivFunctor.map]

@[simp]
theorem map_equiv_option_refl {α : Type _} : EquivFunctor.mapEquiv Option (Equiv.refl α) = 1 :=
  map_equiv_option_one

@[simp]
theorem map_equiv_option_swap {α : Type _} [DecidableEq α] (x y : α) :
  EquivFunctor.mapEquiv Option (swap x y) = swap (some x) (some y) :=
  by 
    ext (_ | i)
    ·
      simp [swap_apply_of_ne_of_ne]
    ·
      byCases' hx : i = x <;> byCases' hy : i = y <;> simp [hx, hy, swap_apply_of_ne_of_ne, EquivFunctor.map]

@[simp]
theorem EquivFunctor.Option.sign {α : Type _} [DecidableEq α] [Fintype α] (e : perm α) :
  perm.sign (EquivFunctor.mapEquiv Option e) = perm.sign e :=
  by 
    apply perm.swap_induction_on e
    ·
      simp [perm.one_def]
    ·
      intro f x y hne h 
      simp [h, hne, perm.mul_def, ←EquivFunctor.map_equiv_trans]

-- error in GroupTheory.Perm.Option: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem map_equiv_remove_none
{α : Type*}
[decidable_eq α]
(σ : perm (option α)) : «expr = »(equiv_functor.map_equiv option (remove_none σ), «expr * »(swap none (σ none), σ)) :=
begin
  ext1 [] [ident x],
  have [] [":", expr «expr = »(option.map «expr⇑ »(remove_none σ) x, swap none (σ none) (σ x))] [],
  { cases [expr x] [],
    { simp [] [] [] [] [] [] },
    { cases [expr h, ":", expr σ (some x)] [],
      { simp [] [] [] ["[", expr remove_none_none _ h, "]"] [] [] },
      { have [ident hn] [":", expr «expr ≠ »(σ (some x), none)] [":=", expr by simp [] [] [] ["[", expr h, "]"] [] []],
        have [ident hσn] [":", expr «expr ≠ »(σ (some x), σ none)] [":=", expr σ.injective.ne (by simp [] [] [] [] [] [])],
        simp [] [] [] ["[", expr remove_none_some _ ⟨_, h⟩, ",", "<-", expr h, ",", expr swap_apply_of_ne_of_ne hn hσn, "]"] [] [] } } },
  simpa [] [] [] [] [] ["using", expr this]
end

-- error in GroupTheory.Perm.Option: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Permutations of `option α` are equivalent to fixing an
`option α` and permuting the remaining with a `perm α`.
The fixed `option α` is swapped with `none`. -/
@[simps #[]]
def equiv.perm.decompose_option
{α : Type*}
[decidable_eq α] : «expr ≃ »(perm (option α), «expr × »(option α, perm α)) :=
{ to_fun := λ σ, (σ none, remove_none σ),
  inv_fun := λ i, «expr * »(swap none i.1, equiv_functor.map_equiv option i.2),
  left_inv := λ σ, by simp [] [] [] [] [] [],
  right_inv := λ ⟨x, σ⟩, begin
    have [] [":", expr «expr = »(remove_none «expr * »(swap none x, equiv_functor.map_equiv option σ), σ)] [":=", expr equiv_functor.map_equiv_option_injective (by simp [] [] [] ["[", "<-", expr mul_assoc, ",", expr equiv_functor.map, "]"] [] [])],
    simp [] [] [] ["[", "<-", expr perm.eq_inv_iff_eq, ",", expr equiv_functor.map, ",", expr this, "]"] [] []
  end }

theorem Equiv.Perm.decompose_option_symm_of_none_apply {α : Type _} [DecidableEq α] (e : perm α) (i : Option α) :
  Equiv.Perm.decomposeOption.symm (none, e) i = i.map e :=
  by 
    simp [EquivFunctor.map]

theorem Equiv.Perm.decompose_option_symm_sign {α : Type _} [DecidableEq α] [Fintype α] (e : perm α) :
  perm.sign (Equiv.Perm.decomposeOption.symm (none, e)) = perm.sign e :=
  by 
    simp 

/-- The set of all permutations of `option α` can be constructed by augmenting the set of
permutations of `α` by each element of `option α` in turn. -/
theorem Finset.univ_perm_option {α : Type _} [DecidableEq α] [Fintype α] :
  @Finset.univ (perm$ Option α) _ =
    (Finset.univ : Finset$ Option α × perm α).map Equiv.Perm.decomposeOption.symm.toEmbedding :=
  (Finset.univ_map_equiv_to_embedding _).symm

