import Mathbin.GroupTheory.Perm.Sign 
import Mathbin.Data.Equiv.Option

/-!
# Permutations of `option α`
-/


open Equivₓ

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
theorem map_equiv_option_refl {α : Type _} : EquivFunctor.mapEquiv Option (Equivₓ.refl α) = 1 :=
  map_equiv_option_one

@[simp]
theorem map_equiv_option_swap {α : Type _} [DecidableEq α] (x y : α) :
  EquivFunctor.mapEquiv Option (swap x y) = swap (some x) (some y) :=
  by 
    ext (_ | i)
    ·
      simp [swap_apply_of_ne_of_ne]
    ·
      byCases' hx : i = x 
      simp [hx, swap_apply_of_ne_of_ne, EquivFunctor.map]
      byCases' hy : i = y <;> simp [hx, hy, swap_apply_of_ne_of_ne, EquivFunctor.map]

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

@[simp]
theorem map_equiv_remove_none {α : Type _} [DecidableEq α] (σ : perm (Option α)) :
  EquivFunctor.mapEquiv Option (remove_none σ) = swap none (σ none)*σ :=
  by 
    ext1 x 
    have  : Option.map (⇑remove_none σ) x = (swap none (σ none)) (σ x)
    ·
      cases x
      ·
        simp 
      ·
        cases h : σ (some x)
        ·
          simp [remove_none_none _ h]
        ·
          have hn : σ (some x) ≠ none :=
            by 
              simp [h]
          have hσn : σ (some x) ≠ σ none :=
            σ.injective.ne
              (by 
                simp )
          simp [remove_none_some _ ⟨_, h⟩, ←h, swap_apply_of_ne_of_ne hn hσn]
    simpa using this

/-- Permutations of `option α` are equivalent to fixing an
`option α` and permuting the remaining with a `perm α`.
The fixed `option α` is swapped with `none`. -/
@[simps]
def Equivₓ.Perm.decomposeOption {α : Type _} [DecidableEq α] : perm (Option α) ≃ Option α × perm α :=
  { toFun := fun σ => (σ none, remove_none σ), invFun := fun i => swap none i.1*EquivFunctor.mapEquiv Option i.2,
    left_inv :=
      fun σ =>
        by 
          simp ,
    right_inv :=
      fun ⟨x, σ⟩ =>
        by 
          have  : remove_none (swap none x*EquivFunctor.mapEquiv Option σ) = σ :=
            EquivFunctor.map_equiv_option_injective
              (by 
                simp [←mul_assocₓ, EquivFunctor.map])
          simp [←perm.eq_inv_iff_eq, EquivFunctor.map, this] }

theorem Equivₓ.Perm.decompose_option_symm_of_none_apply {α : Type _} [DecidableEq α] (e : perm α) (i : Option α) :
  Equivₓ.Perm.decomposeOption.symm (none, e) i = i.map e :=
  by 
    simp [EquivFunctor.map]

theorem Equivₓ.Perm.decompose_option_symm_sign {α : Type _} [DecidableEq α] [Fintype α] (e : perm α) :
  perm.sign (Equivₓ.Perm.decomposeOption.symm (none, e)) = perm.sign e :=
  by 
    simp 

/-- The set of all permutations of `option α` can be constructed by augmenting the set of
permutations of `α` by each element of `option α` in turn. -/
theorem Finset.univ_perm_option {α : Type _} [DecidableEq α] [Fintype α] :
  @Finset.univ (perm$ Option α) _ =
    (Finset.univ : Finset$ Option α × perm α).map Equivₓ.Perm.decomposeOption.symm.toEmbedding :=
  (Finset.univ_map_equiv_to_embedding _).symm

