import Mathbin.Data.Equiv.Basic 
import Mathbin.Control.EquivFunctor

/-!
# Equivalences for `option α`

We define `remove_none` which acts to provide a `e : α ≃ β` if given a `f : option α ≃ option β`.

To construct an `f : option α ≃ option β` from `e : α ≃ β` such that
`f none = none` and `f (some x) = some (e x)`, use
`f = equiv_functor.map_equiv option e`.
-/


namespace Equiv

variable{α β : Type _}(e : Option α ≃ Option β)

private def remove_none_aux (x : α) : β :=
  if h : (e (some x)).isSome then Option.get h else
    Option.get$
      show (e none).isSome from
        by 
          rw [←Option.ne_none_iff_is_some]
          intro hn 
          rw [Option.not_is_some_iff_eq_none, ←hn] at h 
          simpa only using e.injective h

private theorem remove_none_aux_some {x : α} (h : ∃ x', e (some x) = some x') :
  some (remove_none_aux e x) = e (some x) :=
  by 
    simp [remove_none_aux, option.is_some_iff_exists.mpr h]

private theorem remove_none_aux_none {x : α} (h : e (some x) = none) : some (remove_none_aux e x) = e none :=
  by 
    simp [remove_none_aux, option.not_is_some_iff_eq_none.mpr h]

private theorem remove_none_aux_inv (x : α) : remove_none_aux e.symm (remove_none_aux e x) = x :=
  Option.some_injective _
    (by 
      cases h1 : e.symm (some (remove_none_aux e x)) <;> cases h2 : e (some x)
      ·
        rw [remove_none_aux_none _ h1]
        exact (e.eq_symm_apply.mpr h2).symm
      ·
        rw [remove_none_aux_some _ ⟨_, h2⟩] at h1 
        simpa using h1
      ·
        rw [remove_none_aux_none _ h2] at h1 
        simpa using h1
      ·
        rw [remove_none_aux_some _ ⟨_, h1⟩]
        rw [remove_none_aux_some _ ⟨_, h2⟩]
        simp )

/-- Given an equivalence between two `option` types, eliminate `none` from that equivalence by
mapping `e.symm none` to `e none`. -/
def remove_none : α ≃ β :=
  { toFun := remove_none_aux e, invFun := remove_none_aux e.symm, left_inv := remove_none_aux_inv e,
    right_inv := remove_none_aux_inv e.symm }

@[simp]
theorem remove_none_symm : (remove_none e).symm = remove_none e.symm :=
  rfl

theorem remove_none_some {x : α} (h : ∃ x', e (some x) = some x') : some (remove_none e x) = e (some x) :=
  remove_none_aux_some e h

theorem remove_none_none {x : α} (h : e (some x) = none) : some (remove_none e x) = e none :=
  remove_none_aux_none e h

@[simp]
theorem option_symm_apply_none_iff : e.symm none = none ↔ e none = none :=
  ⟨fun h =>
      by 
        simpa using (congr_argₓ e h).symm,
    fun h =>
      by 
        simpa using (congr_argₓ e.symm h).symm⟩

theorem some_remove_none_iff {x : α} : some (remove_none e x) = e none ↔ e.symm none = some x :=
  by 
    cases' h : e (some x) with a
    ·
      rw [remove_none_none _ h]
      simpa using (congr_argₓ e.symm h).symm
    ·
      rw [remove_none_some _ ⟨a, h⟩]
      have  := congr_argₓ e.symm h 
      rw [symm_apply_apply] at this 
      simp only [false_iffₓ, apply_eq_iff_eq]
      simp [this]

@[simp]
theorem remove_none_map_equiv {α β : Type _} (e : α ≃ β) : remove_none (EquivFunctor.mapEquiv Option e) = e :=
  Equiv.ext$
    fun x =>
      Option.some_injective _$
        remove_none_some _
          ⟨e x,
            by 
              simp [EquivFunctor.map]⟩

end Equiv

