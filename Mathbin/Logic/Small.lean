import Mathbin.Data.Equiv.Set

/-!
# Small types

A type is `w`-small if there exists an equivalence to some `S : Type w`.

We provide a noncomputable model `shrink α : Type w`, and `equiv_shrink α : α ≃ shrink α`.

A subsingleton type is `w`-small for any `w`.

If `α ≃ β`, then `small.{w} α ↔ small.{w} β`.
-/


universe u w v

/--
A type is `small.{w}` if there exists an equivalence to some `S : Type w`.
-/
class Small (α : Type v) : Prop where 
  equiv_small : ∃ S : Type w, Nonempty (α ≃ S)

/--
Constructor for `small α` from an explicit witness type and equivalence.
-/
theorem Small.mk' {α : Type v} {S : Type w} (e : α ≃ S) : Small.{w} α :=
  ⟨⟨S, ⟨e⟩⟩⟩

/--
An arbitrarily chosen model in `Type w` for a `w`-small type.
-/
@[nolint has_inhabited_instance]
def Shrink (α : Type v) [Small.{w} α] : Type w :=
  Classical.some (@Small.equiv_small α _)

/--
The noncomputable equivalence between a `w`-small type and a model.
-/
noncomputable def equivShrink (α : Type v) [Small.{w} α] : α ≃ Shrink α :=
  Nonempty.some (Classical.some_spec (@Small.equiv_small α _))

instance (priority := 100) small_self (α : Type v) : Small.{v} α :=
  Small.mk' (Equiv.refl _)

instance (priority := 100) small_max (α : Type v) : Small.{max w v} α :=
  Small.mk' Equiv.ulift.{w}.symm

instance small_ulift (α : Type v) : Small.{v} (Ulift.{w} α) :=
  Small.mk' Equiv.ulift

theorem small_type : Small.{max (u + 1) v} (Type u) :=
  small_max.{max (u + 1) v} _

section 

open_locale Classical

theorem small_congr {α : Type _} {β : Type _} (e : α ≃ β) : Small.{w} α ↔ Small.{w} β :=
  by 
    fsplit
    ·
      rintro ⟨S, ⟨f⟩⟩
      exact Small.mk' (e.symm.trans f)
    ·
      rintro ⟨S, ⟨f⟩⟩
      exact Small.mk' (e.trans f)

instance small_subtype (α : Type v) [Small.{w} α] (P : α → Prop) : Small.{w} { x // P x } :=
  by 
    rw [small_congr (equivShrink α).subtypeEquivOfSubtype']
    infer_instance

theorem small_of_injective {α : Type _} {β : Type _} [Small.{w} β] (f : α → β) (hf : Function.Injective f) :
  Small.{w} α :=
  by 
    rw [small_congr (Equiv.ofInjective f hf)]
    infer_instance

instance (priority := 100) small_subsingleton (α : Type v) [Subsingleton α] : Small.{w} α :=
  by 
    rcases is_empty_or_nonempty α with ⟨⟩ <;> skip
    ·
      rw [small_congr (Equiv.equivPempty α)]
      apply small_self
    ·
      rw [small_congr Equiv.punitOfNonemptyOfSubsingleton]
      apply small_self 
      assumption 
      assumption

/-!
We don't define `small_of_fintype` or `small_of_encodable` in this file,
to keep imports to `logic` to a minimum.
-/


instance small_Pi {α} (β : α → Type _) [Small.{w} α] [∀ a, Small.{w} (β a)] : Small.{w} (∀ a, β a) :=
  ⟨⟨∀ a' : Shrink α, Shrink (β ((equivShrink α).symm a')),
      ⟨Equiv.piCongr (equivShrink α)
          fun a =>
            by 
              simpa using equivShrink (β a)⟩⟩⟩

instance small_sigma {α} (β : α → Type _) [Small.{w} α] [∀ a, Small.{w} (β a)] : Small.{w} (Σa, β a) :=
  ⟨⟨Σa' : Shrink α, Shrink (β ((equivShrink α).symm a')),
      ⟨Equiv.sigmaCongr (equivShrink α)
          fun a =>
            by 
              simpa using equivShrink (β a)⟩⟩⟩

instance small_prod {α β} [Small.{w} α] [Small.{w} β] : Small.{w} (α × β) :=
  ⟨⟨Shrink α × Shrink β, ⟨Equiv.prodCongr (equivShrink α) (equivShrink β)⟩⟩⟩

instance small_sum {α β} [Small.{w} α] [Small.{w} β] : Small.{w} (Sum α β) :=
  ⟨⟨Sum (Shrink α) (Shrink β), ⟨Equiv.sumCongr (equivShrink α) (equivShrink β)⟩⟩⟩

instance small_set {α} [Small.{w} α] : Small.{w} (Set α) :=
  ⟨⟨Set (Shrink α), ⟨Equiv.Set.congr (equivShrink α)⟩⟩⟩

theorem not_small_type : ¬Small.{u} (Type max u v)
| ⟨⟨S, ⟨e⟩⟩⟩ =>
  @Function.cantor_injective (Σα, e.symm α) (fun a => ⟨_, cast (e.3 _).symm a⟩)
    fun a b e => (cast_inj _).1$ eq_of_heq (Sigma.mk.inj e).2

end 

