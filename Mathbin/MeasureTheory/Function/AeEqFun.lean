import Mathbin.MeasureTheory.Integral.Lebesgue
import Mathbin.Order.Filter.Germ
import Mathbin.Topology.ContinuousFunction.Algebra

/-!

# Almost everywhere equal functions

Two measurable functions are treated as identical if they are almost everywhere equal. We form the
set of equivalence classes under the relation of being almost everywhere equal, which is sometimes
known as the `L⁰` space.

See `l1_space.lean` for `L¹` space.

## Notation

* `α →ₘ[μ] β` is the type of `L⁰` space, where `α` and `β` are measurable spaces and `μ`
  is a measure on `α`. `f : α →ₘ β` is a "function" in `L⁰`. In comments, `[f]` is also used
  to denote an `L⁰` function.

  `ₘ` can be typed as `\_m`. Sometimes it is shown as a box if font is missing.


## Main statements

* The linear structure of `L⁰` :
    Addition and scalar multiplication are defined on `L⁰` in the natural way, i.e.,
    `[f] + [g] := [f + g]`, `c • [f] := [c • f]`. So defined, `α →ₘ β` inherits the linear structure
    of `β`. For example, if `β` is a module, then `α →ₘ β` is a module over the same ring.

    See `mk_add_mk`,  `neg_mk`,     `mk_sub_mk`,  `smul_mk`,
        `add_to_fun`, `neg_to_fun`, `sub_to_fun`, `smul_to_fun`

* The order structure of `L⁰` :
    `≤` can be defined in a similar way: `[f] ≤ [g]` if `f a ≤ g a` for almost all `a` in domain.
    And `α →ₘ β` inherits the preorder and partial order of `β`.

    TODO: Define `sup` and `inf` on `L⁰` so that it forms a lattice. It seems that `β` must be a
    linear order, since otherwise `f ⊔ g` may not be a measurable function.

## Implementation notes

* `f.to_fun`     : To find a representative of `f : α →ₘ β`, use `f.to_fun`.
                 For each operation `op` in `L⁰`, there is a lemma called `op_to_fun`,
                 characterizing, say, `(f op g).to_fun`.
* `ae_eq_fun.mk` : To constructs an `L⁰` function `α →ₘ β` from a measurable function `f : α → β`,
                 use `ae_eq_fun.mk`
* `comp`         : Use `comp g f` to get `[g ∘ f]` from `g : β → γ` and `[f] : α →ₘ γ`
* `comp₂`        : Use `comp₂ g f₁ f₂ to get `[λa, g (f₁ a) (f₂ a)]`.
                 For example, `[f + g]` is `comp₂ (+)`


## Tags

function space, almost everywhere equal, `L⁰`, ae_eq_fun

-/


noncomputable section

open_locale Classical Ennreal

open Set Filter TopologicalSpace Ennreal Emetric MeasureTheory Function

variable {α β γ δ : Type _} [MeasurableSpace α] {μ ν : Measureₓ α}

namespace MeasureTheory

section MeasurableSpace

variable [MeasurableSpace β]

variable (β)

/-- The equivalence relation of being almost everywhere equal -/
def measure.ae_eq_setoid (μ : Measureₓ α) : Setoidₓ { f : α → β // AeMeasurable f μ } :=
  ⟨fun f g => (f : α → β) =ᵐ[μ] g, fun f => ae_eq_refl f, fun f g => ae_eq_symm, fun f g h => ae_eq_trans⟩

variable (α)

/-- The space of equivalence classes of measurable functions, where two measurable functions are
    equivalent if they agree almost everywhere, i.e., they differ on a set of measure `0`.  -/
def ae_eq_fun (μ : Measureₓ α) : Type _ :=
  Quotientₓ (μ.ae_eq_setoid β)

variable {α β}

notation:25 α " →ₘ[" μ "] " β => ae_eq_fun α β μ

end MeasurableSpace

namespace AeEqFun

variable [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

/-- Construct the equivalence class `[f]` of an almost everywhere measurable function `f`, based
    on the equivalence relation of being almost everywhere equal. -/
def mk (f : α → β) (hf : AeMeasurable f μ) : α →ₘ[μ] β :=
  Quotientₓ.mk' ⟨f, hf⟩

/-- A measurable representative of an `ae_eq_fun` [f] -/
instance : CoeFun (α →ₘ[μ] β) fun _ => α → β :=
  ⟨fun f => AeMeasurable.mk _ (Quotientₓ.out' f : { f : α → β // AeMeasurable f μ }).2⟩

protected theorem Measurable (f : α →ₘ[μ] β) : Measurable f :=
  AeMeasurable.measurable_mk _

protected theorem AeMeasurable (f : α →ₘ[μ] β) : AeMeasurable f μ :=
  f.measurable.ae_measurable

@[simp]
theorem quot_mk_eq_mk (f : α → β) hf : (Quot.mk (@Setoidₓ.R _ $ μ.ae_eq_setoid β) ⟨f, hf⟩ : α →ₘ[μ] β) = mk f hf :=
  rfl

@[simp]
theorem mk_eq_mk {f g : α → β} {hf hg} : (mk f hf : α →ₘ[μ] β) = mk g hg ↔ f =ᵐ[μ] g :=
  Quotientₓ.eq'

@[simp]
theorem mk_coe_fn (f : α →ₘ[μ] β) : mk f f.ae_measurable = f := by
  conv_rhs => rw [← Quotientₓ.out_eq' f]
  set g : { f : α → β // AeMeasurable f μ } := Quotientₓ.out' f with hg
  have : g = ⟨g.1, g.2⟩ := Subtype.eq rfl
  rw [this, ← mk, mk_eq_mk]
  exact (AeMeasurable.ae_eq_mk _).symm

@[ext]
theorem ext {f g : α →ₘ[μ] β} (h : f =ᵐ[μ] g) : f = g := by
  rwa [← f.mk_coe_fn, ← g.mk_coe_fn, mk_eq_mk]

theorem ext_iff {f g : α →ₘ[μ] β} : f = g ↔ f =ᵐ[μ] g :=
  ⟨fun h => by
    rw [h], fun h => ext h⟩

theorem coe_fn_mk (f : α → β) hf : (mk f hf : α →ₘ[μ] β) =ᵐ[μ] f := by
  apply (AeMeasurable.ae_eq_mk _).symm.trans
  exact @Quotientₓ.mk_out' _ (μ.ae_eq_setoid β) (⟨f, hf⟩ : { f // AeMeasurable f μ })

@[elab_as_eliminator]
theorem induction_on (f : α →ₘ[μ] β) {p : (α →ₘ[μ] β) → Prop} (H : ∀ f hf, p (mk f hf)) : p f :=
  Quotientₓ.induction_on' f $ Subtype.forall.2 H

@[elab_as_eliminator]
theorem induction_on₂ {α' β' : Type _} [MeasurableSpace α'] [MeasurableSpace β'] {μ' : Measureₓ α'} (f : α →ₘ[μ] β)
    (f' : α' →ₘ[μ'] β') {p : (α →ₘ[μ] β) → (α' →ₘ[μ'] β') → Prop} (H : ∀ f hf f' hf', p (mk f hf) (mk f' hf')) :
    p f f' :=
  induction_on f $ fun f hf => induction_on f' $ H f hf

@[elab_as_eliminator]
theorem induction_on₃ {α' β' : Type _} [MeasurableSpace α'] [MeasurableSpace β'] {μ' : Measureₓ α'} {α'' β'' : Type _}
    [MeasurableSpace α''] [MeasurableSpace β''] {μ'' : Measureₓ α''} (f : α →ₘ[μ] β) (f' : α' →ₘ[μ'] β')
    (f'' : α'' →ₘ[μ''] β'') {p : (α →ₘ[μ] β) → (α' →ₘ[μ'] β') → (α'' →ₘ[μ''] β'') → Prop}
    (H : ∀ f hf f' hf' f'' hf'', p (mk f hf) (mk f' hf') (mk f'' hf'')) : p f f' f'' :=
  induction_on f $ fun f hf => induction_on₂ f' f'' $ H f hf

/-- Given a measurable function `g : β → γ`, and an almost everywhere equal function `[f] : α →ₘ β`,
    return the equivalence class of `g ∘ f`, i.e., the almost everywhere equal function
    `[g ∘ f] : α →ₘ γ`. -/
def comp (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) : α →ₘ[μ] γ :=
  (Quotientₓ.liftOn' f fun f => mk (g ∘ (f : α → β)) (hg.comp_ae_measurable f.2)) $ fun f f' H =>
    mk_eq_mk.2 $ H.fun_comp g

@[simp]
theorem comp_mk (g : β → γ) (hg : Measurable g) (f : α → β) hf :
    comp g hg (mk f hf : α →ₘ[μ] β) = mk (g ∘ f) (hg.comp_ae_measurable hf) :=
  rfl

theorem comp_eq_mk (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) :
    comp g hg f = mk (g ∘ f) (hg.comp_ae_measurable f.ae_measurable) := by
  rw [← comp_mk g hg f f.ae_measurable, mk_coe_fn]

theorem coe_fn_comp (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) : comp g hg f =ᵐ[μ] g ∘ f := by
  rw [comp_eq_mk]
  apply coe_fn_mk

/-- The class of `x ↦ (f x, g x)`. -/
def pair (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : α →ₘ[μ] β × γ :=
  (Quotientₓ.liftOn₂' f g fun f g => mk (fun x => (f.1 x, g.1 x)) (f.2.prod_mk g.2)) $ fun f g f' g' Hf Hg =>
    mk_eq_mk.2 $ Hf.prod_mk Hg

@[simp]
theorem pair_mk_mk (f : α → β) hf (g : α → γ) hg :
    (mk f hf : α →ₘ[μ] β).pair (mk g hg) = mk (fun x => (f x, g x)) (hf.prod_mk hg) :=
  rfl

theorem pair_eq_mk (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) :
    f.pair g = mk (fun x => (f x, g x)) (f.ae_measurable.prod_mk g.ae_measurable) := by
  simp only [← pair_mk_mk, mk_coe_fn]

theorem coe_fn_pair (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : f.pair g =ᵐ[μ] fun x => (f x, g x) := by
  rw [pair_eq_mk]
  apply coe_fn_mk

/-- Given a measurable function `g : β → γ → δ`, and almost everywhere equal functions
    `[f₁] : α →ₘ β` and `[f₂] : α →ₘ γ`, return the equivalence class of the function
    `λa, g (f₁ a) (f₂ a)`, i.e., the almost everywhere equal function
    `[λa, g (f₁ a) (f₂ a)] : α →ₘ γ` -/
def comp₂ {γ δ : Type _} [MeasurableSpace γ] [MeasurableSpace δ] (g : β → γ → δ) (hg : Measurable (uncurry g))
    (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) : α →ₘ[μ] δ :=
  comp _ hg (f₁.pair f₂)

@[simp]
theorem comp₂_mk_mk {γ δ : Type _} [MeasurableSpace γ] [MeasurableSpace δ] (g : β → γ → δ) (hg : Measurable (uncurry g))
    (f₁ : α → β) (f₂ : α → γ) hf₁ hf₂ :
    comp₂ g hg (mk f₁ hf₁ : α →ₘ[μ] β) (mk f₂ hf₂) =
      mk (fun a => g (f₁ a) (f₂ a)) (hg.comp_ae_measurable (hf₁.prod_mk hf₂)) :=
  rfl

theorem comp₂_eq_pair {γ δ : Type _} [MeasurableSpace γ] [MeasurableSpace δ] (g : β → γ → δ)
    (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) : comp₂ g hg f₁ f₂ = comp _ hg (f₁.pair f₂) :=
  rfl

theorem comp₂_eq_mk {γ δ : Type _} [MeasurableSpace γ] [MeasurableSpace δ] (g : β → γ → δ) (hg : Measurable (uncurry g))
    (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
    comp₂ g hg f₁ f₂ =
      mk (fun a => g (f₁ a) (f₂ a)) (hg.comp_ae_measurable (f₁.ae_measurable.prod_mk f₂.ae_measurable)) :=
  by
  rw [comp₂_eq_pair, pair_eq_mk, comp_mk] <;> rfl

theorem coe_fn_comp₂ {γ δ : Type _} [MeasurableSpace γ] [MeasurableSpace δ] (g : β → γ → δ)
    (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) : comp₂ g hg f₁ f₂ =ᵐ[μ] fun a => g (f₁ a) (f₂ a) :=
  by
  rw [comp₂_eq_mk]
  apply coe_fn_mk

/-- Interpret `f : α →ₘ[μ] β` as a germ at `μ.ae` forgetting that `f` is almost everywhere
    measurable. -/
def to_germ (f : α →ₘ[μ] β) : germ μ.ae β :=
  (Quotientₓ.liftOn' f fun f => ((f : α → β) : germ μ.ae β)) $ fun f g H => germ.coe_eq.2 H

@[simp]
theorem mk_to_germ (f : α → β) hf : (mk f hf : α →ₘ[μ] β).toGerm = f :=
  rfl

theorem to_germ_eq (f : α →ₘ[μ] β) : f.to_germ = (f : α → β) := by
  rw [← mk_to_germ, mk_coe_fn]

theorem to_germ_injective : injective (to_germ : (α →ₘ[μ] β) → germ μ.ae β) := fun f g H =>
  ext $
    germ.coe_eq.1 $ by
      rwa [← to_germ_eq, ← to_germ_eq]

theorem comp_to_germ (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) : (comp g hg f).toGerm = f.to_germ.map g :=
  induction_on f $ fun f hf => by
    simp

theorem comp₂_to_germ (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
    (comp₂ g hg f₁ f₂).toGerm = f₁.to_germ.map₂ g f₂.to_germ :=
  induction_on₂ f₁ f₂ $ fun f₁ hf₁ f₂ hf₂ => by
    simp

/-- Given a predicate `p` and an equivalence class `[f]`, return true if `p` holds of `f a`
    for almost all `a` -/
def lift_pred (p : β → Prop) (f : α →ₘ[μ] β) : Prop :=
  f.to_germ.lift_pred p

/-- Given a relation `r` and equivalence class `[f]` and `[g]`, return true if `r` holds of
    `(f a, g a)` for almost all `a` -/
def lift_rel (r : β → γ → Prop) (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : Prop :=
  f.to_germ.lift_rel r g.to_germ

theorem lift_rel_mk_mk {r : β → γ → Prop} {f : α → β} {g : α → γ} {hf hg} :
    lift_rel r (mk f hf : α →ₘ[μ] β) (mk g hg) ↔ ∀ᵐ a ∂μ, r (f a) (g a) :=
  Iff.rfl

theorem lift_rel_iff_coe_fn {r : β → γ → Prop} {f : α →ₘ[μ] β} {g : α →ₘ[μ] γ} :
    lift_rel r f g ↔ ∀ᵐ a ∂μ, r (f a) (g a) := by
  rw [← lift_rel_mk_mk, mk_coe_fn, mk_coe_fn]

section Order

instance [Preorderₓ β] : Preorderₓ (α →ₘ[μ] β) :=
  Preorderₓ.lift to_germ

@[simp]
theorem mk_le_mk [Preorderₓ β] {f g : α → β} hf hg : (mk f hf : α →ₘ[μ] β) ≤ mk g hg ↔ f ≤ᵐ[μ] g :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_fn_le [Preorderₓ β] {f g : α →ₘ[μ] β} : (f : α → β) ≤ᵐ[μ] g ↔ f ≤ g :=
  lift_rel_iff_coe_fn.symm

instance [PartialOrderₓ β] : PartialOrderₓ (α →ₘ[μ] β) :=
  PartialOrderₓ.lift to_germ to_germ_injective

section Lattice

section Sup

variable [SemilatticeSup β] [HasMeasurableSup₂ β]

instance : HasSup (α →ₘ[μ] β) where
  sup := fun f g => ae_eq_fun.comp₂ (·⊔·) measurable_sup f g

theorem coe_fn_sup (f g : α →ₘ[μ] β) : ⇑(f⊔g) =ᵐ[μ] fun x => f x⊔g x :=
  coe_fn_comp₂ _ _ _ _

protected theorem le_sup_left (f g : α →ₘ[μ] β) : f ≤ f⊔g := by
  rw [← coe_fn_le]
  filter_upwards [coe_fn_sup f g]
  intro a ha
  rw [ha]
  exact le_sup_left

protected theorem le_sup_right (f g : α →ₘ[μ] β) : g ≤ f⊔g := by
  rw [← coe_fn_le]
  filter_upwards [coe_fn_sup f g]
  intro a ha
  rw [ha]
  exact le_sup_right

protected theorem sup_le (f g f' : α →ₘ[μ] β) (hf : f ≤ f') (hg : g ≤ f') : f⊔g ≤ f' := by
  rw [← coe_fn_le] at hf hg⊢
  filter_upwards [hf, hg, coe_fn_sup f g]
  intro a haf hag ha_sup
  rw [ha_sup]
  exact sup_le haf hag

end Sup

section Inf

variable [SemilatticeInf β] [HasMeasurableInf₂ β]

instance : HasInf (α →ₘ[μ] β) where
  inf := fun f g => ae_eq_fun.comp₂ (·⊓·) measurable_inf f g

theorem coe_fn_inf (f g : α →ₘ[μ] β) : ⇑(f⊓g) =ᵐ[μ] fun x => f x⊓g x :=
  coe_fn_comp₂ _ _ _ _

protected theorem inf_le_left (f g : α →ₘ[μ] β) : f⊓g ≤ f := by
  rw [← coe_fn_le]
  filter_upwards [coe_fn_inf f g]
  intro a ha
  rw [ha]
  exact inf_le_left

protected theorem inf_le_right (f g : α →ₘ[μ] β) : f⊓g ≤ g := by
  rw [← coe_fn_le]
  filter_upwards [coe_fn_inf f g]
  intro a ha
  rw [ha]
  exact inf_le_right

protected theorem le_inf (f' f g : α →ₘ[μ] β) (hf : f' ≤ f) (hg : f' ≤ g) : f' ≤ f⊓g := by
  rw [← coe_fn_le] at hf hg⊢
  filter_upwards [hf, hg, coe_fn_inf f g]
  intro a haf hag ha_inf
  rw [ha_inf]
  exact le_inf haf hag

end Inf

instance [Lattice β] [HasMeasurableSup₂ β] [HasMeasurableInf₂ β] : Lattice (α →ₘ[μ] β) :=
  { ae_eq_fun.partial_order with sup := HasSup.sup, le_sup_left := ae_eq_fun.le_sup_left,
    le_sup_right := ae_eq_fun.le_sup_right, sup_le := ae_eq_fun.sup_le, inf := HasInf.inf,
    inf_le_left := ae_eq_fun.inf_le_left, inf_le_right := ae_eq_fun.inf_le_right, le_inf := ae_eq_fun.le_inf }

end Lattice

end Order

variable (α)

/-- The equivalence class of a constant function: `[λa:α, b]`, based on the equivalence relation of
    being almost everywhere equal -/
def const (b : β) : α →ₘ[μ] β :=
  mk (fun a : α => b) ae_measurable_const

theorem coe_fn_const (b : β) : (const α b : α →ₘ[μ] β) =ᵐ[μ] Function.const α b :=
  coe_fn_mk _ _

variable {α}

instance [Inhabited β] : Inhabited (α →ₘ[μ] β) :=
  ⟨const α (default β)⟩

@[to_additive]
instance [HasOne β] : HasOne (α →ₘ[μ] β) :=
  ⟨const α 1⟩

@[to_additive]
theorem one_def [HasOne β] : (1 : α →ₘ[μ] β) = mk (fun a : α => 1) ae_measurable_const :=
  rfl

@[to_additive]
theorem coe_fn_one [HasOne β] : ⇑(1 : α →ₘ[μ] β) =ᵐ[μ] 1 :=
  coe_fn_const _ _

@[simp, to_additive]
theorem one_to_germ [HasOne β] : (1 : α →ₘ[μ] β).toGerm = 1 :=
  rfl

section Monoidₓ

variable [TopologicalSpace γ] [second_countable_topology γ] [BorelSpace γ] [Monoidₓ γ] [HasContinuousMul γ]

@[to_additive]
instance : Mul (α →ₘ[μ] γ) :=
  ⟨comp₂ (· * ·) measurable_mul⟩

@[simp, to_additive]
theorem mk_mul_mk (f g : α → γ) hf hg : (mk f hf : α →ₘ[μ] γ) * mk g hg = mk (f * g) (hf.mul hg) :=
  rfl

@[to_additive]
theorem coe_fn_mul (f g : α →ₘ[μ] γ) : ⇑(f * g) =ᵐ[μ] f * g :=
  coe_fn_comp₂ _ _ _ _

@[simp, to_additive]
theorem mul_to_germ (f g : α →ₘ[μ] γ) : (f * g).toGerm = f.to_germ * g.to_germ :=
  comp₂_to_germ _ _ _ _

@[to_additive]
instance : Monoidₓ (α →ₘ[μ] γ) :=
  to_germ_injective.Monoid to_germ one_to_germ mul_to_germ

end Monoidₓ

@[to_additive]
instance CommMonoidₓ [TopologicalSpace γ] [second_countable_topology γ] [BorelSpace γ] [CommMonoidₓ γ]
    [HasContinuousMul γ] : CommMonoidₓ (α →ₘ[μ] γ) :=
  to_germ_injective.CommMonoid to_germ one_to_germ mul_to_germ

section Groupₓ

variable [TopologicalSpace γ] [BorelSpace γ] [Groupₓ γ] [TopologicalGroup γ]

@[to_additive]
instance : HasInv (α →ₘ[μ] γ) :=
  ⟨comp HasInv.inv measurable_inv⟩

@[simp, to_additive]
theorem inv_mk (f : α → γ) hf : (mk f hf : α →ₘ[μ] γ)⁻¹ = mk (f⁻¹) hf.inv :=
  rfl

@[to_additive]
theorem coe_fn_inv (f : α →ₘ[μ] γ) : ⇑f⁻¹ =ᵐ[μ] f⁻¹ :=
  coe_fn_comp _ _ _

@[to_additive]
theorem inv_to_germ (f : α →ₘ[μ] γ) : f⁻¹.toGerm = f.to_germ⁻¹ :=
  comp_to_germ _ _ _

variable [second_countable_topology γ]

@[to_additive]
instance : Div (α →ₘ[μ] γ) :=
  ⟨comp₂ Div.div measurable_div⟩

@[simp, to_additive]
theorem mk_div (f g : α → γ) hf hg : mk (f / g) (AeMeasurable.div hf hg) = (mk f hf : α →ₘ[μ] γ) / mk g hg :=
  rfl

@[to_additive]
theorem coe_fn_div (f g : α →ₘ[μ] γ) : ⇑(f / g) =ᵐ[μ] f / g :=
  coe_fn_comp₂ _ _ _ _

@[to_additive]
theorem div_to_germ (f g : α →ₘ[μ] γ) : (f / g).toGerm = f.to_germ / g.to_germ :=
  comp₂_to_germ _ _ _ _

@[to_additive]
instance : Groupₓ (α →ₘ[μ] γ) :=
  to_germ_injective.Group _ one_to_germ mul_to_germ inv_to_germ div_to_germ

end Groupₓ

@[to_additive]
instance [TopologicalSpace γ] [BorelSpace γ] [CommGroupₓ γ] [TopologicalGroup γ] [second_countable_topology γ] :
    CommGroupₓ (α →ₘ[μ] γ) :=
  { ae_eq_fun.group, ae_eq_fun.comm_monoid with }

section Module

variable {𝕜 : Type _} [Semiringₓ 𝕜] [TopologicalSpace 𝕜] [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜]

variable [TopologicalSpace γ] [BorelSpace γ] [AddCommMonoidₓ γ] [Module 𝕜 γ] [HasContinuousSmul 𝕜 γ]

instance : HasScalar 𝕜 (α →ₘ[μ] γ) :=
  ⟨fun c f => comp ((· • ·) c) (measurable_id.const_smul c) f⟩

@[simp]
theorem smul_mk (c : 𝕜) (f : α → γ) hf : c • (mk f hf : α →ₘ[μ] γ) = mk (c • f) (hf.const_smul _) :=
  rfl

theorem coe_fn_smul (c : 𝕜) (f : α →ₘ[μ] γ) : ⇑(c • f) =ᵐ[μ] c • f :=
  coe_fn_comp _ _ _

theorem smul_to_germ (c : 𝕜) (f : α →ₘ[μ] γ) : (c • f).toGerm = c • f.to_germ :=
  comp_to_germ _ _ _

variable [second_countable_topology γ] [HasContinuousAdd γ]

instance : Module 𝕜 (α →ₘ[μ] γ) :=
  to_germ_injective.Module 𝕜 ⟨@to_germ α γ _ μ _, zero_to_germ, add_to_germ⟩ smul_to_germ

end Module

open Ennreal

/-- For `f : α → ℝ≥0∞`, define `∫ [f]` to be `∫ f` -/
def lintegral (f : α →ₘ[μ] ℝ≥0∞) : ℝ≥0∞ :=
  Quotientₓ.liftOn' f (fun f => ∫⁻ a, (f : α → ℝ≥0∞) a ∂μ) fun f g => lintegral_congr_ae

@[simp]
theorem lintegral_mk (f : α → ℝ≥0∞) hf : (mk f hf : α →ₘ[μ] ℝ≥0∞).lintegral = ∫⁻ a, f a ∂μ :=
  rfl

theorem lintegral_coe_fn (f : α →ₘ[μ] ℝ≥0∞) : (∫⁻ a, f a ∂μ) = f.lintegral := by
  rw [← lintegral_mk, mk_coe_fn]

@[simp]
theorem lintegral_zero : lintegral (0 : α →ₘ[μ] ℝ≥0∞) = 0 :=
  lintegral_zero

@[simp]
theorem lintegral_eq_zero_iff {f : α →ₘ[μ] ℝ≥0∞} : lintegral f = 0 ↔ f = 0 :=
  induction_on f $ fun f hf => (lintegral_eq_zero_iff' hf).trans mk_eq_mk.symm

theorem lintegral_add (f g : α →ₘ[μ] ℝ≥0∞) : lintegral (f + g) = lintegral f + lintegral g :=
  induction_on₂ f g $ fun f hf g hg => by
    simp [lintegral_add' hf hg]

theorem lintegral_mono {f g : α →ₘ[μ] ℝ≥0∞} : f ≤ g → lintegral f ≤ lintegral g :=
  induction_on₂ f g $ fun f hf g hg hfg => lintegral_mono_ae hfg

section PosPart

variable [TopologicalSpace γ] [LinearOrderₓ γ] [OrderClosedTopology γ] [second_countable_topology γ] [HasZero γ]
  [OpensMeasurableSpace γ]

/-- Positive part of an `ae_eq_fun`. -/
def pos_part (f : α →ₘ[μ] γ) : α →ₘ[μ] γ :=
  comp (fun x => max x 0) (measurable_id.max measurable_const) f

@[simp]
theorem pos_part_mk (f : α → γ) hf :
    pos_part (mk f hf : α →ₘ[μ] γ) = mk (fun x => max (f x) 0) (hf.max ae_measurable_const) :=
  rfl

theorem coe_fn_pos_part (f : α →ₘ[μ] γ) : ⇑pos_part f =ᵐ[μ] fun a => max (f a) 0 :=
  coe_fn_comp _ _ _

end PosPart

end AeEqFun

end MeasureTheory

namespace ContinuousMap

open MeasureTheory

variable [TopologicalSpace α] [BorelSpace α] (μ)

variable [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]

/-- The equivalence class of `μ`-almost-everywhere measurable functions associated to a continuous
map. -/
def to_ae_eq_fun (f : C(α, β)) : α →ₘ[μ] β :=
  ae_eq_fun.mk f f.continuous.measurable.ae_measurable

theorem coe_fn_to_ae_eq_fun (f : C(α, β)) : f.to_ae_eq_fun μ =ᵐ[μ] f :=
  ae_eq_fun.coe_fn_mk f _

variable [Groupₓ β] [TopologicalGroup β] [second_countable_topology β]

/-- The `mul_hom` from the group of continuous maps from `α` to `β` to the group of equivalence
classes of `μ`-almost-everywhere measurable functions. -/
@[to_additive
      "The `add_hom` from the group of continuous maps from `α` to `β` to the group of\nequivalence classes of `μ`-almost-everywhere measurable functions."]
def to_ae_eq_fun_mul_hom : C(α, β) →* α →ₘ[μ] β where
  toFun := ContinuousMap.toAeEqFun μ
  map_one' := rfl
  map_mul' := fun f g =>
    ae_eq_fun.mk_mul_mk f g f.continuous.measurable.ae_measurable g.continuous.measurable.ae_measurable

variable {𝕜 : Type _} [Semiringₓ 𝕜] [TopologicalSpace 𝕜] [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜]

variable [TopologicalSpace γ] [MeasurableSpace γ] [BorelSpace γ] [AddCommGroupₓ γ] [Module 𝕜 γ] [TopologicalAddGroup γ]
  [HasContinuousSmul 𝕜 γ] [second_countable_topology γ]

/-- The linear map from the group of continuous maps from `α` to `β` to the group of equivalence
classes of `μ`-almost-everywhere measurable functions. -/
def to_ae_eq_fun_linear_map : C(α, γ) →ₗ[𝕜] α →ₘ[μ] γ :=
  { to_ae_eq_fun_add_hom μ with map_smul' := fun c f => ae_eq_fun.smul_mk c f f.continuous.measurable.ae_measurable }

end ContinuousMap

