import Mathbin.Topology.SubsetProperties 
import Mathbin.Topology.Connected 
import Mathbin.Topology.Algebra.Monoid 
import Mathbin.Topology.ContinuousFunction.Basic 
import Mathbin.Tactic.Tfae 
import Mathbin.Tactic.FinCases

/-!
# Locally constant functions

This file sets up the theory of locally constant function from a topological space to a type.

## Main definitions and constructions

* `is_locally_constant f` : a map `f : X → Y` where `X` is a topological space is locally
                            constant if every set in `Y` has an open preimage.
* `locally_constant X Y` : the type of locally constant maps from `X` to `Y`
* `locally_constant.map` : push-forward of locally constant maps
* `locally_constant.comap` : pull-back of locally constant maps

-/


variable{X Y Z α : Type _}[TopologicalSpace X]

open Set Filter

open_locale TopologicalSpace

/-- A function between topological spaces is locally constant if the preimage of any set is open. -/
def IsLocallyConstant (f : X → Y) : Prop :=
  ∀ (s : Set Y), IsOpen (f ⁻¹' s)

namespace IsLocallyConstant

protected theorem tfae (f : X → Y) :
  tfae
    [IsLocallyConstant f, ∀ x, ∀ᶠx' in 𝓝 x, f x' = f x, ∀ x, IsOpen { x' | f x' = f x }, ∀ y, IsOpen (f ⁻¹' {y}),
      ∀ x, ∃ (U : Set X)(hU : IsOpen U)(hx : x ∈ U), ∀ x' (_ : x' ∈ U), f x' = f x] :=
  by 
    tfaeHave 1 → 4 
    exact fun h y => h {y}
    tfaeHave 4 → 3 
    exact fun h x => h (f x)
    tfaeHave 3 → 2 
    exact fun h x => IsOpen.mem_nhds (h x) rfl 
    tfaeHave 2 → 5
    ·
      intro h x 
      rcases mem_nhds_iff.1 (h x) with ⟨U, eq, hU, hx⟩
      exact ⟨U, hU, hx, Eq⟩
    tfaeHave 5 → 1
    ·
      intro h s 
      refine' is_open_iff_forall_mem_open.2 fun x hx => _ 
      rcases h x with ⟨U, hU, hxU, eq⟩
      exact ⟨U, fun x' hx' => mem_preimage.2$ (Eq x' hx').symm ▸ hx, hU, hxU⟩
    tfaeFinish

@[nontriviality]
theorem of_discrete [DiscreteTopology X] (f : X → Y) : IsLocallyConstant f :=
  fun s => is_open_discrete _

theorem is_open_fiber {f : X → Y} (hf : IsLocallyConstant f) (y : Y) : IsOpen { x | f x = y } :=
  hf {y}

theorem is_closed_fiber {f : X → Y} (hf : IsLocallyConstant f) (y : Y) : IsClosed { x | f x = y } :=
  ⟨hf («expr ᶜ» {y})⟩

theorem is_clopen_fiber {f : X → Y} (hf : IsLocallyConstant f) (y : Y) : IsClopen { x | f x = y } :=
  ⟨is_open_fiber hf _, is_closed_fiber hf _⟩

theorem iff_exists_open (f : X → Y) :
  IsLocallyConstant f ↔ ∀ x, ∃ (U : Set X)(hU : IsOpen U)(hx : x ∈ U), ∀ x' (_ : x' ∈ U), f x' = f x :=
  (IsLocallyConstant.tfae f).out 0 4

theorem iff_eventually_eq (f : X → Y) : IsLocallyConstant f ↔ ∀ x, ∀ᶠy in 𝓝 x, f y = f x :=
  (IsLocallyConstant.tfae f).out 0 1

theorem exists_open {f : X → Y} (hf : IsLocallyConstant f) (x : X) :
  ∃ (U : Set X)(hU : IsOpen U)(hx : x ∈ U), ∀ x' (_ : x' ∈ U), f x' = f x :=
  (iff_exists_open f).1 hf x

protected theorem eventually_eq {f : X → Y} (hf : IsLocallyConstant f) (x : X) : ∀ᶠy in 𝓝 x, f y = f x :=
  (iff_eventually_eq f).1 hf x

protected theorem Continuous [TopologicalSpace Y] {f : X → Y} (hf : IsLocallyConstant f) : Continuous f :=
  ⟨fun U hU => hf _⟩

theorem iff_continuous {_ : TopologicalSpace Y} [DiscreteTopology Y] (f : X → Y) : IsLocallyConstant f ↔ Continuous f :=
  ⟨IsLocallyConstant.continuous, fun h s => h.is_open_preimage s (is_open_discrete _)⟩

theorem iff_continuous_bot (f : X → Y) : IsLocallyConstant f ↔ @Continuous X Y _ ⊥ f :=
  iff_continuous f

theorem of_constant (f : X → Y) (h : ∀ x y, f x = f y) : IsLocallyConstant f :=
  (iff_eventually_eq f).2$ fun x => eventually_of_forall$ fun x' => h _ _

theorem const (y : Y) : IsLocallyConstant (Function.const X y) :=
  of_constant _$ fun _ _ => rfl

theorem comp {f : X → Y} (hf : IsLocallyConstant f) (g : Y → Z) : IsLocallyConstant (g ∘ f) :=
  fun s =>
    by 
      rw [Set.preimage_comp]
      exact hf _

theorem prod_mk {Y'} {f : X → Y} {f' : X → Y'} (hf : IsLocallyConstant f) (hf' : IsLocallyConstant f') :
  IsLocallyConstant fun x => (f x, f' x) :=
  (iff_eventually_eq _).2$
    fun x => (hf.eventually_eq x).mp$ (hf'.eventually_eq x).mono$ fun x' hf' hf => Prod.extₓ hf hf'

-- error in Topology.LocallyConstant.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem comp₂
{Y₁ Y₂ Z : Type*}
{f : X → Y₁}
{g : X → Y₂}
(hf : is_locally_constant f)
(hg : is_locally_constant g)
(h : Y₁ → Y₂ → Z) : is_locally_constant (λ x, h (f x) (g x)) :=
(hf.prod_mk hg).comp (λ x : «expr × »(Y₁, Y₂), h x.1 x.2)

theorem comp_continuous [TopologicalSpace Y] {g : Y → Z} {f : X → Y} (hg : IsLocallyConstant g) (hf : Continuous f) :
  IsLocallyConstant (g ∘ f) :=
  fun s =>
    by 
      rw [Set.preimage_comp]
      exact hf.is_open_preimage _ (hg _)

/-- A locally constant function is constant on any preconnected set. -/
theorem apply_eq_of_is_preconnected {f : X → Y} (hf : IsLocallyConstant f) {s : Set X} (hs : IsPreconnected s) {x y : X}
  (hx : x ∈ s) (hy : y ∈ s) : f x = f y :=
  by 
    let U := f ⁻¹' {f y}
    suffices  : x ∉ «expr ᶜ» U 
    exact not_not.1 this 
    intro hxV 
    specialize hs U («expr ᶜ» U) (hf {f y}) (hf («expr ᶜ» {f y})) _ ⟨y, ⟨hy, rfl⟩⟩ ⟨x, ⟨hx, hxV⟩⟩
    ·
      simp only [union_compl_self, subset_univ]
    ·
      simpa only [inter_empty, not_nonempty_empty, inter_compl_self] using hs

theorem iff_is_const [PreconnectedSpace X] {f : X → Y} : IsLocallyConstant f ↔ ∀ x y, f x = f y :=
  ⟨fun h x y => h.apply_eq_of_is_preconnected is_preconnected_univ trivialₓ trivialₓ, of_constant _⟩

-- error in Topology.LocallyConstant.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem range_finite [compact_space X] {f : X → Y} (hf : is_locally_constant f) : (set.range f).finite :=
begin
  letI [] [":", expr topological_space Y] [":=", expr «expr⊥»()],
  haveI [] [":", expr discrete_topology Y] [":=", expr ⟨rfl⟩],
  rw [expr @iff_continuous X Y «expr‹ ›»(_) «expr‹ ›»(_)] ["at", ident hf],
  exact [expr finite_of_is_compact_of_discrete _ (is_compact_range hf)]
end

@[toAdditive]
theorem one [HasOne Y] : IsLocallyConstant (1 : X → Y) :=
  const 1

@[toAdditive]
theorem inv [HasInv Y] ⦃f : X → Y⦄ (hf : IsLocallyConstant f) : IsLocallyConstant (f⁻¹) :=
  hf.comp fun x => x⁻¹

@[toAdditive]
theorem mul [Mul Y] ⦃f g : X → Y⦄ (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) : IsLocallyConstant (f*g) :=
  hf.comp₂ hg (·*·)

@[toAdditive]
theorem div [Div Y] ⦃f g : X → Y⦄ (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) : IsLocallyConstant (f / g) :=
  hf.comp₂ hg (· / ·)

-- error in Topology.LocallyConstant.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a composition of a function `f` followed by an injection `g` is locally
constant, then the locally constant property descends to `f`. -/
theorem desc
{α β : Type*}
(f : X → α)
(g : α → β)
(h : is_locally_constant «expr ∘ »(g, f))
(inj : function.injective g) : is_locally_constant f :=
begin
  rw [expr (is_locally_constant.tfae f).out 0 3] [],
  intros [ident a],
  have [] [":", expr «expr = »(«expr ⁻¹' »(f, {a}), «expr ⁻¹' »(«expr ∘ »(g, f), {g a}))] [],
  { ext [] [ident x] [],
    simp [] [] ["only"] ["[", expr mem_singleton_iff, ",", expr function.comp_app, ",", expr mem_preimage, "]"] [] [],
    exact [expr ⟨λ h, by rw [expr h] [], λ h, inj h⟩] },
  rw [expr this] [],
  apply [expr h]
end

end IsLocallyConstant

/-- A (bundled) locally constant function from a topological space `X` to a type `Y`. -/
structure LocallyConstant(X Y : Type _)[TopologicalSpace X] where 
  toFun : X → Y 
  IsLocallyConstant : IsLocallyConstant to_fun

namespace LocallyConstant

instance  [Inhabited Y] : Inhabited (LocallyConstant X Y) :=
  ⟨⟨_, IsLocallyConstant.const (default Y)⟩⟩

instance  : CoeFun (LocallyConstant X Y) fun _ => X → Y :=
  ⟨LocallyConstant.toFun⟩

initialize_simps_projections LocallyConstant (toFun → apply)

@[simp]
theorem to_fun_eq_coe (f : LocallyConstant X Y) : f.to_fun = f :=
  rfl

@[simp]
theorem coe_mk (f : X → Y) h : «expr⇑ » (⟨f, h⟩ : LocallyConstant X Y) = f :=
  rfl

-- error in Topology.LocallyConstant.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem congr_fun {f g : locally_constant X Y} (h : «expr = »(f, g)) (x : X) : «expr = »(f x, g x) :=
congr_arg (λ h : locally_constant X Y, h x) h

-- error in Topology.LocallyConstant.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem congr_arg (f : locally_constant X Y) {x y : X} (h : «expr = »(x, y)) : «expr = »(f x, f y) :=
congr_arg (λ x : X, f x) h

theorem coe_injective : @Function.Injective (LocallyConstant X Y) (X → Y) coeFn
| ⟨f, hf⟩, ⟨g, hg⟩, h =>
  have  : f = g := h 
  by 
    subst f

@[simp, normCast]
theorem coe_inj {f g : LocallyConstant X Y} : (f : X → Y) = g ↔ f = g :=
  coe_injective.eq_iff

@[ext]
theorem ext ⦃f g : LocallyConstant X Y⦄ (h : ∀ x, f x = g x) : f = g :=
  coe_injective (funext h)

theorem ext_iff {f g : LocallyConstant X Y} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => ext h⟩

section CodomainTopologicalSpace

variable[TopologicalSpace Y](f : LocallyConstant X Y)

protected theorem Continuous : Continuous f :=
  f.is_locally_constant.continuous

/-- We can turn a locally-constant function into a bundled `continuous_map`. -/
def to_continuous_map : C(X, Y) :=
  ⟨f, f.continuous⟩

/-- As a shorthand, `locally_constant.to_continuous_map` is available as a coercion -/
instance  : Coe (LocallyConstant X Y) C(X, Y) :=
  ⟨to_continuous_map⟩

@[simp]
theorem to_continuous_map_eq_coe : f.to_continuous_map = f :=
  rfl

@[simp]
theorem coe_continuous_map : ((f : C(X, Y)) : X → Y) = (f : X → Y) :=
  rfl

theorem to_continuous_map_injective : Function.Injective (to_continuous_map : LocallyConstant X Y → C(X, Y)) :=
  fun _ _ h => ext (ContinuousMap.congr_fun h)

end CodomainTopologicalSpace

/-- The constant locally constant function on `X` with value `y : Y`. -/
def const (X : Type _) {Y : Type _} [TopologicalSpace X] (y : Y) : LocallyConstant X Y :=
  ⟨Function.const X y, IsLocallyConstant.const _⟩

@[simp]
theorem coe_const (y : Y) : (const X y : X → Y) = Function.const X y :=
  rfl

/-- The locally constant function to `fin 2` associated to a clopen set. -/
def of_clopen {X : Type _} [TopologicalSpace X] {U : Set X} [∀ x, Decidable (x ∈ U)] (hU : IsClopen U) :
  LocallyConstant X (Finₓ 2) :=
  { toFun := fun x => if x ∈ U then 0 else 1,
    IsLocallyConstant :=
      by 
        rw [(IsLocallyConstant.tfae fun x => if x ∈ U then (0 : Finₓ 2) else 1).out 0 3]
        intro e 
        finCases e
        ·
          convert hU.1 using 1 
          ext 
          simp only [Nat.one_ne_zero, mem_singleton_iff, Finₓ.one_eq_zero_iff, mem_preimage, ite_eq_left_iff]
          tauto
        ·
          rw [←is_closed_compl_iff]
          convert hU.2 
          ext 
          simp  }

@[simp]
theorem of_clopen_fiber_zero {X : Type _} [TopologicalSpace X] {U : Set X} [∀ x, Decidable (x ∈ U)] (hU : IsClopen U) :
  of_clopen hU ⁻¹' ({0} : Set (Finₓ 2)) = U :=
  by 
    ext 
    simp only [of_clopen, Nat.one_ne_zero, mem_singleton_iff, Finₓ.one_eq_zero_iff, coe_mk, mem_preimage,
      ite_eq_left_iff]
    tauto

@[simp]
theorem of_clopen_fiber_one {X : Type _} [TopologicalSpace X] {U : Set X} [∀ x, Decidable (x ∈ U)] (hU : IsClopen U) :
  of_clopen hU ⁻¹' ({1} : Set (Finₓ 2)) = «expr ᶜ» U :=
  by 
    ext 
    simp only [of_clopen, Nat.one_ne_zero, mem_singleton_iff, coe_mk, Finₓ.zero_eq_one_iff, mem_preimage,
      ite_eq_right_iff, mem_compl_eq]
    tauto

-- error in Topology.LocallyConstant.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem locally_constant_eq_of_fiber_zero_eq
{X : Type*}
[topological_space X]
(f g : locally_constant X (fin 2))
(h : «expr = »(«expr ⁻¹' »(f, ({0} : set (fin 2))), «expr ⁻¹' »(g, {0}))) : «expr = »(f, g) :=
begin
  simp [] [] ["only"] ["[", expr set.ext_iff, ",", expr mem_singleton_iff, ",", expr mem_preimage, "]"] [] ["at", ident h],
  ext1 [] [ident x],
  have [] [] [":=", expr h x],
  set [] [ident a] [] [":="] [expr f x] [],
  set [] [ident b] [] [":="] [expr g x] [],
  fin_cases [ident a] []; fin_cases [ident b] []; finish [] []
end

theorem range_finite [CompactSpace X] (f : LocallyConstant X Y) : (Set.Range f).Finite :=
  f.is_locally_constant.range_finite

theorem apply_eq_of_is_preconnected (f : LocallyConstant X Y) {s : Set X} (hs : IsPreconnected s) {x y : X} (hx : x ∈ s)
  (hy : y ∈ s) : f x = f y :=
  f.is_locally_constant.apply_eq_of_is_preconnected hs hx hy

theorem apply_eq_of_preconnected_space [PreconnectedSpace X] (f : LocallyConstant X Y) (x y : X) : f x = f y :=
  f.is_locally_constant.apply_eq_of_is_preconnected is_preconnected_univ trivialₓ trivialₓ

theorem eq_const [PreconnectedSpace X] (f : LocallyConstant X Y) (x : X) : f = const X (f x) :=
  ext$ fun y => apply_eq_of_preconnected_space f _ _

theorem exists_eq_const [PreconnectedSpace X] [Nonempty Y] (f : LocallyConstant X Y) : ∃ y, f = const X y :=
  by 
    rcases Classical.em (Nonempty X) with (⟨⟨x⟩⟩ | hX)
    ·
      exact ⟨f x, f.eq_const x⟩
    ·
      exact ⟨Classical.arbitrary Y, ext$ fun x => (hX ⟨x⟩).elim⟩

/-- Push forward of locally constant maps under any map, by post-composition. -/
def map (f : Y → Z) : LocallyConstant X Y → LocallyConstant X Z :=
  fun g =>
    ⟨f ∘ g,
      fun s =>
        by 
          rw [Set.preimage_comp]
          apply g.is_locally_constant⟩

@[simp]
theorem map_apply (f : Y → Z) (g : LocallyConstant X Y) : «expr⇑ » (map f g) = (f ∘ g) :=
  rfl

@[simp]
theorem map_id : @map X Y Y _ id = id :=
  by 
    ext 
    rfl

@[simp]
theorem map_comp {Y₁ Y₂ Y₃ : Type _} (g : Y₂ → Y₃) (f : Y₁ → Y₂) : (@map X _ _ _ g ∘ map f) = map (g ∘ f) :=
  by 
    ext 
    rfl

/-- Given a locally constant function to `α → β`, construct a family of locally constant
functions with values in β indexed by α. -/
def flip {X α β : Type _} [TopologicalSpace X] (f : LocallyConstant X (α → β)) (a : α) : LocallyConstant X β :=
  f.map fun f => f a

-- error in Topology.LocallyConstant.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If α is finite, this constructs a locally constant function to `α → β` given a
family of locally constant functions with values in β indexed by α. -/
def unflip
{X α β : Type*}
[fintype α]
[topological_space X]
(f : α → locally_constant X β) : locally_constant X (α → β) :=
{ to_fun := λ x a, f a x,
  is_locally_constant := begin
    rw [expr (is_locally_constant.tfae (λ x a, f a x)).out 0 3] [],
    intros [ident g],
    have [] [":", expr «expr = »(«expr ⁻¹' »(λ
       (x : X)
       (a : α), f a x, {g}), «expr⋂ , »((a : α), «expr ⁻¹' »(f a, {g a})))] [],
    by tidy [],
    rw [expr this] [],
    apply [expr is_open_Inter],
    intros [ident a],
    apply [expr (f a).is_locally_constant]
  end }

@[simp]
theorem unflip_flip {X α β : Type _} [Fintype α] [TopologicalSpace X] (f : LocallyConstant X (α → β)) :
  unflip f.flip = f :=
  by 
    ext 
    rfl

@[simp]
theorem flip_unflip {X α β : Type _} [Fintype α] [TopologicalSpace X] (f : α → LocallyConstant X β) :
  (unflip f).flip = f :=
  by 
    ext 
    rfl

section Comap

open_locale Classical

variable[TopologicalSpace Y]

/-- Pull back of locally constant maps under any map, by pre-composition.

This definition only makes sense if `f` is continuous,
in which case it sends locally constant functions to their precomposition with `f`.
See also `locally_constant.coe_comap`. -/
noncomputable def comap (f : X → Y) : LocallyConstant Y Z → LocallyConstant X Z :=
  if hf : Continuous f then fun g => ⟨g ∘ f, g.is_locally_constant.comp_continuous hf⟩ else
    by 
      byCases' H : Nonempty X
      ·
        intros g 
        exact const X (g$ f$ Classical.arbitrary X)
      ·
        intro g 
        refine' ⟨fun x => (H ⟨x⟩).elim, _⟩
        intro s 
        rw [is_open_iff_nhds]
        intro x 
        exact (H ⟨x⟩).elim

@[simp]
theorem coe_comap (f : X → Y) (g : LocallyConstant Y Z) (hf : Continuous f) : «expr⇑ » (comap f g) = (g ∘ f) :=
  by 
    rw [comap, dif_pos hf]
    rfl

@[simp]
theorem comap_id : @comap X X Z _ _ id = id :=
  by 
    ext 
    simp only [continuous_id, id.def, Function.comp.right_id, coe_comap]

theorem comap_comp [TopologicalSpace Z] (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) :
  (@comap _ _ α _ _ f ∘ comap g) = comap (g ∘ f) :=
  by 
    ext 
    simp only [hf, hg, hg.comp hf, coe_comap]

theorem comap_const (f : X → Y) (y : Y) (h : ∀ x, f x = y) :
  (comap f : LocallyConstant Y Z → LocallyConstant X Z) = fun g => ⟨fun x => g y, IsLocallyConstant.const _⟩ :=
  by 
    ext 
    rw [coe_comap]
    ·
      simp only [h, coe_mk, Function.comp_app]
    ·
      rw
        [show f = fun x => y by 
          ext <;> apply h]
      exact continuous_const

end Comap

section Desc

/-- If a locally constant function factors through an injection, then it factors through a locally
constant function. -/
def desc {X α β : Type _} [TopologicalSpace X] {g : α → β} (f : X → α) (h : LocallyConstant X β) (cond : (g ∘ f) = h)
  (inj : Function.Injective g) : LocallyConstant X α :=
  { toFun := f,
    IsLocallyConstant :=
      IsLocallyConstant.desc _ g
        (by 
          rw [cond]
          exact h.2)
        inj }

@[simp]
theorem coe_desc {X α β : Type _} [TopologicalSpace X] (f : X → α) (g : α → β) (h : LocallyConstant X β)
  (cond : (g ∘ f) = h) (inj : Function.Injective g) : «expr⇑ » (desc f h cond inj) = f :=
  rfl

end Desc

end LocallyConstant

