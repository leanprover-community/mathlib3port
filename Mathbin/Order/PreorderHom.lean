import Mathbin.Order.GaloisConnection 
import Mathbin.Order.CompleteLattice 
import Mathbin.Tactic.Monotonicity.Default 
import Mathbin.Order.BoundedOrder 
import Mathbin.Logic.Function.Iterate

/-!
# Preorder homomorphisms

This file defines preorder homomorphisms, which are bundled monotone functions. A preorder
homomorphism `f : α →ₘ β` is a function `α → β` along with a proof that `∀ x y, x ≤ y → f x ≤ f y`.

## Main definitions

In this file we define `preorder_hom α β` a.k.a. `α →ₘ β` to be a bundled monotone map.

We also define many `preorder_hom`s. In some cases we define two versions, one with `ₘ` suffix and
one without it (e.g., `preorder_hom.compₘ` and `preorder_hom.comp`). This means that the former
function is a "more bundled" version of the latter. We can't just drop the "less bundled" version
because the more bundled version usually does not work with dot notation.

* `preorder_hom.id`: identity map as `α →ₘ α`;
* `preorder_hom.curry`: an order isomorphism between `α × β →ₘ γ` and `α →ₘ β →ₘ γ`;
* `preorder_hom.comp`: composition of two bundled monotone maps;
* `preorder_hom.compₘ`: composition of bundled monotone maps as a bundled monotone map;
* `preorder_hom.const`: constant function as a bundled monotone map;
* `preorder_hom.prod`: combine `α →ₘ β` and `α →ₘ γ` into `α →ₘ β × γ`;
* `preorder_hom.prodₘ`: a more bundled version of `preorder_hom.prod`;
* `preorder_hom.prod_iso`: order isomorphism between `α →ₘ β × γ` and `(α →ₘ β) × (α →ₘ γ)`;
* `preorder_hom.diag`: diagonal embedding of `α` into `α × α` as a bundled monotone map;
* `preorder_hom.on_diag`: restrict a monotone map `α →ₘ α →ₘ β` to the diagonal;
* `preorder_hom.fst`: projection `prod.fst : α × β → α` as a bundled monotone map;
* `preorder_hom.snd`: projection `prod.snd : α × β → β` as a bundled monotone map;
* `preorder_hom.prod_map`: `prod.map f g` as a bundled monotone map;
* `pi.eval_preorder_hom`: evaluation of a function at a point `function.eval i` as a bundled
  monotone map;
* `preorder_hom.coe_fn_hom`: coercion to function as a bundled monotone map;
* `preorder_hom.apply`: application of a `preorder_hom` at a point as a bundled monotone map;
* `preorder_hom.pi`: combine a family of monotone maps `f i : α →ₘ π i` into a monotone map
  `α →ₘ Π i, π i`;
* `preorder_hom.pi_iso`: order isomorphism between `α →ₘ Π i, π i` and `Π i, α →ₘ π i`;
* `preorder_hom.subtyle.val`: embedding `subtype.val : subtype p → α` as a bundled monotone map;
* `preorder_hom.dual`: reinterpret a monotone map `α →ₘ β` as a monotone map
  `order_dual α →ₘ order_dual β`;
* `preorder_hom.dual_iso`: order isomorphism between `α →ₘ β` and
  `order_dual (order_dual α →ₘ order_dual β)`;

We also define two functions to convert other bundled maps to `α →ₘ β`:

* `order_embedding.to_preorder_hom`: convert `α ↪o β` to `α →ₘ β`;
* `rel_hom.to_preorder_hom`: conver a `rel_hom` between strict orders to a `preorder_hom`.

## Tags

monotone map, bundled morphism
-/


/-- Bundled monotone (aka, increasing) function -/
structure PreorderHom(α β : Type _)[Preorderₓ α][Preorderₓ β] where 
  toFun : α → β 
  monotone' : Monotone to_fun

infixr:25 " →ₘ " => PreorderHom

namespace PreorderHom

variable{α β γ δ : Type _}[Preorderₓ α][Preorderₓ β][Preorderₓ γ][Preorderₓ δ]

instance  : CoeFun (α →ₘ β) fun _ => α → β :=
  ⟨PreorderHom.toFun⟩

initialize_simps_projections PreorderHom (toFun → coe)

protected theorem Monotone (f : α →ₘ β) : Monotone f :=
  f.monotone'

protected theorem mono (f : α →ₘ β) : Monotone f :=
  f.monotone

@[simp]
theorem to_fun_eq_coe {f : α →ₘ β} : f.to_fun = f :=
  rfl

@[simp]
theorem coe_fun_mk {f : α → β} (hf : _root_.monotone f) : (mk f hf : α → β) = f :=
  rfl

@[ext]
theorem ext (f g : α →ₘ β) (h : (f : α → β) = g) : f = g :=
  by 
    cases f 
    cases g 
    congr 
    exact h

/-- One can lift an unbundled monotone function to a bundled one. -/
instance  : CanLift (α → β) (α →ₘ β) :=
  { coe := coeFn, cond := Monotone, prf := fun f h => ⟨⟨f, h⟩, rfl⟩ }

/-- The identity function as bundled monotone function. -/
@[simps (config := { fullyApplied := ff })]
def id : α →ₘ α :=
  ⟨id, monotone_id⟩

instance  : Inhabited (α →ₘ α) :=
  ⟨id⟩

/-- The preorder structure of `α →ₘ β` is pointwise inequality: `f ≤ g ↔ ∀ a, f a ≤ g a`. -/
instance  : Preorderₓ (α →ₘ β) :=
  @Preorderₓ.lift (α →ₘ β) (α → β) _ coeFn

instance  {β : Type _} [PartialOrderₓ β] : PartialOrderₓ (α →ₘ β) :=
  @PartialOrderₓ.lift (α →ₘ β) (α → β) _ coeFn ext

theorem le_def {f g : α →ₘ β} : f ≤ g ↔ ∀ x, f x ≤ g x :=
  Iff.rfl

@[simp, normCast]
theorem coe_le_coe {f g : α →ₘ β} : (f : α → β) ≤ g ↔ f ≤ g :=
  Iff.rfl

@[simp]
theorem mk_le_mk {f g : α → β} {hf hg} : mk f hf ≤ mk g hg ↔ f ≤ g :=
  Iff.rfl

@[mono]
theorem apply_mono {f g : α →ₘ β} {x y : α} (h₁ : f ≤ g) (h₂ : x ≤ y) : f x ≤ g y :=
  (h₁ x).trans$ g.mono h₂

/-- Curry/uncurry as an order isomorphism between `α × β →ₘ γ` and `α →ₘ β →ₘ γ`. -/
def curry : (α × β →ₘ γ) ≃o (α →ₘ β →ₘ γ) :=
  { toFun :=
      fun f => ⟨fun x => ⟨Function.curry f x, fun y₁ y₂ h => f.mono ⟨le_rfl, h⟩⟩, fun x₁ x₂ h y => f.mono ⟨h, le_rfl⟩⟩,
    invFun := fun f => ⟨Function.uncurry fun x => f x, fun x y h => (f.mono h.1 x.2).trans$ (f y.1).mono h.2⟩,
    left_inv :=
      fun f =>
        by 
          ext ⟨x, y⟩
          rfl,
    right_inv :=
      fun f =>
        by 
          ext x y 
          rfl,
    map_rel_iff' :=
      fun f g =>
        by 
          simp [le_def] }

@[simp]
theorem curry_apply (f : α × β →ₘ γ) (x : α) (y : β) : curry f x y = f (x, y) :=
  rfl

@[simp]
theorem curry_symm_apply (f : α →ₘ β →ₘ γ) (x : α × β) : curry.symm f x = f x.1 x.2 :=
  rfl

/-- The composition of two bundled monotone functions. -/
@[simps (config := { fullyApplied := ff })]
def comp (g : β →ₘ γ) (f : α →ₘ β) : α →ₘ γ :=
  ⟨g ∘ f, g.mono.comp f.mono⟩

@[mono]
theorem comp_mono ⦃g₁ g₂ : β →ₘ γ⦄ (hg : g₁ ≤ g₂) ⦃f₁ f₂ : α →ₘ β⦄ (hf : f₁ ≤ f₂) : g₁.comp f₁ ≤ g₂.comp f₂ :=
  fun x => (hg _).trans (g₂.mono$ hf _)

-- error in Order.PreorderHom: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The composition of two bundled monotone functions, a fully bundled version. -/
@[simps #[expr { fully_applied := ff }]]
def compₘ : «expr →ₘ »(«expr →ₘ »(β, γ), «expr →ₘ »(«expr →ₘ »(α, β), «expr →ₘ »(α, γ))) :=
curry ⟨λ f : «expr × »(«expr →ₘ »(β, γ), «expr →ₘ »(α, β)), f.1.comp f.2, λ f₁ f₂ h, comp_mono h.1 h.2⟩

@[simp]
theorem comp_id (f : α →ₘ β) : comp f id = f :=
  by 
    ext 
    rfl

@[simp]
theorem id_comp (f : α →ₘ β) : comp id f = f :=
  by 
    ext 
    rfl

/-- Constant function bundled as a `preorder_hom`. -/
@[simps (config := { fullyApplied := ff })]
def const (α : Type _) [Preorderₓ α] {β : Type _} [Preorderₓ β] : β →ₘ α →ₘ β :=
  { toFun := fun b => ⟨Function.const α b, fun _ _ _ => le_rfl⟩, monotone' := fun b₁ b₂ h x => h }

@[simp]
theorem const_comp (f : α →ₘ β) (c : γ) : (const β c).comp f = const α c :=
  rfl

@[simp]
theorem comp_const (γ : Type _) [Preorderₓ γ] (f : α →ₘ β) (c : α) : f.comp (const γ c) = const γ (f c) :=
  rfl

/-- Given two bundled monotone maps `f`, `g`, `f.prod g` is the map `x ↦ (f x, g x)` bundled as a
`preorder_hom`. -/
@[simps]
protected def Prod (f : α →ₘ β) (g : α →ₘ γ) : α →ₘ β × γ :=
  ⟨fun x => (f x, g x), fun x y h => ⟨f.mono h, g.mono h⟩⟩

@[mono]
theorem prod_mono {f₁ f₂ : α →ₘ β} (hf : f₁ ≤ f₂) {g₁ g₂ : α →ₘ γ} (hg : g₁ ≤ g₂) : f₁.prod g₁ ≤ f₂.prod g₂ :=
  fun x => Prod.le_def.2 ⟨hf _, hg _⟩

theorem comp_prod_comp_same (f₁ f₂ : β →ₘ γ) (g : α →ₘ β) : (f₁.comp g).Prod (f₂.comp g) = (f₁.prod f₂).comp g :=
  rfl

-- error in Order.PreorderHom: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Given two bundled monotone maps `f`, `g`, `f.prod g` is the map `x ↦ (f x, g x)` bundled as a
`preorder_hom`. This is a fully bundled version. -/
@[simps #[]]
def prodₘ : «expr →ₘ »(«expr →ₘ »(α, β), «expr →ₘ »(«expr →ₘ »(α, γ), «expr →ₘ »(α, «expr × »(β, γ)))) :=
curry ⟨λ f : «expr × »(«expr →ₘ »(α, β), «expr →ₘ »(α, γ)), f.1.prod f.2, λ f₁ f₂ h, prod_mono h.1 h.2⟩

/-- Diagonal embedding of `α` into `α × α` as a `preorder_hom`. -/
@[simps]
def diag : α →ₘ α × α :=
  id.Prod id

/-- Restriction of `f : α →ₘ α →ₘ β` to the diagonal. -/
@[simps (config := { simpRhs := tt })]
def on_diag (f : α →ₘ α →ₘ β) : α →ₘ β :=
  (curry.symm f).comp diag

/-- `prod.fst` as a `preorder_hom`. -/
@[simps]
def fst : α × β →ₘ α :=
  ⟨Prod.fst, fun x y h => h.1⟩

/-- `prod.snd` as a `preorder_hom`. -/
@[simps]
def snd : α × β →ₘ β :=
  ⟨Prod.snd, fun x y h => h.2⟩

@[simp]
theorem fst_prod_snd : (fst : α × β →ₘ α).Prod snd = id :=
  by 
    ext ⟨x, y⟩ : 2
    rfl

@[simp]
theorem fst_comp_prod (f : α →ₘ β) (g : α →ₘ γ) : fst.comp (f.prod g) = f :=
  ext _ _ rfl

@[simp]
theorem snd_comp_prod (f : α →ₘ β) (g : α →ₘ γ) : snd.comp (f.prod g) = g :=
  ext _ _ rfl

/-- Order isomorphism between the space of monotone maps to `β × γ` and the product of the spaces
of monotone maps to `β` and `γ`. -/
@[simps]
def prod_iso : (α →ₘ β × γ) ≃o (α →ₘ β) × (α →ₘ γ) :=
  { toFun := fun f => (fst.comp f, snd.comp f), invFun := fun f => f.1.Prod f.2,
    left_inv :=
      fun f =>
        by 
          ext <;> rfl,
    right_inv :=
      fun f =>
        by 
          ext <;> rfl,
    map_rel_iff' := fun f g => forall_and_distrib.symm }

/-- `prod.map` of two `preorder_hom`s as a `preorder_hom`. -/
@[simps]
def prod_mapₓ (f : α →ₘ β) (g : γ →ₘ δ) : α × γ →ₘ β × δ :=
  ⟨Prod.mapₓ f g, fun x y h => ⟨f.mono h.1, g.mono h.2⟩⟩

variable{ι : Type _}{π : ι → Type _}[∀ i, Preorderₓ (π i)]

/-- Evaluation of an unbundled function at a point (`function.eval`) as a `preorder_hom`. -/
@[simps (config := { fullyApplied := ff })]
def _root_.pi.eval_preorder_hom (i : ι) : (∀ j, π j) →ₘ π i :=
  ⟨Function.eval i, Function.monotone_eval i⟩

/-- The "forgetful functor" from `α →ₘ β` to `α → β` that takes the underlying function,
is monotone. -/
@[simps (config := { fullyApplied := ff })]
def coe_fn_hom : (α →ₘ β) →ₘ α → β :=
  { toFun := fun f => f, monotone' := fun x y h => h }

/-- Function application `λ f, f a` (for fixed `a`) is a monotone function from the
monotone function space `α →ₘ β` to `β`. See also `pi.eval_preorder_hom`.  -/
@[simps (config := { fullyApplied := ff })]
def apply (x : α) : (α →ₘ β) →ₘ β :=
  (Pi.evalPreorderHom x).comp coe_fn_hom

/-- Construct a bundled monotone map `α →ₘ Π i, π i` from a family of monotone maps
`f i : α →ₘ π i`. -/
@[simps]
def pi (f : ∀ i, α →ₘ π i) : α →ₘ ∀ i, π i :=
  ⟨fun x i => f i x, fun x y h i => (f i).mono h⟩

/-- Order isomorphism between bundled monotone maps `α →ₘ Π i, π i` and families of bundled monotone
maps `Π i, α →ₘ π i`. -/
@[simps]
def pi_iso : (α →ₘ ∀ i, π i) ≃o ∀ i, α →ₘ π i :=
  { toFun := fun f i => (Pi.evalPreorderHom i).comp f, invFun := pi,
    left_inv :=
      fun f =>
        by 
          ext x i 
          rfl,
    right_inv :=
      fun f =>
        by 
          ext x i 
          rfl,
    map_rel_iff' := fun f g => forall_swap }

/-- `subtype.val` as a bundled monotone function.  -/
@[simps (config := { fullyApplied := ff })]
def Subtype.val (p : α → Prop) : Subtype p →ₘ α :=
  ⟨Subtype.val, fun x y h => h⟩

/-- There is a unique monotone map from a subsingleton to itself. -/
@[local instance]
def Unique [Subsingleton α] : Unique (α →ₘ α) :=
  { default := PreorderHom.id, uniq := fun a => ext _ _ (Subsingleton.elimₓ _ _) }

theorem preorder_hom_eq_id [Subsingleton α] (g : α →ₘ α) : g = PreorderHom.id :=
  Subsingleton.elimₓ _ _

/-- Reinterpret a bundled monotone function as a monotone function between dual orders. -/
@[simps]
protected def dual : (α →ₘ β) ≃ (OrderDual α →ₘ OrderDual β) :=
  { toFun := fun f => ⟨OrderDual.toDual ∘ f ∘ OrderDual.ofDual, f.mono.dual⟩,
    invFun := fun f => ⟨OrderDual.ofDual ∘ f ∘ OrderDual.toDual, f.mono.dual⟩, left_inv := fun f => ext _ _ rfl,
    right_inv := fun f => ext _ _ rfl }

/-- `preorder_hom.dual` as an order isomorphism. -/
def dual_iso (α β : Type _) [Preorderₓ α] [Preorderₓ β] : (α →ₘ β) ≃o OrderDual (OrderDual α →ₘ OrderDual β) :=
  { toEquiv := PreorderHom.dual.trans OrderDual.toDual, map_rel_iff' := fun f g => Iff.rfl }

@[simps]
instance  {β : Type _} [SemilatticeSup β] : HasSup (α →ₘ β) :=
  { sup := fun f g => ⟨fun a => f a⊔g a, f.mono.sup g.mono⟩ }

instance  {β : Type _} [SemilatticeSup β] : SemilatticeSup (α →ₘ β) :=
  { (_ : PartialOrderₓ (α →ₘ β)) with sup := HasSup.sup, le_sup_left := fun a b x => le_sup_left,
    le_sup_right := fun a b x => le_sup_right, sup_le := fun a b c h₀ h₁ x => sup_le (h₀ x) (h₁ x) }

@[simps]
instance  {β : Type _} [SemilatticeInf β] : HasInf (α →ₘ β) :=
  { inf := fun f g => ⟨fun a => f a⊓g a, f.mono.inf g.mono⟩ }

instance  {β : Type _} [SemilatticeInf β] : SemilatticeInf (α →ₘ β) :=
  { (_ : PartialOrderₓ (α →ₘ β)), (dual_iso α β).symm.toGaloisInsertion.liftSemilatticeInf with inf := ·⊓· }

instance  {β : Type _} [Lattice β] : Lattice (α →ₘ β) :=
  { (_ : SemilatticeSup (α →ₘ β)), (_ : SemilatticeInf (α →ₘ β)) with  }

@[simps]
instance  {β : Type _} [Preorderₓ β] [OrderBot β] : HasBot (α →ₘ β) :=
  { bot := const α ⊥ }

instance  {β : Type _} [Preorderₓ β] [OrderBot β] : OrderBot (α →ₘ β) :=
  { bot := ⊥, bot_le := fun a x => bot_le }

@[simps]
instance  {β : Type _} [Preorderₓ β] [OrderTop β] : HasTop (α →ₘ β) :=
  { top := const α ⊤ }

instance  {β : Type _} [Preorderₓ β] [OrderTop β] : OrderTop (α →ₘ β) :=
  { top := ⊤, le_top := fun a x => le_top }

instance  {β : Type _} [CompleteLattice β] : HasInfₓ (α →ₘ β) :=
  { inf := fun s => ⟨fun x => ⨅(f : _)(_ : f ∈ s), (f : _) x, fun x y h => binfi_le_binfi fun f _ => f.mono h⟩ }

@[simp]
theorem Inf_apply {β : Type _} [CompleteLattice β] (s : Set (α →ₘ β)) (x : α) :
  Inf s x = ⨅(f : _)(_ : f ∈ s), (f : _) x :=
  rfl

theorem infi_apply {ι : Sort _} {β : Type _} [CompleteLattice β] (f : ι → α →ₘ β) (x : α) : (⨅i, f i) x = ⨅i, f i x :=
  (Inf_apply _ _).trans infi_range

@[simp, normCast]
theorem coe_infi {ι : Sort _} {β : Type _} [CompleteLattice β] (f : ι → α →ₘ β) :
  ((⨅i, f i : α →ₘ β) : α → β) = ⨅i, f i :=
  funext$ fun x => (infi_apply f x).trans (@_root_.infi_apply _ _ _ _ (fun i => f i) _).symm

instance  {β : Type _} [CompleteLattice β] : HasSupₓ (α →ₘ β) :=
  { sup := fun s => ⟨fun x => ⨆(f : _)(_ : f ∈ s), (f : _) x, fun x y h => bsupr_le_bsupr fun f _ => f.mono h⟩ }

@[simp]
theorem Sup_apply {β : Type _} [CompleteLattice β] (s : Set (α →ₘ β)) (x : α) :
  Sup s x = ⨆(f : _)(_ : f ∈ s), (f : _) x :=
  rfl

theorem supr_apply {ι : Sort _} {β : Type _} [CompleteLattice β] (f : ι → α →ₘ β) (x : α) : (⨆i, f i) x = ⨆i, f i x :=
  (Sup_apply _ _).trans supr_range

@[simp, normCast]
theorem coe_supr {ι : Sort _} {β : Type _} [CompleteLattice β] (f : ι → α →ₘ β) :
  ((⨆i, f i : α →ₘ β) : α → β) = ⨆i, f i :=
  funext$ fun x => (supr_apply f x).trans (@_root_.supr_apply _ _ _ _ (fun i => f i) _).symm

instance  {β : Type _} [CompleteLattice β] : CompleteLattice (α →ₘ β) :=
  { (_ : Lattice (α →ₘ β)), PreorderHom.orderTop, PreorderHom.orderBot with sup := Sup,
    le_Sup := fun s f hf x => le_supr_of_le f (le_supr _ hf), Sup_le := fun s f hf x => bsupr_le fun g hg => hf g hg x,
    inf := Inf, le_Inf := fun s f hf x => le_binfi fun g hg => hf g hg x,
    Inf_le := fun s f hf x => infi_le_of_le f (infi_le _ hf) }

-- error in Order.PreorderHom: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem iterate_sup_le_sup_iff
{α : Type*}
[semilattice_sup α]
(f : «expr →ₘ »(α, α)) : «expr ↔ »(∀
 n₁
 n₂
 a₁
 a₂, «expr ≤ »(«expr ^[ ]»(f, «expr + »(n₁, n₂)) «expr ⊔ »(a₁, a₂), «expr ⊔ »(«expr ^[ ]»(f, n₁) a₁, «expr ^[ ]»(f, n₂) a₂)), ∀
 a₁ a₂, «expr ≤ »(f «expr ⊔ »(a₁, a₂), «expr ⊔ »(f a₁, a₂))) :=
begin
  split; intros [ident h],
  { exact [expr h 1 0] },
  { intros [ident n₁, ident n₂, ident a₁, ident a₂],
    have [ident h'] [":", expr ∀
     n a₁ a₂, «expr ≤ »(«expr ^[ ]»(f, n) «expr ⊔ »(a₁, a₂), «expr ⊔ »(«expr ^[ ]»(f, n) a₁, a₂))] [],
    { intros [ident n],
      induction [expr n] [] ["with", ident n, ident ih] []; intros [ident a₁, ident a₂],
      { refl },
      { calc
          «expr = »(«expr ^[ ]»(f, «expr + »(n, 1)) «expr ⊔ »(a₁, a₂), «expr ^[ ]»(f, n) (f «expr ⊔ »(a₁, a₂))) : function.iterate_succ_apply f n _
          «expr ≤ »(..., «expr ^[ ]»(f, n) «expr ⊔ »(f a₁, a₂)) : f.mono.iterate n (h a₁ a₂)
          «expr ≤ »(..., «expr ⊔ »(«expr ^[ ]»(f, n) (f a₁), a₂)) : ih _ _
          «expr = »(..., «expr ⊔ »(«expr ^[ ]»(f, «expr + »(n, 1)) a₁, a₂)) : by rw ["<-", expr function.iterate_succ_apply] [] } },
    calc
      «expr = »(«expr ^[ ]»(f, «expr + »(n₁, n₂)) «expr ⊔ »(a₁, a₂), «expr ^[ ]»(f, n₁) («expr ^[ ]»(f, n₂) «expr ⊔ »(a₁, a₂))) : function.iterate_add_apply f n₁ n₂ _
      «expr = »(..., «expr ^[ ]»(f, n₁) («expr ^[ ]»(f, n₂) «expr ⊔ »(a₂, a₁))) : by rw [expr sup_comm] []
      «expr ≤ »(..., «expr ^[ ]»(f, n₁) «expr ⊔ »(«expr ^[ ]»(f, n₂) a₂, a₁)) : f.mono.iterate n₁ (h' n₂ _ _)
      «expr = »(..., «expr ^[ ]»(f, n₁) «expr ⊔ »(a₁, «expr ^[ ]»(f, n₂) a₂)) : by rw [expr sup_comm] []
      «expr ≤ »(..., «expr ⊔ »(«expr ^[ ]»(f, n₁) a₁, «expr ^[ ]»(f, n₂) a₂)) : h' n₁ a₁ _ }
end

end PreorderHom

namespace OrderEmbedding

/-- Convert an `order_embedding` to a `preorder_hom`. -/
@[simps (config := { fullyApplied := ff })]
def to_preorder_hom {X Y : Type _} [Preorderₓ X] [Preorderₓ Y] (f : X ↪o Y) : X →ₘ Y :=
  { toFun := f, monotone' := f.monotone }

end OrderEmbedding

section RelHom

variable{α β : Type _}[PartialOrderₓ α][Preorderₓ β]

namespace RelHom

variable(f : (· < · : α → α → Prop) →r (· < · : β → β → Prop))

/-- A bundled expression of the fact that a map between partial orders that is strictly monotone
is weakly monotone. -/
@[simps (config := { fullyApplied := ff })]
def to_preorder_hom : α →ₘ β :=
  { toFun := f, monotone' := StrictMono.monotone fun x y => f.map_rel }

end RelHom

theorem RelEmbedding.to_preorder_hom_injective (f : (· < · : α → α → Prop) ↪r (· < · : β → β → Prop)) :
  Function.Injective (f : (· < · : α → α → Prop) →r (· < · : β → β → Prop)).toPreorderHom :=
  fun _ _ h => f.injective h

end RelHom

