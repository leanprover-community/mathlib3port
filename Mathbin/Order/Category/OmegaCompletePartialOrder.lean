import Mathbin.Order.OmegaCompletePartialOrder 
import Mathbin.Order.Category.Preorder 
import Mathbin.CategoryTheory.Limits.Shapes.Products 
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers 
import Mathbin.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Category of types with a omega complete partial order

In this file, we bundle the class `omega_complete_partial_order` into a
concrete category and prove that continuous functions also form
a `omega_complete_partial_order`.

## Main definitions

 * `ωCPO`
   * an instance of `category` and `concrete_category`

 -/


open CategoryTheory

universe u v

/-- The category of types with a omega complete partial order. -/
def ωCPO : Type (u + 1) :=
  bundled OmegaCompletePartialOrder

namespace ωCPO

open OmegaCompletePartialOrder

instance : bundled_hom @continuous_hom :=
  { toFun := @continuous_hom.simps.apply, id := @continuous_hom.id, comp := @continuous_hom.comp,
    hom_ext := @continuous_hom.coe_inj }

-- ././Mathport/Syntax/Translate/Basic.lean:748:9: unsupported derive handler large_category
-- ././Mathport/Syntax/Translate/Basic.lean:748:9: unsupported derive handler concrete_category
deriving instance [anonymous], [anonymous] for ωCPO

instance : CoeSort ωCPO (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled ωCPO from the underlying type and typeclass. -/
def of (α : Type _) [OmegaCompletePartialOrder α] : ωCPO :=
  bundled.of α

instance : Inhabited ωCPO :=
  ⟨of PUnit⟩

instance (α : ωCPO) : OmegaCompletePartialOrder α :=
  α.str

section 

open CategoryTheory.Limits

namespace HasProducts

/-- The pi-type gives a cone for a product. -/
def product {J : Type v} (f : J → ωCPO.{v}) : fan f :=
  fan.mk (of (∀ j, f j)) fun j => continuous_hom.of_mono (Pi.evalOrderHom j) fun c => rfl

/-- The pi-type is a limit cone for the product. -/
def is_product (J : Type v) (f : J → ωCPO) : is_limit (product f) :=
  { lift :=
      fun s =>
        ⟨⟨fun t j => s.π.app j t, fun x y h j => (s.π.app j).Monotone h⟩,
          fun x => funext fun j => (s.π.app j).Continuous x⟩,
    uniq' :=
      fun s m w =>
        by 
          ext t j 
          change m t j = s.π.app j t 
          rw [←w j]
          rfl }

instance (J : Type v) (f : J → ωCPO.{v}) : has_product f :=
  has_limit.mk ⟨_, is_product _ f⟩

end HasProducts

instance omega_complete_partial_order_equalizer {α β : Type _} [OmegaCompletePartialOrder α]
  [OmegaCompletePartialOrder β] (f g : α →𝒄 β) : OmegaCompletePartialOrder { a : α // f a = g a } :=
  OmegaCompletePartialOrder.subtype _$
    fun c hc =>
      by 
        rw [f.continuous, g.continuous]
        congr 1 
        ext 
        apply hc _ ⟨_, rfl⟩

namespace HasEqualizers

/-- The equalizer inclusion function as a `continuous_hom`. -/
def equalizer_ι {α β : Type _} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β] (f g : α →𝒄 β) :
  { a : α // f a = g a } →𝒄 α :=
  continuous_hom.of_mono (OrderHom.Subtype.val _) fun c => rfl

/-- A construction of the equalizer fork. -/
def equalizer {X Y : ωCPO.{v}} (f g : X ⟶ Y) : fork f g :=
  @fork.of_ι _ _ _ _ _ _ (ωCPO.of { a // f a = g a }) (equalizer_ι f g) (continuous_hom.ext _ _ fun x => x.2)

/-- The equalizer fork is a limit. -/
def is_equalizer {X Y : ωCPO.{v}} (f g : X ⟶ Y) : is_limit (equalizer f g) :=
  fork.is_limit.mk' _$
    fun s =>
      ⟨{ toFun :=
            fun x =>
              ⟨s.ι x,
                by 
                  apply continuous_hom.congr_fun s.condition⟩,
          monotone' := fun x y h => s.ι.monotone h, cont := fun x => Subtype.ext (s.ι.continuous x) },
        by 
          ext 
          rfl,
        fun m hm =>
          by 
            ext 
            apply continuous_hom.congr_fun hm⟩

end HasEqualizers

instance : has_products ωCPO.{v} :=
  fun J => { HasLimit := fun F => has_limit_of_iso discrete.nat_iso_functor.symm }

instance {X Y : ωCPO.{v}} (f g : X ⟶ Y) : has_limit (parallel_pair f g) :=
  has_limit.mk ⟨_, has_equalizers.is_equalizer f g⟩

instance : has_equalizers ωCPO.{v} :=
  has_equalizers_of_has_limit_parallel_pair _

instance : has_limits ωCPO.{v} :=
  limits_from_equalizers_and_products

end 

end ωCPO

