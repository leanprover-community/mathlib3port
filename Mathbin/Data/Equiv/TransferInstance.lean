import Mathbin.Algebra.Algebra.Basic 
import Mathbin.Algebra.Field.Basic 
import Mathbin.Algebra.Group.TypeTags 
import Mathbin.RingTheory.Ideal.LocalRing 
import Mathbin.Data.Equiv.Basic

/-!
# Transfer algebraic structures across `equiv`s

In this file we prove theorems of the following form: if `β` has a
group structure and `α ≃ β` then `α` has a group structure, and
similarly for monoids, semigroups, rings, integral domains, fields and
so on.

Note that most of these constructions can also be obtained using the `transport` tactic.

## Tags

equiv, group, ring, field, module, algebra
-/


universe u v

variable {α : Type u} {β : Type v}

namespace Equiv

section Instances

variable (e : α ≃ β)

/-- Transfer `has_one` across an `equiv` -/
@[toAdditive "Transfer `has_zero` across an `equiv`"]
protected def HasOne [HasOne β] : HasOne α :=
  ⟨e.symm 1⟩

@[toAdditive]
theorem one_def [HasOne β] : @HasOne.one _ (Equiv.hasOne e) = e.symm 1 :=
  rfl

/-- Transfer `has_mul` across an `equiv` -/
@[toAdditive "Transfer `has_add` across an `equiv`"]
protected def Mul [Mul β] : Mul α :=
  ⟨fun x y => e.symm (e x*e y)⟩

@[toAdditive]
theorem mul_def [Mul β] (x y : α) : @Mul.mul _ (Equiv.hasMul e) x y = e.symm (e x*e y) :=
  rfl

/-- Transfer `has_div` across an `equiv` -/
@[toAdditive "Transfer `has_sub` across an `equiv`"]
protected def Div [Div β] : Div α :=
  ⟨fun x y => e.symm (e x / e y)⟩

@[toAdditive]
theorem div_def [Div β] (x y : α) : @Div.div _ (Equiv.hasDiv e) x y = e.symm (e x / e y) :=
  rfl

/-- Transfer `has_inv` across an `equiv` -/
@[toAdditive "Transfer `has_neg` across an `equiv`"]
protected def HasInv [HasInv β] : HasInv α :=
  ⟨fun x => e.symm (e x⁻¹)⟩

@[toAdditive]
theorem inv_def [HasInv β] (x : α) : @HasInv.inv _ (Equiv.hasInv e) x = e.symm (e x⁻¹) :=
  rfl

/-- Transfer `has_scalar` across an `equiv` -/
protected def HasScalar {R : Type _} [HasScalar R β] : HasScalar R α :=
  ⟨fun r x => e.symm (r • e x)⟩

theorem smul_def {R : Type _} [HasScalar R β] (r : R) (x : α) :
  @HasScalar.smul _ _ (Equiv.hasScalar e) r x = e.symm (r • e x) :=
  rfl

-- error in Data.Equiv.TransferInstance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
An equivalence `e : α ≃ β` gives a multiplicative equivalence `α ≃* β`
where the multiplicative structure on `α` is
the one obtained by transporting a multiplicative structure on `β` back along `e`.
-/
@[to_additive #[expr "An equivalence `e : α ≃ β` gives a additive equivalence `α ≃+ β`\nwhere the additive structure on `α` is\nthe one obtained by transporting an additive structure on `β` back along `e`."]]
def mul_equiv (e : «expr ≃ »(α, β)) [has_mul β] : by { letI [] [] [":=", expr equiv.has_mul e],
  exact [expr «expr ≃* »(α, β)] } :=
begin
  introsI [],
  exact [expr { map_mul' := λ x y, by { apply [expr e.symm.injective], simp [] [] [] [] [] [], refl }, ..e }]
end

@[simp, toAdditive]
theorem mul_equiv_apply (e : α ≃ β) [Mul β] (a : α) : (MulEquiv e) a = e a :=
  rfl

-- error in Data.Equiv.TransferInstance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem mul_equiv_symm_apply (e : «expr ≃ »(α, β)) [has_mul β] (b : β) : by { letI [] [] [":=", expr equiv.has_mul e],
  exact [expr «expr = »((mul_equiv e).symm b, e.symm b)] } :=
begin
  intros [],
  refl
end

-- error in Data.Equiv.TransferInstance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
An equivalence `e : α ≃ β` gives a ring equivalence `α ≃+* β`
where the ring structure on `α` is
the one obtained by transporting a ring structure on `β` back along `e`.
-/ def ring_equiv (e : «expr ≃ »(α, β)) [has_add β] [has_mul β] : by { letI [] [] [":=", expr equiv.has_add e],
  letI [] [] [":=", expr equiv.has_mul e],
  exact [expr «expr ≃+* »(α, β)] } :=
begin
  introsI [],
  exact [expr { map_add' := λ x y, by { apply [expr e.symm.injective],
       simp [] [] [] [] [] [],
       refl },
     map_mul' := λ x y, by { apply [expr e.symm.injective],
       simp [] [] [] [] [] [],
       refl },
     ..e }]
end

@[simp]
theorem ring_equiv_apply (e : α ≃ β) [Add β] [Mul β] (a : α) : (RingEquiv e) a = e a :=
  rfl

-- error in Data.Equiv.TransferInstance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ring_equiv_symm_apply
(e : «expr ≃ »(α, β))
[has_add β]
[has_mul β]
(b : β) : by { letI [] [] [":=", expr equiv.has_add e],
  letI [] [] [":=", expr equiv.has_mul e],
  exact [expr «expr = »((ring_equiv e).symm b, e.symm b)] } :=
begin
  intros [],
  refl
end

/-- Transfer `semigroup` across an `equiv` -/
@[toAdditive "Transfer `add_semigroup` across an `equiv`"]
protected def Semigroupₓ [Semigroupₓ β] : Semigroupₓ α :=
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.semigroup _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `semigroup_with_zero` across an `equiv` -/
protected def SemigroupWithZero [SemigroupWithZero β] : SemigroupWithZero α :=
  let mul := e.has_mul 
  let zero := e.has_zero 
  by 
    skip <;> apply e.injective.semigroup_with_zero _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `comm_semigroup` across an `equiv` -/
@[toAdditive "Transfer `add_comm_semigroup` across an `equiv`"]
protected def CommSemigroupₓ [CommSemigroupₓ β] : CommSemigroupₓ α :=
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.comm_semigroup _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `mul_zero_class` across an `equiv` -/
protected def MulZeroClass [MulZeroClass β] : MulZeroClass α :=
  let zero := e.has_zero 
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.mul_zero_class _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `mul_one_class` across an `equiv` -/
@[toAdditive "Transfer `add_zero_class` across an `equiv`"]
protected def MulOneClass [MulOneClass β] : MulOneClass α :=
  let one := e.has_one 
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.mul_one_class _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `mul_zero_one_class` across an `equiv` -/
protected def MulZeroOneClass [MulZeroOneClass β] : MulZeroOneClass α :=
  let zero := e.has_zero 
  let one := e.has_one 
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.mul_zero_one_class _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `monoid` across an `equiv` -/
@[toAdditive "Transfer `add_monoid` across an `equiv`"]
protected def Monoidₓ [Monoidₓ β] : Monoidₓ α :=
  let one := e.has_one 
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.monoid _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `comm_monoid` across an `equiv` -/
@[toAdditive "Transfer `add_comm_monoid` across an `equiv`"]
protected def CommMonoidₓ [CommMonoidₓ β] : CommMonoidₓ α :=
  let one := e.has_one 
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.comm_monoid _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `group` across an `equiv` -/
@[toAdditive "Transfer `add_group` across an `equiv`"]
protected def Groupₓ [Groupₓ β] : Groupₓ α :=
  let one := e.has_one 
  let mul := e.has_mul 
  let inv := e.has_inv 
  let div := e.has_div 
  by 
    skip <;> apply e.injective.group _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `comm_group` across an `equiv` -/
@[toAdditive "Transfer `add_comm_group` across an `equiv`"]
protected def CommGroupₓ [CommGroupₓ β] : CommGroupₓ α :=
  let one := e.has_one 
  let mul := e.has_mul 
  let inv := e.has_inv 
  let div := e.has_div 
  by 
    skip <;> apply e.injective.comm_group _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `non_unital_non_assoc_semiring` across an `equiv` -/
protected def NonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring β] : NonUnitalNonAssocSemiring α :=
  let zero := e.has_zero 
  let add := e.has_add 
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.non_unital_non_assoc_semiring _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `non_unital_semiring` across an `equiv` -/
protected def NonUnitalSemiring [NonUnitalSemiring β] : NonUnitalSemiring α :=
  let zero := e.has_zero 
  let add := e.has_add 
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.non_unital_semiring _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `non_assoc_semiring` across an `equiv` -/
protected def NonAssocSemiring [NonAssocSemiring β] : NonAssocSemiring α :=
  let zero := e.has_zero 
  let add := e.has_add 
  let one := e.has_one 
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.non_assoc_semiring _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `semiring` across an `equiv` -/
protected def Semiringₓ [Semiringₓ β] : Semiringₓ α :=
  let zero := e.has_zero 
  let add := e.has_add 
  let one := e.has_one 
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.semiring _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `comm_semiring` across an `equiv` -/
protected def CommSemiringₓ [CommSemiringₓ β] : CommSemiringₓ α :=
  let zero := e.has_zero 
  let add := e.has_add 
  let one := e.has_one 
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.comm_semiring _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `ring` across an `equiv` -/
protected def Ringₓ [Ringₓ β] : Ringₓ α :=
  let zero := e.has_zero 
  let add := e.has_add 
  let one := e.has_one 
  let mul := e.has_mul 
  let neg := e.has_neg 
  let sub := e.has_sub 
  by 
    skip <;> apply e.injective.ring _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `comm_ring` across an `equiv` -/
protected def CommRingₓ [CommRingₓ β] : CommRingₓ α :=
  let zero := e.has_zero 
  let add := e.has_add 
  let one := e.has_one 
  let mul := e.has_mul 
  let neg := e.has_neg 
  let sub := e.has_sub 
  by 
    skip <;> apply e.injective.comm_ring _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `nonzero` across an `equiv` -/
protected theorem Nontrivial [Nontrivial β] : Nontrivial α :=
  e.surjective.nontrivial

/-- Transfer `is_domain` across an `equiv` -/
protected theorem IsDomain [Ringₓ α] [Ringₓ β] [IsDomain β] (e : α ≃+* β) : IsDomain α :=
  Function.Injective.is_domain e.to_ring_hom e.injective

/-- Transfer `division_ring` across an `equiv` -/
protected def DivisionRing [DivisionRing β] : DivisionRing α :=
  let zero := e.has_zero 
  let add := e.has_add 
  let one := e.has_one 
  let mul := e.has_mul 
  let neg := e.has_neg 
  let sub := e.has_sub 
  let inv := e.has_inv 
  let div := e.has_div 
  by 
    skip <;> apply e.injective.division_ring _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `field` across an `equiv` -/
protected def Field [Field β] : Field α :=
  let zero := e.has_zero 
  let add := e.has_add 
  let one := e.has_one 
  let mul := e.has_mul 
  let neg := e.has_neg 
  let sub := e.has_sub 
  let inv := e.has_inv 
  let div := e.has_div 
  by 
    skip <;> apply e.injective.field _ <;> intros  <;> exact e.apply_symm_apply _

section R

variable (R : Type _)

include R

section 

variable [Monoidₓ R]

/-- Transfer `mul_action` across an `equiv` -/
protected def MulAction (e : α ≃ β) [MulAction R β] : MulAction R α :=
  { Equiv.hasScalar e with
    one_smul :=
      by 
        simp [smul_def],
    mul_smul :=
      by 
        simp [smul_def, mul_smul] }

-- error in Data.Equiv.TransferInstance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Transfer `distrib_mul_action` across an `equiv` -/
protected
def distrib_mul_action (e : «expr ≃ »(α, β)) [add_comm_monoid β] : begin
  letI [] [] [":=", expr equiv.add_comm_monoid e],
  exact [expr ∀ [distrib_mul_action R β], distrib_mul_action R α]
end :=
begin
  intros [],
  letI [] [] [":=", expr equiv.add_comm_monoid e],
  exact [expr ({ smul_zero := by simp [] [] [] ["[", expr zero_def, ",", expr smul_def, "]"] [] [],
     smul_add := by simp [] [] [] ["[", expr add_def, ",", expr smul_def, ",", expr smul_add, "]"] [] [],
     ..equiv.mul_action R e } : distrib_mul_action R α)]
end

end 

section 

variable [Semiringₓ R]

-- error in Data.Equiv.TransferInstance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Transfer `module` across an `equiv` -/ protected def module (e : «expr ≃ »(α, β)) [add_comm_monoid β] : begin
  letI [] [] [":=", expr equiv.add_comm_monoid e],
  exact [expr ∀ [module R β], module R α]
end :=
begin
  introsI [],
  exact [expr ({ zero_smul := by simp [] [] [] ["[", expr zero_def, ",", expr smul_def, "]"] [] [],
     add_smul := by simp [] [] [] ["[", expr add_def, ",", expr smul_def, ",", expr add_smul, "]"] [] [],
     ..equiv.distrib_mul_action R e } : module R α)]
end

-- error in Data.Equiv.TransferInstance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
An equivalence `e : α ≃ β` gives a linear equivalence `α ≃ₗ[R] β`
where the `R`-module structure on `α` is
the one obtained by transporting an `R`-module structure on `β` back along `e`.
-/ def linear_equiv (e : «expr ≃ »(α, β)) [add_comm_monoid β] [module R β] : begin
  letI [] [] [":=", expr equiv.add_comm_monoid e],
  letI [] [] [":=", expr equiv.module R e],
  exact [expr «expr ≃ₗ[ ] »(α, R, β)]
end :=
begin
  introsI [],
  exact [expr { map_smul' := λ r x, by { apply [expr e.symm.injective],
       simp [] [] [] [] [] [],
       refl },
     ..equiv.add_equiv e }]
end

end 

section 

variable [CommSemiringₓ R]

-- error in Data.Equiv.TransferInstance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Transfer `algebra` across an `equiv` -/ protected def algebra (e : «expr ≃ »(α, β)) [semiring β] : begin
  letI [] [] [":=", expr equiv.semiring e],
  exact [expr ∀ [algebra R β], algebra R α]
end :=
begin
  introsI [],
  fapply [expr ring_hom.to_algebra'],
  { exact [expr ((ring_equiv e).symm : «expr →+* »(β, α)).comp (algebra_map R β)] },
  { intros [ident r, ident x],
    simp [] [] ["only"] ["[", expr function.comp_app, ",", expr ring_hom.coe_comp, "]"] [] [],
    have [ident p] [] [":=", expr ring_equiv_symm_apply e],
    dsimp [] [] [] ["at", ident p],
    erw [expr p] [],
    clear [ident p],
    apply [expr (ring_equiv e).injective],
    simp [] [] ["only"] ["[", expr (ring_equiv e).map_mul, "]"] [] [],
    simp [] [] [] ["[", expr algebra.commutes, "]"] [] [] }
end

-- error in Data.Equiv.TransferInstance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
An equivalence `e : α ≃ β` gives an algebra equivalence `α ≃ₐ[R] β`
where the `R`-algebra structure on `α` is
the one obtained by transporting an `R`-algebra structure on `β` back along `e`.
-/ def alg_equiv (e : «expr ≃ »(α, β)) [semiring β] [algebra R β] : begin
  letI [] [] [":=", expr equiv.semiring e],
  letI [] [] [":=", expr equiv.algebra R e],
  exact [expr «expr ≃ₐ[ ] »(α, R, β)]
end :=
begin
  introsI [],
  exact [expr { commutes' := λ r, by { apply [expr e.symm.injective],
       simp [] [] [] [] [] [],
       refl },
     ..equiv.ring_equiv e }]
end

end 

end R

end Instances

end Equiv

namespace RingEquiv

-- error in Data.Equiv.TransferInstance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem local_ring {A B : Type*} [comm_ring A] [local_ring A] [comm_ring B] (e : «expr ≃+* »(A, B)) : local_ring B :=
begin
  haveI [] [] [":=", expr e.symm.to_equiv.nontrivial],
  refine [expr @local_of_surjective A B _ _ _ _ e e.to_equiv.surjective]
end

end RingEquiv

