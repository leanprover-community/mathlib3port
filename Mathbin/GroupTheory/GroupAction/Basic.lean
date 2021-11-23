import Mathbin.GroupTheory.GroupAction.Defs 
import Mathbin.GroupTheory.GroupAction.Group 
import Mathbin.GroupTheory.QuotientGroup 
import Mathbin.Data.Setoid.Basic 
import Mathbin.Data.Fintype.Card

/-!
# Basic properties of group actions
-/


universe u v w

variable{α : Type u}{β : Type v}{γ : Type w}

open_locale BigOperators Pointwise

open Function

namespace MulAction

variable(α)[Monoidₓ α][MulAction α β]

/-- The orbit of an element under an action. -/
@[toAdditive "The orbit of an element under an action."]
def orbit (b : β) :=
  Set.Range fun x : α => x • b

variable{α}

@[toAdditive]
theorem mem_orbit_iff {b₁ b₂ : β} : b₂ ∈ orbit α b₁ ↔ ∃ x : α, x • b₁ = b₂ :=
  Iff.rfl

@[simp, toAdditive]
theorem mem_orbit (b : β) (x : α) : x • b ∈ orbit α b :=
  ⟨x, rfl⟩

@[simp, toAdditive]
theorem mem_orbit_self (b : β) : b ∈ orbit α b :=
  ⟨1,
    by 
      simp [MulAction.one_smul]⟩

@[toAdditive]
theorem orbit_nonempty (b : β) : Set.Nonempty (orbit α b) :=
  Set.range_nonempty _

@[toAdditive]
theorem maps_to_smul_orbit (a : α) (b : β) : Set.MapsTo ((· • ·) a) (orbit α b) (orbit α b) :=
  Set.range_subset_iff.2$ fun a' => ⟨a*a', mul_smul _ _ _⟩

@[toAdditive]
theorem smul_orbit_subset (a : α) (b : β) : a • orbit α b ⊆ orbit α b :=
  (maps_to_smul_orbit a b).image_subset

@[toAdditive]
theorem orbit_smul_subset (a : α) (b : β) : orbit α (a • b) ⊆ orbit α b :=
  Set.range_subset_iff.2$ fun a' => mul_smul a' a b ▸ mem_orbit _ _

@[toAdditive]
instance  {b : β} : MulAction α (orbit α b) :=
  { smul := fun a => (maps_to_smul_orbit a b).restrict _ _ _, one_smul := fun a => Subtype.ext (one_smul α a),
    mul_smul := fun a a' b' => Subtype.ext (mul_smul a a' b') }

@[simp, toAdditive]
theorem orbit.coe_smul {b : β} {a : α} {b' : orbit α b} : «expr↑ » (a • b') = a • (b' : β) :=
  rfl

variable(α)(β)

/-- The set of elements fixed under the whole action. -/
@[toAdditive "The set of elements fixed under the whole action."]
def fixed_points : Set β :=
  { b:β | ∀ x : α, x • b = b }

/-- `fixed_by g` is the subfield of elements fixed by `g`. -/
@[toAdditive "`fixed_by g` is the subfield of elements fixed by `g`."]
def fixed_by (g : α) : Set β :=
  { x | g • x = x }

@[toAdditive]
theorem fixed_eq_Inter_fixed_by : fixed_points α β = ⋂g : α, fixed_by α β g :=
  Set.ext$
    fun x =>
      ⟨fun hx => Set.mem_Inter.2$ fun g => hx g,
        fun hx g =>
          by 
            exact (Set.mem_Inter.1 hx g : _)⟩

variable{α}(β)

@[simp, toAdditive]
theorem mem_fixed_points {b : β} : b ∈ fixed_points α β ↔ ∀ x : α, x • b = b :=
  Iff.rfl

@[simp, toAdditive]
theorem mem_fixed_by {g : α} {b : β} : b ∈ fixed_by α β g ↔ g • b = b :=
  Iff.rfl

@[toAdditive]
theorem mem_fixed_points' {b : β} : b ∈ fixed_points α β ↔ ∀ b', b' ∈ orbit α b → b' = b :=
  ⟨fun h b h₁ =>
      let ⟨x, hx⟩ := mem_orbit_iff.1 h₁ 
      hx ▸ h x,
    fun h b => h _ (mem_orbit _ _)⟩

variable(α){β}

/-- The stabilizer of a point `b` as a submonoid of `α`. -/
@[toAdditive "The stabilizer of a point `b` as an additive submonoid of `α`."]
def stabilizer.submonoid (b : β) : Submonoid α :=
  { Carrier := { a | a • b = b }, one_mem' := one_smul _ b,
    mul_mem' :=
      fun a a' ha : a • b = b hb : a' • b = b =>
        show (a*a') • b = b by 
          rw [←smul_smul, hb, ha] }

@[simp, toAdditive]
theorem mem_stabilizer_submonoid_iff {b : β} {a : α} : a ∈ stabilizer.submonoid α b ↔ a • b = b :=
  Iff.rfl

@[toAdditive]
theorem orbit_eq_univ [is_pretransitive α β] (x : β) : orbit α x = Set.Univ :=
  (surjective_smul α x).range_eq

end MulAction

namespace MulAction

variable(α)

variable[Groupₓ α][MulAction α β]

/-- The stabilizer of an element under an action, i.e. what sends the element to itself.
A subgroup. -/
@[toAdditive
      "The stabilizer of an element under an action, i.e. what sends the element to itself.\nAn additive subgroup."]
def stabilizer (b : β) : Subgroup α :=
  { stabilizer.submonoid α b with
    inv_mem' :=
      fun a ha : a • b = b =>
        show a⁻¹ • b = b by 
          rw [inv_smul_eq_iff, ha] }

variable{α}{β}

@[simp, toAdditive]
theorem mem_stabilizer_iff {b : β} {a : α} : a ∈ stabilizer α b ↔ a • b = b :=
  Iff.rfl

@[simp, toAdditive]
theorem smul_orbit (a : α) (b : β) : a • orbit α b = orbit α b :=
  (smul_orbit_subset a b).antisymm$
    calc orbit α b = a • a⁻¹ • orbit α b := (smul_inv_smul _ _).symm 
      _ ⊆ a • orbit α b := Set.image_subset _ (smul_orbit_subset _ _)
      

@[simp, toAdditive]
theorem orbit_smul (a : α) (b : β) : orbit α (a • b) = orbit α b :=
  (orbit_smul_subset a b).antisymm$
    calc orbit α b = orbit α (a⁻¹ • a • b) :=
      by 
        rw [inv_smul_smul]
      _ ⊆ orbit α (a • b) := orbit_smul_subset _ _
      

/-- The action of a group on an orbit is transitive. -/
@[toAdditive "The action of an additive group on an orbit is transitive."]
instance  (x : β) : is_pretransitive α (orbit α x) :=
  ⟨by 
      rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      use b*a⁻¹
      ext1 
      simp [mul_smul]⟩

@[toAdditive]
theorem orbit_eq_iff {a b : β} : orbit α a = orbit α b ↔ a ∈ orbit α b :=
  ⟨fun h => h ▸ mem_orbit_self _, fun ⟨c, hc⟩ => hc ▸ orbit_smul _ _⟩

@[toAdditive]
theorem mem_fixed_points_iff_card_orbit_eq_one {a : β} [Fintype (orbit α a)] :
  a ∈ fixed_points α β ↔ Fintype.card (orbit α a) = 1 :=
  by 
    rw [Fintype.card_eq_one_iff, mem_fixed_points]
    split 
    ·
      exact
        fun h =>
          ⟨⟨a, mem_orbit_self _⟩,
            fun ⟨b, ⟨x, hx⟩⟩ =>
              Subtype.eq$
                by 
                  simp [h x, hx.symm]⟩
    ·
      intro h x 
      rcases h with ⟨⟨z, hz⟩, hz₁⟩
      calc x • a = z := Subtype.mk.injₓ (hz₁ ⟨x • a, mem_orbit _ _⟩)_ = a :=
        (Subtype.mk.injₓ (hz₁ ⟨a, mem_orbit_self _⟩)).symm

variable(α){β}

@[toAdditive]
theorem mem_orbit_smul (g : α) (a : β) : a ∈ orbit α (g • a) :=
  by 
    simp only [orbit_smul, mem_orbit_self]

@[toAdditive]
theorem smul_mem_orbit_smul (g h : α) (a : β) : g • a ∈ orbit α (h • a) :=
  by 
    simp only [orbit_smul, mem_orbit]

variable(α)(β)

-- error in GroupTheory.GroupAction.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The relation 'in the same orbit'. -/
@[to_additive #[expr "The relation 'in the same orbit'."]]
def orbit_rel : setoid β :=
{ r := λ a b, «expr ∈ »(a, orbit α b),
  iseqv := ⟨mem_orbit_self, λ
   a
   b, by simp [] [] [] ["[", expr orbit_eq_iff.symm, ",", expr eq_comm, "]"] [] [], λ
   a b, by simp [] [] [] ["[", expr orbit_eq_iff.symm, ",", expr eq_comm, "]"] [] [] { contextual := tt }⟩ }

local notation "Ω" => Quotientₓ$ orbit_rel α β

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action.
This version works with any right inverse to `quotient.mk'` in order to stay computable. In most
cases you'll want to use `quotient.out'`, so we provide `mul_action.self_equiv_sigma_orbits` as
a special case. -/
@[toAdditive
      "Decomposition of a type `X` as a disjoint union of its orbits under an additive group\naction. This version works with any right inverse to `quotient.mk'` in order to stay computable.\nIn most cases you'll want to use `quotient.out'`, so we provide `add_action.self_equiv_sigma_orbits`\nas a special case."]
def self_equiv_sigma_orbits' {φ : Ω → β} (hφ : RightInverse φ Quotientₓ.mk') : β ≃ Σω : Ω, orbit α (φ ω) :=
  calc β ≃ Σω : Ω, { b // Quotientₓ.mk' b = ω } := (Equiv.sigmaPreimageEquiv Quotientₓ.mk').symm 
    _ ≃ Σω : Ω, orbit α (φ ω) :=
    Equiv.sigmaCongrRight
      fun ω =>
        Equiv.subtypeEquivRight$
          fun x =>
            by 
              rw [←hφ ω, Quotientₓ.eq', hφ ω]
              rfl
    

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action. -/
@[toAdditive "Decomposition of a type `X` as a disjoint union of its orbits under an additive group\naction."]
noncomputable def self_equiv_sigma_orbits : β ≃ Σω : Ω, orbit α ω.out' :=
  self_equiv_sigma_orbits' α β Quotientₓ.out_eq'

variable{α β}

/-- If the stabilizer of `x` is `S`, then the stabilizer of `g • x` is `gSg⁻¹`. -/
theorem stabilizer_smul_eq_stabilizer_map_conj (g : α) (x : β) :
  stabilizer α (g • x) = (stabilizer α x).map (MulAut.conj g).toMonoidHom :=
  by 
    ext h 
    rw [mem_stabilizer_iff, ←smul_left_cancel_iff (g⁻¹), smul_smul, smul_smul, smul_smul, mul_left_invₓ, one_smul,
      ←mem_stabilizer_iff, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

/-- A bijection between the stabilizers of two elements in the same orbit. -/
noncomputable def stabilizer_equiv_stabilizer_of_orbit_rel {x y : β} (h : (orbit_rel α β).Rel x y) :
  stabilizer α x ≃* stabilizer α y :=
  let g : α := Classical.some h 
  have hg : g • y = x := Classical.some_spec h 
  have this : stabilizer α x = (stabilizer α y).map (MulAut.conj g).toMonoidHom :=
    by 
      rw [←hg, stabilizer_smul_eq_stabilizer_map_conj]
  (MulEquiv.subgroupCongr this).trans ((MulAut.conj g).subgroupEquivMap$ stabilizer α y).symm

end MulAction

namespace AddAction

variable[AddGroupₓ α][AddAction α β]

/-- If the stabilizer of `x` is `S`, then the stabilizer of `g +ᵥ x` is `g + S + (-g)`. -/
theorem stabilizer_vadd_eq_stabilizer_map_conj (g : α) (x : β) :
  stabilizer α (g +ᵥ x) = (stabilizer α x).map (AddAut.conj g).toAddMonoidHom :=
  by 
    ext h 
    rw [mem_stabilizer_iff, ←vadd_left_cancel_iff (-g), vadd_vadd, vadd_vadd, vadd_vadd, add_left_negₓ, zero_vadd,
      ←mem_stabilizer_iff, AddSubgroup.mem_map_equiv, AddAut.conj_symm_apply]

/-- A bijection between the stabilizers of two elements in the same orbit. -/
noncomputable def stabilizer_equiv_stabilizer_of_orbit_rel {x y : β} (h : (orbit_rel α β).Rel x y) :
  stabilizer α x ≃+ stabilizer α y :=
  let g : α := Classical.some h 
  have hg : g +ᵥ y = x := Classical.some_spec h 
  have this : stabilizer α x = (stabilizer α y).map (AddAut.conj g).toAddMonoidHom :=
    by 
      rw [←hg, stabilizer_vadd_eq_stabilizer_map_conj]
  (AddEquiv.addSubgroupCongr this).trans ((AddAut.conj g).addSubgroupEquivMap$ stabilizer α y).symm

end AddAction

namespace MulAction

variable[Groupₓ α][MulAction α β]

open QuotientGroup

/-- Action on left cosets. -/
@[toAdditive "Action on left cosets."]
def mul_left_cosets (H : Subgroup α) (x : α) (y : Quotientₓ H) : Quotientₓ H :=
  Quotientₓ.liftOn' y (fun y => QuotientGroup.mk ((x : α)*y))
    fun a b hab : _ ∈ H =>
      QuotientGroup.eq.2
        (by 
          rwa [mul_inv_rev, ←mul_assocₓ, mul_assocₓ (a⁻¹), inv_mul_selfₓ, mul_oneₓ])

@[toAdditive]
instance Quotientₓ (H : Subgroup α) : MulAction α (Quotientₓ H) :=
  { smul := mul_left_cosets H,
    one_smul :=
      fun a =>
        Quotientₓ.induction_on' a
          fun a =>
            QuotientGroup.eq.2
              (by 
                simp [Subgroup.one_mem]),
    mul_smul :=
      fun x y a =>
        Quotientₓ.induction_on' a
          fun a =>
            QuotientGroup.eq.2
              (by 
                simp [mul_inv_rev, Subgroup.one_mem, mul_assocₓ]) }

@[simp, toAdditive]
theorem quotient.smul_mk (H : Subgroup α) (a x : α) :
  (a • QuotientGroup.mk x : QuotientGroup.Quotient H) = QuotientGroup.mk (a*x) :=
  rfl

@[simp, toAdditive]
theorem quotient.smul_coe (H : Subgroup α) (a x : α) : (a • x : QuotientGroup.Quotient H) = «expr↑ » (a*x) :=
  rfl

@[toAdditive]
instance mul_left_cosets_comp_subtype_val (H I : Subgroup α) : MulAction I (Quotientₓ H) :=
  MulAction.compHom (Quotientₓ H) (Subgroup.subtype I)

variable(α){β}(x : β)

/-- The canonical map from the quotient of the stabilizer to the set. -/
@[toAdditive "The canonical map from the quotient of the stabilizer to the set. "]
def of_quotient_stabilizer (g : Quotientₓ (MulAction.stabilizer α x)) : β :=
  Quotientₓ.liftOn' g (· • x)$
    fun g1 g2 H =>
      calc g1 • x = g1 • (g1⁻¹*g2) • x := congr_argₓ _ H.symm 
        _ = g2 • x :=
        by 
          rw [smul_smul, mul_inv_cancel_left]
        

@[simp, toAdditive]
theorem of_quotient_stabilizer_mk (g : α) : of_quotient_stabilizer α x (QuotientGroup.mk g) = g • x :=
  rfl

@[toAdditive]
theorem of_quotient_stabilizer_mem_orbit g : of_quotient_stabilizer α x g ∈ orbit α x :=
  Quotientₓ.induction_on' g$ fun g => ⟨g, rfl⟩

@[toAdditive]
theorem of_quotient_stabilizer_smul (g : α) (g' : Quotientₓ (MulAction.stabilizer α x)) :
  of_quotient_stabilizer α x (g • g') = g • of_quotient_stabilizer α x g' :=
  Quotientₓ.induction_on' g'$ fun _ => mul_smul _ _ _

@[toAdditive]
theorem injective_of_quotient_stabilizer : Function.Injective (of_quotient_stabilizer α x) :=
  fun y₁ y₂ =>
    Quotientₓ.induction_on₂' y₁ y₂$
      fun g₁ g₂ H : g₁ • x = g₂ • x =>
        Quotientₓ.sound'$
          show (g₁⁻¹*g₂) • x = x by 
            rw [mul_smul, ←H, inv_smul_smul]

/-- Orbit-stabilizer theorem. -/
@[toAdditive "Orbit-stabilizer theorem."]
noncomputable def orbit_equiv_quotient_stabilizer (b : β) : orbit α b ≃ Quotientₓ (stabilizer α b) :=
  Equiv.symm$
    Equiv.ofBijective (fun g => ⟨of_quotient_stabilizer α b g, of_quotient_stabilizer_mem_orbit α b g⟩)
      ⟨fun x y hxy =>
          injective_of_quotient_stabilizer α b
            (by 
              convert congr_argₓ Subtype.val hxy),
        fun ⟨b, ⟨g, hgb⟩⟩ => ⟨g, Subtype.eq hgb⟩⟩

/-- Orbit-stabilizer theorem. -/
@[toAdditive "Orbit-stabilizer theorem."]
noncomputable def orbit_prod_stabilizer_equiv_group (b : β) : orbit α b × stabilizer α b ≃ α :=
  (Equiv.prodCongr (orbit_equiv_quotient_stabilizer α _) (Equiv.refl _)).trans
    Subgroup.groupEquivQuotientTimesSubgroup.symm

/-- Orbit-stabilizer theorem. -/
@[toAdditive "Orbit-stabilizer theorem."]
theorem card_orbit_mul_card_stabilizer_eq_card_group (b : β) [Fintype α] [Fintype$ orbit α b]
  [Fintype$ stabilizer α b] : (Fintype.card (orbit α b)*Fintype.card (stabilizer α b)) = Fintype.card α :=
  by 
    rw [←Fintype.card_prod, Fintype.card_congr (orbit_prod_stabilizer_equiv_group α b)]

@[simp, toAdditive]
theorem orbit_equiv_quotient_stabilizer_symm_apply (b : β) (a : α) :
  ((orbit_equiv_quotient_stabilizer α b).symm a : β) = a • b :=
  rfl

@[simp, toAdditive]
theorem stabilizer_quotient {G} [Groupₓ G] (H : Subgroup G) : MulAction.stabilizer G ((1 : G) : Quotientₓ H) = H :=
  by 
    ext 
    simp [QuotientGroup.eq]

variable(β)

local notation "Ω" => Quotientₓ$ orbit_rel α β

/-- **Class formula** : given `G` a group acting on `X` and `φ` a function mapping each orbit of `X`
under this action (that is, each element of the quotient of `X` by the relation `orbit_rel G X`) to
an element in this orbit, this gives a (noncomputable) bijection between `X` and the disjoint union
of `G/Stab(φ(ω))` over all orbits `ω`. In most cases you'll want `φ` to be `quotient.out'`, so we
provide `mul_action.self_equiv_sigma_orbits_quotient_stabilizer` as a special case. -/
@[toAdditive
      "**Class formula** : given `G` an additive group acting on `X` and `φ` a function\nmapping each orbit of `X` under this action (that is, each element of the quotient of `X` by the\nrelation `orbit_rel G X`) to an element in this orbit, this gives a (noncomputable) bijection\nbetween `X` and the disjoint union of `G/Stab(φ(ω))` over all orbits `ω`. In most cases you'll want\n`φ` to be `quotient.out'`, so we provide `add_action.self_equiv_sigma_orbits_quotient_stabilizer`\nas a special case. "]
noncomputable def self_equiv_sigma_orbits_quotient_stabilizer' {φ : Ω → β} (hφ : left_inverse Quotientₓ.mk' φ) :
  β ≃ Σω : Ω, Quotientₓ (stabilizer α (φ ω)) :=
  calc β ≃ Σω : Ω, orbit α (φ ω) := self_equiv_sigma_orbits' α β hφ 
    _ ≃ Σω : Ω, Quotientₓ (stabilizer α (φ ω)) := Equiv.sigmaCongrRight fun ω => orbit_equiv_quotient_stabilizer α (φ ω)
    

-- error in GroupTheory.GroupAction.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **Class formula** for a finite group acting on a finite type. See
`mul_action.card_eq_sum_card_group_div_card_stabilizer` for a specialized version using
`quotient.out'`. -/
@[to_additive #[expr "**Class formula** for a finite group acting on a finite type. See\n`add_action.card_eq_sum_card_add_group_div_card_stabilizer` for a specialized version using\n`quotient.out'`."]]
theorem card_eq_sum_card_group_div_card_stabilizer'
[fintype α]
[fintype β]
[fintype exprΩ()]
[∀ b : β, «expr $ »(fintype, stabilizer α b)]
{φ : exprΩ() → β}
(hφ : left_inverse quotient.mk' φ) : «expr = »(fintype.card β, «expr∑ , »((ω : exprΩ()), «expr / »(fintype.card α, fintype.card (stabilizer α (φ ω))))) :=
begin
  classical,
  have [] [":", expr ∀
   ω : exprΩ(), «expr = »(«expr / »(fintype.card α, fintype.card «expr↥ »(stabilizer α (φ ω))), fintype.card «expr $ »(quotient, stabilizer α (φ ω)))] [],
  { intro [ident ω],
    rw ["[", expr fintype.card_congr (@subgroup.group_equiv_quotient_times_subgroup α _ «expr $ »(stabilizer α, φ ω)), ",", expr fintype.card_prod, ",", expr nat.mul_div_cancel, "]"] [],
    exact [expr fintype.card_pos_iff.mpr (by apply_instance)] },
  simp_rw ["[", expr this, ",", "<-", expr fintype.card_sigma, ",", expr fintype.card_congr (self_equiv_sigma_orbits_quotient_stabilizer' α β hφ), "]"] []
end

/-- **Class formula**. This is a special case of
`mul_action.self_equiv_sigma_orbits_quotient_stabilizer'` with `φ = quotient.out'`. -/
@[toAdditive
      "**Class formula**. This is a special case of\n`add_action.self_equiv_sigma_orbits_quotient_stabilizer'` with `φ = quotient.out'`. "]
noncomputable def self_equiv_sigma_orbits_quotient_stabilizer : β ≃ Σω : Ω, Quotientₓ (stabilizer α ω.out') :=
  self_equiv_sigma_orbits_quotient_stabilizer' α β Quotientₓ.out_eq'

/-- **Class formula** for a finite group acting on a finite type. -/
@[toAdditive "**Class formula** for a finite group acting on a finite type."]
theorem card_eq_sum_card_group_div_card_stabilizer [Fintype α] [Fintype β] [Fintype Ω]
  [∀ b : β, Fintype$ stabilizer α b] : Fintype.card β = ∑ω : Ω, Fintype.card α / Fintype.card (stabilizer α ω.out') :=
  card_eq_sum_card_group_div_card_stabilizer' α β Quotientₓ.out_eq'

/-- **Burnside's lemma** : a (noncomputable) bijection between the disjoint union of all
`{x ∈ X | g • x = x}` for `g ∈ G` and the product `G × X/G`, where `G` is a group acting on `X` and
`X/G`denotes the quotient of `X` by the relation `orbit_rel G X`. -/
@[toAdditive
      "**Burnside's lemma** : a (noncomputable) bijection between the disjoint union of all\n`{x ∈ X | g • x = x}` for `g ∈ G` and the product `G × X/G`, where `G` is an additive group acting\non `X` and `X/G`denotes the quotient of `X` by the relation `orbit_rel G X`. "]
noncomputable def sigma_fixed_by_equiv_orbits_prod_group : (Σa : α, fixed_by α β a) ≃ Ω × α :=
  calc (Σa : α, fixed_by α β a) ≃ { ab : α × β // ab.1 • ab.2 = ab.2 } := (Equiv.subtypeProdEquivSigmaSubtype _).symm 
    _ ≃ { ba : β × α // ba.2 • ba.1 = ba.1 } := (Equiv.prodComm α β).subtypeEquiv fun ab => Iff.rfl 
    _ ≃ Σb : β, stabilizer α b := Equiv.subtypeProdEquivSigmaSubtype fun b : β a => a ∈ stabilizer α b 
    _ ≃ Σωb : Σω : Ω, orbit α ω.out', stabilizer α (ωb.2 : β) := (self_equiv_sigma_orbits α β).sigmaCongrLeft' 
    _ ≃ Σω : Ω, Σb : orbit α ω.out', stabilizer α (b : β) :=
    Equiv.sigmaAssoc fun ω : Ω b : orbit α ω.out' => stabilizer α (b : β)
    _ ≃ Σω : Ω, Σb : orbit α ω.out', stabilizer α ω.out' :=
    Equiv.sigmaCongrRight
      fun ω => Equiv.sigmaCongrRight$ fun ⟨b, hb⟩ => (stabilizer_equiv_stabilizer_of_orbit_rel hb).toEquiv 
    _ ≃ Σω : Ω, orbit α ω.out' × stabilizer α ω.out' := Equiv.sigmaCongrRight fun ω => Equiv.sigmaEquivProd _ _ 
    _ ≃ Σω : Ω, α := Equiv.sigmaCongrRight fun ω => orbit_prod_stabilizer_equiv_group α ω.out' 
    _ ≃ Ω × α := Equiv.sigmaEquivProd Ω α
    

/-- **Burnside's lemma** : given a finite group `G` acting on a set `X`, the average number of
elements fixed by each `g ∈ G` is the number of orbits. -/
@[toAdditive
      "**Burnside's lemma** : given a finite additive group `G` acting on a set `X`,\nthe average number of elements fixed by each `g ∈ G` is the number of orbits. "]
theorem sum_card_fixed_by_eq_card_orbits_mul_card_group [Fintype α] [∀ a, Fintype$ fixed_by α β a] [Fintype Ω] :
  (∑a : α, Fintype.card (fixed_by α β a)) = Fintype.card Ω*Fintype.card α :=
  by 
    rw [←Fintype.card_prod, ←Fintype.card_sigma, Fintype.card_congr (sigma_fixed_by_equiv_orbits_prod_group α β)]

@[toAdditive]
instance is_pretransitive_quotient G [Groupₓ G] (H : Subgroup G) : is_pretransitive G (QuotientGroup.Quotient H) :=
  { exists_smul_eq :=
      by 
        rintro ⟨x⟩ ⟨y⟩
        refine' ⟨y*x⁻¹, quotient_group.eq.mpr _⟩
        simp only [H.one_mem, mul_left_invₓ, inv_mul_cancel_right] }

end MulAction

section 

variable[Monoidₓ α][AddMonoidₓ β][DistribMulAction α β]

theorem List.smul_sum {r : α} {l : List β} : r • l.sum = (l.map ((· • ·) r)).Sum :=
  (DistribMulAction.toAddMonoidHom β r).map_list_sum l

/-- `smul` by a `k : M` over a ring is injective, if `k` is not a zero divisor.
The general theory of such `k` is elaborated by `is_smul_regular`.
The typeclass that restricts all terms of `M` to have this property is `no_zero_smul_divisors`. -/
theorem smul_cancel_of_non_zero_divisor {M R : Type _} [Monoidₓ M] [Ringₓ R] [DistribMulAction M R] (k : M)
  (h : ∀ x : R, k • x = 0 → x = 0) {a b : R} (h' : k • a = k • b) : a = b :=
  by 
    rw [←sub_eq_zero]
    refine' h _ _ 
    rw [smul_sub, h', sub_self]

end 

section 

variable[Monoidₓ α][Monoidₓ β][MulDistribMulAction α β]

theorem List.smul_prod {r : α} {l : List β} : r • l.prod = (l.map ((· • ·) r)).Prod :=
  (MulDistribMulAction.toMonoidHom β r).map_list_prod l

end 

section 

variable[Monoidₓ α][AddCommMonoidₓ β][DistribMulAction α β]

theorem Multiset.smul_sum {r : α} {s : Multiset β} : r • s.sum = (s.map ((· • ·) r)).Sum :=
  (DistribMulAction.toAddMonoidHom β r).map_multiset_sum s

theorem Finset.smul_sum {r : α} {f : γ → β} {s : Finset γ} : (r • ∑x in s, f x) = ∑x in s, r • f x :=
  (DistribMulAction.toAddMonoidHom β r).map_sum f s

end 

section 

variable[Monoidₓ α][CommMonoidₓ β][MulDistribMulAction α β]

theorem Multiset.smul_prod {r : α} {s : Multiset β} : r • s.prod = (s.map ((· • ·) r)).Prod :=
  (MulDistribMulAction.toMonoidHom β r).map_multiset_prod s

theorem Finset.smul_prod {r : α} {f : γ → β} {s : Finset γ} : (r • ∏x in s, f x) = ∏x in s, r • f x :=
  (MulDistribMulAction.toMonoidHom β r).map_prod f s

end 

namespace Subgroup

variable{G : Type _}[Groupₓ G](H : Subgroup G)

theorem normal_core_eq_ker : H.normal_core = (MulAction.toPermHom G (QuotientGroup.Quotient H)).ker :=
  by 
    refine'
      le_antisymmₓ
        (fun g hg =>
          Equiv.Perm.ext
            fun q =>
              QuotientGroup.induction_on q
                fun g' => (MulAction.quotient.smul_mk H g g').trans (quotient_group.eq.mpr _))
        (subgroup.normal_le_normal_core.mpr fun g hg => _)
    ·
      rw [mul_inv_rev, ←inv_invₓ g', inv_invₓ]
      exact H.normal_core.inv_mem hg (g'⁻¹)
    ·
      rw [←H.inv_mem_iff, ←mul_oneₓ (g⁻¹), ←QuotientGroup.eq, ←mul_oneₓ g]
      exact (MulAction.quotient.smul_mk H g 1).symm.trans (equiv.perm.ext_iff.mp hg (1 : G))

noncomputable instance fintype_quotient_normal_core [Fintype (QuotientGroup.Quotient H)] :
  Fintype (QuotientGroup.Quotient H.normal_core) :=
  by 
    rw [H.normal_core_eq_ker]
    classical 
    exact Fintype.ofEquiv _ (QuotientGroup.quotientKerEquivRange _).symm.toEquiv

end Subgroup

