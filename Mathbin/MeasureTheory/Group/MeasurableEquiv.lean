import Mathbin.MeasureTheory.Group.Arithmetic

/-!
# (Scalar) multiplication and (vector) addition as measurable equivalences

In this file we define the following measurable equivalences:

* `measurable_equiv.smul`: if a group `G` acts on `α` by measurable maps, then each element `c : G`
  defines a measurable automorphism of `α`;
* `measurable_equiv.vadd`: additive version of `measurable_equiv.smul`;
* `measurable_equiv.smul₀`: if a group with zero `G` acts on `α` by measurable maps, then each
  nonzero element `c : G` defines a measurable automorphism of `α`;
* `measurable_equiv.mul_left`: if `G` is a group with measurable multiplication, then left
  multiplication by `g : G` is a measurable automorphism of `G`;
* `measurable_equiv.add_left`: additive version of `measurable_equiv.mul_left`;
* `measurable_equiv.mul_right`: if `G` is a group with measurable multiplication, then right
  multiplication by `g : G` is a measurable automorphism of `G`;
* `measurable_equiv.add_right`: additive version of `measurable_equiv.mul_right`;
* `measurable_equiv.mul_left₀`, `measurable_equiv.mul_right₀`: versions of
  `measurable_equiv.mul_left` and `measurable_equiv.mul_right` for groups with zero;
* `measurable_equiv.inv`, `measurable_equiv.inv₀`: `has_inv.inv` as a measurable automorphism
  of a group (or a group with zero);
* `measurable_equiv.neg`: negation as a measurable automorphism of an additive group.

We also deduce that the corresponding maps are measurable embeddings.

## Tags

measurable, equivalence, group action
-/


namespace MeasurableEquiv

variable {G G₀ α : Type _} [MeasurableSpace G] [MeasurableSpace G₀] [MeasurableSpace α] [Groupₓ G] [GroupWithZeroₓ G₀]
  [MulAction G α] [MulAction G₀ α] [HasMeasurableSmul G α] [HasMeasurableSmul G₀ α]

/-- If a group `G` acts on `α` by measurable maps, then each element `c : G` defines a measurable
automorphism of `α`. -/
@[toAdditive
      "If an additive group `G` acts on `α` by measurable maps, then each element `c : G`\ndefines a measurable automorphism of `α`.",
  simps (config := { fullyApplied := ff }) toEquiv apply]
def smul (c : G) : α ≃ᵐ α :=
  { toEquiv := MulAction.toPerm c, measurable_to_fun := measurable_const_smul c,
    measurable_inv_fun := measurable_const_smul (c⁻¹) }

@[toAdditive]
theorem _root_.measurable_embedding_const_smul (c : G) : MeasurableEmbedding ((· • ·) c : α → α) :=
  (smul c).MeasurableEmbedding

@[simp, toAdditive]
theorem symm_smul (c : G) : (smul c : α ≃ᵐ α).symm = smul (c⁻¹) :=
  ext rfl

/-- If a group with zero `G₀` acts on `α` by measurable maps, then each nonzero element `c : G₀`
defines a measurable automorphism of `α` -/
def smul₀ (c : G₀) (hc : c ≠ 0) : α ≃ᵐ α :=
  MeasurableEquiv.smul (Units.mk0 c hc)

@[simp]
theorem coe_smul₀ {c : G₀} (hc : c ≠ 0) : «expr⇑ » (smul₀ c hc : α ≃ᵐ α) = (· • ·) c :=
  rfl

@[simp]
theorem symm_smul₀ {c : G₀} (hc : c ≠ 0) : (smul₀ c hc : α ≃ᵐ α).symm = smul₀ (c⁻¹) (inv_ne_zero hc) :=
  ext rfl

theorem _root_.measurable_embedding_const_smul₀ {c : G₀} (hc : c ≠ 0) : MeasurableEmbedding ((· • ·) c : α → α) :=
  (smul₀ c hc).MeasurableEmbedding

section Mul

variable [HasMeasurableMul G] [HasMeasurableMul G₀]

/-- If `G` is a group with measurable multiplication, then left multiplication by `g : G` is a
measurable automorphism of `G`. -/
@[toAdditive
      "If `G` is an additive group with measurable addition, then addition of `g : G`\non the left is a measurable automorphism of `G`."]
def mul_left (g : G) : G ≃ᵐ G :=
  smul g

@[simp, toAdditive]
theorem coe_mul_left (g : G) : «expr⇑ » (mul_left g) = (·*·) g :=
  rfl

@[simp, toAdditive]
theorem symm_mul_left (g : G) : (mul_left g).symm = mul_left (g⁻¹) :=
  ext rfl

@[simp, toAdditive]
theorem to_equiv_mul_left (g : G) : (mul_left g).toEquiv = Equiv.mulLeft g :=
  rfl

@[toAdditive]
theorem _root_.measurable_embedding_mul_left (g : G) : MeasurableEmbedding ((·*·) g) :=
  (mul_left g).MeasurableEmbedding

/-- If `G` is a group with measurable multiplication, then right multiplication by `g : G` is a
measurable automorphism of `G`. -/
@[toAdditive
      "If `G` is an additive group with measurable addition, then addition of `g : G`\non the right is a measurable automorphism of `G`."]
def mul_right (g : G) : G ≃ᵐ G :=
  { toEquiv := Equiv.mulRight g, measurable_to_fun := measurable_mul_const g,
    measurable_inv_fun := measurable_mul_const (g⁻¹) }

@[toAdditive]
theorem _root_.measurable_embedding_mul_right (g : G) : MeasurableEmbedding fun x => x*g :=
  (mul_right g).MeasurableEmbedding

@[simp, toAdditive]
theorem coe_mul_right (g : G) : «expr⇑ » (mul_right g) = fun x => x*g :=
  rfl

@[simp, toAdditive]
theorem symm_mul_right (g : G) : (mul_right g).symm = mul_right (g⁻¹) :=
  ext rfl

@[simp, toAdditive]
theorem to_equiv_mul_right (g : G) : (mul_right g).toEquiv = Equiv.mulRight g :=
  rfl

/-- If `G₀` is a group with zero with measurable multiplication, then left multiplication by a
nonzero element `g : G₀` is a measurable automorphism of `G₀`. -/
def mul_left₀ (g : G₀) (hg : g ≠ 0) : G₀ ≃ᵐ G₀ :=
  smul₀ g hg

theorem _root_.measurable_embedding_mul_left₀ {g : G₀} (hg : g ≠ 0) : MeasurableEmbedding ((·*·) g) :=
  (mul_left₀ g hg).MeasurableEmbedding

@[simp]
theorem coe_mul_left₀ {g : G₀} (hg : g ≠ 0) : «expr⇑ » (mul_left₀ g hg) = (·*·) g :=
  rfl

@[simp]
theorem symm_mul_left₀ {g : G₀} (hg : g ≠ 0) : (mul_left₀ g hg).symm = mul_left₀ (g⁻¹) (inv_ne_zero hg) :=
  ext rfl

@[simp]
theorem to_equiv_mul_left₀ {g : G₀} (hg : g ≠ 0) : (mul_left₀ g hg).toEquiv = Equiv.mulLeft₀ g hg :=
  rfl

/-- If `G₀` is a group with zero with measurable multiplication, then right multiplication by a
nonzero element `g : G₀` is a measurable automorphism of `G₀`. -/
def mul_right₀ (g : G₀) (hg : g ≠ 0) : G₀ ≃ᵐ G₀ :=
  { toEquiv := Equiv.mulRight₀ g hg, measurable_to_fun := measurable_mul_const g,
    measurable_inv_fun := measurable_mul_const (g⁻¹) }

theorem _root_.measurable_embedding_mul_right₀ {g : G₀} (hg : g ≠ 0) : MeasurableEmbedding fun x => x*g :=
  (mul_right₀ g hg).MeasurableEmbedding

@[simp]
theorem coe_mul_right₀ {g : G₀} (hg : g ≠ 0) : «expr⇑ » (mul_right₀ g hg) = fun x => x*g :=
  rfl

@[simp]
theorem symm_mul_right₀ {g : G₀} (hg : g ≠ 0) : (mul_right₀ g hg).symm = mul_right₀ (g⁻¹) (inv_ne_zero hg) :=
  ext rfl

@[simp]
theorem to_equiv_mul_right₀ {g : G₀} (hg : g ≠ 0) : (mul_right₀ g hg).toEquiv = Equiv.mulRight₀ g hg :=
  rfl

end Mul

variable (G G₀)

/-- Inversion as a measurable automorphism of a group. -/
@[toAdditive "Negation as a measurable automorphism of an additive group.",
  simps (config := { fullyApplied := ff }) toEquiv apply]
def inv [HasMeasurableInv G] : G ≃ᵐ G :=
  { toEquiv := Equiv.inv G, measurable_to_fun := measurable_inv, measurable_inv_fun := measurable_inv }

/-- Inversion as a measurable automorphism of a group with zero. -/
@[simps (config := { fullyApplied := ff }) toEquiv apply]
def inv₀ [HasMeasurableInv G₀] : G₀ ≃ᵐ G₀ :=
  { toEquiv := Equiv.inv₀ G₀, measurable_to_fun := measurable_inv, measurable_inv_fun := measurable_inv }

variable {G G₀}

@[simp]
theorem symm_inv [HasMeasurableInv G] : (inv G).symm = inv G :=
  rfl

@[simp]
theorem symm_inv₀ [HasMeasurableInv G₀] : (inv₀ G₀).symm = inv₀ G₀ :=
  rfl

end MeasurableEquiv

