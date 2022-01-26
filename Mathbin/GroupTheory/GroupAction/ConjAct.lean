import Mathbin.GroupTheory.GroupAction.Basic
import Mathbin.GroupTheory.Subgroup.Basic

/-!
# Conjugation action of a group on itself

This file defines the conjugation action of a group on itself. See also `mul_aut.conj` for
the definition of conjugation as a homomorphism into the automorphism group.

## Main definitions

A type alias `conj_act G` is introduced for a group `G`. The group `conj_act G` acts on `G`
by conjugation. The group `conj_act G` also acts on any normal subgroup of `G` by conjugation.

## Implementation Notes

The scalar action in defined in this file can also be written using `mul_aut.conj g • h`. This
has the advantage of not using the type alias `conj_act`, but the downside of this approach
is that some theorems about the group actions will not apply when since this
`mul_aut.conj g • h` describes an action of `mul_aut G` on `G`, and not an action of `G`.

-/


variable (G : Type _)

/-- A type alias for a group `G`. `conj_act G` acts on `G` by conjugation -/
def ConjAct : Type _ :=
  G

namespace ConjAct

open MulAction Subgroup

variable {G}

instance : ∀ [Groupₓ G], Groupₓ (ConjAct G) :=
  id

instance : ∀ [DivInvMonoidₓ G], DivInvMonoidₓ (ConjAct G) :=
  id

instance : ∀ [GroupWithZeroₓ G], GroupWithZeroₓ (ConjAct G) :=
  id

instance : ∀ [Fintype G], Fintype (ConjAct G) :=
  id

@[simp]
theorem card [Fintype G] : Fintype.card (ConjAct G) = Fintype.card G :=
  rfl

section DivInvMonoidₓ

variable [DivInvMonoidₓ G]

instance : Inhabited (ConjAct G) :=
  ⟨1⟩

/-- Reinterpret `g : conj_act G` as an element of `G`. -/
def of_conj_act : ConjAct G ≃* G :=
  ⟨id, id, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

/-- Reinterpret `g : G` as an element of `conj_act G`. -/
def to_conj_act : G ≃* ConjAct G :=
  of_conj_act.symm

/-- A recursor for `conj_act`, for use as `induction x using conj_act.rec` when `x : conj_act G`. -/
protected def rec {C : ConjAct G → Sort _} (h : ∀ g, C (to_conj_act g)) : ∀ g, C g :=
  h

@[simp]
theorem of_mul_symm_eq : (@of_conj_act G _).symm = to_conj_act :=
  rfl

@[simp]
theorem to_mul_symm_eq : (@to_conj_act G _).symm = of_conj_act :=
  rfl

@[simp]
theorem to_conj_act_of_conj_act (x : ConjAct G) : to_conj_act (of_conj_act x) = x :=
  rfl

@[simp]
theorem of_conj_act_to_conj_act (x : G) : of_conj_act (to_conj_act x) = x :=
  rfl

@[simp]
theorem of_conj_act_one : of_conj_act (1 : ConjAct G) = 1 :=
  rfl

@[simp]
theorem to_conj_act_one : to_conj_act (1 : G) = 1 :=
  rfl

@[simp]
theorem of_conj_act_inv (x : ConjAct G) : of_conj_act x⁻¹ = (of_conj_act x)⁻¹ :=
  rfl

@[simp]
theorem to_conj_act_inv (x : G) : to_conj_act x⁻¹ = (to_conj_act x)⁻¹ :=
  rfl

@[simp]
theorem of_conj_act_mul (x y : ConjAct G) : of_conj_act (x * y) = of_conj_act x * of_conj_act y :=
  rfl

@[simp]
theorem to_conj_act_mul (x y : G) : to_conj_act (x * y) = to_conj_act x * to_conj_act y :=
  rfl

instance : HasScalar (ConjAct G) G where
  smul := fun g h => of_conj_act g * h * (of_conj_act g)⁻¹

theorem smul_def (g : ConjAct G) (h : G) : g • h = of_conj_act g * h * (of_conj_act g)⁻¹ :=
  rfl

@[simp]
theorem forall (p : ConjAct G → Prop) : (∀ x : ConjAct G, p x) ↔ ∀ x : G, p (to_conj_act x) :=
  Iff.rfl

end DivInvMonoidₓ

section GroupWithZeroₓ

variable [GroupWithZeroₓ G]

@[simp]
theorem of_conj_act_zero : of_conj_act (0 : ConjAct G) = 0 :=
  rfl

@[simp]
theorem to_conj_act_zero : to_conj_act (0 : G) = 0 :=
  rfl

instance : MulAction (ConjAct G) G where
  smul := · • ·
  one_smul := by
    simp [smul_def]
  mul_smul := by
    simp [smul_def, mul_assoc, mul_inv_rev₀]

end GroupWithZeroₓ

variable [Groupₓ G]

instance : MulDistribMulAction (ConjAct G) G where
  smul := · • ·
  smul_mul := by
    simp [smul_def, mul_assoc]
  smul_one := by
    simp [smul_def]
  one_smul := by
    simp [smul_def]
  mul_smul := by
    simp [smul_def, mul_assoc]

theorem smul_eq_mul_aut_conj (g : ConjAct G) (h : G) : g • h = MulAut.conj (of_conj_act g) h :=
  rfl

/-- The set of fixed points of the conjugation action of `G` on itself is the center of `G`. -/
theorem fixed_points_eq_center : fixed_points (ConjAct G) G = center G := by
  ext x
  simp [mem_center_iff, smul_def, mul_inv_eq_iff_eq_mul]

/-- As normal subgroups are closed under conjugation, they inherit the conjugation action
  of the underlying group. -/
instance subgroup.conj_action {H : Subgroup G} [hH : H.normal] : HasScalar (ConjAct G) H :=
  ⟨fun g h => ⟨g • h, hH.conj_mem h.1 h.2 (of_conj_act g)⟩⟩

theorem subgroup.coe_conj_smul {H : Subgroup G} [hH : H.normal] (g : ConjAct G) (h : H) : ↑(g • h) = g • (h : G) :=
  rfl

instance subgroup.conj_mul_distrib_mul_action {H : Subgroup G} [hH : H.normal] : MulDistribMulAction (ConjAct G) H :=
  Subtype.coe_injective.MulDistribMulAction H.subtype subgroup.coe_conj_smul

/-- Group conjugation on a normal subgroup. Analogous to `mul_aut.conj`. -/
def _root_.mul_aut.conj_normal {H : Subgroup G} [hH : H.normal] : G →* MulAut H :=
  (MulDistribMulAction.toMulAut (ConjAct G) H).comp to_conj_act.toMonoidHom

@[simp]
theorem _root_.mul_aut.conj_normal_apply {H : Subgroup G} [H.normal] (g : G) (h : H) :
    ↑(MulAut.conjNormal g h) = g * h * g⁻¹ :=
  rfl

@[simp]
theorem _root_.mul_aut.conj_normal_symm_apply {H : Subgroup G} [H.normal] (g : G) (h : H) :
    ↑((MulAut.conjNormal g).symm h) = g⁻¹ * h * g := by
  change _ * _⁻¹⁻¹ = _
  rw [inv_invₓ]
  rfl

@[simp]
theorem _root_.mul_aut.conj_normal_inv_apply {H : Subgroup G} [H.normal] (g : G) (h : H) :
    ↑((MulAut.conjNormal g)⁻¹ h) = g⁻¹ * h * g :=
  MulAut.conj_normal_symm_apply g h

theorem _root_.mul_aut.conj_normal_coe {H : Subgroup G} [H.normal] {h : H} : MulAut.conjNormal ↑h = MulAut.conj h :=
  MulEquiv.ext fun x => rfl

instance normal_of_characteristic_of_normal {H : Subgroup G} [hH : H.normal] {K : Subgroup H} [h : K.characteristic] :
    (K.map H.subtype).Normal :=
  ⟨fun a ha b => by
    obtain ⟨a, ha, rfl⟩ := ha
    exact K.apply_coe_mem_map H.subtype ⟨_, (set_like.ext_iff.mp (h.fixed (MulAut.conjNormal b)) a).mpr ha⟩⟩

end ConjAct

