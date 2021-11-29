import Mathbin.Algebra.MonoidAlgebra.Basic 
import Mathbin.Algebra.CharP.Invertible 
import Mathbin.Algebra.Regular.Basic 
import Mathbin.LinearAlgebra.Basis

/-!
# Maschke's theorem

We prove **Maschke's theorem** for finite groups,
in the formulation that every submodule of a `k[G]` module has a complement,
when `k` is a field with `invertible (fintype.card G : k)`.

We do the core computation in greater generality.
For any `[comm_ring k]` in which  `[invertible (fintype.card G : k)]`,
and a `k[G]`-linear map `i : V → W` which admits a `k`-linear retraction `π`,
we produce a `k[G]`-linear retraction by
taking the average over `G` of the conjugates of `π`.

## Implementation Notes
* These results assume `invertible (fintype.card G : k)` which is equivalent to the more
familiar `¬(ring_char k ∣ fintype.card G)`. It is possible to convert between them using
`invertible_of_ring_char_not_dvd` and `not_ring_char_dvd_of_invertible`.


## Future work
It's not so far to give the usual statement, that every finite dimensional representation
of a finite group is semisimple (i.e. a direct sum of irreducibles).
-/


universe u

noncomputable theory

open Module

open MonoidAlgebra

open_locale BigOperators

section 

variable{k : Type u}[CommRingₓ k]{G : Type u}[Groupₓ G]

variable{V : Type u}[AddCommGroupₓ V][Module k V][Module (MonoidAlgebra k G) V]

variable[IsScalarTower k (MonoidAlgebra k G) V]

variable{W : Type u}[AddCommGroupₓ W][Module k W][Module (MonoidAlgebra k G) W]

variable[IsScalarTower k (MonoidAlgebra k G) W]

/-!
We now do the key calculation in Maschke's theorem.

Given `V → W`, an inclusion of `k[G]` modules,,
assume we have some retraction `π` (i.e. `∀ v, π (i v) = v`),
just as a `k`-linear map.
(When `k` is a field, this will be available cheaply, by choosing a basis.)

We now construct a retraction of the inclusion as a `k[G]`-linear map,
by the formula
$$ \frac{1}{|G|} \sum_{g \in G} g⁻¹ • π(g • -). $$
-/


namespace LinearMap

variable(π : W →ₗ[k] V)

include π

/--
We define the conjugate of `π` by `g`, as a `k`-linear map.
-/
def conjugate (g : G) : W →ₗ[k] V :=
  ((group_smul.linear_map k V (g⁻¹)).comp π).comp (group_smul.linear_map k W g)

variable(i : V →ₗ[MonoidAlgebra k G] W)(h : ∀ (v : V), π (i v) = v)

section 

include h

theorem conjugate_i (g : G) (v : V) : (conjugate π g) (i v) = v :=
  by 
    dsimp [conjugate]
    simp only [←i.map_smul, h, ←mul_smul, single_mul_single, mul_oneₓ, mul_left_invₓ]
    change (1 : MonoidAlgebra k G) • v = v 
    simp 

end 

variable(G)[Fintype G]

/--
The sum of the conjugates of `π` by each element `g : G`, as a `k`-linear map.

(We postpone dividing by the size of the group as long as possible.)
-/
def sum_of_conjugates : W →ₗ[k] V :=
  ∑g : G, π.conjugate g

/--
In fact, the sum over `g : G` of the conjugate of `π` by `g` is a `k[G]`-linear map.
-/
def sum_of_conjugates_equivariant : W →ₗ[MonoidAlgebra k G] V :=
  MonoidAlgebra.equivariantOfLinearOfComm (π.sum_of_conjugates G)
    fun g v =>
      by 
        dsimp [sum_of_conjugates]
        simp only [LinearMap.sum_apply, Finset.smul_sum]
        dsimp [conjugate]
        convLHS => rw [←Finset.univ_map_embedding (mulRightEmbedding (g⁻¹))]simp only [mulRightEmbedding]
        simp only [←mul_smul, single_mul_single, mul_inv_rev, mul_oneₓ, Function.Embedding.coe_fn_mk, Finset.sum_map,
          inv_invₓ, inv_mul_cancel_right]
        recover

section 

variable[inv : Invertible (Fintype.card G : k)]

include inv

/--
We construct our `k[G]`-linear retraction of `i` as
$$ \frac{1}{|G|} \sum_{g \in G} g⁻¹ • π(g • -). $$
-/
def equivariant_projection : W →ₗ[MonoidAlgebra k G] V :=
  ⅟ (Fintype.card G : k) • π.sum_of_conjugates_equivariant G

include h

theorem equivariant_projection_condition (v : V) : (π.equivariant_projection G) (i v) = v :=
  by 
    rw [equivariant_projection, smul_apply, sum_of_conjugates_equivariant, equivariant_of_linear_of_comm_apply,
      sum_of_conjugates]
    rw [LinearMap.sum_apply]
    simp only [conjugate_i π i h]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_smul_cast k, ←mul_smul, Invertible.inv_of_mul_self, one_smul]

end 

end LinearMap

end 

namespace CharZero

variable{k : Type u}[Field k]{G : Type u}[Fintype G][Groupₓ G][CharZero k]

instance  : Invertible (Fintype.card G : k) :=
  invertibleOfRingCharNotDvd
    (by 
      simp [Fintype.card_eq_zero_iff])

end CharZero

namespace MonoidAlgebra

variable{k : Type u}[Field k]{G : Type u}[Fintype G][Invertible (Fintype.card G : k)]

variable[Groupₓ G]

variable{V : Type u}[AddCommGroupₓ V][Module k V][Module (MonoidAlgebra k G) V]

variable[IsScalarTower k (MonoidAlgebra k G) V]

variable{W : Type u}[AddCommGroupₓ W][Module k W][Module (MonoidAlgebra k G) W]

variable[IsScalarTower k (MonoidAlgebra k G) W]

-- error in RepresentationTheory.Maschke: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_left_inverse_of_injective
(f : «expr →ₗ[ ] »(V, monoid_algebra k G, W))
(hf : «expr = »(f.ker, «expr⊥»())) : «expr∃ , »((g : «expr →ₗ[ ] »(W, monoid_algebra k G, V)), «expr = »(g.comp f, linear_map.id)) :=
begin
  obtain ["⟨", ident φ, ",", ident hφ, "⟩", ":=", expr (f.restrict_scalars k).exists_left_inverse_of_injective (by simp [] [] ["only"] ["[", expr hf, ",", expr submodule.restrict_scalars_bot, ",", expr linear_map.ker_restrict_scalars, "]"] [] [])],
  refine [expr ⟨φ.equivariant_projection G, _⟩],
  apply [expr linear_map.ext],
  intro [ident v],
  simp [] [] ["only"] ["[", expr linear_map.id_coe, ",", expr id.def, ",", expr linear_map.comp_apply, "]"] [] [],
  apply [expr linear_map.equivariant_projection_condition],
  intro [ident v],
  have [] [] [":=", expr congr_arg linear_map.to_fun hφ],
  exact [expr congr_fun this v]
end

namespace Submodule

theorem exists_is_compl (p : Submodule (MonoidAlgebra k G) V) : ∃ q : Submodule (MonoidAlgebra k G) V, IsCompl p q :=
  let ⟨f, hf⟩ := MonoidAlgebra.exists_left_inverse_of_injective p.subtype p.ker_subtype
  ⟨f.ker, LinearMap.is_compl_of_proj$ LinearMap.ext_iff.1 hf⟩

/-- This also implies an instance `is_semisimple_module (monoid_algebra k G) V`. -/
instance IsComplemented : IsComplemented (Submodule (MonoidAlgebra k G) V) :=
  ⟨exists_is_compl⟩

end Submodule

end MonoidAlgebra

