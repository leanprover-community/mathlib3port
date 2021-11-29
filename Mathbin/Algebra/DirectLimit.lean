import Mathbin.Data.Finset.Order 
import Mathbin.Algebra.DirectSum.Module 
import Mathbin.RingTheory.FreeCommRing 
import Mathbin.RingTheory.Ideal.Operations

/-!
# Direct limit of modules, abelian groups, rings, and fields.

See Atiyah-Macdonald PP.32-33, Matsumura PP.269-270

Generalizes the notion of "union", or "gluing", of incomparable modules over the same ring,
or incomparable abelian groups, or rings, or fields.

It is constructed as a quotient of the free module (for the module case) or quotient of
the free commutative ring (for the ring case) instead of a quotient of the disjoint union
so as to make the operations (addition etc.) "computable".

-/


universe u v w u₁

open Submodule

variable {R : Type u} [Ringₓ R]

variable {ι : Type v}

variable [dec_ι : DecidableEq ι] [DirectedOrder ι]

variable (G : ι → Type w)

/-- A directed system is a functor from the category (directed poset) to another category.
This is used for abelian groups and rings and fields because their maps are not bundled.
See module.directed_system -/
class DirectedSystem (f : ∀ i j, i ≤ j → G i → G j) : Prop where 
  map_self{} : ∀ i x h, f i i h x = x 
  map_map{} : ∀ i j k hij hjk x, f j k hjk (f i j hij x) = f i k (le_transₓ hij hjk) x

namespace Module

variable [∀ i, AddCommGroupₓ (G i)] [∀ i, Module R (G i)]

/-- A directed system is a functor from the category (directed poset) to the category of
`R`-modules. -/
class DirectedSystem (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) : Prop where 
  map_self{} : ∀ i x h, f i i h x = x 
  map_map{} : ∀ i j k hij hjk x, f j k hjk (f i j hij x) = f i k (le_transₓ hij hjk) x

variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

include dec_ι

/-- The direct limit of a directed system is the modules glued together along the maps. -/
def direct_limit : Type max v w :=
  (span R$
      { a | ∃ (i j : _)(H : i ≤ j)(x : _), DirectSum.lof R ι G i x - DirectSum.lof R ι G j (f i j H x) = a }).Quotient

namespace DirectLimit

instance : AddCommGroupₓ (direct_limit G f) :=
  quotient.add_comm_group _

instance : Module R (direct_limit G f) :=
  quotient.module _

instance : Inhabited (direct_limit G f) :=
  ⟨0⟩

variable (R ι)

/-- The canonical map from a component to the direct limit. -/
def of i : G i →ₗ[R] direct_limit G f :=
  (mkq _).comp$ DirectSum.lof R ι G i

variable {R ι G f}

@[simp]
theorem of_f {i j hij x} : of R ι G f j (f i j hij x) = of R ι G f i x :=
  Eq.symm$ (Submodule.Quotient.eq _).2$ subset_span ⟨i, j, hij, x, rfl⟩

/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
theorem exists_of [Nonempty ι] (z : direct_limit G f) : ∃ i x, of R ι G f i x = z :=
  Nonempty.elimₓ
      (by 
        infer_instance)$
    fun ind : ι =>
      Quotientₓ.induction_on' z$
        fun z =>
          DirectSum.induction_on z ⟨ind, 0, LinearMap.map_zero _⟩ (fun i x => ⟨i, x, rfl⟩)
            fun p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩ =>
              let ⟨k, hik, hjk⟩ := DirectedOrder.directed i j
              ⟨k, f i k hik x+f j k hjk y,
                by 
                  rw [LinearMap.map_add, of_f, of_f, ihx, ihy] <;> rfl⟩

@[elab_as_eliminator]
protected theorem induction_on [Nonempty ι] {C : direct_limit G f → Prop} (z : direct_limit G f)
  (ih : ∀ i x, C (of R ι G f i x)) : C z :=
  let ⟨i, x, h⟩ := exists_of z 
  h ▸ ih i x

variable {P : Type u₁} [AddCommGroupₓ P] [Module R P] (g : ∀ i, G i →ₗ[R] P)

variable (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

include Hg

variable (R ι G f)

/-- The universal property of the direct limit: maps from the components to another module
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift : direct_limit G f →ₗ[R] P :=
  liftq _ (DirectSum.toModule R ι P g)
    (span_le.2$
      fun a ⟨i, j, hij, x, hx⟩ =>
        by 
          rw [←hx, SetLike.mem_coe, LinearMap.sub_mem_ker_iff, DirectSum.to_module_lof, DirectSum.to_module_lof, Hg])

variable {R ι G f}

omit Hg

theorem lift_of {i} x : lift R ι G f g Hg (of R ι G f i x) = g i x :=
  DirectSum.to_module_lof R _ _

theorem lift_unique [Nonempty ι] (F : direct_limit G f →ₗ[R] P) x :
  F x =
    lift R ι G f (fun i => F.comp$ of R ι G f i)
      (fun i j hij x =>
        by 
          rw [LinearMap.comp_apply, of_f] <;> rfl)
      x :=
  direct_limit.induction_on x$
    fun i x =>
      by 
        rw [lift_of] <;> rfl

section Totalize

open_locale Classical

variable (G f)

omit dec_ι

/-- `totalize G f i j` is a linear map from `G i` to `G j`, for *every* `i` and `j`.
If `i ≤ j`, then it is the map `f i j` that comes with the directed system `G`,
and otherwise it is the zero map. -/
noncomputable def totalize : ∀ i j, G i →ₗ[R] G j :=
  fun i j => if h : i ≤ j then f i j h else 0

variable {G f}

theorem totalize_apply i j x : totalize G f i j x = if h : i ≤ j then f i j h x else 0 :=
  if h : i ≤ j then
    by 
      dsimp only [totalize] <;> rw [dif_pos h, dif_pos h]
  else
    by 
      dsimp only [totalize] <;> rw [dif_neg h, dif_neg h, LinearMap.zero_apply]

end Totalize

variable [DirectedSystem G f]

open_locale Classical

theorem to_module_totalize_of_le {x : DirectSum ι G} {i j : ι} (hij : i ≤ j) (hx : ∀ k _ : k ∈ x.support, k ≤ i) :
  DirectSum.toModule R ι (G j) (fun k => totalize G f k j) x =
    f i j hij (DirectSum.toModule R ι (G i) (fun k => totalize G f k i) x) :=
  by 
    rw [←@Dfinsupp.sum_single ι G _ _ _ x]
    unfold Dfinsupp.sum 
    simp only [LinearMap.map_sum]
    refine' Finset.sum_congr rfl fun k hk => _ 
    rw [DirectSum.single_eq_lof R k (x k)]
    simp [totalize_apply, hx k hk, le_transₓ (hx k hk) hij, DirectedSystem.map_map f]

theorem of.zero_exact_aux [Nonempty ι] {x : DirectSum ι G} (H : Submodule.Quotient.mk x = (0 : direct_limit G f)) :
  ∃ j, (∀ k _ : k ∈ x.support, k ≤ j) ∧ DirectSum.toModule R ι (G j) (fun i => totalize G f i j) x = (0 : G j) :=
  Nonempty.elimₓ
      (by 
        infer_instance)$
    fun ind : ι =>
      span_induction ((quotient.mk_eq_zero _).1 H)
        (fun x ⟨i, j, hij, y, hxy⟩ =>
          let ⟨k, hik, hjk⟩ := DirectedOrder.directed i j
          ⟨k,
            by 
              clear_ 
              subst hxy 
              split 
              ·
                intro i0 hi0 
                rw [Dfinsupp.mem_support_iff, DirectSum.sub_apply, ←DirectSum.single_eq_lof, ←DirectSum.single_eq_lof,
                  Dfinsupp.single_apply, Dfinsupp.single_apply] at hi0 
                splitIfs  at hi0 with hi hj hj
                ·
                  rwa [hi] at hik
                ·
                  rwa [hi] at hik
                ·
                  rwa [hj] at hjk 
                exfalso 
                apply hi0 
                rw [sub_zero]
              simp [LinearMap.map_sub, totalize_apply, hik, hjk, DirectedSystem.map_map f, DirectSum.apply_eq_component,
                DirectSum.component.of]⟩)
        ⟨ind, fun _ h => (Finset.not_mem_empty _ h).elim, LinearMap.map_zero _⟩
        (fun x y ⟨i, hi, hxi⟩ ⟨j, hj, hyj⟩ =>
          let ⟨k, hik, hjk⟩ := DirectedOrder.directed i j
          ⟨k,
            fun l hl =>
              (Finset.mem_union.1 (Dfinsupp.support_add hl)).elim (fun hl => le_transₓ (hi _ hl) hik)
                fun hl => le_transₓ (hj _ hl) hjk,
            by 
              simp [LinearMap.map_add, hxi, hyj, to_module_totalize_of_le hik hi, to_module_totalize_of_le hjk hj]⟩)
        fun a x ⟨i, hi, hxi⟩ =>
          ⟨i, fun k hk => hi k (DirectSum.support_smul _ _ hk),
            by 
              simp [LinearMap.map_smul, hxi]⟩

-- error in Algebra.DirectLimit: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
theorem of.zero_exact
{i x}
(H : «expr = »(of R ι G f i x, 0)) : «expr∃ , »((j hij), «expr = »(f i j hij x, (0 : G j))) :=
by haveI [] [":", expr nonempty ι] [":=", expr ⟨i⟩]; exact [expr let ⟨j, hj, hxj⟩ := of.zero_exact_aux H in
 if hx0 : «expr = »(x, 0) then ⟨i, le_refl _, by simp [] [] [] ["[", expr hx0, "]"] [] []⟩ else have hij : «expr ≤ »(i, j), from «expr $ »(hj _, by simp [] [] [] ["[", expr direct_sum.apply_eq_component, ",", expr hx0, "]"] [] []),
 ⟨j, hij, by simpa [] [] [] ["[", expr totalize_apply, ",", expr hij, "]"] [] ["using", expr hxj]⟩]

end DirectLimit

end Module

namespace AddCommGroupₓ

variable [∀ i, AddCommGroupₓ (G i)]

include dec_ι

/-- The direct limit of a directed system is the abelian groups glued together along the maps. -/
def direct_limit (f : ∀ i j, i ≤ j → G i →+ G j) : Type _ :=
  @Module.DirectLimit ℤ _ ι _ _ G _ _ fun i j hij => (f i j hij).toIntLinearMap

namespace DirectLimit

variable (f : ∀ i j, i ≤ j → G i →+ G j)

omit dec_ι

protected theorem DirectedSystem [DirectedSystem G fun i j h => f i j h] :
  Module.DirectedSystem G fun i j hij => (f i j hij).toIntLinearMap :=
  ⟨DirectedSystem.map_self fun i j h => f i j h, DirectedSystem.map_map fun i j h => f i j h⟩

include dec_ι

attribute [local instance] direct_limit.directed_system

instance : AddCommGroupₓ (direct_limit G f) :=
  Module.DirectLimit.addCommGroup G fun i j hij => (f i j hij).toIntLinearMap

instance : Inhabited (direct_limit G f) :=
  ⟨0⟩

/-- The canonical map from a component to the direct limit. -/
def of i : G i →ₗ[ℤ] direct_limit G f :=
  Module.DirectLimit.of ℤ ι G (fun i j hij => (f i j hij).toIntLinearMap) i

variable {G f}

@[simp]
theorem of_f {i j} hij x : of G f j (f i j hij x) = of G f i x :=
  Module.DirectLimit.of_f

@[elab_as_eliminator]
protected theorem induction_on [Nonempty ι] {C : direct_limit G f → Prop} (z : direct_limit G f)
  (ih : ∀ i x, C (of G f i x)) : C z :=
  Module.DirectLimit.induction_on z ih

/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
theorem of.zero_exact [DirectedSystem G fun i j h => f i j h] i x (h : of G f i x = 0) : ∃ j hij, f i j hij x = 0 :=
  Module.DirectLimit.of.zero_exact h

variable (P : Type u₁) [AddCommGroupₓ P]

variable (g : ∀ i, G i →+ P)

variable (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

variable (G f)

/-- The universal property of the direct limit: maps from the components to another abelian group
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift : direct_limit G f →ₗ[ℤ] P :=
  Module.DirectLimit.lift ℤ ι G (fun i j hij => (f i j hij).toIntLinearMap) (fun i => (g i).toIntLinearMap) Hg

variable {G f}

@[simp]
theorem lift_of i x : lift G f P g Hg (of G f i x) = g i x :=
  Module.DirectLimit.lift_of _ _ _

theorem lift_unique [Nonempty ι] (F : direct_limit G f →+ P) x :
  F x =
    lift G f P (fun i => F.comp (of G f i).toAddMonoidHom)
      (fun i j hij x =>
        by 
          simp )
      x :=
  direct_limit.induction_on x$
    fun i x =>
      by 
        simp 

end DirectLimit

end AddCommGroupₓ

namespace Ringₓ

variable [∀ i, CommRingₓ (G i)]

section 

variable (f : ∀ i j, i ≤ j → G i → G j)

open FreeCommRing

/-- The direct limit of a directed system is the rings glued together along the maps. -/
def direct_limit : Type max v w :=
  (Ideal.span
      { a |
        (∃ i j H x, of (⟨j, f i j H x⟩ : Σi, G i) - of ⟨i, x⟩ = a) ∨
          (∃ i, of (⟨i, 1⟩ : Σi, G i) - 1 = a) ∨
            (∃ i x y, (of (⟨i, x+y⟩ : Σi, G i) - of ⟨i, x⟩+of ⟨i, y⟩) = a) ∨
              ∃ i x y, (of (⟨i, x*y⟩ : Σi, G i) - of ⟨i, x⟩*of ⟨i, y⟩) = a }).Quotient

namespace DirectLimit

instance : CommRingₓ (direct_limit G f) :=
  Ideal.Quotient.commRing _

instance : Ringₓ (direct_limit G f) :=
  CommRingₓ.toRing _

instance : Inhabited (direct_limit G f) :=
  ⟨0⟩

/-- The canonical map from a component to the direct limit. -/
def of i : G i →+* direct_limit G f :=
  RingHom.mk'
    { toFun := fun x => Ideal.Quotient.mk _ (of (⟨i, x⟩ : Σi, G i)),
      map_one' := Ideal.Quotient.eq.2$ subset_span$ Or.inr$ Or.inl ⟨i, rfl⟩,
      map_mul' := fun x y => Ideal.Quotient.eq.2$ subset_span$ Or.inr$ Or.inr$ Or.inr ⟨i, x, y, rfl⟩ }
    fun x y => Ideal.Quotient.eq.2$ subset_span$ Or.inr$ Or.inr$ Or.inl ⟨i, x, y, rfl⟩

variable {G f}

@[simp]
theorem of_f {i j} hij x : of G f j (f i j hij x) = of G f i x :=
  Ideal.Quotient.eq.2$ subset_span$ Or.inl ⟨i, j, hij, x, rfl⟩

/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
theorem exists_of [Nonempty ι] (z : direct_limit G f) : ∃ i x, of G f i x = z :=
  Nonempty.elimₓ
      (by 
        infer_instance)$
    fun ind : ι =>
      Quotientₓ.induction_on' z$
        fun x =>
          FreeAbelianGroup.induction_on x ⟨ind, 0, (of _ _ ind).map_zero⟩
            (fun s =>
              Multiset.induction_on s ⟨ind, 1, (of _ _ ind).map_one⟩
                fun a s ih =>
                  let ⟨i, x⟩ := a 
                  let ⟨j, y, hs⟩ := ih 
                  let ⟨k, hik, hjk⟩ := DirectedOrder.directed i j
                  ⟨k, f i k hik x*f j k hjk y,
                    by 
                      rw [(of _ _ _).map_mul, of_f, of_f, hs] <;> rfl⟩)
            (fun s ⟨i, x, ih⟩ =>
              ⟨i, -x,
                by 
                  rw [(of _ _ _).map_neg, ih] <;> rfl⟩)
            fun p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩ =>
              let ⟨k, hik, hjk⟩ := DirectedOrder.directed i j
              ⟨k, f i k hik x+f j k hjk y,
                by 
                  rw [(of _ _ _).map_add, of_f, of_f, ihx, ihy] <;> rfl⟩

section 

open_locale Classical

open Polynomial

variable {f' : ∀ i j, i ≤ j → G i →+* G j}

theorem polynomial.exists_of [Nonempty ι] (q : Polynomial (direct_limit G fun i j h => f' i j h)) :
  ∃ i p, Polynomial.map (of G (fun i j h => f' i j h) i) p = q :=
  Polynomial.induction_on q
    (fun z =>
      let ⟨i, x, h⟩ := exists_of z
      ⟨i, C x,
        by 
          rw [map_C, h]⟩)
    (fun q₁ q₂ ⟨i₁, p₁, ih₁⟩ ⟨i₂, p₂, ih₂⟩ =>
      let ⟨i, h1, h2⟩ := DirectedOrder.directed i₁ i₂
      ⟨i, p₁.map (f' i₁ i h1)+p₂.map (f' i₂ i h2),
        by 
          rw [Polynomial.map_add, map_map, map_map, ←ih₁, ←ih₂]
          congr 2 <;> ext x <;> simpRw [RingHom.comp_apply, of_f]⟩)
    fun n z ih =>
      let ⟨i, x, h⟩ := exists_of z
      ⟨i, C x*X^n+1,
        by 
          rw [Polynomial.map_mul, map_C, h, Polynomial.map_pow, map_X]⟩

end 

@[elab_as_eliminator]
theorem induction_on [Nonempty ι] {C : direct_limit G f → Prop} (z : direct_limit G f) (ih : ∀ i x, C (of G f i x)) :
  C z :=
  let ⟨i, x, hx⟩ := exists_of z 
  hx ▸ ih i x

section OfZeroExact

open_locale Classical

variable (f' : ∀ i j, i ≤ j → G i →+* G j)

variable [DirectedSystem G fun i j h => f' i j h]

variable (G f)

-- error in Algebra.DirectLimit: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem of.zero_exact_aux2
{x : free_comm_ring «exprΣ , »((i), G i)}
{s t}
(hxs : is_supported x s)
{j k}
(hj : ∀ z : «exprΣ , »((i), G i), «expr ∈ »(z, s) → «expr ≤ »(z.1, j))
(hk : ∀ z : «exprΣ , »((i), G i), «expr ∈ »(z, t) → «expr ≤ »(z.1, k))
(hjk : «expr ≤ »(j, k))
(hst : «expr ⊆ »(s, t)) : «expr = »(f' j k hjk (lift (λ
   ix : s, f' ix.1.1 j (hj ix ix.2) ix.1.2) (restriction s x)), lift (λ
  ix : t, f' ix.1.1 k (hk ix ix.2) ix.1.2) (restriction t x)) :=
begin
  refine [expr subring.in_closure.rec_on hxs _ _ _ _],
  { rw ["[", expr (restriction _).map_one, ",", expr (free_comm_ring.lift _).map_one, ",", expr (f' j k hjk).map_one, ",", expr (restriction _).map_one, ",", expr (free_comm_ring.lift _).map_one, "]"] [] },
  { rw ["[", expr (restriction _).map_neg, ",", expr (restriction _).map_one, ",", expr (free_comm_ring.lift _).map_neg, ",", expr (free_comm_ring.lift _).map_one, ",", expr (f' j k hjk).map_neg, ",", expr (f' j k hjk).map_one, ",", expr (restriction _).map_neg, ",", expr (restriction _).map_one, ",", expr (free_comm_ring.lift _).map_neg, ",", expr (free_comm_ring.lift _).map_one, "]"] [] },
  { rintros ["_", "⟨", ident p, ",", ident hps, ",", ident rfl, "⟩", ident n, ident ih],
    rw ["[", expr (restriction _).map_mul, ",", expr (free_comm_ring.lift _).map_mul, ",", expr (f' j k hjk).map_mul, ",", expr ih, ",", expr (restriction _).map_mul, ",", expr (free_comm_ring.lift _).map_mul, ",", expr restriction_of, ",", expr dif_pos hps, ",", expr lift_of, ",", expr restriction_of, ",", expr dif_pos (hst hps), ",", expr lift_of, "]"] [],
    dsimp ["only"] [] [] [],
    have [] [] [":=", expr directed_system.map_map (λ i j h, f' i j h)],
    dsimp ["only"] [] [] ["at", ident this],
    rw [expr this] [],
    refl },
  { rintros [ident x, ident y, ident ihx, ident ihy],
    rw ["[", expr (restriction _).map_add, ",", expr (free_comm_ring.lift _).map_add, ",", expr (f' j k hjk).map_add, ",", expr ihx, ",", expr ihy, ",", expr (restriction _).map_add, ",", expr (free_comm_ring.lift _).map_add, "]"] [] }
end

variable {G f f'}

-- error in Algebra.DirectLimit: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem of.zero_exact_aux
[nonempty ι]
{x : free_comm_ring «exprΣ , »((i), G i)}
(H : «expr = »(ideal.quotient.mk _ x, (0 : direct_limit G (λ
   i
   j
   h, f' i j h)))) : «expr∃ , »((j
  s), «expr∃ , »((H : ∀
   k : «exprΣ , »((i), G i), «expr ∈ »(k, s) → «expr ≤ »(k.1, j)), «expr ∧ »(is_supported x s, «expr = »(lift (λ
     ix : s, f' ix.1.1 j (H ix ix.2) ix.1.2) (restriction s x), (0 : G j))))) :=
begin
  refine [expr span_induction (ideal.quotient.eq_zero_iff_mem.1 H) _ _ _ _],
  { rintros [ident x, "(", "⟨", ident i, ",", ident j, ",", ident hij, ",", ident x, ",", ident rfl, "⟩", "|", "⟨", ident i, ",", ident rfl, "⟩", "|", "⟨", ident i, ",", ident x, ",", ident y, ",", ident rfl, "⟩", "|", "⟨", ident i, ",", ident x, ",", ident y, ",", ident rfl, "⟩", ")"],
    { refine [expr ⟨j, {⟨i, x⟩, ⟨j, f' i j hij x⟩}, _, is_supported_sub «expr $ »(is_supported_of.2, or.inr rfl) «expr $ »(is_supported_of.2, or.inl rfl), _⟩],
      { rintros [ident k, "(", ident rfl, "|", "⟨", ident rfl, "|", "_", "⟩", ")"],
        exact [expr hij],
        refl },
      { rw ["[", expr (restriction _).map_sub, ",", expr (free_comm_ring.lift _).map_sub, ",", expr restriction_of, ",", expr dif_pos, ",", expr restriction_of, ",", expr dif_pos, ",", expr lift_of, ",", expr lift_of, "]"] [],
        dsimp ["only"] [] [] [],
        have [] [] [":=", expr directed_system.map_map (λ i j h, f' i j h)],
        dsimp ["only"] [] [] ["at", ident this],
        rw [expr this] [],
        exact [expr sub_self _],
        exacts ["[", expr or.inr rfl, ",", expr or.inl rfl, "]"] } },
    { refine [expr ⟨i, {⟨i, 1⟩}, _, is_supported_sub (is_supported_of.2 rfl) is_supported_one, _⟩],
      { rintros [ident k, "(", ident rfl, "|", ident h, ")"],
        refl },
      { rw ["[", expr (restriction _).map_sub, ",", expr (free_comm_ring.lift _).map_sub, ",", expr restriction_of, ",", expr dif_pos, ",", expr (restriction _).map_one, ",", expr lift_of, ",", expr (free_comm_ring.lift _).map_one, "]"] [],
        dsimp ["only"] [] [] [],
        rw ["[", expr (f' i i _).map_one, ",", expr sub_self, "]"] [],
        { exact [expr set.mem_singleton _] } } },
    { refine [expr ⟨i, {⟨i, «expr + »(x, y)⟩, ⟨i, x⟩, ⟨i, y⟩}, _, is_supported_sub «expr $ »(is_supported_of.2, or.inl rfl) (is_supported_add «expr $ »(is_supported_of.2, «expr $ »(or.inr, or.inl rfl)) «expr $ »(is_supported_of.2, «expr $ »(or.inr, or.inr rfl))), _⟩],
      { rintros [ident k, "(", ident rfl, "|", "⟨", ident rfl, "|", "⟨", ident rfl, "|", ident hk, "⟩", "⟩", ")"]; refl },
      { rw ["[", expr (restriction _).map_sub, ",", expr (restriction _).map_add, ",", expr restriction_of, ",", expr restriction_of, ",", expr restriction_of, ",", expr dif_pos, ",", expr dif_pos, ",", expr dif_pos, ",", expr (free_comm_ring.lift _).map_sub, ",", expr (free_comm_ring.lift _).map_add, ",", expr lift_of, ",", expr lift_of, ",", expr lift_of, "]"] [],
        dsimp ["only"] [] [] [],
        rw [expr (f' i i _).map_add] [],
        exact [expr sub_self _],
        exacts ["[", expr or.inl rfl, ",", expr or.inr (or.inr rfl), ",", expr or.inr (or.inl rfl), "]"] } },
    { refine [expr ⟨i, {⟨i, «expr * »(x, y)⟩, ⟨i, x⟩, ⟨i, y⟩}, _, is_supported_sub «expr $ »(is_supported_of.2, or.inl rfl) (is_supported_mul «expr $ »(is_supported_of.2, «expr $ »(or.inr, or.inl rfl)) «expr $ »(is_supported_of.2, «expr $ »(or.inr, or.inr rfl))), _⟩],
      { rintros [ident k, "(", ident rfl, "|", "⟨", ident rfl, "|", "⟨", ident rfl, "|", ident hk, "⟩", "⟩", ")"]; refl },
      { rw ["[", expr (restriction _).map_sub, ",", expr (restriction _).map_mul, ",", expr restriction_of, ",", expr restriction_of, ",", expr restriction_of, ",", expr dif_pos, ",", expr dif_pos, ",", expr dif_pos, ",", expr (free_comm_ring.lift _).map_sub, ",", expr (free_comm_ring.lift _).map_mul, ",", expr lift_of, ",", expr lift_of, ",", expr lift_of, "]"] [],
        dsimp ["only"] [] [] [],
        rw [expr (f' i i _).map_mul] [],
        exacts ["[", expr sub_self _, ",", expr or.inl rfl, ",", expr or.inr (or.inr rfl), ",", expr or.inr (or.inl rfl), "]"] } } },
  { refine [expr nonempty.elim (by apply_instance) (assume ind : ι, _)],
    refine [expr ⟨ind, «expr∅»(), λ _, false.elim, is_supported_zero, _⟩],
    rw ["[", expr (restriction _).map_zero, ",", expr (free_comm_ring.lift _).map_zero, "]"] [] },
  { rintros [ident x, ident y, "⟨", ident i, ",", ident s, ",", ident hi, ",", ident hxs, ",", ident ihs, "⟩", "⟨", ident j, ",", ident t, ",", ident hj, ",", ident hyt, ",", ident iht, "⟩"],
    rcases [expr directed_order.directed i j, "with", "⟨", ident k, ",", ident hik, ",", ident hjk, "⟩"],
    have [] [":", expr ∀ z : «exprΣ , »((i), G i), «expr ∈ »(z, «expr ∪ »(s, t)) → «expr ≤ »(z.1, k)] [],
    { rintros [ident z, "(", ident hz, "|", ident hz, ")"],
      exact [expr le_trans (hi z hz) hik],
      exact [expr le_trans (hj z hz) hjk] },
    refine [expr ⟨k, «expr ∪ »(s, t), this, is_supported_add «expr $ »(is_supported_upwards hxs, set.subset_union_left s t) «expr $ »(is_supported_upwards hyt, set.subset_union_right s t), _⟩],
    { rw ["[", expr (restriction _).map_add, ",", expr (free_comm_ring.lift _).map_add, ",", "<-", expr of.zero_exact_aux2 G f' hxs hi this hik (set.subset_union_left s t), ",", "<-", expr of.zero_exact_aux2 G f' hyt hj this hjk (set.subset_union_right s t), ",", expr ihs, ",", expr (f' i k hik).map_zero, ",", expr iht, ",", expr (f' j k hjk).map_zero, ",", expr zero_add, "]"] [] } },
  { rintros [ident x, ident y, "⟨", ident j, ",", ident t, ",", ident hj, ",", ident hyt, ",", ident iht, "⟩"],
    rw [expr smul_eq_mul] [],
    rcases [expr exists_finset_support x, "with", "⟨", ident s, ",", ident hxs, "⟩"],
    rcases [expr (s.image sigma.fst).exists_le, "with", "⟨", ident i, ",", ident hi, "⟩"],
    rcases [expr directed_order.directed i j, "with", "⟨", ident k, ",", ident hik, ",", ident hjk, "⟩"],
    have [] [":", expr ∀ z : «exprΣ , »((i), G i), «expr ∈ »(z, «expr ∪ »(«expr↑ »(s), t)) → «expr ≤ »(z.1, k)] [],
    { rintros [ident z, "(", ident hz, "|", ident hz, ")"],
      exacts ["[", expr «expr $ »(hi z.1, finset.mem_image.2 ⟨z, hz, rfl⟩).trans hik, ",", expr (hj z hz).trans hjk, "]"] },
    refine [expr ⟨k, «expr ∪ »(«expr↑ »(s), t), this, is_supported_mul «expr $ »(is_supported_upwards hxs, set.subset_union_left «expr↑ »(s) t) «expr $ »(is_supported_upwards hyt, set.subset_union_right «expr↑ »(s) t), _⟩],
    rw ["[", expr (restriction _).map_mul, ",", expr (free_comm_ring.lift _).map_mul, ",", "<-", expr of.zero_exact_aux2 G f' hyt hj this hjk (set.subset_union_right «expr↑ »(s) t), ",", expr iht, ",", expr (f' j k hjk).map_zero, ",", expr mul_zero, "]"] [] }
end

-- error in Algebra.DirectLimit: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
theorem of.zero_exact
{i x}
(hix : «expr = »(of G (λ
   i j h, f' i j h) i x, 0)) : «expr∃ , »((j) (hij : «expr ≤ »(i, j)), «expr = »(f' i j hij x, 0)) :=
by haveI [] [":", expr nonempty ι] [":=", expr ⟨i⟩]; exact [expr let ⟨j, s, H, hxs, hx⟩ := of.zero_exact_aux hix in
 have hixs : «expr ∈ »((⟨i, x⟩ : «exprΣ , »((i), G i)), s), from is_supported_of.1 hxs,
 ⟨j, H ⟨i, x⟩ hixs, by rw ["[", expr restriction_of, ",", expr dif_pos hixs, ",", expr lift_of, "]"] ["at", ident hx]; exact [expr hx]⟩]

end OfZeroExact

variable (f' : ∀ i j, i ≤ j → G i →+* G j)

/-- If the maps in the directed system are injective, then the canonical maps
from the components to the direct limits are injective. -/
theorem of_injective [DirectedSystem G fun i j h => f' i j h] (hf : ∀ i j hij, Function.Injective (f' i j hij)) i :
  Function.Injective (of G (fun i j h => f' i j h) i) :=
  by 
    suffices  : ∀ x, of G (fun i j h => f' i j h) i x = 0 → x = 0
    ·
      intro x y hxy 
      rw [←sub_eq_zero]
      apply this 
      rw [(of G _ i).map_sub, hxy, sub_self]
    intro x hx 
    rcases of.zero_exact hx with ⟨j, hij, hfx⟩
    apply hf i j hij 
    rw [hfx, (f' i j hij).map_zero]

variable (P : Type u₁) [CommRingₓ P]

variable (g : ∀ i, G i →+* P)

variable (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

include Hg

open FreeCommRing

variable (G f)

/-- The universal property of the direct limit: maps from the components to another ring
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
def lift : direct_limit G f →+* P :=
  Ideal.Quotient.lift _ (FreeCommRing.lift$ fun x : Σi, G i => g x.1 x.2)
    (by 
      suffices  : Ideal.span _ ≤ Ideal.comap (FreeCommRing.lift fun x : Σi : ι, G i => g x.fst x.snd) ⊥
      ·
        intro x hx 
        exact (mem_bot P).1 (this hx)
      rw [Ideal.span_le]
      intro x hx 
      rw [SetLike.mem_coe, Ideal.mem_comap, mem_bot]
      rcases hx with (⟨i, j, hij, x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, x, y, rfl⟩ | ⟨i, x, y, rfl⟩) <;>
        simp only [RingHom.map_sub, lift_of, Hg, RingHom.map_one, RingHom.map_add, RingHom.map_mul, (g i).map_one,
          (g i).map_add, (g i).map_mul, sub_self])

variable {G f}

omit Hg

@[simp]
theorem lift_of i x : lift G f P g Hg (of G f i x) = g i x :=
  FreeCommRing.lift_of _ _

theorem lift_unique [Nonempty ι] (F : direct_limit G f →+* P) x :
  F x =
    lift G f P (fun i => F.comp$ of G f i)
      (fun i j hij x =>
        by 
          simp )
      x :=
  direct_limit.induction_on x$
    fun i x =>
      by 
        simp 

end DirectLimit

end 

end Ringₓ

namespace Field

variable [Nonempty ι] [∀ i, Field (G i)]

variable (f : ∀ i j, i ≤ j → G i → G j)

variable (f' : ∀ i j, i ≤ j → G i →+* G j)

namespace DirectLimit

instance Nontrivial [DirectedSystem G fun i j h => f' i j h] : Nontrivial (Ringₓ.DirectLimit G fun i j h => f' i j h) :=
  ⟨⟨0, 1,
      Nonempty.elimₓ
          (by 
            infer_instance)$
        fun i : ι =>
          by 
            change (0 : Ringₓ.DirectLimit G fun i j h => f' i j h) ≠ 1
            rw [←(Ringₓ.DirectLimit.of _ _ _).map_one]
            intro H 
            rcases Ringₓ.DirectLimit.of.zero_exact H.symm with ⟨j, hij, hf⟩
            rw [(f' i j hij).map_one] at hf 
            exact one_ne_zero hf⟩⟩

theorem exists_inv {p : Ringₓ.DirectLimit G f} : p ≠ 0 → ∃ y, (p*y) = 1 :=
  Ringₓ.DirectLimit.induction_on p$
    fun i x H =>
      ⟨Ringₓ.DirectLimit.of G f i (x⁻¹),
        by 
          erw [←(Ringₓ.DirectLimit.of _ _ _).map_mul,
            mul_inv_cancel
              fun h : x = 0 =>
                H$
                  by 
                    rw [h, (Ringₓ.DirectLimit.of _ _ _).map_zero],
            (Ringₓ.DirectLimit.of _ _ _).map_one]⟩

section 

open_locale Classical

/-- Noncomputable multiplicative inverse in a direct limit of fields. -/
noncomputable def inv (p : Ringₓ.DirectLimit G f) : Ringₓ.DirectLimit G f :=
  if H : p = 0 then 0 else Classical.some (direct_limit.exists_inv G f H)

protected theorem mul_inv_cancel {p : Ringₓ.DirectLimit G f} (hp : p ≠ 0) : (p*inv G f p) = 1 :=
  by 
    rw [inv, dif_neg hp, Classical.some_spec (direct_limit.exists_inv G f hp)]

protected theorem inv_mul_cancel {p : Ringₓ.DirectLimit G f} (hp : p ≠ 0) : (inv G f p*p) = 1 :=
  by 
    rw [_root_.mul_comm, direct_limit.mul_inv_cancel G f hp]

/-- Noncomputable field structure on the direct limit of fields.
See note [reducible non-instances]. -/
@[reducible]
protected noncomputable def Field [DirectedSystem G fun i j h => f' i j h] :
  Field (Ringₓ.DirectLimit G fun i j h => f' i j h) :=
  { Ringₓ.DirectLimit.commRing G fun i j h => f' i j h, direct_limit.nontrivial G fun i j h => f' i j h with
    inv := inv G fun i j h => f' i j h, mul_inv_cancel := fun p => direct_limit.mul_inv_cancel G fun i j h => f' i j h,
    inv_zero := dif_pos rfl }

end 

end DirectLimit

end Field

