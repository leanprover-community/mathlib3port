import Mathbin.Algebra.Ring.Prod 
import Mathbin.RingTheory.Ideal.Quotient 
import Mathbin.RingTheory.Subring 
import Mathbin.Topology.Algebra.Group

/-!

# Topological (semi)rings

A topological (semi)ring is a (semi)ring equipped with a topology such that all operations are
continuous. Besides this definition, this file proves that the topological closure of a subring
(resp. an ideal) is a subring (resp. an ideal) and defines products and quotients
of topological (semi)rings.

## Main Results

- `subring.topological_closure`/`subsemiring.topological_closure`: the topological closure of a
  `subring`/`subsemiring` is itself a `sub(semi)ring`.
- `prod.topological_ring`/`prod.topological_ring`: The product of two topological (semi)rings.
- `pi.topological_ring`/`pi.topological_ring`: The arbitrary product of topological (semi)rings.
- `ideal.closure`: The closure of an ideal is an ideal.
- `topological_ring_quotient`: The quotient of a topological ring by an ideal is a topological ring.

-/


open Classical Set Filter TopologicalSpace Function

open_locale Classical TopologicalSpace Filter

section TopologicalRing

variable(α : Type _)

/-- A topological (semi)ring is a (semi)ring `R` where addition and multiplication are continuous.
If `R` is a ring, then negation is automatically continuous, as it is multiplication with `-1`. -/
class TopologicalRing[TopologicalSpace α][Semiringₓ α] extends HasContinuousAdd α, HasContinuousMul α : Prop

section 

variable{α}[TopologicalSpace α][Semiringₓ α][TopologicalRing α]

/-- The (topological-space) closure of a subsemiring of a topological semiring is
itself a subsemiring. -/
def Subsemiring.topologicalClosure (s : Subsemiring α) : Subsemiring α :=
  { s.to_submonoid.topological_closure, s.to_add_submonoid.topological_closure with Carrier := Closure (s : Set α) }

@[simp]
theorem Subsemiring.topological_closure_coe (s : Subsemiring α) :
  (s.topological_closure : Set α) = Closure (s : Set α) :=
  rfl

instance Subsemiring.topological_closure_topological_ring (s : Subsemiring α) : TopologicalRing s.topological_closure :=
  { s.to_add_submonoid.topological_closure_has_continuous_add,
    s.to_submonoid.topological_closure_has_continuous_mul with  }

theorem Subsemiring.subring_topological_closure (s : Subsemiring α) : s ≤ s.topological_closure :=
  subset_closure

theorem Subsemiring.is_closed_topological_closure (s : Subsemiring α) : IsClosed (s.topological_closure : Set α) :=
  by 
    convert is_closed_closure

theorem Subsemiring.topological_closure_minimal (s : Subsemiring α) {t : Subsemiring α} (h : s ≤ t)
  (ht : IsClosed (t : Set α)) : s.topological_closure ≤ t :=
  closure_minimal h ht

/-- The product topology on the cartesian product of two topological semirings
  makes the product into a topological semiring. -/
instance  {β : Type _} [Semiringₓ β] [TopologicalSpace β] [TopologicalRing β] : TopologicalRing (α × β) :=
  {  }

instance  {β : Type _} {C : β → Type _} [∀ b, TopologicalSpace (C b)] [∀ b, Semiringₓ (C b)]
  [∀ b, TopologicalRing (C b)] : TopologicalRing (∀ b, C b) :=
  {  }

end 

section 

variable{R : Type _}[Ringₓ R][TopologicalSpace R]

-- error in Topology.Algebra.Ring: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem topological_ring.of_add_group_of_nhds_zero
[topological_add_group R]
(hmul : «expr $ »(tendsto (uncurry ((«expr * ») : R → R → R)) «expr ×ᶠ »(expr𝓝() 0, expr𝓝() 0), expr𝓝() 0))
(hmul_left : ∀ x₀ : R, «expr $ »(tendsto (λ x : R, «expr * »(x₀, x)) (expr𝓝() 0), expr𝓝() 0))
(hmul_right : ∀ x₀ : R, «expr $ »(tendsto (λ x : R, «expr * »(x, x₀)) (expr𝓝() 0), expr𝓝() 0)) : topological_ring R :=
begin
  refine [expr { ..«expr‹ ›»(topological_add_group R), .. }],
  have [ident hleft] [":", expr ∀ x₀ : R, «expr = »(expr𝓝() x₀, map (λ x, «expr + »(x₀, x)) (expr𝓝() 0))] [],
  by simp [] [] [] [] [] [],
  have [ident hadd] [":", expr tendsto (uncurry ((«expr + ») : R → R → R)) «expr ×ᶠ »(expr𝓝() 0, expr𝓝() 0) (expr𝓝() 0)] [],
  { rw ["<-", expr nhds_prod_eq] [],
    convert [] [expr continuous_add.tendsto ((0 : R), (0 : R))] [],
    rw [expr zero_add] [] },
  rw [expr continuous_iff_continuous_at] [],
  rintro ["⟨", ident x₀, ",", ident y₀, "⟩"],
  rw ["[", expr continuous_at, ",", expr nhds_prod_eq, ",", expr hleft x₀, ",", expr hleft y₀, ",", expr hleft «expr * »(x₀, y₀), ",", expr filter.prod_map_map_eq, ",", expr tendsto_map'_iff, "]"] [],
  suffices [] [":", expr tendsto «expr ∘ »(λ
    x : R, «expr + »(x, «expr * »(x₀, y₀)), «expr ∘ »(λ
     p : «expr × »(R, R), «expr + »(p.1, p.2), λ
     p : «expr × »(R, R), («expr + »(«expr * »(p.1, y₀), «expr * »(x₀, p.2)), «expr * »(p.1, p.2)))) «expr ×ᶠ »(expr𝓝() 0, expr𝓝() 0) «expr $ »(map (λ
     x : R, «expr + »(x, «expr * »(x₀, y₀))), expr𝓝() 0)],
  { convert [] [expr this] ["using", 1],
    { ext [] [] [],
      simp [] [] ["only"] ["[", expr comp_app, ",", expr mul_add, ",", expr add_mul, "]"] [] [],
      abel [] [] [] },
    { simp [] [] ["only"] ["[", expr add_comm, "]"] [] [] } },
  refine [expr tendsto_map.comp (hadd.comp (tendsto.prod_mk _ hmul))],
  exact [expr hadd.comp (((hmul_right y₀).comp tendsto_fst).prod_mk ((hmul_left x₀).comp tendsto_snd))]
end

-- error in Topology.Algebra.Ring: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem topological_ring.of_nhds_zero
(hadd : «expr $ »(tendsto (uncurry ((«expr + ») : R → R → R)) «expr ×ᶠ »(expr𝓝() 0, expr𝓝() 0), expr𝓝() 0))
(hneg : tendsto (λ x, «expr- »(x) : R → R) (expr𝓝() 0) (expr𝓝() 0))
(hmul : «expr $ »(tendsto (uncurry ((«expr * ») : R → R → R)) «expr ×ᶠ »(expr𝓝() 0, expr𝓝() 0), expr𝓝() 0))
(hmul_left : ∀ x₀ : R, «expr $ »(tendsto (λ x : R, «expr * »(x₀, x)) (expr𝓝() 0), expr𝓝() 0))
(hmul_right : ∀ x₀ : R, «expr $ »(tendsto (λ x : R, «expr * »(x, x₀)) (expr𝓝() 0), expr𝓝() 0))
(hleft : ∀ x₀ : R, «expr = »(expr𝓝() x₀, map (λ x, «expr + »(x₀, x)) (expr𝓝() 0))) : topological_ring R :=
begin
  haveI [] [] [":=", expr topological_add_group.of_comm_of_nhds_zero hadd hneg hleft],
  exact [expr topological_ring.of_add_group_of_nhds_zero hmul hmul_left hmul_right]
end

end 

variable{α}[Ringₓ α][TopologicalSpace α][TopologicalRing α]

instance (priority := 100)TopologicalRing.to_topological_add_group : TopologicalAddGroup α :=
  { continuous_add := continuous_add,
    continuous_neg :=
      by 
        simpa only [neg_one_mul, id.def] using (@continuous_const α α _ _ (-1)).mul continuous_id }

/-- In a topological ring, the left-multiplication `add_monoid_hom` is continuous. -/
theorem mul_left_continuous (x : α) : Continuous (AddMonoidHom.mulLeft x) :=
  continuous_const.mul continuous_id

/-- In a topological ring, the right-multiplication `add_monoid_hom` is continuous. -/
theorem mul_right_continuous (x : α) : Continuous (AddMonoidHom.mulRight x) :=
  continuous_id.mul continuous_const

/-- The (topological-space) closure of a subring of a topological semiring is
itself a subring. -/
def Subring.topologicalClosure (S : Subring α) : Subring α :=
  { S.to_submonoid.topological_closure, S.to_add_subgroup.topological_closure with Carrier := Closure (S : Set α) }

instance Subring.topological_closure_topological_ring (s : Subring α) : TopologicalRing s.topological_closure :=
  { s.to_add_subgroup.topological_closure_topological_add_group,
    s.to_submonoid.topological_closure_has_continuous_mul with  }

theorem Subring.subring_topological_closure (s : Subring α) : s ≤ s.topological_closure :=
  subset_closure

theorem Subring.is_closed_topological_closure (s : Subring α) : IsClosed (s.topological_closure : Set α) :=
  by 
    convert is_closed_closure

theorem Subring.topological_closure_minimal (s : Subring α) {t : Subring α} (h : s ≤ t) (ht : IsClosed (t : Set α)) :
  s.topological_closure ≤ t :=
  closure_minimal h ht

end TopologicalRing

section TopologicalCommRing

variable{α : Type _}[TopologicalSpace α][CommRingₓ α][TopologicalRing α]

/-- The closure of an ideal in a topological ring as an ideal. -/
def Ideal.closure (S : Ideal α) : Ideal α :=
  { AddSubmonoid.topologicalClosure S.to_add_submonoid with Carrier := Closure S,
    smul_mem' := fun c x hx => map_mem_closure (mul_left_continuous _) hx$ fun a => S.mul_mem_left c }

@[simp]
theorem Ideal.coe_closure (S : Ideal α) : (S.closure : Set α) = Closure S :=
  rfl

end TopologicalCommRing

section TopologicalRing

variable{α : Type _}[TopologicalSpace α][CommRingₓ α](N : Ideal α)

open Ideal.Quotient

instance topologicalRingQuotientTopology : TopologicalSpace N.quotient :=
  by 
    dunfold Ideal.Quotient Submodule.Quotient <;> infer_instance

variable[TopologicalRing α]

theorem QuotientRing.is_open_map_coe : IsOpenMap (mk N) :=
  by 
    intro s s_op 
    change IsOpen (mk N ⁻¹' (mk N '' s))
    rw [quotient_ring_saturate]
    exact is_open_Union fun ⟨n, _⟩ => is_open_map_add_left n s s_op

theorem QuotientRing.quotient_map_coe_coe : QuotientMap fun p : α × α => (mk N p.1, mk N p.2) :=
  IsOpenMap.to_quotient_map ((QuotientRing.is_open_map_coe N).Prod (QuotientRing.is_open_map_coe N))
    ((continuous_quot_mk.comp continuous_fst).prod_mk (continuous_quot_mk.comp continuous_snd))
    (by 
      rintro ⟨⟨x⟩, ⟨y⟩⟩ <;> exact ⟨(x, y), rfl⟩)

instance topological_ring_quotient : TopologicalRing N.quotient :=
  { continuous_add :=
      have cont : Continuous (mk N ∘ fun p : α × α => p.fst+p.snd) := continuous_quot_mk.comp continuous_add
      (QuotientMap.continuous_iff (QuotientRing.quotient_map_coe_coe N)).mpr cont,
    continuous_mul :=
      have cont : Continuous (mk N ∘ fun p : α × α => p.fst*p.snd) := continuous_quot_mk.comp continuous_mul
      (QuotientMap.continuous_iff (QuotientRing.quotient_map_coe_coe N)).mpr cont }

end TopologicalRing

/-!
### Lattice of ring topologies
We define a type class `ring_topology α` which endows a ring `α` with a topology such that all ring
operations are continuous.

Ring topologies on a fixed ring `α` are ordered, by reverse inclusion. They form a complete lattice,
with `⊥` the discrete topology and `⊤` the indiscrete topology.

Any function `f : α → β` induces `coinduced f : topological_space α → ring_topology β`. -/


universe u v

/-- A ring topology on a ring `α` is a topology for which addition, negation and multiplication
are continuous. -/
@[ext]
structure RingTopology(α : Type u)[Ringₓ α] extends TopologicalSpace α, TopologicalRing α : Type u

namespace RingTopology

variable{α : Type _}[Ringₓ α]

instance Inhabited {α : Type u} [Ringₓ α] : Inhabited (RingTopology α) :=
  ⟨{ toTopologicalSpace := ⊤, continuous_add := continuous_top, continuous_mul := continuous_top }⟩

@[ext]
theorem ext' {f g : RingTopology α} (h : f.is_open = g.is_open) : f = g :=
  by 
    ext 
    rw [h]

/-- The ordering on ring topologies on the ring `α`.
  `t ≤ s` if every set open in `s` is also open in `t` (`t` is finer than `s`). -/
instance  : PartialOrderₓ (RingTopology α) :=
  PartialOrderₓ.lift RingTopology.toTopologicalSpace$ ext

local notation "cont" => @Continuous _ _

-- error in Topology.Algebra.Ring: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private def def_Inf (S : set (ring_topology α)) : ring_topology α :=
let Inf_S' := Inf «expr '' »(to_topological_space, S) in
{ to_topological_space := Inf_S',
  continuous_add := begin
    apply [expr continuous_Inf_rng],
    rintros ["_", "⟨", "⟨", ident t, ",", ident tr, "⟩", ",", ident haS, ",", ident rfl, "⟩"],
    resetI,
    have [ident h] [] [":=", expr continuous_Inf_dom (set.mem_image_of_mem to_topological_space haS) continuous_id],
    have [ident h_continuous_id] [] [":=", expr @continuous.prod_map _ _ _ _ t t Inf_S' Inf_S' _ _ h h],
    have [ident h_continuous_add] [":", expr exprcont() (id _) t (λ
      p : «expr × »(α, α), «expr + »(p.fst, p.snd))] [":=", expr continuous_add],
    exact [expr @continuous.comp _ _ _ (id _) (id _) t _ _ h_continuous_add h_continuous_id]
  end,
  continuous_mul := begin
    apply [expr continuous_Inf_rng],
    rintros ["_", "⟨", "⟨", ident t, ",", ident tr, "⟩", ",", ident haS, ",", ident rfl, "⟩"],
    resetI,
    have [ident h] [] [":=", expr continuous_Inf_dom (set.mem_image_of_mem to_topological_space haS) continuous_id],
    have [ident h_continuous_id] [] [":=", expr @continuous.prod_map _ _ _ _ t t Inf_S' Inf_S' _ _ h h],
    have [ident h_continuous_mul] [":", expr exprcont() (id _) t (λ
      p : «expr × »(α, α), «expr * »(p.fst, p.snd))] [":=", expr continuous_mul],
    exact [expr @continuous.comp _ _ _ (id _) (id _) t _ _ h_continuous_mul h_continuous_id]
  end }

/-- Ring topologies on `α` form a complete lattice, with `⊥` the discrete topology and `⊤` the
indiscrete topology.

The infimum of a collection of ring topologies is the topology generated by all their open sets
(which is a ring topology).

The supremum of two ring topologies `s` and `t` is the infimum of the family of all ring topologies
contained in the intersection of `s` and `t`. -/
instance  : CompleteSemilatticeInf (RingTopology α) :=
  { RingTopology.partialOrder with inf := def_Inf,
    Inf_le :=
      fun S a haS =>
        by 
          apply topological_space.complete_lattice.Inf_le 
          use a, ⟨haS, rfl⟩,
    le_Inf :=
      by 
        intro S a hab 
        apply topological_space.complete_lattice.le_Inf 
        rintro _ ⟨b, hbS, rfl⟩
        exact hab b hbS }

instance  : CompleteLattice (RingTopology α) :=
  completeLatticeOfCompleteSemilatticeInf _

/--  Given `f : α → β` and a topology on `α`, the coinduced ring topology on `β` is the finest
topology such that `f` is continuous and `β` is a topological ring. -/
def coinduced {α β : Type _} [t : TopologicalSpace α] [Ringₓ β] (f : α → β) : RingTopology β :=
  Inf { b:RingTopology β | TopologicalSpace.coinduced f t ≤ b.to_topological_space }

theorem coinduced_continuous {α β : Type _} [t : TopologicalSpace α] [Ringₓ β] (f : α → β) :
  cont t (coinduced f).toTopologicalSpace f :=
  by 
    rw [continuous_iff_coinduced_le]
    refine' le_Inf _ 
    rintro _ ⟨t', ht', rfl⟩
    exact ht'

end RingTopology

