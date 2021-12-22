import Mathbin.GroupTheory.GroupAction.Defs

/-! # Group actions on and by `units M`

This file provides the action of a unit on a type `α`, `has_scalar (units M) α`, in the presence of
`has_scalar M α`, with the obvious definition stated in `units.smul_def`. This definition preserves
`mul_action` and `distrib_mul_action` structures too.

Additionally, a `mul_action G M` for some group `G` satisfying some additional properties admits a
`mul_action G (units M)` structure, again with the obvious definition stated in `units.coe_smul`.
These instances use a primed name.

The results are repeated for `add_units` and `has_vadd` where relevant.
-/


variable {G H M N : Type _} {α : Type _}

namespace Units

/-! ### Action of the units of `M` on a type `α` -/


-- failed to format: format: uncaught backtrack exception
@[ to_additive ] instance [ Monoidₓ M ] [ HasScalar M α ] : HasScalar ( Units M ) α where smul m a := ( m : M ) • a

@[to_additive]
theorem smul_def [Monoidₓ M] [HasScalar M α] (m : Units M) (a : α) : m • a = (m : M) • a :=
  rfl

theorem _root_.is_unit.inv_smul [Monoidₓ α] {a : α} (h : IsUnit a) : h.unit⁻¹ • a = 1 :=
  h.coe_inv_mul

-- failed to format: format: uncaught backtrack exception
@[ to_additive ]
  instance
    [ Monoidₓ M ] [ HasScalar M α ] [ HasFaithfulScalar M α ] : HasFaithfulScalar ( Units M ) α
    where eq_of_smul_eq_smul u₁ u₂ h := Units.ext $ eq_of_smul_eq_smul h

-- failed to format: format: uncaught backtrack exception
@[ to_additive ]
  instance
    [ Monoidₓ M ] [ MulAction M α ] : MulAction ( Units M ) α
    where one_smul := ( one_smul M : _ ) mul_smul m n := mul_smul ( m : M ) n

-- failed to format: format: uncaught backtrack exception
instance
  [ Monoidₓ M ] [ AddMonoidₓ α ] [ DistribMulAction M α ] : DistribMulAction ( Units M ) α
  where smul_add m := smul_add ( m : M ) smul_zero m := smul_zero m

-- failed to format: format: uncaught backtrack exception
instance
  [ Monoidₓ M ] [ Monoidₓ α ] [ MulDistribMulAction M α ] : MulDistribMulAction ( Units M ) α
  where smul_mul m := smul_mul' ( m : M ) smul_one m := smul_one m

-- failed to format: format: uncaught backtrack exception
instance
  smul_comm_class_left
  [ Monoidₓ M ] [ HasScalar M α ] [ HasScalar N α ] [ SmulCommClass M N α ] : SmulCommClass ( Units M ) N α
  where smul_comm m n := ( smul_comm ( m : M ) n : _ )

-- failed to format: format: uncaught backtrack exception
instance
  smul_comm_class_right
  [ Monoidₓ N ] [ HasScalar M α ] [ HasScalar N α ] [ SmulCommClass M N α ] : SmulCommClass M ( Units N ) α
  where smul_comm m n := ( smul_comm m ( n : N ) : _ )

-- failed to format: format: uncaught backtrack exception
instance
  [ Monoidₓ M ] [ HasScalar M N ] [ HasScalar M α ] [ HasScalar N α ] [ IsScalarTower M N α ]
    : IsScalarTower ( Units M ) N α
  where smul_assoc m n := ( smul_assoc ( m : M ) n : _ )

/-! ### Action of a group `G` on units of `M` -/


-- failed to format: format: uncaught backtrack exception
/--
    If an action `G` associates and commutes with multiplication on `M`, then it lifts to an
    action on `units M`. Notably, this provides `mul_action (units M) (units N)` under suitable
    conditions.
    -/
  instance
    mul_action'
    [ Groupₓ G ] [ Monoidₓ M ] [ MulAction G M ] [ SmulCommClass G M M ] [ IsScalarTower G M M ]
      : MulAction G ( Units M )
    where
      smul
          g m
          :=
          ⟨
            g • ( m : M )
              ,
              g ⁻¹ • ↑ m ⁻¹
              ,
              by rw [ smul_mul_smul , Units.mul_inv , mul_right_invₓ , one_smul ]
              ,
              by rw [ smul_mul_smul , Units.inv_mul , mul_left_invₓ , one_smul ]
            ⟩
        one_smul m := Units.ext $ one_smul _ _
        mul_smul g₁ g₂ m := Units.ext $ mul_smul _ _ _

@[simp]
theorem coe_smul [Groupₓ G] [Monoidₓ M] [MulAction G M] [SmulCommClass G M M] [IsScalarTower G M M] (g : G)
    (m : Units M) : ↑(g • m) = g • (m : M) :=
  rfl

/--  Note that this lemma exists more generally as the global `smul_inv` -/
@[simp]
theorem smul_inv [Groupₓ G] [Monoidₓ M] [MulAction G M] [SmulCommClass G M M] [IsScalarTower G M M] (g : G)
    (m : Units M) : (g • m)⁻¹ = g⁻¹ • m⁻¹ :=
  ext rfl

-- failed to format: format: uncaught backtrack exception
/-- Transfer `smul_comm_class G H M` to `smul_comm_class G H (units M)` -/
  instance
    smul_comm_class'
    [ Groupₓ G ]
        [ Groupₓ H ]
        [ Monoidₓ M ]
        [ MulAction G M ]
        [ SmulCommClass G M M ]
        [ MulAction H M ]
        [ SmulCommClass H M M ]
        [ IsScalarTower G M M ]
        [ IsScalarTower H M M ]
        [ SmulCommClass G H M ]
      : SmulCommClass G H ( Units M )
    where smul_comm g h m := Units.ext $ smul_comm g h ( m : M )

-- failed to format: format: uncaught backtrack exception
/-- Transfer `is_scalar_tower G H M` to `is_scalar_tower G H (units M)` -/
  instance
    is_scalar_tower'
    [ HasScalar G H ]
        [ Groupₓ G ]
        [ Groupₓ H ]
        [ Monoidₓ M ]
        [ MulAction G M ]
        [ SmulCommClass G M M ]
        [ MulAction H M ]
        [ SmulCommClass H M M ]
        [ IsScalarTower G M M ]
        [ IsScalarTower H M M ]
        [ IsScalarTower G H M ]
      : IsScalarTower G H ( Units M )
    where smul_assoc g h m := Units.ext $ smul_assoc g h ( m : M )

-- failed to format: format: uncaught backtrack exception
/-- Transfer `is_scalar_tower G M α` to `is_scalar_tower G (units M) α` -/
  instance
    is_scalar_tower'_left
    [ Groupₓ G ]
        [ Monoidₓ M ]
        [ MulAction G M ]
        [ HasScalar M α ]
        [ HasScalar G α ]
        [ SmulCommClass G M M ]
        [ IsScalarTower G M M ]
        [ IsScalarTower G M α ]
      : IsScalarTower G ( Units M ) α
    where smul_assoc g m := ( smul_assoc g ( m : M ) : _ )

example [Monoidₓ M] [Monoidₓ N] [MulAction M N] [SmulCommClass M N N] [IsScalarTower M N N] :
    MulAction (Units M) (Units N) :=
  Units.mulAction'

/--  A stronger form of `units.mul_action'`. -/
instance mul_distrib_mul_action' [Groupₓ G] [Monoidₓ M] [MulDistribMulAction G M] [SmulCommClass G M M]
    [IsScalarTower G M M] : MulDistribMulAction G (Units M) :=
  { Units.mulAction' with smul := · • ·, smul_one := fun m => Units.ext $ smul_one _,
    smul_mul := fun g m₁ m₂ => Units.ext $ smul_mul' _ _ _ }

end Units

theorem IsUnit.smul [Groupₓ G] [Monoidₓ M] [MulAction G M] [SmulCommClass G M M] [IsScalarTower G M M] {m : M} (g : G)
    (h : IsUnit m) : IsUnit (g • m) :=
  let ⟨u, hu⟩ := h
  hu ▸ ⟨g • u, Units.coe_smul _ _⟩

