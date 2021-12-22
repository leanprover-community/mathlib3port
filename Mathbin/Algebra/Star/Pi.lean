import Mathbin.Algebra.Star.Basic
import Mathbin.Algebra.Ring.Pi
import Mathbin.Algebra.Module.Pi

/-!
# `star` on pi types

We put a `has_star` structure on pi types that operates elementwise, such that it describes the
complex conjugation of vectors.
-/


universe u v w

variable {I : Type u}

variable {f : I → Type v}

namespace Pi

-- failed to format: format: uncaught backtrack exception
instance [ ∀ i , HasStar ( f i ) ] : HasStar ( ∀ i , f i ) where star x i := star ( x i )

@[simp]
theorem star_apply [∀ i, HasStar (f i)] (x : ∀ i, f i) (i : I) : star x i = star (x i) :=
  rfl

theorem star_def [∀ i, HasStar (f i)] (x : ∀ i, f i) : star x = fun i => star (x i) :=
  rfl

-- failed to format: format: uncaught backtrack exception
instance
  [ ∀ i , HasInvolutiveStar ( f i ) ] : HasInvolutiveStar ( ∀ i , f i )
  where star_involutive _ := funext $ fun _ => star_star _

-- failed to format: format: uncaught backtrack exception
instance
  [ ∀ i , Monoidₓ ( f i ) ] [ ∀ i , StarMonoid ( f i ) ] : StarMonoid ( ∀ i , f i )
  where star_mul _ _ := funext $ fun _ => star_mul _ _

-- failed to format: format: uncaught backtrack exception
instance
  [ ∀ i , AddMonoidₓ ( f i ) ] [ ∀ i , StarAddMonoid ( f i ) ] : StarAddMonoid ( ∀ i , f i )
  where star_add _ _ := funext $ fun _ => star_add _ _

instance [∀ i, Semiringₓ (f i)] [∀ i, StarRing (f i)] : StarRing (∀ i, f i) :=
  { Pi.starAddMonoid, (Pi.starMonoid : StarMonoid (∀ i, f i)) with }

-- failed to format: format: uncaught backtrack exception
instance
  { R : Type w } [ ∀ i , HasScalar R ( f i ) ] [ HasStar R ] [ ∀ i , HasStar ( f i ) ] [ ∀ i , StarModule R ( f i ) ]
    : StarModule R ( ∀ i , f i )
  where star_smul r x := funext $ fun i => star_smul r ( x i )

end Pi

