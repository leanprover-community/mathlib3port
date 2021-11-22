import Mathbin.Algebra.Star.Basic 
import Mathbin.Algebra.Ring.Pi 
import Mathbin.Algebra.Module.Pi

/-!
# `star` on pi types

We put a `has_star` structure on pi types that operates elementwise, such that it describes the
complex conjugation of vectors.
-/


universe u v w

variable{I : Type u}

variable{f : I → Type v}

namespace Pi

instance  [∀ i, HasStar (f i)] : HasStar (∀ i, f i) :=
  { star := fun x i => star (x i) }

@[simp]
theorem star_apply [∀ i, HasStar (f i)] (x : ∀ i, f i) (i : I) : star x i = star (x i) :=
  rfl

theorem star_def [∀ i, HasStar (f i)] (x : ∀ i, f i) : star x = fun i => star (x i) :=
  rfl

instance  [∀ i, HasInvolutiveStar (f i)] : HasInvolutiveStar (∀ i, f i) :=
  { star_involutive := fun _ => funext$ fun _ => star_star _ }

instance  [∀ i, Monoidₓ (f i)] [∀ i, StarMonoid (f i)] : StarMonoid (∀ i, f i) :=
  { star_mul := fun _ _ => funext$ fun _ => star_mul _ _ }

instance  [∀ i, AddMonoidₓ (f i)] [∀ i, StarAddMonoid (f i)] : StarAddMonoid (∀ i, f i) :=
  { star_add := fun _ _ => funext$ fun _ => star_add _ _ }

instance  [∀ i, Semiringₓ (f i)] [∀ i, StarRing (f i)] : StarRing (∀ i, f i) :=
  { Pi.starAddMonoid, (Pi.starMonoid : StarMonoid (∀ i, f i)) with  }

instance  {R : Type w} [∀ i, HasScalar R (f i)] [HasStar R] [∀ i, HasStar (f i)] [∀ i, StarModule R (f i)] :
  StarModule R (∀ i, f i) :=
  { star_smul := fun r x => funext$ fun i => star_smul r (x i) }

end Pi

