import Mathbin.Algebra.Homology.Single
import Mathbin.Tactic.Linarith.Default

/-!
# Augmentation and truncation of `ℕ`-indexed (co)chain complexes.
-/


open CategoryTheory

open CategoryTheory.Limits

open HomologicalComplex

universe v u

variable {V : Type u} [category.{v} V]

namespace ChainComplex

/-- The truncation of a `ℕ`-indexed chain complex,
deleting the object at `0` and shifting everything else down.
-/
@[simps]
def truncate [has_zero_morphisms V] : ChainComplex V ℕ ⥤ ChainComplex V ℕ where
  obj := fun C =>
    { x := fun i => C.X (i + 1), d := fun i j => C.d (i + 1) (j + 1),
      shape' := fun i j w => by
        apply C.shape
        simpa }
  map := fun C D f => { f := fun i => f.f (i + 1) }

/-- There is a canonical chain map from the truncation of a chain map `C` to
the "single object" chain complex consisting of the truncated object `C.X 0` in degree 0.
The components of this chain map are `C.d 1 0` in degree 0, and zero otherwise.
-/
def truncate_to [has_zero_object V] [has_zero_morphisms V] (C : ChainComplex V ℕ) :
    truncate.obj C ⟶ (single₀ V).obj (C.X 0) :=
  (to_single₀_equiv (truncate.obj C) (C.X 0)).symm
    ⟨C.d 1 0, by
      tidy⟩

variable [has_zero_morphisms V]

/-- We can "augment" a chain complex by inserting an arbitrary object in degree zero
(shifting everything else up), along with a suitable differential.
-/
def augment (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) : ChainComplex V ℕ where
  x := fun i =>
    match i with
    | 0 => X
    | i + 1 => C.X i
  d := fun i j =>
    match i, j with
    | 1, 0 => f
    | i + 1, j + 1 => C.d i j
    | _, _ => 0
  shape' := fun i j s => by
    simp at s
    rcases i with (_ | _ | i) <;>
      cases j <;>
        unfold_aux <;>
          try
            simp
    · simpa using s
      
    · rw [C.shape]
      simpa [← Ne.def, Nat.succ_ne_succ] using s
      
  d_comp_d' := fun i j k hij hjk => by
    rcases i with (_ | _ | i) <;>
      rcases j with (_ | _ | j) <;>
        cases k <;>
          unfold_aux <;>
            try
              simp
    cases i
    · exact w
      
    · rw [C.shape, zero_comp]
      simpa using i.succ_succ_ne_one.symm
      

@[simp]
theorem augment_X_zero (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) : (augment C f w).x 0 = X :=
  rfl

@[simp]
theorem augment_X_succ (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) (i : ℕ) :
    (augment C f w).x (i + 1) = C.X i :=
  rfl

@[simp]
theorem augment_d_one_zero (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
    (augment C f w).d 1 0 = f :=
  rfl

@[simp]
theorem augment_d_succ_succ (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) (i j : ℕ) :
    (augment C f w).d (i + 1) (j + 1) = C.d i j := by
  dsimp [augment]
  rcases i with (_ | i)
  rfl
  rfl

/-- Truncating an augmented chain complex is isomorphic (with components the identity)
to the original complex.
-/
def truncate_augment (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
    truncate.obj (augment C f w) ≅ C where
  Hom := { f := fun i => 𝟙 _ }
  inv :=
    { f := fun i => by
        cases i <;> exact 𝟙 _,
      comm' := fun i j => by
        cases i <;>
          cases j <;>
            · dsimp
              simp
               }
  hom_inv_id' := by
    ext i
    cases i <;>
      · dsimp
        simp
        
  inv_hom_id' := by
    ext i
    cases i <;>
      · dsimp
        simp
        

@[simp]
theorem truncate_augment_hom_f (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) (i : ℕ) :
    (truncate_augment C f w).Hom.f i = 𝟙 (C.X i) :=
  rfl

@[simp]
theorem truncate_augment_inv_f (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) (i : ℕ) :
    (truncate_augment C f w).inv.f i = 𝟙 ((truncate.obj (augment C f w)).x i) := by
  cases i <;> rfl

@[simp]
theorem chain_complex_d_succ_succ_zero (C : ChainComplex V ℕ) (i : ℕ) : C.d (i + 2) 0 = 0 := by
  rw [C.shape]
  simpa using i.succ_succ_ne_one.symm

/-- Augmenting a truncated complex with the original object and morphism is isomorphic
(with components the identity) to the original complex.
-/
def augment_truncate (C : ChainComplex V ℕ) : augment (truncate.obj C) (C.d 1 0) (C.d_comp_d _ _ _) ≅ C where
  Hom :=
    { f := fun i => by
        cases i <;> exact 𝟙 _,
      comm' := fun i j => by
        rcases i with (_ | _ | i) <;>
          cases j <;>
            · dsimp
              simp
               }
  inv :=
    { f := fun i => by
        cases i <;> exact 𝟙 _,
      comm' := fun i j => by
        rcases i with (_ | _ | i) <;>
          cases j <;>
            · dsimp
              simp
               }
  hom_inv_id' := by
    ext i
    cases i <;>
      · dsimp
        simp
        
  inv_hom_id' := by
    ext i
    cases i <;>
      · dsimp
        simp
        

@[simp]
theorem augment_truncate_hom_f_zero (C : ChainComplex V ℕ) : (augment_truncate C).Hom.f 0 = 𝟙 (C.X 0) :=
  rfl

@[simp]
theorem augment_truncate_hom_f_succ (C : ChainComplex V ℕ) (i : ℕ) :
    (augment_truncate C).Hom.f (i + 1) = 𝟙 (C.X (i + 1)) :=
  rfl

@[simp]
theorem augment_truncate_inv_f_zero (C : ChainComplex V ℕ) : (augment_truncate C).inv.f 0 = 𝟙 (C.X 0) :=
  rfl

@[simp]
theorem augment_truncate_inv_f_succ (C : ChainComplex V ℕ) (i : ℕ) :
    (augment_truncate C).inv.f (i + 1) = 𝟙 (C.X (i + 1)) :=
  rfl

/-- A chain map from a chain complex to a single object chain complex in degree zero
can be reinterpreted as a chain complex.

Ths is the inverse construction of `truncate_to`.
-/
def to_single₀_as_complex [has_zero_object V] (C : ChainComplex V ℕ) (X : V) (f : C ⟶ (single₀ V).obj X) :
    ChainComplex V ℕ :=
  let ⟨f, w⟩ := to_single₀_equiv C X f
  augment C f w

end ChainComplex

namespace CochainComplex

/-- The truncation of a `ℕ`-indexed cochain complex,
deleting the object at `0` and shifting everything else down.
-/
@[simps]
def truncate [has_zero_morphisms V] : CochainComplex V ℕ ⥤ CochainComplex V ℕ where
  obj := fun C =>
    { x := fun i => C.X (i + 1), d := fun i j => C.d (i + 1) (j + 1),
      shape' := fun i j w => by
        apply C.shape
        simpa }
  map := fun C D f => { f := fun i => f.f (i + 1) }

/-- There is a canonical chain map from the truncation of a cochain complex `C` to
the "single object" cochain complex consisting of the truncated object `C.X 0` in degree 0.
The components of this chain map are `C.d 0 1` in degree 0, and zero otherwise.
-/
def to_truncate [has_zero_object V] [has_zero_morphisms V] (C : CochainComplex V ℕ) :
    (single₀ V).obj (C.X 0) ⟶ truncate.obj C :=
  (from_single₀_equiv (truncate.obj C) (C.X 0)).symm
    ⟨C.d 0 1, by
      tidy⟩

variable [has_zero_morphisms V]

/-- We can "augment" a cochain complex by inserting an arbitrary object in degree zero
(shifting everything else up), along with a suitable differential.
-/
def augment (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) : CochainComplex V ℕ where
  x := fun i =>
    match i with
    | 0 => X
    | i + 1 => C.X i
  d := fun i j =>
    match i, j with
    | 0, 1 => f
    | i + 1, j + 1 => C.d i j
    | _, _ => 0
  shape' := fun i j s => by
    simp at s
    rcases j with (_ | _ | j) <;>
      cases i <;>
        unfold_aux <;>
          try
            simp
    · simpa using s
      
    · rw [C.shape]
      simp only [ComplexShape.up_rel]
      contrapose! s
      rw [← s]
      
  d_comp_d' := fun i j k hij hjk => by
    rcases k with (_ | _ | k) <;>
      rcases j with (_ | _ | j) <;>
        cases i <;>
          unfold_aux <;>
            try
              simp
    cases k
    · exact w
      
    · rw [C.shape, comp_zero]
      simp only [Nat.nat_zero_eq_zero, ComplexShape.up_rel, zero_addₓ]
      exact (Nat.one_lt_succ_succ _).Ne
      

@[simp]
theorem augment_X_zero (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) :
    (augment C f w).x 0 = X :=
  rfl

@[simp]
theorem augment_X_succ (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) (i : ℕ) :
    (augment C f w).x (i + 1) = C.X i :=
  rfl

@[simp]
theorem augment_d_zero_one (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) :
    (augment C f w).d 0 1 = f :=
  rfl

@[simp]
theorem augment_d_succ_succ (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) (i j : ℕ) :
    (augment C f w).d (i + 1) (j + 1) = C.d i j := by
  dsimp [augment]
  rcases i with (_ | i)
  rfl
  rfl

/-- Truncating an augmented cochain complex is isomorphic (with components the identity)
to the original complex.
-/
def truncate_augment (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) :
    truncate.obj (augment C f w) ≅ C where
  Hom := { f := fun i => 𝟙 _ }
  inv :=
    { f := fun i => by
        cases i <;> exact 𝟙 _,
      comm' := fun i j => by
        cases i <;>
          cases j <;>
            · dsimp
              simp
               }
  hom_inv_id' := by
    ext i
    cases i <;>
      · dsimp
        simp
        
  inv_hom_id' := by
    ext i
    cases i <;>
      · dsimp
        simp
        

@[simp]
theorem truncate_augment_hom_f (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) (i : ℕ) :
    (truncate_augment C f w).Hom.f i = 𝟙 (C.X i) :=
  rfl

@[simp]
theorem truncate_augment_inv_f (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) (i : ℕ) :
    (truncate_augment C f w).inv.f i = 𝟙 ((truncate.obj (augment C f w)).x i) := by
  cases i <;> rfl

@[simp]
theorem cochain_complex_d_succ_succ_zero (C : CochainComplex V ℕ) (i : ℕ) : C.d 0 (i + 2) = 0 := by
  rw [C.shape]
  simp only [ComplexShape.up_rel, zero_addₓ]
  exact (Nat.one_lt_succ_succ _).Ne

/-- Augmenting a truncated complex with the original object and morphism is isomorphic
(with components the identity) to the original complex.
-/
def augment_truncate (C : CochainComplex V ℕ) : augment (truncate.obj C) (C.d 0 1) (C.d_comp_d _ _ _) ≅ C where
  Hom :=
    { f := fun i => by
        cases i <;> exact 𝟙 _,
      comm' := fun i j => by
        rcases j with (_ | _ | j) <;>
          cases i <;>
            · dsimp
              simp
               }
  inv :=
    { f := fun i => by
        cases i <;> exact 𝟙 _,
      comm' := fun i j => by
        rcases j with (_ | _ | j) <;>
          cases i <;>
            · dsimp
              simp
               }
  hom_inv_id' := by
    ext i
    cases i <;>
      · dsimp
        simp
        
  inv_hom_id' := by
    ext i
    cases i <;>
      · dsimp
        simp
        

@[simp]
theorem augment_truncate_hom_f_zero (C : CochainComplex V ℕ) : (augment_truncate C).Hom.f 0 = 𝟙 (C.X 0) :=
  rfl

@[simp]
theorem augment_truncate_hom_f_succ (C : CochainComplex V ℕ) (i : ℕ) :
    (augment_truncate C).Hom.f (i + 1) = 𝟙 (C.X (i + 1)) :=
  rfl

@[simp]
theorem augment_truncate_inv_f_zero (C : CochainComplex V ℕ) : (augment_truncate C).inv.f 0 = 𝟙 (C.X 0) :=
  rfl

@[simp]
theorem augment_truncate_inv_f_succ (C : CochainComplex V ℕ) (i : ℕ) :
    (augment_truncate C).inv.f (i + 1) = 𝟙 (C.X (i + 1)) :=
  rfl

/-- A chain map from a single object cochain complex in degree zero to a cochain complex
can be reinterpreted as a cochain complex.

Ths is the inverse construction of `to_truncate`.
-/
def from_single₀_as_complex [has_zero_object V] (C : CochainComplex V ℕ) (X : V) (f : (single₀ V).obj X ⟶ C) :
    CochainComplex V ℕ :=
  let ⟨f, w⟩ := from_single₀_equiv C X f
  augment C f w

end CochainComplex

