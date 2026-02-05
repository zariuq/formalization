import categoryTheory.thin
import Mathlib.Data.Set.Basic

universe v u u₂ v₂
open CategoryTheory

namespace specialCats

class FP_cat (C : Type u) extends Category C where
  -- Terminal object
  unit : C
  term : ∀ X : C, X ⟶ unit
  unit_η : ∀ (X : C) (f : X ⟶ unit), f = term X
  -- Binary products
  prod : C → C → C
  pr1 : ∀ {X Y : C}, (prod X Y) ⟶ X
  pr2 : ∀ {X Y : C}, (prod X Y) ⟶ Y
  pair : ∀ {X Y Z : C}, (Z ⟶ X) → (Z ⟶ Y) → (Z ⟶ (prod X Y))
  prod_β1 : ∀ {X Y Z : C} {f : Z ⟶ X} {g : Z ⟶ Y}, (pair f g) ≫ pr1 = f
  prod_β2 : ∀ {X Y Z : C} {f : Z ⟶ X} {g : Z ⟶ Y}, (pair f g) ≫ pr2 = g
  prod_η : ∀ {X Y : C}, pair pr1 pr2 = 𝟙 (prod X Y)

instance {C : Type u} [FP_cat C] : One C :=
{
    one := FP_cat.unit
}
instance {C : Type u} [FP_cat C] : Mul C :=
{
    mul := fun X Y => FP_cat.prod X Y
}

def homprod {C : Type u} [FP_cat C] {W X Y Z : C}
   (f : W ⟶ X) (g : Y ⟶ Z) : W * Y ⟶ X * Z :=
   FP_cat.pair (FP_cat.pr1 ≫ f) (FP_cat.pr2 ≫ g)
infixr:100 " *** " => homprod

-- #check category

class CC_cat (C : Type u) extends FP_cat C where
  exp : C → C → C
  eval : ∀ {Y Z : C}, (exp Y Z) * Y ⟶ Z
  curry : ∀ {X Y Z : C}, (X * Y ⟶ Z) → (X ⟶ (exp Y Z))
  curry_β : ∀ {X Y Z : C} (u : X * Y ⟶ Z), ((curry u) *** 𝟙 Y) ≫ eval = u
  curry_η : ∀ {X Y Z : C} (v : X ⟶ (exp Y Z)), curry ((v *** 𝟙 Y) ≫ eval) = v

infixr:80 " ⟹ " => CC_cat.exp


end specialCats


namespace downsetCCC

open specialCats

class downsets (P : Type u) [PartialOrder P] : Type u where
  X : Set P
  down_closed : ∀ (x x' : P), x ≤ x' → x' ∈ X → x ∈ X

instance {P : Type u} [PartialOrder P] : HasSubset (downsets P) :=
  ⟨fun A B => ∀ x, x ∈ A.X → x ∈ B.X⟩

theorem downset_ext {P : Type u} [PartialOrder P] : ∀ {A B : downsets P}, A.X = B.X → A = B
| ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

instance {P : Type u} [PartialOrder P] : Membership P (downsets P) :=
  ⟨fun A x => x ∈ A.X⟩

def down_closed_external {P : Type u} [PartialOrder P] :
  ∀ (X : downsets P) (x x' : P), x ≤ x' → x' ∈ X → x ∈ X := by
  intro X x x' xlex' x'inX
  exact X.down_closed x x' xlex' x'inX

instance {P : Type u} [PartialOrder P] : Inter (downsets P) :=
  ⟨fun ⟨A, A_down⟩ ⟨B, B_down⟩ =>
    ⟨A ∩ B, by
      intro x x' h x'inboth
      cases x'inboth with
      | intro inA inB =>
        constructor
        · apply A_down
          · exact h
          · exact inA
        · apply B_down
          · exact h
          · exact inB
    ⟩⟩

def down {P : Type u} (P_struct : PartialOrder P) : PartialOrder (downsets P) :=
{
  le := (· ⊆ ·),
  le_refl := by
    intro A x h
    exact h,
  le_antisymm := by
    intro A B h1 h2
    apply downset_ext
    apply Set.ext
    intro x
    constructor
    · intro hx
      exact h1 x hx
    · intro hx
      exact h2 x hx,
  le_trans := by
    intro A B C h1 h2 x h
    apply h2
    apply h1
    exact h
}

def down_pre {P : Type u} [P_struct : PartialOrder P] : Preorder (downsets P) :=
  (down P_struct).toPreorder

instance {P : Type u} [PartialOrder P] : Preorder (downsets P) :=
  down_pre

instance {P : Type u} [PartialOrder P] : thin_cat (downsets P) :=
  thin_cat.from_preorder down_pre

def downset_embed {P : Type u} [P_struct : PartialOrder P] : P → downsets P :=
  fun p =>
    ⟨{x : P | x ≤ p}, by
      intro x x' xlex' h
      exact le_trans xlex' h
    ⟩

def down_exp {P : Type u} [P_struct : PartialOrder P] (X Y : downsets P) : downsets P :=
  ⟨{x : P | ∀ (z : P), z ≤ x ∧ z ∈ X → z ∈ Y}, by
    intro x x' xlex' h z hz
    apply h
    rcases hz with ⟨zlex, zinX⟩
    exact ⟨le_trans zlex xlex', zinX⟩
  ⟩

instance {P : Type u} [P_struct : PartialOrder P] : CC_cat (downsets P) :=
{
  unit := ⟨Set.univ, by intro x x' _ _; exact True.intro⟩,
  term := by
    intro X
    cases X with
    | mk A A_down =>
      apply CategoryTheory.homOfLE
      intro x h
      exact True.intro,
  unit_η := fun X f => by apply thin_cat.K,
  prod := (· ∩ ·),
  pr1 := by
    intro X Y
    cases X with
    | mk A A_down =>
      cases Y with
      | mk B B_down =>
        apply CategoryTheory.homOfLE
        intro x h
        exact h.left,
  pr2 := by
    intro X Y
    cases X with
    | mk A A_down =>
      cases Y with
      | mk B B_down =>
        apply CategoryTheory.homOfLE
        intro x h
        exact h.right,
  pair := by
    intro X Y Z F G
    have k : Z ⊆ X := CategoryTheory.leOfHom F
    have l : Z ⊆ Y := CategoryTheory.leOfHom G
    cases X with
    | mk A A_down =>
      cases Y with
      | mk B B_down =>
        cases Z with
        | mk C C_down =>
          apply CategoryTheory.homOfLE
          intro z h
          constructor
          · exact k z h
          · exact l z h,
  prod_β1 := by
    intro X Y Z f g
    apply thin_cat.K,
  prod_β2 := by
    intro X Y Z f g
    apply thin_cat.K,
  prod_η := by
    intro X Y
    apply thin_cat.K,
  exp := down_exp,
  eval := by
    intro X Y
    cases X with
    | mk A A_down =>
      cases Y with
      | mk B B_down =>
        apply CategoryTheory.homOfLE
        intro z h
        rcases h with ⟨zin_exp, zin_A⟩
        dsimp at zin_exp
        apply zin_exp
        exact ⟨le_rfl, zin_A⟩,
  curry := by
    intro X Y Z XYleZ
    have betterXYleZ : X ∩ Y ⊆ Z := CategoryTheory.leOfHom XYleZ
    cases X with
    | mk A A_down =>
      cases Y with
      | mk B B_down =>
        cases Z with
        | mk C C_down =>
          apply CategoryTheory.homOfLE
          intro z zinA
          dsimp [down_exp]
          intro z' hz
          rcases hz with ⟨z'lez, z'inB⟩
          have z'inA : z' ∈ A := by
            apply A_down
            · exact z'lez
            · exact zinA
          have ABleC : A ∩ B ⊆ C := by
            intro t ht
            exact betterXYleZ t ht
          exact ABleC (a := z') ⟨z'inA, z'inB⟩,
  curry_β := by
    intro X Y Z u
    apply thin_cat.K,
  curry_η := by
    intro X Y Z v
    apply thin_cat.K
}

end downsetCCC
