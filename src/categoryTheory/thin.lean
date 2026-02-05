import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Set.Basic

universe v u u₂ v₂
open CategoryTheory

class thin_cat (C : Type u) extends Category C where
  K : ∀ (X Y : C) (f g : X ⟶ Y), f = g



namespace thin_cat

  def preorder_cat_full {C : Type u} [Preorder C] {X Y : C} (F : X ⟶ Y)
    : ∃ p : X ≤ Y, F = CategoryTheory.homOfLE p := by
    refine ⟨CategoryTheory.leOfHom F, ?_⟩
    simpa using (CategoryTheory.homOfLE_leOfHom (h := F)).symm

  def from_preorder {P : Type u} (P_struct : Preorder P) : thin_cat P := by
    classical
    let _ : Preorder P := P_struct
    refine { toCategory := (inferInstance : Category P), K := ?_ }
    intro X Y F G
    exact Subsingleton.elim _ _

end thin_cat
