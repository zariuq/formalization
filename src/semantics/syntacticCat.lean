import semantics.syntacticPoset
import categoryTheory.CCC
import Mathlib.CategoryTheory.Category.Preorder

open CategoryTheory
open deduction_basic

namespace synCat
  open synPoset

  variable {Form : Type}

  -- Form the category out of this poset
  def syn_cat [Der : has_struct_derives Form] : thin_cat (Form _eq)
    := thin_cat.from_preorder synPoset.syn_eq_pre
  instance [Der : has_struct_derives Form] : thin_cat (Form _eq) := syn_cat

  -- Methods for directly turning formulas into objects and derivations into morphisms
  def syn_obj [Der : has_struct_derives Form] (φ : Form) : Form _eq := 
    Form_eq_in φ
  def syn_hom [Der : has_struct_derives Form] :
      ∀ {φ ψ : Form}, (φ ⊢ ψ) → (syn_obj φ ⟶ syn_obj ψ) :=
  by
    intro φ ψ h
    exact CategoryTheory.homOfLE h

  def syn_hom_inv [Der : has_struct_derives Form] :
      ∀ {φ ψ : Form}, (syn_obj φ ⟶ syn_obj ψ) → (φ ⊢ ψ) :=
  by
    intro φ ψ H
    exact CategoryTheory.leOfHom H

  def derives_of_hom [Der : has_struct_derives Form] {φ ψ : Form} (f : syn_obj φ ⟶ syn_obj ψ) :
    Der.derives {φ} ψ :=
    CategoryTheory.leOfHom f

end synCat

-- Note: Lean 3 custom tactics removed during port.
