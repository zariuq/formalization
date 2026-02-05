import semantics.syntacticCat
import semantics.syntacticPoset_cartesian
import categoryTheory.CCC
import Mathlib.CategoryTheory.Monad.Basic

open deduction_cart
open deduction_monadic
open synPoset_cartesian
open synCat
open specialCats

namespace synCat_cartesian

instance syn_FP_cat {Form : Type} [And : has_and Form] : FP_cat (Form _eq) :=
{
  toCategory := (inferInstance : CategoryTheory.Category (Form _eq)),
  unit := syn_obj And.top,
  term := by
    intro X
    refine CategoryTheory.homOfLE ?_
    refine Quotient.inductionOn X ?_
    intro φ
    simpa [synPoset.Form_eq_order, syn_obj] using And.truth (Φ := {φ})
  ,
  unit_η := fun X f => by apply thin_cat.K,
  prod := and_eq,
  pr1 := by
    intro X Y
    refine CategoryTheory.homOfLE ?_
    refine Quotient.inductionOn₂ X Y ?_
    intro φ ψ
    simpa [synPoset.Form_eq_order, and_eq] using cart_x.and_eliml1 (φ := φ) (ψ := ψ)
  ,
  pr2 := by
    intro X Y
    refine CategoryTheory.homOfLE ?_
    refine Quotient.inductionOn₂ X Y ?_
    intro φ ψ
    simpa [synPoset.Form_eq_order, and_eq] using cart_x.and_elimr1 (φ := φ) (ψ := ψ)
  ,
  pair := by
    intro X Y Z f g
    have hf : Z ≤ X := CategoryTheory.leOfHom f
    have hg : Z ≤ Y := CategoryTheory.leOfHom g
    refine CategoryTheory.homOfLE ?_
    revert hf hg
    refine Quotient.inductionOn₃ X Y Z ?_
    intro φ ψ θ hf hg
    have hf' : θ ⊢ φ := by simpa [synPoset.Form_eq_order] using hf
    have hg' : θ ⊢ ψ := by simpa [synPoset.Form_eq_order] using hg
    have hθ : θ ⊢ φ & ψ := And.and_intro hf' hg'
    simpa [synPoset.Form_eq_order, and_eq] using hθ
  ,
  prod_β1 := by
    intro X Y Z f g
    apply thin_cat.K,
  prod_β2 := by
    intro X Y Z f g
    apply thin_cat.K,
  prod_η := by
    intro X Y
    apply thin_cat.K
}
instance syn_CC_cat {Form : Type} [Impl : has_impl Form] : CC_cat (Form _eq) :=
{
  toFP_cat := syn_FP_cat,
  exp := impl_eq,
  eval := by
    intro Y Z
    refine CategoryTheory.homOfLE ?_
    refine Quotient.inductionOn₂ Y Z ?_
    intro φ ψ
    simpa [synPoset.Form_eq_order, and_eq, impl_eq] using cart_x.modus_ponens (φ := φ) (ψ := ψ)
  ,
  curry := by
    intro X Y Z f
    have h : X * Y ≤ Z := CategoryTheory.leOfHom f
    refine CategoryTheory.homOfLE ?_
    revert h
    refine Quotient.inductionOn₃ X Y Z ?_
    intro φ ψ θ h
    have h' : φ & ψ ⊢ θ := by simpa [synPoset.Form_eq_order, and_eq] using h
    have : φ ⊢ ψ ⊃ θ := cart_x.impl_ε (φ := φ) (ψ := ψ) (θ := θ) h'
    simpa [synPoset.Form_eq_order, impl_eq] using this
  ,
  curry_β := by
    intro X Y Z u
    apply thin_cat.K,
  curry_η := by
    intro X Y Z v
    apply thin_cat.K,
}

end synCat_cartesian


/- Instances -/
namespace PPC_synCat

  open synPoset
  open PPC_defn
  open synPoset_cartesian
  open PPC_synPoset

  def ℂ_PPC : thin_cat PPC_eq := syn_cat 
  instance : FP_cat PPC_eq := synCat_cartesian.syn_FP_cat
  instance : CC_cat PPC_eq := synCat_cartesian.syn_CC_cat

end PPC_synCat

namespace MPPC_synCat

  open synPoset
  open MPPC_defn
  open synPoset_cartesian
  open MPPC_synPoset

  def ℂ_MPPC : thin_cat MPPC_eq := syn_cat 
  instance : FP_cat MPPC_eq := synCat_cartesian.syn_FP_cat
  instance : CC_cat MPPC_eq := synCat_cartesian.syn_CC_cat

end MPPC_synCat
