import semantics.syntacticCat_cartesian
import semantics.syntacticPoset_monadic
import Mathlib.CategoryTheory.Monad.Basic

open deduction_basic
open deduction_monadic
open synPoset_monadic
open CategoryTheory

namespace synCat_monadic
 
lemma diamond_le {Form : Type} [Diam : has_diamond Form] {X Y : Form _eq} :
    X ≤ Y → diamond_eq X ≤ diamond_eq Y := by
  intro hXY
  revert hXY
  refine Quotient.inductionOn₂ X Y ?_
  intro φ ψ hφψ
  dsimp [diamond_eq, synPoset.Form_eq_order] at hφψ ⊢
  exact Diam.dmap hφψ

lemma diamond_pure_le {Form : Type} [Diam : has_diamond Form] :
    ∀ X : Form _eq, X ≤ diamond_eq X := by
  intro X
  refine Quotient.inductionOn X ?_
  intro φ
  dsimp [diamond_eq, synPoset.Form_eq_order]
  exact Diam.dpure (derive_refl φ)

lemma diamond_join_le {Form : Type} [Diam : has_diamond Form] :
    ∀ X : Form _eq, diamond_eq (diamond_eq X) ≤ diamond_eq X := by
  intro X
  refine Quotient.inductionOn X ?_
  intro φ
  dsimp [diamond_eq, synPoset.Form_eq_order]
  apply Diam.djoin
  exact derive_refl (◇◇φ)

def diamond_functor {Form : Type} [Diam : has_diamond Form] : (Form _eq) ⥤ (Form _eq) :=
{
  obj := diamond_eq,
  map := by
    intro X Y f
    exact CategoryTheory.homOfLE (diamond_le (CategoryTheory.leOfHom f))
  ,
  map_id := by
    intro X
    apply thin_cat.K
  ,
  map_comp := by
    intro X Y Z f g
    apply thin_cat.K
}

def diamond_monad {Form : Type} [Diam : has_diamond Form] : CategoryTheory.Monad (Form _eq) :=
{
  toFunctor := diamond_functor,
  η := {
    app := fun X => CategoryTheory.homOfLE (diamond_pure_le X),
    naturality := by
      intro X Y f
      apply thin_cat.K
  },
  μ := {
    app := fun X => CategoryTheory.homOfLE (diamond_join_le X),
    naturality := by
      intro X Y f
      apply thin_cat.K
  },
  assoc := by
    intro X
    apply thin_cat.K,
  left_unit := by
    intro X
    apply thin_cat.K,
  right_unit := by
    intro X
    apply thin_cat.K
}
end synCat_monadic

/- Instances -/
namespace MPPC_monad

  open MPPC_synPoset

  def MPPC_diamond : CategoryTheory.Monad MPPC_eq := synCat_monadic.diamond_monad

end MPPC_monad
