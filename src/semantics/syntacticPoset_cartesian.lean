import semantics.syntacticPoset
import deduction.deduction_cartesian
import deduction.PPC_natDeduct
import deduction.MPPC_natDeduct
import Mathlib.Order.Notation

namespace synPoset_cartesian

open synPoset
open deduction_basic
open deduction_cart
open deduction_monadic

variable {Form : Type}

  -- ⊤ : Form_eq
  instance [Der : has_ltop Form] : Top (Form _eq) := ⟨⦃Der.top⦄⟩

  lemma and_liftable1 [Der : has_and Form] :
    ∀ φ ψ ψ' : Form, (ψ ⊣⊢ ψ') → ⦃φ & ψ⦄ = ⦃φ & ψ'⦄ := by
    intro φ ψ ψ' h
    apply Quotient.sound
    cases h with
    | intro ψψ' ψ'ψ =>
      constructor
      · apply Der.and_intro
        · apply cart_x.and_eliml1
        · apply derive_trans
          · apply cart_x.and_elimr1
          · exact ψψ'
      · apply Der.and_intro
        · apply cart_x.and_eliml1
        · apply derive_trans
          · apply cart_x.and_elimr1
          · exact ψ'ψ

  lemma and_liftable2 [Der : has_and Form] :
    ∀ φ φ' ψ : Form, (φ ⊣⊢ φ') → ⦃φ & ψ⦄ = ⦃φ' & ψ⦄ := by
      intro φ φ' ψ h
      apply Quotient.sound
      cases h with
      | intro φφ' φ'φ =>
        constructor
        · apply Der.and_intro
          · apply derive_trans φ
            · apply cart_x.and_eliml1
            · exact φφ'
          · apply cart_x.and_elimr1
        · apply Der.and_intro
          · apply derive_trans φ'
            · apply cart_x.and_eliml1
            · exact φ'φ
          · apply cart_x.and_elimr1

  def and_eq [Der : has_and Form] : Form _eq → Form _eq → Form _eq :=
    fun x y =>
      Quotient.liftOn₂ x y (fun φ ψ => ⦃φ & ψ⦄) (by
        intro a b a' b' ha hb
        exact (and_liftable2 (φ := a) (φ' := a') (ψ := b) ha).trans
          (and_liftable1 (φ := a') (ψ := b) (ψ' := b') hb))

  -- ⊓ : Form_eq → Form_eq → Form_eq
  instance [Der : has_and Form] : Min (Form _eq) := ⟨and_eq⟩



  lemma impl_liftable1 [Der : has_impl Form] :
    ∀ φ ψ ψ' : Form, (ψ ⊣⊢ ψ') → ⦃Der.impl φ ψ⦄ = ⦃Der.impl φ ψ'⦄ := by
      intro φ ψ ψ' h
      apply Quotient.sound
      cases h with
      | intro ψψ' ψ'ψ =>
        constructor
        · apply Der.impl_intro
          apply Der.derive_Trans ψ
          · apply cart_x.and_internal
            exact cart_x.modus_ponens
          · exact ψψ'
        · apply Der.impl_intro
          apply Der.derive_Trans ψ'
          · apply cart_x.and_internal
            exact cart_x.modus_ponens
          · exact ψ'ψ

  lemma impl_liftable2 [Der : has_impl Form] :
    ∀ φ φ' ψ : Form, (φ ⊣⊢ φ') → ⦃Der.impl φ ψ⦄ = ⦃Der.impl φ' ψ⦄ := by
      intro φ φ' ψ h
      apply Quotient.sound
      cases h with
      | intro φφ' φ'φ =>
        constructor
        · apply Der.impl_intro
          apply Der.impl_elim φ
          · apply Der.weak1
            apply derive_refl
          · apply cart_x.insert_trans
            exact φ'φ
        · apply Der.impl_intro
          apply Der.impl_elim φ'
          · apply Der.weak1
            apply derive_refl
          · apply cart_x.insert_trans
            exact φφ'


  def impl_eq [Der : has_impl Form] : Form _eq → Form _eq → Form _eq :=
    fun x y =>
      Quotient.liftOn₂ x y (fun φ ψ => ⦃Der.impl φ ψ⦄) (by
        intro a b a' b' ha hb
        exact (impl_liftable2 (φ := a) (φ' := a') (ψ := b) ha).trans
          (impl_liftable1 (φ := a') (ψ := b) (ψ' := b') hb))

  -- ⇨ : Form_eq → Form_eq → Form_eq
  instance [Der : has_impl Form] : HImp (Form _eq) := ⟨impl_eq⟩

end synPoset_cartesian

/- Instances -/
namespace PPC_synPoset 

  open synPoset
  open PPC_defn
  open synPoset_cartesian

  def PPC_eq := @Form_eq PPC_Form PPC_has_derives.PPC_Der

end PPC_synPoset

namespace MPPC_synPoset 

  open synPoset
  open MPPC_defn
  open synPoset_cartesian

  def MPPC_eq := @Form_eq MPPC_Form MPPC_has_derives.MPPC_Der
  
end MPPC_synPoset
