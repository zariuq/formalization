import deduction.deduction
import Mathlib.Order.BoundedOrder.Basic

namespace deduction_cart

open deduction_basic

/- Truth -/
class has_ltop (Form : Type u) extends has_struct_derives Form where
  top : Form
  truth : ∀ {Φ : Hyp}, derives Φ top

instance {Form : Type u} [Der : has_ltop Form] : Top Form := ⟨Der.top⟩

/- Logical And -/
class has_and (Form : Type u) extends has_ltop Form where
  and : Form → Form → Form
  and_intro {Φ} {φ ψ : Form} : derives Φ φ → derives Φ ψ → derives Φ (and φ ψ)
  and_eliml {Φ} {φ ψ : Form} : derives Φ (and φ ψ) → derives Φ φ
  and_elimr {Φ} {φ ψ : Form} : derives Φ (and φ ψ) → derives Φ ψ

infix:79 " & " => has_and.and

/- Implication -/
class has_impl (Form : Type u) extends has_and Form where
  impl : Form → Form → Form
  impl_intro {Φ} (φ) {ψ} : derives (insert φ Φ) ψ → derives Φ (impl φ ψ)
  impl_elim {Φ} (φ) {ψ} : derives Φ (impl φ ψ) → derives Φ φ → derives Φ ψ

infix:80 " ⊃ " => has_impl.impl

/- All three -/
end deduction_cart


namespace cart_x
  open deduction_basic
  open deduction_cart

  lemma and_intro1 {Form : Type u} [Der : has_and Form] {φ ψ : Form} :
    Der.derives (Der.insertHyp.insert ψ {φ}) (φ & ψ) := by
    apply Der.and_intro
    apply Der.weak1
    apply derive_refl
    apply Der.hyp
    apply Der.inInsert

  lemma and_internal {Form : Type u} [Der : has_and Form] {φ ψ θ : Form} :
    (φ & ψ ⊢ θ) → Der.derives (Der.insertHyp.insert ψ {φ}) θ := by
    intro h
    apply Der.derive_Trans (φ & ψ)
    · exact and_intro1
    · exact h

  lemma and_eliml1 {Form : Type u} [Der : has_and Form] {φ ψ : Form} :
    φ & ψ ⊢ φ := by
    apply Der.and_eliml
    apply derive_refl

  lemma and_elimr1 {Form : Type u} [Der : has_and Form] {φ ψ : Form} :
    φ & ψ ⊢ ψ := by
    apply Der.and_elimr
    apply derive_refl

  lemma modus_ponens {Form : Type u} [Der : has_impl Form] :
    ∀ {φ ψ : Form}, (φ ⊃ ψ) & φ ⊢ ψ := by
    intro φ ψ
    apply Der.impl_elim φ
    · apply and_eliml1
    · apply and_elimr1

  lemma impl_ε {Form : Type u} [Der : has_impl Form] :
    ∀ {φ ψ θ : Form}, φ & ψ ⊢ θ  →  φ ⊢ ψ ⊃ θ := by
    intro φ ψ θ h
    apply Der.impl_intro
    apply Der.derive_Trans
    · apply and_intro1
    · exact h

  lemma insert_trans {Form : Type u} [Der : has_impl Form] {Φ} {φ ψ : Form} :
    (φ ⊢ ψ) → Der.derives (Der.insertHyp.insert φ Φ) ψ := by
    intro h
    apply Der.derive_Trans φ
    · apply Der.hyp
      apply Der.inInsert
    · exact h
end cart_x
