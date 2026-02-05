import deduction.deduction
import Mathlib.CategoryTheory.Category.Preorder
open deduction_basic

namespace synPoset

  variable {Form : Type}

  instance syn_preorder [Der : has_struct_derives Form] : Preorder Form :=
  { le := fun φ ψ => φ ⊢ ψ
    le_refl := derive_refl
    le_trans := by
      intro φ ψ θ hφψ hψθ
      exact derive_trans ψ hφψ hψθ }

  def inter_der [Der : has_struct_derives Form] (φ ψ : Form) : Prop :=
    φ ⊢ ψ ∧ ψ ⊢ φ

  infix:78 "⊣⊢" => inter_der

  instance syn_setoid [Der : has_struct_derives Form] : Setoid Form :=
  { r := (· ⊣⊢ ·)
    iseqv := by
      refine ⟨?_, ?_, ?_⟩
      · intro φ
        exact ⟨derive_refl φ, derive_refl φ⟩
      · intro φ ψ h
        exact ⟨h.2, h.1⟩
      · intro φ ψ θ hφψ hψθ
        refine ⟨?_, ?_⟩
        · exact derive_trans ψ hφψ.1 hψθ.1
        · exact derive_trans ψ hψθ.2 hφψ.2 }

  -- notation (name:=syn_setoid.r) φ `⊣⊢` ψ :78 := syn_setoid.r φ ψ 

  def Form_eq [Der : has_struct_derives Form] : Type := Quotient (syn_setoid (Form := Form))
  def Form_eq_x (F : Type) [Der : has_struct_derives F] : Type := @Form_eq F Der

  notation:max F " _eq" => Form_eq_x F

  def Form_eq_in [Der : has_struct_derives Form] (φ : Form) : Form _eq :=
    Quotient.mk (syn_setoid (Form := Form)) φ

  notation "⦃" φ "⦄" => Form_eq_in φ

  -- Lemmas that ⊢ respects ⊣⊢
  lemma syn_preorder_liftable1 [Der : has_struct_derives Form] :
    ∀ φ ψ θ : Form, ψ ⊣⊢ θ → (φ ⊢ ψ) = (φ ⊢ θ) := by
    intro φ ψ θ ψiffθ
    cases ψiffθ with
    | intro ψθ θψ =>
      apply propext
      constructor
      · intro φψ
        apply derive_trans
        · exact φψ
        · exact ψθ
      · intro φθ
        apply derive_trans
        · exact φθ
        · exact θψ

  lemma syn_preorder_liftable2 [Der : has_struct_derives Form] :
    ∀ φ ψ θ : Form, φ ⊣⊢ ψ → (φ ⊢ θ) = (ψ ⊢ θ) := by
    intro φ ψ θ φiffψ
    cases φiffψ with
    | intro φψ ψφ =>
      apply propext
      constructor
      · intro φθ
        apply derive_trans
        · exact ψφ
        · exact φθ
      · intro ψθ
        apply derive_trans
        · exact φψ
        · exact ψθ

  def Form_eq_order [Der : has_struct_derives Form] : @Form_eq Form Der → @Form_eq Form Der → Prop :=
    fun x y =>
      Quotient.liftOn₂ x y (fun φ ψ => φ ⊢ ψ) (by
        intro a b a' b' ha hb
        have h1 : (a ⊢ b) = (a' ⊢ b) :=
          syn_preorder_liftable2 (φ := a) (ψ := a') (θ := b) ha
        have h2 : (a' ⊢ b) = (a' ⊢ b') :=
          syn_preorder_liftable1 (φ := a') (ψ := b) (θ := b') hb
        exact h1.trans h2)

  instance syn_poset [Der : has_struct_derives Form] : PartialOrder (@Form_eq Form Der) :=
  { le := @Form_eq_order Form Der,
    le_refl := by
      intro x
      refine Quotient.inductionOn x ?_
      intro φ
      dsimp [Form_eq_order, syn_preorder]
      apply derive_refl
    ,
    le_trans := by
      intro a b c hab hbc
      revert hab hbc
      refine Quotient.inductionOn₃ a b c ?_
      intro φ ψ θ hab hbc
      have hab' : φ ⊢ ψ := by simpa [Form_eq_order] using hab
      have hbc' : ψ ⊢ θ := by simpa [Form_eq_order] using hbc
      simpa [Form_eq_order] using derive_trans ψ hab' hbc'
    ,
    le_antisymm := by
      intro a b hab hba
      revert hab hba
      refine Quotient.inductionOn₂ a b ?_
      intro φ ψ hab hba
      have hab' : φ ⊢ ψ := by simpa [Form_eq_order] using hab
      have hba' : ψ ⊢ φ := by simpa [Form_eq_order] using hba
      apply Quotient.sound
      exact ⟨hab', hba'⟩
  }

  instance syn_eq_pre {Form : Type} [Der : has_struct_derives Form] : Preorder (Form _eq) :=
    (syn_poset (Form := Form) (Der := Der)).toPreorder

end synPoset
