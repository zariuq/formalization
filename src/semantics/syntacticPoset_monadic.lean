import semantics.syntacticCat_cartesian


namespace synPoset_monadic

open synPoset
open deduction_basic
open deduction_cart
open deduction_monadic

variable {Form : Type}


lemma diamond_liftable [Der : has_diamond Form] : ∀ φ φ' : Form,
  (φ ⊣⊢ φ') → ⦃ ◇φ ⦄ = ⦃◇φ'⦄ := by
  intro φ φ' h
  apply Quotient.sound
  cases h with
  | intro φφ' φ'φ =>
    constructor
    · apply Der.dmap
      exact φφ'
    · apply Der.dmap
      exact φ'φ

def diamond_eq [Der : has_diamond Form] : Form _eq → Form _eq :=
  Quotient.lift (fun φ => ⦃Der.diamond φ⦄) diamond_liftable

end synPoset_monadic
