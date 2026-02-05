import deduction.deduction
import deduction.deduction_cartesian

namespace deduction_monadic

open deduction_basic
open deduction_cart

/- Diamond -/
class has_diamond (Form : Type u) extends has_struct_derives Form where
  diamond : Form → Form
  dmap  : ∀ {Φ : Hyp} {φ ψ : Form},
    derives (insert φ Φ) ψ → derives (insert (diamond φ) Φ) (diamond ψ)
  dpure : ∀ {Φ : Hyp} {φ : Form},
    derives Φ φ → derives Φ (diamond φ)
  djoin : ∀ {Φ : Hyp} {φ : Form},
    derives Φ (diamond (diamond φ)) → derives Φ (diamond φ)

notation:81 "◇" φ => has_diamond.diamond φ

end deduction_monadic
