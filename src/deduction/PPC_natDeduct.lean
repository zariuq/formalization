import deduction.deduction_cartesian
import Mathlib.Data.Set.Insert
open deduction_basic

namespace PPC_defn

    inductive PPC_Form : Type
    | top : PPC_Form
    | var : ℕ → PPC_Form
    | and : PPC_Form → PPC_Form → PPC_Form
    | impl : PPC_Form → PPC_Form → PPC_Form


    @[reducible] def PPC_Hyp : Type := Set PPC_Form

    instance : Union PPC_Hyp := inferInstance
    instance : Membership PPC_Form PPC_Hyp := inferInstance
    instance : Insert PPC_Form PPC_Hyp := inferInstance
    instance : EmptyCollection PPC_Hyp := inferInstance


    inductive PPC_derives : PPC_Hyp → PPC_Form → Prop 
    | hyp {Φ : PPC_Hyp} {φ : PPC_Form}  
        : (φ ∈ Φ) →  PPC_derives Φ φ
    | truth {Φ}                               
        : PPC_derives Φ PPC_Form.top
    | and_intro {Φ} {φ ψ : PPC_Form}    
        : PPC_derives Φ φ → PPC_derives Φ ψ → PPC_derives Φ (PPC_Form.and φ ψ)
    | and_eliml {Φ} {φ ψ : PPC_Form}    
        : PPC_derives Φ (PPC_Form.and φ ψ) → PPC_derives Φ φ
    | and_elimr {Φ} {φ ψ : PPC_Form}    
        : PPC_derives Φ (PPC_Form.and φ ψ) → PPC_derives Φ ψ
    | impl_intro {Φ : PPC_Hyp} (φ : PPC_Form) {ψ : PPC_Form}   
        : PPC_derives (insert φ Φ) ψ → PPC_derives Φ (PPC_Form.impl φ ψ)
    | impl_elim {Φ : PPC_Hyp} (φ : PPC_Form) {ψ : PPC_Form} 
        : PPC_derives Φ (PPC_Form.impl φ ψ) → PPC_derives Φ φ → PPC_derives Φ ψ
    | weak {Φ Ψ : PPC_Hyp} {φ : PPC_Form}
        : PPC_derives Φ φ → PPC_derives (Φ ∪ Ψ) φ
    open PPC_derives

end PPC_defn




namespace PPC_has_derives

    open PPC_defn
    open PPC_defn.PPC_derives
    open deduction_basic
    open deduction_cart

    instance PPC_hasHyp : has_Hyp PPC_Form :=
      { Hyp := PPC_Hyp
        emptyHyp := inferInstance
        insertHyp := inferInstance }

    instance PPC_Der : has_struct_derives PPC_Form where
      tohas_derives :=
        { tohas_Hyp := PPC_hasHyp
          derives := PPC_derives
          derive_Trans := by
            intro Φ ψ θ hφψ hψθ
            have helper : PPC_derives Φ (PPC_Form.impl ψ θ) := by
              apply impl_intro
              have : PPC_derives (insert ψ (∅ : PPC_Hyp) ∪ Φ) θ := by
                apply weak (Φ := insert ψ (∅ : PPC_Hyp)) (Ψ := Φ)
                exact hψθ
              simpa [Set.insert_union, Set.empty_union] using this
            apply impl_elim ψ
            · exact helper
            · exact hφψ }
      memHyp := (inferInstance : Membership PPC_Form PPC_Hyp)
      inInsert := by
        intro φ Φ
        exact Set.mem_insert φ Φ
      hyp := @hyp
      weak1 := by
        intro Φ φ ψ h
        have : PPC_derives (Φ ∪ insert ψ (∅ : PPC_Hyp)) φ := by
          apply weak (Φ := Φ) (Ψ := insert ψ (∅ : PPC_Hyp))
          exact h
        simpa [Set.union_insert, Set.union_empty] using this

    instance PPC_top : deduction_cart.has_ltop PPC_Form :=
    { tohas_struct_derives := PPC_Der
      top := PPC_Form.top
      truth := @truth }
    instance PPC_and : deduction_cart.has_and PPC_Form :=
    { tohas_ltop := PPC_top
      and := PPC_Form.and
      and_intro := @and_intro
      and_eliml := @and_eliml
      and_elimr := @and_elimr }
    instance PPC_impl : deduction_cart.has_impl PPC_Form :=
    { tohas_and := PPC_and
      impl := PPC_Form.impl
      impl_intro := @impl_intro
      impl_elim := @impl_elim }

end PPC_has_derives
