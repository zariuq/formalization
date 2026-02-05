import deduction.deduction_monadic
import Mathlib.Data.Set.Insert
open deduction_basic



namespace MPPC_defn

    inductive MPPC_Form : Type
    | top : MPPC_Form
    | var : ℕ → MPPC_Form
    | and : MPPC_Form → MPPC_Form → MPPC_Form
    | impl : MPPC_Form → MPPC_Form → MPPC_Form
    | diamond : MPPC_Form → MPPC_Form


    @[reducible] def MPPC_Hyp : Type := Set MPPC_Form

    instance : Union MPPC_Hyp := inferInstance
    instance : Membership MPPC_Form MPPC_Hyp := inferInstance
    instance : Insert MPPC_Form MPPC_Hyp := inferInstance
    instance : EmptyCollection MPPC_Hyp := inferInstance

    inductive isModal : MPPC_Hyp → Prop
    | ModalEmpty : isModal ∅
    | ModalInsert : ∀ (Φ : MPPC_Hyp) (φ : MPPC_Form), 
        isModal Φ → isModal (insert (MPPC_Form.diamond φ) Φ)

    inductive MPPC_derives : MPPC_Hyp → MPPC_Form → Prop 
    | hyp {Φ : MPPC_Hyp} {φ : MPPC_Form}  
        : (φ ∈ Φ) →  MPPC_derives Φ φ
    | truth {Φ}                               
        : MPPC_derives Φ MPPC_Form.top 
    | and_intro {Φ} {φ ψ : MPPC_Form}    
        : MPPC_derives Φ φ → MPPC_derives Φ ψ → MPPC_derives Φ (MPPC_Form.and φ ψ)
    | and_eliml {Φ} {φ ψ : MPPC_Form}    
        : MPPC_derives Φ (MPPC_Form.and φ ψ) → MPPC_derives Φ φ
    | and_elimr {Φ} {φ ψ : MPPC_Form}    
        : MPPC_derives Φ (MPPC_Form.and φ ψ) → MPPC_derives Φ ψ
    | impl_intro {Φ : MPPC_Hyp} (φ : MPPC_Form) {ψ : MPPC_Form}   
        : MPPC_derives (insert φ Φ) ψ → MPPC_derives Φ (MPPC_Form.impl φ ψ)
    | impl_elim {Φ : MPPC_Hyp} (φ : MPPC_Form) {ψ : MPPC_Form} 
        : MPPC_derives Φ (MPPC_Form.impl φ ψ) → MPPC_derives Φ φ → MPPC_derives Φ ψ
    | weak {Φ Ψ : MPPC_Hyp} {φ : MPPC_Form}
        : MPPC_derives Φ φ → MPPC_derives (Φ ∪ Ψ) φ
    | dmap {Φ : MPPC_Hyp}{φ ψ : MPPC_Form} 
        : MPPC_derives (insert φ Φ) ψ → MPPC_derives (insert (MPPC_Form.diamond φ) Φ) (MPPC_Form.diamond ψ)
    | dpure {Φ : MPPC_Hyp} {φ : MPPC_Form}
        : MPPC_derives Φ φ → MPPC_derives Φ (MPPC_Form.diamond φ)
    | djoin {Φ : MPPC_Hyp} {φ : MPPC_Form}
        : MPPC_derives Φ (MPPC_Form.diamond (MPPC_Form.diamond φ)) → MPPC_derives Φ (MPPC_Form.diamond φ)
    open MPPC_derives

notation:81 "◇" φ => MPPC_Form.diamond φ

end MPPC_defn


namespace MPPC_has_derives

    open MPPC_defn
    open MPPC_defn.MPPC_derives
    open deduction_basic
    open deduction_cart
    open deduction_monadic
    open MPPC_defn.MPPC_Form

    instance MPPC_hasHyp : has_Hyp MPPC_Form :=
      { Hyp := MPPC_Hyp
        emptyHyp := inferInstance
        insertHyp := inferInstance }


    instance MPPC_Der : has_struct_derives MPPC_Form where
      tohas_derives :=
        { tohas_Hyp := MPPC_hasHyp
          derives := MPPC_derives
          derive_Trans := by
            intro Φ ψ θ hφψ hψθ
            have helper : MPPC_derives Φ (MPPC_Form.impl ψ θ) := by
              apply impl_intro
              have : MPPC_derives (insert ψ (∅ : MPPC_Hyp) ∪ Φ) θ := by
                apply weak (Φ := insert ψ (∅ : MPPC_Hyp)) (Ψ := Φ)
                exact hψθ
              simpa [Set.insert_union, Set.empty_union] using this
            apply impl_elim ψ
            · exact helper
            · exact hφψ }
      memHyp := (inferInstance : Membership MPPC_Form MPPC_Hyp)
      inInsert := by
        intro φ Φ
        exact Set.mem_insert φ Φ
      hyp := @hyp
      weak1 := by
        intro Φ φ ψ h
        have : MPPC_derives (Φ ∪ insert ψ (∅ : MPPC_Hyp)) φ := by
          apply weak (Φ := Φ) (Ψ := insert ψ (∅ : MPPC_Hyp))
          exact h
        simpa [Set.union_insert, Set.union_empty] using this

    instance MPPC_top : deduction_cart.has_ltop MPPC_Form :=
    { tohas_struct_derives := MPPC_Der
      top := MPPC_Form.top
      truth := @truth }
    instance MPPC_and : deduction_cart.has_and MPPC_Form :=
    { tohas_ltop := MPPC_top
      and := MPPC_Form.and
      and_intro := @and_intro
      and_eliml := @and_eliml
      and_elimr := @and_elimr }
    instance MPPC_impl : deduction_cart.has_impl MPPC_Form :=
    { tohas_and := MPPC_and
      impl := MPPC_Form.impl
      impl_intro := @impl_intro
      impl_elim := @impl_elim }
    instance MPPC_diamond : deduction_monadic.has_diamond MPPC_Form :=
    { tohas_struct_derives := MPPC_Der
      diamond := MPPC_Form.diamond
      dmap := @dmap
      dpure := @dpure
      djoin := @djoin }

end MPPC_has_derives
