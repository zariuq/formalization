namespace deduction_basic
  set_option quotPrecheck false
  universe u v

  class has_Hyp (Form : Type u) where
    Hyp : Type v
    [emptyHyp : EmptyCollection Hyp]
    [insertHyp : Insert Form Hyp]
  attribute [instance] has_Hyp.emptyHyp has_Hyp.insertHyp
  instance singleHyp {Form : Type u} [hasHyp : has_Hyp Form] : Singleton Form hasHyp.Hyp :=
    ⟨fun φ => hasHyp.insertHyp.insert φ hasHyp.emptyHyp.emptyCollection⟩

  instance lawfulSingleHyp {Form : Type u} [hasHyp : has_Hyp Form] :
    LawfulSingleton Form hasHyp.Hyp :=
    ⟨by intro φ; rfl⟩

  class has_derives (Form : Type u) extends has_Hyp Form where
    derives : Hyp → Form → Prop
    derive_Trans :
      ∀ {Φ : Hyp} (ψ) {θ : Form},
        derives Φ ψ → derives (insert ψ (∅ : Hyp)) θ → derives Φ θ

  def der {Form : Type u} [Der : has_derives Form] : Form → Form → Prop :=
    fun φ ψ => has_derives.derives {φ} ψ

  infix:60 " ⊢ " => der

  theorem derive_trans {Form : Type u} [Der : has_derives Form] :
    ∀ {φ : Form} (ψ) {θ}, (φ ⊢ ψ) → (ψ ⊢ θ) → (φ ⊢ θ) := by
    intro φ
    apply Der.derive_Trans

  class has_struct_derives (Form : Type u) extends has_derives Form where
    [memHyp : Membership Form Hyp]
    inInsert : ∀ {φ : Form} {Φ : Hyp}, φ ∈ insert φ Φ
    hyp : ∀ {Φ} {φ}, (φ ∈ Φ) → derives Φ φ
    weak1 : ∀ {Φ} {φ} (ψ), derives Φ φ → derives (insert ψ Φ) φ

  theorem derive_refl {Form : Type u} [Der : has_struct_derives Form] :
    ∀ φ : Form, φ ⊢ φ := by
    intro φ
    apply Der.hyp
    apply Der.inInsert

end deduction_basic
