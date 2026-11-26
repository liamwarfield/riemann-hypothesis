module

public import Formalism.WeaklyAdmissibleFiltrations.Statement

@[expose] public section

theorem UpperTheory.Reformulated.B.Qh15.aux1 :
    ∀ {A : Type} [inst : CommRing A], SMulCommClass A A A := by
  intro A _
  infer_instance

theorem UpperTheory.Reformulated.B.Qh15.aux2 :
    ∀ {G A : Type} [inst : Group G] [inst_1 : CommRing A] (κ : G →* Aˣ), (κ 1 : A) • (LinearMap.id (R := A) (M := A)) = 1 := by
  intro G A _ _ κ
  ext
  simp

theorem UpperTheory.Reformulated.B.Qh15.aux3 :
    ∀ {G A : Type} [inst : Group G] [inst_1 : CommRing A] (κ : G →* Aˣ) (g h : G),
      (κ (g * h) : A) • (LinearMap.id (R := A) (M := A)) = ((κ g : A) • (LinearMap.id (R := A) (M := A))) * ((κ h : A) • (LinearMap.id (R := A) (M := A))) := by
  intro G A _ _ κ g h
  ext
  simp [mul_comm]

noncomputable def UpperTheory.Reformulated.B.Qh15.chRep :
    {G A : Type} → [inst : Group G] → [inst_1 : CommRing A] → (G →* Aˣ) → Representation A G A :=
    fun {G A : Type} [Group G] [CommRing A] (κ : G →* Aˣ) ↦
      { toFun := fun (g : G) ↦ (κ g : A) • LinearMap.id,
        map_one' := UpperTheory.Reformulated.B.Qh15.aux2 κ,
        map_mul' := UpperTheory.Reformulated.B.Qh15.aux3 κ }

theorem UpperTheory.Reformulated.B.Qh15.act_mul :
    ∀ {G : Type} [inst : Group G] {Qp K₀ K : Type} [inst_1 : Field Qp] [inst_2 : Field K₀]
      [inst_3 : Field K] [inst_4 : Algebra Qp K₀] [inst_5 : Algebra Qp K] [inst_6 : Algebra K₀ K]
      [inst_7 : IsScalarTower Qp K₀ K] {B BdR : Type} [inst_8 : CommRing B] [inst_9 : CommRing BdR]
      [inst_10 : Algebra Qp B] [inst_11 : Algebra K₀ B] [inst_12 : IsScalarTower Qp K₀ B]
      [inst_13 : Algebra Qp BdR] [inst_14 : Algebra K₀ BdR] [inst_15 : Algebra K BdR]
      [inst_16 : IsScalarTower Qp K BdR] [inst_17 : IsScalarTower K₀ K BdR]
      [inst_18 : IsScalarTower Qp K₀ BdR]
      (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {E : Type}
      [inst_19 : Field E] [inst_20 : Algebra Qp E] (κ : G →* Eˣ) (g : G) (x y : TensorProduct Qp E B),
      (Formalism.WeaklyAdmissibleFiltrations.actVB PD (UpperTheory.Reformulated.B.Qh15.chRep κ) g) x *
          (Formalism.WeaklyAdmissibleFiltrations.actVB PD (UpperTheory.Reformulated.B.Qh15.chRep κ⁻¹) g)
            y =
        (Formalism.WeaklyAdmissibleFiltrations.actVB PD (UpperTheory.Reformulated.B.Qh15.chRep 1) g)
          (x * y) := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD E _ _ κ g x y
  have hch : ∀ (μ : G →* Eˣ) (a : E), UpperTheory.Reformulated.B.Qh15.chRep μ g a = (μ g : E) * a :=
    fun μ a => rfl
  have hact : ∀ (μ : G →* Eˣ) (a : E) (b : B),
      Formalism.WeaklyAdmissibleFiltrations.actVB PD (UpperTheory.Reformulated.B.Qh15.chRep μ) g (a ⊗ₜ[Qp] b) =
        ((μ g : E) * a) ⊗ₜ[Qp] PD.actB g b := by
    intro μ a b
    rw [← hch]
    rfl
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, zero_mul]
  | add x₁ x₂ h₁ h₂ => simp only [map_add (f := _), add_mul, h₁, h₂]
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, mul_zero]
    | add y₁ y₂ h₁ h₂ => simp only [map_add (f := _), mul_add, h₁, h₂]
    | tmul c d =>
      have hu : (κ g : E) * a * ((κ⁻¹ g : E) * c) = ((1 : G →* Eˣ) g : E) * (a * c) := by
        rw [mul_mul_mul_comm, ← Units.val_mul, MonoidHom.inv_apply, mul_inv_cancel,
          MonoidHom.one_apply]
      rw [Algebra.TensorProduct.tmul_mul_tmul, hact, hact, hact,
        Algebra.TensorProduct.tmul_mul_tmul, hu, map_mul]
