module

public import Formalism.PeriodIntegrals.ScMuExists
public import Formalism.PeriodIntegrals.DSInfCharCap
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.CapelliHighestWeightConjugated
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.SmRight
open Matrix PI.UpqRep

noncomputable section

namespace PI.UnitaryGroupMassFormula.CapelliEig

def UHGrp : Prop :=
  ∀ (k r : ℕ), ∀ a ∈ UH (Hpk k r), IsUnit a ∧ a⁻¹ ∈ UH (Hpk k r) ∧ ∀ b ∈ UH (Hpk k r), a * b ∈ UH (Hpk k r)

def MulH : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Hs →L[ℂ] Hs)),
    IsDSHpk k r ε lam σ → ∀ x ∈ UH (Hpk k r), ∀ y ∈ UH (Hpk k r), σ (x * y) = (σ x).comp (σ y)

def SmRight : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Hs →L[ℂ] Hs)),
    IsDSHpk k r ε lam σ → ∀ v : Hs, v ∈ smoothVecs (k := k) (r := r) σ →
    ∀ c ∈ UH (Hpk k r), σ c v ∈ smoothVecs (k := k) (r := r) σ

def Loc : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H P Q : Matrix (Fin n) (Fin n) ℂ) (F₁ F₂ : Matrix (Fin n) (Fin n) ℂ → E) (u : ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ),
    Q * P = 1 → P * Q = 1 → H = Pᴴ * Formalism.REAL.Jm ε * P →
    (∀ x, Formalism.QuantumDeterminants.inUH H x → F₁ x = F₂ x) → Formalism.QuantumDeterminants.inUH H g →
    Formalism.QuantumDeterminants.capelliH H u F₁ g = Formalism.QuantumDeterminants.capelliH H u F₂ g

def CoefSm : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Hs →L[ℂ] Hs))
    (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq],
    IsHCParam lam → IsDSHpk k r ε lam σ →
    ∀ (P : Hs →L[ℂ] Wp) (Q : Wq →L[ℂ] Hs), (∀ w, Q w ∈ smoothVecs (k := k) (r := r) σ) →
    ∀ Y : ℂ, ∀ g ∈ UH (Hpk k r),
      PI.CapelliEig.capC (k := k) (r := r) Y (fun x => P.comp ((σ x).comp Q)) g =
        Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • P.comp ((σ g).comp Q)

end PI.UnitaryGroupMassFormula.CapelliEig

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.HeckeMultiplication
open Matrix PI.UpqRep

noncomputable section

namespace PI.UnitaryGroupMassFormula.CapelliEig

theorem unitary_Hecke_group : UHGrp := by
  intro k r a ha
  have hH : Hpk k r * Hpk k r = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hdet : IsUnit a.det := by
    have h1 := congrArg Matrix.det ha'
    rw [Matrix.det_mul, Matrix.det_mul] at h1
    have hHd : (Hpk k r).det * (Hpk k r).det = 1 := by rw [← Matrix.det_mul, hH, Matrix.det_one]
    refine isUnit_iff_ne_zero.mpr (fun h0 => ?_)
    rw [h0, mul_zero] at h1
    rw [← h1, zero_mul] at hHd
    exact zero_ne_one hHd
  refine ⟨(Matrix.isUnit_iff_isUnit_det a).mpr hdet, ?_, ?_⟩
  · show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
    have hai : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hdet
    calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [ha']
      _ = (a * a⁻¹)ᴴ * Hpk k r * (a * a⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [hai, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · intro b hb
    have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
    show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
    calc (a * b)ᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [ha', hb']

theorem Hecke_multiplication : MulH := by
  intro k r ε lam Hs _ _ σ hσ x hx y hy
  obtain ⟨P₀, ⟨⟨hunit, hcay⟩, _⟩, hds⟩ := hσ
  have hdet : IsUnit P₀.det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hPQ : P₀ * P₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hQP : P₀⁻¹ * P₀ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hH : Formalism.QuantumDeterminants.Hpk k r = P₀ᴴ * Formalism.REAL.Jm ε * P₀ := hcay.symm
  have hx' : Formalism.REAL.inUJ ε (P₀ * x * P₀⁻¹) := Formalism.QuantumDeterminants.ioh_inUJ ε _ P₀ P₀⁻¹ x hPQ hH hx
  have hy' : Formalism.REAL.inUJ ε (P₀ * y * P₀⁻¹) := Formalism.QuantumDeterminants.ioh_inUJ ε _ P₀ P₀⁻¹ y hPQ hH hy
  have hm := hds.2.2.1.1.2 (P₀ * x * P₀⁻¹) hx' (P₀ * y * P₀⁻¹) hy'
  have e1 : P₀⁻¹ * (P₀ * x * P₀⁻¹ * (P₀ * y * P₀⁻¹)) * P₀ = x * y := by
    calc P₀⁻¹ * (P₀ * x * P₀⁻¹ * (P₀ * y * P₀⁻¹)) * P₀
        = (P₀⁻¹ * P₀) * x * (P₀⁻¹ * P₀) * y * (P₀⁻¹ * P₀) := by simp only [Matrix.mul_assoc]
      _ = x * y := by rw [hQP]; simp only [Matrix.one_mul, Matrix.mul_one]
  have e2 : ∀ z, P₀⁻¹ * (P₀ * z * P₀⁻¹) * P₀ = z := by
    intro z
    calc P₀⁻¹ * (P₀ * z * P₀⁻¹) * P₀ = (P₀⁻¹ * P₀) * z * (P₀⁻¹ * P₀) := by simp only [Matrix.mul_assoc]
      _ = z := by rw [hQP, Matrix.one_mul, Matrix.mul_one]
  simp only [e1, e2] at hm
  exact hm

end PI.UnitaryGroupMassFormula.CapelliEig

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.CoreDefs
open Matrix PI.UpqRep

noncomputable section

namespace PI.UnitaryGroupMassFormula.CapelliEig

def CapTransport : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H P Q : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → E) (u : ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ),
    Q * P = 1 → P * Q = 1 → H = Pᴴ * Formalism.REAL.Jm ε * P →
    Formalism.REAL.SmoothOnGV ε (fun x => F (Q * x * P)) → Formalism.QuantumDeterminants.inUH H g →
    Formalism.QuantumDeterminants.capelliH H u F g = Formalism.QuantumDeterminants.capelli ε u (fun x => F (Q * x * P)) (P * g * Q)

def FunAct : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σ : Matrix (Fin n) (Fin n) ℂ → (Hs →L[ℂ] Hs))
    (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq],
    IsDS ε lam σ → ∀ (P : Hs →L[ℂ] Wp) (Q : Wq →L[ℂ] Hs),
    (∀ w, Q w ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ) →
    ∀ (u : ℂ) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g → ∀ w : Wq,
      Formalism.QuantumDeterminants.capelli ε u (fun x => P.comp ((σ x).comp Q)) g w =
        P (σ g (PI.DSInfCharCap.actU ε σ (Formalism.REAL.qdet (PI.DSInfCharCap.Egl n) u) (Q w)))

def SmTrans : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Hs →L[ℂ] Hs))
    (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (P₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), IsCayleyU k r ε P₀ →
    ∀ (P : Hs →L[ℂ] Wp) (Q : Wq →L[ℂ] Hs), (∀ w, Q w ∈ smoothVecs (k := k) (r := r) σ) →
      (∀ w, Q w ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) (fun x => σ (P₀⁻¹ * x * P₀))) ∧
      Formalism.REAL.SmoothOnGV ε (fun x => P.comp ((σ (P₀⁻¹ * x * P₀)).comp Q))

end PI.UnitaryGroupMassFormula.CapelliEig

end
end
