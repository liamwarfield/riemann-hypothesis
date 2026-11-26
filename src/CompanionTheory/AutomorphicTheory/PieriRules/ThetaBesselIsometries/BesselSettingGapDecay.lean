module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselPeriodAdjointPair
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalue
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FreeAlgebraActionCapelliDeterminantEqOperator
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BaseRepCapelliEigenDual

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingGapBound
section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingGapBound
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselFirstLeft

theorem sigmaFinite_of_haar {k r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (h : B.IsHaarOn U μ) : SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun {K} hK => h.finite_compact K hK⟩
  infer_instance

theorem left_integral {k r : ℕ} (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp) (hk : 1 ≤ k) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hW : B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) (hl : IsBeL R z π μW μN l)
    {Y x : R.H} (hY : Y ∈ R.sm) (hx : x ∈ R.TK) :
    Integrable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2) *
        ⟪x, R.σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.2)⁻¹) Y⟫_ℂ) • π (Matrix.of p.1)) (μW.prod μN) ∧
    ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2) *
        ⟪x, R.σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.2)⁻¹) Y⟫_ℂ) • π (Matrix.of p.1) ∂(μW.prod μN) =
      (innerSL ℂ (l x)).smulRight (l Y) := _root_.GlobalTheory.BesselFirstLeft.left_integral (k := k) (r := r) (Wp := Wp) (Y := Y) (x := x) R z π μW μN l hk hz hT hW hN hl hY hx

theorem bessel_integrate_left : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∀ γ ∈ JF.Om k r D.z D.z', ∃ A : R.H → Wq → Wq → Wp, (∀ y a c (t : ℂ), A y (t • a) c = star t • A y a c) ∧ ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ (X : Wq →L[ℂ] Wp) (c : Wq), B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ c = A y (ContinuousLinearMap.adjoint X (l x)) c := by
  intro hyp k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ D l l' hDS hgap hok hl hl' γ hγ
  refine ⟨fun y a c => ∫ q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
    (star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd (Matrix.of q.2)) * ⟪a, D.π' (Matrix.of q.1)⁻¹ c⟫_ℂ) •
      l (R.σ (γ * Matrix.of q.2 * Matrix.of q.1) y) ∂(D.μW'.prod D.μN), ?_, ?_⟩
  · intro y a c t
    rw [← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [inner_smul_left, smul_smul]
    congr 1
    rw [starRingEnd_apply]; ring
  intro x hx y hy X c
  haveI := sigmaFinite_of_haar D.haarW
  haveI := sigmaFinite_of_haar D.haarW'
  haveI := sigmaFinite_of_haar D.haarN
  obtain ⟨hmul, -, -, hsm, hTK, -⟩ := GlobalTheory.rep_basic_of_isDS hyp.1.2.2.1 k r ε mu R hDS
  have hcoef : IsCoef R l l' (fun g => ⟪x, R.σ g y⟫_ℂ • X) ⟪l x, X (l' y)⟫_ℂ :=
    ⟨1, fun _ => x, fun _ => y, fun _ => X, fun _ => ⟨hx, hy⟩, fun g _ => by simp, by simp⟩
  have hcc := (GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap hyp k r ε mu h R Wp Wq l l' _ _ hDS hgap hok hcoef).2 0
  have hint := (Formalism.FourierDecayAlt.P.bessel_integral_converges k r Wp Wq D _ _ (GlobalTheory.T.decayThresholds_of_spectralGapCondition k r h hok).1 hcc).1 γ hγ
  have hJ : B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ =
      ∫ p, JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ p ∂D.μSS := rfl
  rw [hJ, ContinuousLinearMap.integral_apply hint]
  have hint' : Integrable (fun p => JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ p c)
      ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) :=
    (ContinuousLinearMap.apply ℂ Wp c).integrable_comp hint
  rw [B.RealPlaceData.μSS, integral_prod_symm _ hint']
  have hae := (GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z D.μW D.μN D.k_pos D.z_mem D.T_pos
    (((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μW).2.2 _ D.z_mem D.T_pos D.k_pos).2 D.haarW)
    ((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μN).2.1.2 D.haarN)).2.2.2.2.2
  have hae' := (GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z' D.μW' D.μN D.k_pos D.z'_mem D.T'_pos
    (((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μW').2.2 _ D.z'_mem D.T'_pos D.k_pos).2 D.haarW')
    ((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μN).2.1.2 D.haarN)).2.2.2.2.2
  obtain ⟨-, -, -, -, hU, hNG⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z Formalism.QuantumDeterminants.cStd D.z_mem
  obtain ⟨-, -, -, -, hU', -⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z' Formalism.QuantumDeterminants.cStd D.z'_mem
  refine integral_congr_ae ?_
  filter_upwards [hae'] with q hq
  have hg : γ * Matrix.of q.2 * Matrix.of q.1 ∈ GG k r :=
    Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hγ.1 (hNG _ hq.2)) (hU' _ hq.1 _ hq.1).2.2
  obtain ⟨hI, hE⟩ := left_integral R D.z D.π D.μW D.μN l D.k_pos D.z_mem D.T_pos D.haarW D.haarN hl
    (hsm _ hg y (hTK y hy)) hx
  have hE' := congrArg (fun T : Wp →L[ℂ] Wp =>
    star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd (Matrix.of q.2)) • T (X (D.π' (Matrix.of q.1)⁻¹ c))) hE
  simp only [ContinuousLinearMap.integral_apply hI] at hE'
  rw [← integral_smul] at hE'
  rw [ContinuousLinearMap.adjoint_inner_left, ← smul_smul]
  refine Eq.trans (integral_congr_ae ?_) hE'
  filter_upwards [hae] with p hp
  have hs : (Matrix.of p.1 : Mx k r)⁻¹ * (Matrix.of p.2 : Mx k r)⁻¹ ∈ GG k r :=
    Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv (hU _ hp.1 _ hp.1).2.2) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv (hNG _ hp.2))
  rw [← hmul _ hs _ hg]
  simp only [JF.integrand, JF.xiP, B.rho, B.sgs, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    map_smul, smul_smul, Matrix.mul_assoc]
  congr 1
  ring

end GlobalTheory.BesselFirstLeft
end
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingGapBoundStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.bessel_orbital_integral_factors_through_left_functional : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∀ γ ∈ JF.Om k r D.z D.z', ∃ A : R.H → Wq → Wq → Wp, (∀ y a c (t : ℂ), A y (t • a) c = star t • A y a c) ∧ ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ (X : Wq →L[ℂ] Wp) (c : Wq), B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ c = A y (ContinuousLinearMap.adjoint X (l x)) c := by
  first | exact @GlobalTheory.BesselFirstLeft.bessel_integrate_left | exact GlobalTheory.BesselFirstLeft.bessel_integrate_left | (intros; apply GlobalTheory.BesselFirstLeft.bessel_integrate_left <;> assumption)
end Gp91
end
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingGapBoundDual
section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingGapBoundDual
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem besselInner_haar {k r : ℕ} {U : Set (Mx k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} (h : B.IsHaarOn U μ) :
    PI.BesselPeriodGGP.IsHaarOn U μ :=
  ⟨Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite h, h.ne_zero, h.conc, h.left⟩

theorem besselInner_integral {k r : ℕ} (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
    (D : B.RealPlaceData k r Wp Wq)
    (hmul : ∀ g ∈ GG k r, ∀ h ∈ GG k r, ∀ v, R.σ (g * h) v = R.σ g (R.σ h v))
    (huni : ∀ g ∈ GG k r, ∀ v w, ⟪R.σ g v, R.σ g w⟫_ℂ = ⟪v, w⟫_ℂ)
    {γ : Mx k r} (hγ : γ ∈ GG k r) (x y : R.H) (X : Wq →L[ℂ] Wp)
    (a : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (ha1 : Matrix.of a.1 ∈ GG k r) (ha2 : Matrix.of a.2 ∈ GG k r)
    (hint : Integrable (beInt D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ y (R.σ (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) x))
      (D.μW'.prod D.μN)) :
    ∫ b, JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ (a, b) ∂(D.μW'.prod D.μN) =
      Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of a.2) • (D.π (Matrix.of a.1)).comp (X.comp
        (be D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ D.μW' D.μN y (R.σ (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) x))) := _root_.GlobalTheory.besselInner_integral (k := k) (r := r) (Wp := Wp) (Wq := Wq) (γ := γ) R D hmul huni hγ x y X a ha1 ha2 hint

theorem besselJ_coef_through_right : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∀ γ ∈ JF.Om k r D.z D.z', ∃ Bb : R.H → Wp → Wq → Wp, (∀ x b c (t : ℂ), Bb x (t • b) c = t • Bb x b c) ∧ ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ (X : Wq →L[ℂ] Wp) (c : Wq), B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ c = Bb x (X (l' y)) c := by
  intro hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ D l l' hDS hgap hOK _ hl' γ hγ
  obtain ⟨hmul, -, huni, -, hsm, hTK, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hDS
  refine ⟨fun x b c => ∫ a : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of a.2) *
        ⟪l' (R.σ (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) x), c⟫_ℂ) • D.π (Matrix.of a.1) b ∂(D.μW.prod D.μN), ?_, ?_⟩
  · intro x b c t
    simp only
    rw [← integral_smul]
    congr 1
    funext a
    rw [map_smul, smul_comm]
  intro x hx y hy X c
  have hcoef : IsCoef R l l' (fun g => ⟪x, R.σ g y⟫_ℂ • X) ⟪l x, X (l' y)⟫_ℂ :=
    ⟨1, fun _ => x, fun _ => y, fun _ => X, fun _ => ⟨hx, hy⟩, fun g _ => by simp, by simp⟩
  have hcc := (GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap hH k r ε mu h R Wp Wq l l' _ _ hDS hgap hOK hcoef).2 0
  have hI := (Formalism.FourierDecayAlt.P.bessel_integral_converges k r Wp Wq D _ _ (GlobalTheory.T.decayThresholds_of_spectralGapCondition k r h hOK).1 hcc).1 γ hγ
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have hJ : B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ =
      ∫ p, JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) := rfl
  have hI' : Integrable (JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ)
      ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) := hI
  rw [hJ, integral_prod _ hI', ContinuousLinearMap.integral_apply hI'.integral_prod_left]
  obtain ⟨-, -, -, -, -, hae⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z D.μW D.μN D.k_pos D.z_mem D.T_pos
    (besselInner_haar D.haarW) (besselInner_haar D.haarN)
  obtain ⟨-, -, -, -, hW, hN⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z Formalism.QuantumDeterminants.cStd D.z_mem
  refine integral_congr_ae ?_
  filter_upwards [hae] with a ha
  have ha1 : Matrix.of a.1 ∈ GG k r := (hW _ ha.1 _ ha.1).2.2
  have ha2 : Matrix.of a.2 ∈ GG k r := hN _ ha.2
  have hg0 : γ⁻¹ * Matrix.of a.2 * Matrix.of a.1 ∈ GG k r :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hγ.1) ha2) ha1
  obtain ⟨hint, hbe⟩ := hl'.2 y (hsm y hy) _ (hTK _ hg0 x hx)
  rw [besselInner_integral R D hmul huni hγ.1 x y X a ha1 ha2 hint, hbe]
  simp [smul_smul]

end GlobalTheory
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingGapBoundDualStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.bessel_orbital_integral_factors_through_right_functional : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∀ γ ∈ JF.Om k r D.z D.z', ∃ Bb : R.H → Wp → Wq → Wp, (∀ x b c (t : ℂ), Bb x (t • b) c = t • Bb x b c) ∧ ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ (X : Wq →L[ℂ] Wp) (c : Wq), B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ c = Bb x (X (l' y)) c := by
  first | exact @GlobalTheory.besselJ_coef_through_right | exact GlobalTheory.besselJ_coef_through_right | (intros; apply GlobalTheory.besselJ_coef_through_right <;> assumption)
end Gp91
end
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingGapDecay
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselOrbital

theorem bessel_integral_eq_smul : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∃ OO : Mx k r → (Wq →L[ℂ] Wp), ∀ F s, IsCoef R l l' F s → ∀ γ ∈ JF.Om k r D.z D.z', Integrable (JF.integrand D F γ) D.μSS ∧ B.JF D F γ = s • OO γ := by
  classical
  intro hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ D l l' hDS hgap hok hl hl'
  have hpt : ∀ γ ∈ JF.Om k r D.z D.z', ∃ O : Wq →L[ℂ] Wp, ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ X : Wq →L[ℂ] Wp,
      B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ = ⟪l x, X (l' y)⟫_ℂ • O := by
    intro γ hγ
    obtain ⟨A, hA1, hA2⟩ := GlobalTheory.T.bessel_orbital_integral_factors_through_left_functional hH k r ε mu h R Wp Wq D l l' hDS hgap hok hl hl' γ hγ
    obtain ⟨Bb, hB1, hB2⟩ := GlobalTheory.T.bessel_orbital_integral_factors_through_right_functional hH k r ε mu h R Wp Wq D l l' hDS hgap hok hl hl' γ hγ
    obtain ⟨O, hO⟩ := GlobalTheory.T.factorisation_of_conjHomogeneous_and_homogeneous R.TK Wp Wq (fun x => l x) (fun y => l' y)
      (fun x y X => B.JF D (fun g => ⟪(x : R.H), R.σ g y⟫_ℂ • X) γ)
      (fun y => A y) (fun x => Bb x) (fun y => hA1 y) (fun x => hB1 x)
      (fun x y X c => hA2 x x.2 y y.2 X c) (fun x y X c => hB2 x x.2 y y.2 X c)
    exact ⟨O, fun x hx y hy X => hO ⟨x, hx⟩ ⟨y, hy⟩ X⟩
  choose! OO hOO using hpt
  have hint : ∀ F s, IsCoef R l l' F s → ∀ γ ∈ JF.Om k r D.z D.z',
      Integrable (JF.integrand D F γ) D.μSS := by
    intro F s hF γ hγ
    exact (Formalism.FourierDecayAlt.P.bessel_integral_converges k r Wp Wq D _ F (GlobalTheory.T.decayThresholds_of_spectralGapCondition k r h hok).1
      ((GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap hH k r ε mu h R Wp Wq l l' F s hDS hgap hok hF).2 0)).1 γ hγ
  refine ⟨OO, fun F s hF γ hγ => ⟨hint F s hF γ hγ, ?_⟩⟩
  obtain ⟨m, x, y, X, hxy, hFe, hs⟩ := hF
  have hγG : γ ∈ GG k r := hγ.1
  obtain ⟨hloc, -, hsum, -⟩ := GlobalTheory.T.besselFunction_locality_invariantFactor_finiteSum k r Wp Wq D γ hγG
  rw [(hloc F (fun g => ∑ i, ⟪x i, R.σ g (y i)⟫_ℂ • X i) hFe).1,
    hsum (Fin m) (fun i g => ⟪x i, R.σ g (y i)⟫_ℂ • X i) ?_, hs, Finset.sum_smul]
  · exact Finset.sum_congr rfl fun i _ => hOO γ hγ _ (hxy i).1 _ (hxy i).2 _
  · intro i
    refine hint _ ⟪l (x i), X i (l' (y i))⟫_ℂ ⟨1, fun _ => x i, fun _ => y i, fun _ => X i,
      fun _ => hxy i, fun g _ => ?_, ?_⟩ γ hγ
    · simp
    · simp

end GlobalTheory.BesselOrbital
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingGapDecayStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.bessel_orbital_integral_integrable_and_eq_smul : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∃ OO : Mx k r → (Wq →L[ℂ] Wp), ∀ F s, IsCoef R l l' F s → ∀ γ ∈ JF.Om k r D.z D.z', Integrable (JF.integrand D F γ) D.μSS ∧ B.JF D F γ = s • OO γ := by
  first | exact @GlobalTheory.BesselOrbital.bessel_integral_eq_smul | exact GlobalTheory.BesselOrbital.bessel_integral_eq_smul | (intros; apply GlobalTheory.BesselOrbital.bessel_integral_eq_smul <;> assumption)
end Gp91
end
