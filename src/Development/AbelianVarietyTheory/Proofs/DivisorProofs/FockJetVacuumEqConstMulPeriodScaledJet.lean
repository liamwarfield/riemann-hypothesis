module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAnalyticSetupPeriodLatticePair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSemicharacterEqNegOnePowTraceExponent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableFockVacuumGaussianDefinitePair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableFockVacuumGaussianDefinitePair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare GlobalTheory.VacUnique

variable {D : D7}

def entryR {m n : ℕ} (τ : D.what₂.Tau) (a : Fin m) (b : Fin n) : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) b).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) τ))

theorem entryR_apply {m n : ℕ} (τ : D.what₂.Tau) (a : Fin m) (b : Fin n) (Z : D.what₂.Tau → Fin m → Fin n → ℂ) :
    entryR τ a b Z = Z τ a b := rfl

def dSq {m n : ℕ} (Z : D.what₂.Tau → Fin m → Fin n → ℂ) : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℝ :=
  ∑ τ, ∑ a, ∑ b, (2 : ℕ) • (innerSL ℝ (Z τ a b)).comp (entryR τ a b)

theorem dSq_apply {m n : ℕ} (Z V : D.what₂.Tau → Fin m → Fin n → ℂ) :
    dSq Z V = ∑ τ, ∑ a, ∑ b, 2 * (V τ a b * starRingEnd ℂ (Z τ a b)).re := by
  simp [dSq, ContinuousLinearMap.sum_apply, entryR_apply, Complex.inner, two_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hasFDerivAt_sqSum {m n : ℕ} (Z : D.what₂.Tau → Fin m → Fin n → ℂ) :
    HasFDerivAt (fun Z : D.what₂.Tau → Fin m → Fin n → ℂ => sqSum Z) (dSq Z) Z := by
  unfold sqSum dSq
  refine HasFDerivAt.fun_sum (𝕜 := ℝ) (u := Finset.univ) (A := fun τ (Z : D.what₂.Tau → Fin m → Fin n → ℂ) => ∑ a, ∑ b, ‖Z τ a b‖ ^ 2)
    fun τ _ => ?_
  refine HasFDerivAt.fun_sum (𝕜 := ℝ) (u := Finset.univ) (A := fun a (Z : D.what₂.Tau → Fin m → Fin n → ℂ) => ∑ b, ‖Z τ a b‖ ^ 2)
    fun a _ => ?_
  refine HasFDerivAt.fun_sum (𝕜 := ℝ) (u := Finset.univ) (A := fun b (Z : D.what₂.Tau → Fin m → Fin n → ℂ) => ‖Z τ a b‖ ^ 2)
    fun b _ => ?_
  exact (entryR τ a b).hasFDerivAt.norm_sq

def frL {m n : ℕ} (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) :
    (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℂ] (D.what₂.Tau → Fin m → Fin n → ℂ) :=
  let l : (D.what₂.Tau → Fin m → Fin n → ℂ) →ₗ[ℂ] (D.what₂.Tau → Fin m → Fin n → ℂ) :=
    { toFun := frPt B B'
      map_add' := fun x y => by
        funext τ
        show B' τ * Matrix.of (x τ + y τ) * (B τ)⁻¹ = B' τ * Matrix.of (x τ) * (B τ)⁻¹ + B' τ * Matrix.of (y τ) * (B τ)⁻¹
        rw [show Matrix.of (x τ + y τ) = Matrix.of (x τ) + Matrix.of (y τ) from rfl, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by
        funext τ
        show B' τ * Matrix.of (c • x τ) * (B τ)⁻¹ = c • (B' τ * Matrix.of (x τ) * (B τ)⁻¹)
        rw [show Matrix.of (c • x τ) = c • Matrix.of (x τ) from rfl, Matrix.mul_smul, Matrix.smul_mul] }
  ⟨l, LinearMap.continuous_of_finiteDimensional l⟩

theorem frL_apply {m n : ℕ} (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (Z : D.what₂.Tau → Fin m → Fin n → ℂ) : frL B B' Z = frPt B B' Z := rfl

def toCLin {m n : ℕ} (L : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ)
    (hL : ∀ v, L (Complex.I • v) = Complex.I * L v) : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℂ] ℂ :=
  let l : (D.what₂.Tau → Fin m → Fin n → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := L
      map_add' := L.map_add
      map_smul' := fun c v => by
        have e : c • v = c.re • v + c.im • (Complex.I • v) := by
          funext τ a b
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
          conv_lhs => rw [← Complex.re_add_im c]
          ring
        rw [e, map_add L, L.map_smul, L.map_smul, hL, RingHom.id_apply, Complex.real_smul, Complex.real_smul]
        conv_rhs => rw [← Complex.re_add_im c]
        ring }
  ⟨l, LinearMap.continuous_of_finiteDimensional l⟩

theorem toCLin_restrict {m n : ℕ} (L : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ)
    (hL : ∀ v, L (Complex.I • v) = Complex.I * L v) : (toCLin L hL).restrictScalars ℝ = L := by
  ext v; rfl

end GlobalTheory.VacRealForm

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare GlobalTheory.VacUnique

variable {D : D7}

theorem realPlace_cmTrace_zero_element_eq_I_mul_abs (τ : D.what₂.Tau) : tauE D τ D.host.xi0 = ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * Complex.I := by
  have hre := GlobalTheory.RealSymplForm.realPlace_imaginaryGenerator_re_eq_zero D τ
  have him := Formalism.L2.Theta.xi_zero_im_pos D τ
  have hn := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB.norm_embedding_hostFormConstant_eq D (tauE D τ)
  have e : tauE D τ D.host.xi0 = (((tauE D τ D.host.xi0).im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos him] at hn
  rw [e, hn]

theorem hAt_frame {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1) (τ : D.what₂.Tau)
    (Z V : Fin T.rank → Fin S.rank → ℂ) :
    hAt S T τ (GlobalTheory.FockPos.frAt frT τ * Matrix.of Z * (GlobalTheory.FockPos.frAt frS τ)⁻¹)
      (GlobalTheory.FockPos.frAt frT τ * Matrix.of V * (GlobalTheory.FockPos.frAt frS τ)⁻¹) =
      ∑ a, ∑ b, starRingEnd ℂ (V a b) * Z a b := by
  set B := GlobalTheory.FockPos.frAt frS τ
  set B' := GlobalTheory.FockPos.frAt frT τ
  have h1 : Bᴴ * gramAt D S τ * B = 1 := GlobalTheory.FockPos.frAt_on frS hS τ
  have h2 : B'ᴴ * gramAt D T τ * B' = 1 := GlobalTheory.FockPos.frAt_on frT hT τ
  have hBd : IsUnit B.det := isUnit_iff_ne_zero.2 (GlobalTheory.FockPos.frAt_det_ne frS τ)
  have hGi : (gramAt D S τ)⁻¹ = B * Bᴴ := by
    apply Matrix.inv_eq_right_inv
    have e1 : Bᴴ * (gramAt D S τ * B) = 1 := by rw [← Matrix.mul_assoc]; exact h1
    rw [← Matrix.mul_assoc]
    exact mul_eq_one_comm.1 e1
  have hBB : Bᴴ * (B⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hBd, Matrix.conjTranspose_one]
  have e : (gramAt D S τ)⁻¹ * (B' * Matrix.of V * B⁻¹)ᴴ * gramAt D T τ * (B' * Matrix.of Z * B⁻¹) =
      B * ((Matrix.of V)ᴴ * Matrix.of Z * B⁻¹) := by
    rw [hGi]
    calc B * Bᴴ * (B' * Matrix.of V * B⁻¹)ᴴ * gramAt D T τ * (B' * Matrix.of Z * B⁻¹)
        = B * ((Bᴴ * (B⁻¹)ᴴ) * (Matrix.of V)ᴴ * (B'ᴴ * gramAt D T τ * B') * Matrix.of Z * B⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = B * ((Matrix.of V)ᴴ * Matrix.of Z * B⁻¹) := by
          rw [hBB, h2, Matrix.one_mul, Matrix.mul_one]
  unfold hAt
  rw [e, Matrix.trace_mul_comm, Matrix.nonsing_inv_mul_cancel_right _ _ hBd]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
  exact Finset.sum_comm

end GlobalTheory.VacRealForm

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare GlobalTheory.VacUnique

variable {D : D7}

theorem omO_frame {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1) (Z V : RW T S) :
    omO S T (frPt (fun τ => GlobalTheory.FockPos.frAt frS τ) (fun τ => GlobalTheory.FockPos.frAt frT τ) Z)
      (frPt (fun τ => GlobalTheory.FockPos.frAt frS τ) (fun τ => GlobalTheory.FockPos.frAt frT τ) V) =
      ∑ τ, ∑ a, ∑ b, 2 * (((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * Complex.I * (starRingEnd ℂ (V τ a b) * Z τ a b)).re := by
  rw [omO_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  unfold GlobalTheory.VacUnique.omAt
  rw [frPt, frPt, hAt_frame frS frT hS hT τ (Z τ) (V τ), realPlace_cmTrace_zero_element_eq_I_mul_abs]
  simp only [Finset.mul_sum, Complex.re_sum]

theorem differentiable_gZ_of_frames {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E)
    (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hcS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hcT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ S T f) (hfock : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) :
    Differentiable ℂ (gZ σ S T (fun τ => (frS.1).map (tauE D τ)) (fun τ => (frT.1).map (tauE D τ)) f) := by
  obtain rfl := GlobalTheory.FockPos.cart_one frS hS hcS
  obtain rfl := GlobalTheory.FockPos.cart_one frT hT hcT
  obtain ⟨hd, hann⟩ := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T _ _ f hf hfock
  have hJ : ∀ z : RW T S, jO S T (fun _ => (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ))
      (fun _ => (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)) z = Complex.I • z := fun z => by
    funext τ i k
    simp [jO_apply, cplxO, Matrix.mul_apply, Matrix.one_apply, Pi.mul_apply, Pi.one_apply]
    first
      | exact congrFun (congrFun (Matrix.one_mul (M := (z τ : Matrix (Fin T.rank) (Fin S.rank) ℂ))) i) k
      | (erw [Matrix.mul_apply]; simp [Matrix.one_apply])
      | (rw [Matrix.one_mul])
  set F : RW T S → ℂ := fun z => f (iotaW σ T S z) with hF
  set Φ := frL (fun τ => GlobalTheory.FockPos.frAt frS τ) (fun τ => GlobalTheory.FockPos.frAt frT τ) with hΦ
  intro Z
  have h1 : HasFDerivAt (fun Z => F (Φ Z)) ((fderiv ℝ F (Φ Z)).comp (Φ.restrictScalars ℝ)) Z :=
    (hd (Φ Z)).hasFDerivAt.comp Z (Φ.restrictScalars ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun Z : RW T S => Complex.exp ((Real.pi * Formalism.L2.Pj.xiR D * sqSum Z : ℝ) : ℂ))
      (Complex.exp ((Real.pi * Formalism.L2.Pj.xiR D * sqSum Z : ℝ) : ℂ) •
        Complex.ofRealCLM.comp ((Real.pi * Formalism.L2.Pj.xiR D) • dSq Z)) Z :=
    (Complex.ofRealCLM.hasFDerivAt.comp Z ((hasFDerivAt_sqSum Z).const_mul (Real.pi * Formalism.L2.Pj.xiR D))).cexp
  have h3 := h1.mul h2
  refine (hasFDerivAt_of_restrictScalars ℝ h3 (toCLin_restrict _ ?_)).differentiableAt
  intro v
  have hω1 : omO S T (Φ Z) (Φ v) = -(Formalism.L2.Pj.xiR D * dSq Z (Complex.I • v)) := by
    rw [hΦ, frL_apply, frL_apply, omO_frame frS frT hS hT, dSq_apply]
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hω2 : omO S T (Φ Z) (Complex.I • Φ v) = Formalism.L2.Pj.xiR D * dSq Z v := by
    rw [← map_smul, hΦ, frL_apply, frL_apply, omO_frame frS frT hS hT, dSq_apply]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have ha := hann (Φ Z) (Φ v)
  rw [hJ, hω1, hω2, show f (iotaW σ T S (Φ Z)) = F (Φ Z) from rfl] at ha
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', map_smul, Complex.ofRealCLM_apply, smul_eq_mul]
  push_cast at ha ⊢
  generalize Complex.exp ((Real.pi : ℂ) * (Formalism.L2.Pj.xiR D : ℂ) * (sqSum Z : ℂ)) = E
  generalize (fderiv ℝ F (Φ Z)) (Complex.I • Φ v) = b at ha ⊢
  generalize (fderiv ℝ F (Φ Z)) (Φ v) = a at ha ⊢
  linear_combination (-Complex.I * E) * ha + (F (Φ Z) * E * Real.pi * Formalism.L2.Pj.xiR D * ((dSq Z (Complex.I • v) : ℝ) : ℂ) +
    E * b - Complex.I * F (Φ Z) * E * Real.pi * Formalism.L2.Pj.xiR D * ((dSq Z v : ℝ) : ℂ)) * Complex.I_sq

end GlobalTheory.VacRealForm

namespace GlobalTheory.VacRealForm

theorem differentiable_gZ_top : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart W.θ σ → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → Differentiable ℂ (GlobalTheory.VacRealForm.gZ σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f) := by
  intro D T L sc G W U N σ hσ t j hj f hf
  exact differentiable_gZ_of_frames hσ hf.1 _ _ (N.fr (.top j)) (N.fr (.top (j + 1)))
    (N.fr_on (.top j) (show j ≤ D.R.m by omega)) (N.fr_on (.top (j + 1)) (show j + 1 ≤ D.R.m from hj)) _ _
    (W.cart_is (.top j) (show j ≤ D.R.m by omega)) (W.cart_is (.top (j + 1)) (show j + 1 ≤ D.R.m from hj)) f
    hf.2.theta hf.2.fock

end GlobalTheory.VacRealForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableFockVacuumGaussianDefinitePairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiable_fockVacuum_gaussian_definitePair : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart W.θ σ → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → Differentiable ℂ (GlobalTheory.VacRealForm.gZ σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f) := by
  first | exact @GlobalTheory.VacRealForm.differentiable_gZ_top | exact GlobalTheory.VacRealForm.differentiable_gZ_top | (intros; apply GlobalTheory.VacRealForm.differentiable_gZ_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumRealRestrictionGaussianMulTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumRealRestrictionSatisfiesStandardThetaLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusTranslateThetaCoordinateOfRealPartLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusTranslateThetaCoordinateOfRealPartLaw
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare GlobalTheory.VacUnique

theorem U_thY_of_law : ∀ {D : D7} (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (B : GL (Fin S.rank) D.host.E) (B' : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B'.1 * T.gram * B'.1 = 1 → ∀ (δ : ℂ), δ ≠ 0 → ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (f : WO S T → ℂ) (c : ℂ), (∀ z : GlobalTheory.FockCompare.RW T S, f (GlobalTheory.FockCompare.iotaW σ T S (z + GlobalTheory.VacUnique.infRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1))) = c * Complex.exp (-(↑Real.pi * Complex.I) * ↑(-(GlobalTheory.VacUnique.omO S T (GlobalTheory.VacUnique.infRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1)) z))) * f (GlobalTheory.FockCompare.iotaW σ T S z)) → ∀ Y, Formalism.MainNotions.TaylorLogMetric.U D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • Formalism.MainNotions.TaylorLogMetric.embV D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) M) (GlobalTheory.VacRealForm.thY σ S T (fun τ => B.1.map (tauE D τ)) (fun τ => B'.1.map (tauE D τ)) f δ) Y = c * GlobalTheory.VacRealForm.thY σ S T (fun τ => B.1.map (tauE D τ)) (fun τ => B'.1.map (tauE D τ)) f δ Y := by
  intro D σ S T B B' hB hB' δ hδ M f c hf Y
  set Bc : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ := fun τ => B.1.map (tauE D τ) with hBc
  set B'c : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ := fun τ => B'.1.map (tauE D τ) with hB'c
  set X : RW T S := Formalism.MainNotions.TaylorLogMetric.embV D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) M with hXdef
  set Z : RW T S := δ⁻¹ • Y with hZ
  have hY : Y = δ • Z := by rw [hZ, smul_smul, mul_inv_cancel₀ hδ, one_smul]
  have hinv : ∀ τ, ((B⁻¹ : GL (Fin S.rank) D.host.E).1).map (tauE D τ) = (B.1.map (tauE D τ))⁻¹ := fun τ =>
    (Matrix.inv_eq_left_inv (by
      rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)])).symm
  have hX : infRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1) = frPt Bc B'c X := by
    funext τ
    show (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1).map (tauE D τ) = B'c τ * Matrix.of (X τ) * (Bc τ)⁻¹
    rw [Matrix.map_mul, Matrix.map_mul, hinv]
    rfl
  have hadd : δ⁻¹ • (Y + δ • X) = Z + X := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  have hfr : frPt Bc B'c (Z + X) = frPt Bc B'c Z + frPt Bc B'c X := (frL Bc B'c).map_add Z X
  have hlaw := hf (frPt Bc B'c Z)
  rw [hX] at hlaw
  have hom : omO S T (frPt Bc B'c X) (frPt Bc B'c Z) =
      ∑ τ, ∑ a, ∑ b, 2 * (((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * Complex.I * (starRingEnd ℂ (Z τ a b) * X τ a b)).re :=
    omO_frame B B' hB hB' X Z
  have harea : Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) =
      Complex.normSq δ * (Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d / 2 :=
    GlobalTheory.MomDict.area_lamOf D _ δ D.host.ccK_ne_bot
  have hxi := (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D).1
  have hN : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0 := by
    have h : Ideal.absNorm D.host.ccK ≠ 0 := fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast h
  have hd : Real.sqrt D.host.d ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)).ne'
  have hδn : Complex.normSq δ ≠ 0 := (Complex.normSq_pos.2 hδ).ne'
  have hHf : ∀ u v : RW T S, Formalism.MainNotions.TaylorLogMetric.Hf D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • u) (δ • v) =
      2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, u τ a b * starRingEnd ℂ (v τ a b) := by
    intro u v
    show (∑ τ, ∑ a, ∑ b, (δ • u) τ a b * starRingEnd ℂ ((δ • v) τ a b)) /
      (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) : ℂ) = _
    have e : ∀ τ a b, (δ • u) τ a b * starRingEnd ℂ ((δ • v) τ a b) =
        (Complex.normSq δ : ℂ) * (u τ a b * starRingEnd ℂ (v τ a b)) := fun τ a b => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, ← Complex.mul_conj]; ring
    simp only [e, ← Finset.mul_sum]
    rw [harea, hxi]
    have h1 : ((Complex.normSq δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hδn
    have h2 : ((Ideal.absNorm D.host.ccK : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN
    have h3 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd
    generalize (∑ τ, ∑ a, ∑ b, u τ a b * starRingEnd ℂ (v τ a b)) = s
    rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one,
      Complex.ofReal_ofNat]
    field_simp
  have key : -(↑Real.pi * Complex.I) * ↑(-(omO S T (frPt Bc B'c X) (frPt Bc B'c Z))) +
      ((Real.pi * Formalism.L2.Pj.xiR D * sqSum (Z + X) : ℝ) : ℂ) +
      (-(Real.pi : ℂ) * Formalism.MainNotions.TaylorLogMetric.Hf D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • Z) (δ • X) -
        (Real.pi : ℂ) * Formalism.MainNotions.TaylorLogMetric.Hf D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X) (δ • X) / 2) =
      ((Real.pi * Formalism.L2.Pj.xiR D * sqSum Z : ℝ) : ℂ) := by
    have hOm : omO S T (frPt Bc B'c X) (frPt Bc B'c Z) =
        2 * Formalism.L2.Pj.xiR D * (∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)).im := by
      rw [hom]
      simp only [Complex.im_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im]
      ring
    have hSq : sqSum (Z + X) = sqSum Z + 2 * (∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)).re + sqSum X := by
      unfold sqSum
      simp only [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [Pi.add_apply, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.add_re, Complex.add_im,
        Complex.conj_re, Complex.conj_im]
      ring
    have hQ : (∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) = ((sqSum X : ℝ) : ℂ) := by
      unfold sqSum
      push_cast
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [hHf, hHf, hOm, hSq, hQ]
    generalize (∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) = p
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im] <;> ring
  show gZ σ S T Bc B'c f (δ⁻¹ • (Y + δ • X)) * _ = c * gZ σ S T Bc B'c f (δ⁻¹ • Y)
  rw [hadd, ← hZ]
  unfold gZ
  rw [hfr, hlaw, hY, ← key, Complex.exp_add, Complex.exp_add]
  ring

end GlobalTheory.VacRealForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusTranslateThetaCoordinateOfRealPartLawStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusTranslate_thetaCoordinate_of_realPart_law : ∀ {D : D7} (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (B : GL (Fin S.rank) D.host.E) (B' : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B'.1 * T.gram * B'.1 = 1 → ∀ (δ : ℂ), δ ≠ 0 → ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (f : WO S T → ℂ) (c : ℂ), (∀ z : GlobalTheory.FockCompare.RW T S, f (GlobalTheory.FockCompare.iotaW σ T S (z + GlobalTheory.VacUnique.infRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1))) = c * Complex.exp (-(↑Real.pi * Complex.I) * ↑(-(GlobalTheory.VacUnique.omO S T (GlobalTheory.VacUnique.infRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1)) z))) * f (GlobalTheory.FockCompare.iotaW σ T S z)) → ∀ Y, Formalism.MainNotions.TaylorLogMetric.U D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • Formalism.MainNotions.TaylorLogMetric.embV D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) M) (GlobalTheory.VacRealForm.thY σ S T (fun τ => B.1.map (tauE D τ)) (fun τ => B'.1.map (tauE D τ)) f δ) Y = c * GlobalTheory.VacRealForm.thY σ S T (fun τ => B.1.map (tauE D τ)) (fun τ => B'.1.map (tauE D τ)) f δ Y := by
  first | exact @GlobalTheory.VacRealForm.U_thY_of_law | exact GlobalTheory.VacRealForm.U_thY_of_law | (intros; apply GlobalTheory.VacRealForm.U_thY_of_law <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLatticeStandardPointsScaledEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLatticeStandardPointsScaledEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LaStdEntries

open Formalism.MainNotions.TaylorLogMetric Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {D : D7}

def entSub (D : D7) (a b : ℕ) (S : Submodule (𝓞 D.host.E) D.host.E) :
    Submodule (𝓞 D.host.E) (Matrix (Fin b) (Fin a) D.host.E) where
  carrier := {A | ∀ i j, A i j ∈ S}
  add_mem' hA hB i j := by simpa using S.add_mem (hA i j) (hB i j)
  zero_mem' i j := by simp
  smul_mem' o A hA i j := by simpa using S.smul_mem o (hA i j)

theorem homL_le {a b : ℕ} :
    homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D b) ≤ entSub D a b 1 := by
  refine Submodule.span_le.mpr ?_
  intro A hA i j
  have hj : (Pi.single j (1 : D.host.E) : Fin a → D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D a := by
    simp only [Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi, Set.mem_univ, true_implies]
    intro k
    by_cases hk : k = j
    · subst hk; simp [Submodule.one_eq_range]
    · simp [Pi.single_apply, hk]
  have h := hA _ hj
  simp only [Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at h
  have := h i
  simpa [Matrix.mulVec_single] using this

theorem YYl_le {a b : ℕ} :
    YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D b)
      ≤ entSub D a b (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
  refine Submodule.span_le.mpr ?_
  rintro B ⟨x, hx, A, hA, rfl⟩ i j
  obtain ⟨o, ho⟩ := (Submodule.mem_one).1 (homL_le hA i j)
  show x * A i j ∈ _
  rw [← ho, mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ o hx

theorem K_mul_mem_AA {c : 𝓞 D.host.K} (hc : c ∈ D.host.ccK) {x : D.host.E}
    (hx : x ∈ D.host.AA0) : ((c : D.host.K) : D.host.E) * x ∈ D.host.AA := by
  show _ ∈ (D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0
  refine FractionalIdeal.mul_mem_mul ?_ hx
  rw [FractionalIdeal.mem_coeIdeal]
  exact ⟨_, Ideal.mem_map_of_mem _ hc, rfl⟩

theorem La_std_rep : ∀ {D : D7} (δ : ℂ) {a b : ℕ} (x : Formalism.MainNotions.TaylorLogMetric.VC D a b),
    x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D b) →
    ∃ M : Matrix (Fin b) (Fin a) D.host.E, (∀ i j, M i j ∈ D.host.AA) ∧
      x = δ • Formalism.MainNotions.TaylorLogMetric.embV D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) M := by
  intro D δ a b x hx
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    obtain ⟨c, hc, rfl⟩ := FL.lam_mem D D.host.ccK δ w hw
    refine ⟨((c : D.host.K) : D.host.E) • A, fun i j => ?_, ?_⟩
    · simpa using K_mul_mem_AA hc (YYl_le hA i j)
    · rw [GlobalTheory.MomSetup.embV_smulK, smul_smul]
  | zero => exact ⟨0, fun i j => (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).zero_mem, by rw [GlobalTheory.MomSetup.embV_zero, smul_zero]⟩
  | add x y _ _ h1 h2 =>
    obtain ⟨A, hA, rfl⟩ := h1
    obtain ⟨B, hB, rfl⟩ := h2
    exact ⟨A + B, fun i j => (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).add_mem (hA i j) (hB i j),
      by rw [GlobalTheory.MomSetup.embV_add, smul_add]⟩
  | neg x _ h =>
    obtain ⟨A, hA, rfl⟩ := h
    exact ⟨-A, fun i j => (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).neg_mem (hA i j), by rw [GlobalTheory.MomSetup.embV_neg, smul_neg]⟩

end GlobalTheory.LaStdEntries
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLatticeStandardPointsScaledEmbeddingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusLattice_standard_points_scaled_embedding : ∀ {D : D7} (δ : ℂ) {a b : ℕ} (x : Formalism.MainNotions.TaylorLogMetric.VC D a b), x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D b) → ∃ M : Matrix (Fin b) (Fin a) D.host.E, (∀ i j, M i j ∈ D.host.AA) ∧ x = δ • Formalism.MainNotions.TaylorLogMetric.embV D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) M := by
  first | exact @GlobalTheory.LaStdEntries.La_std_rep | exact GlobalTheory.LaStdEntries.La_std_rep | (intros; apply GlobalTheory.LaStdEntries.La_std_rep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalFrameFinitePartMemCompletedLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalFrameFinitePartMemCompletedLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameLat

theorem frame_finRat_mem_latO : ∀ {D : D7} (S T : HSp D) (B : GL (Fin S.rank) D.host.E) (B' : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → ∀ M : Matrix (Fin T.rank) (Fin S.rank) D.host.E, (∀ i j, M i j ∈ D.host.AA) → GlobalTheory.VacUnique.finRat S T (-(B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1)) ∈ latO S T (colLat B : Set (Fin S.rank → D.host.E)) (colLat B' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  intro D S T B B' hB M hM
  have hinv : ((B⁻¹ : GL (Fin S.rank) D.host.E).1) = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram := by
    have h1 : ((B⁻¹ : GL (Fin S.rank) D.host.E).1) * B.1 = 1 := by
      have := congrArg Units.val (inv_mul_cancel B); simpa using this
    have h2 : B.1 * ((B⁻¹ : GL (Fin S.rank) D.host.E).1) = 1 := by
      have := congrArg Units.val (mul_inv_cancel B); simpa using this
    calc ((B⁻¹ : GL (Fin S.rank) D.host.E).1)
        = (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1) * ((B⁻¹ : GL (Fin S.rank) D.host.E).1) := by rw [hB, one_mul]
      _ = _ := by rw [Matrix.mul_assoc _ B.1, h2, Matrix.mul_one]
  have key : -(B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1) = ∑ l, ∑ k,
      GlobalTheory.LatVac.genMap S T (-M l k) (fun m => B.1 m k) (fun i => B'.1 i l) := by
    rw [hinv]
    ext i j
    simp only [GlobalTheory.LatVac.genMap, Matrix.neg_apply, Matrix.sum_apply, Matrix.of_apply, Matrix.mul_apply]
    have hc : ∀ k m, Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 k m = star (B.1 m k) := fun _ _ => rfl
    simp only [hc, Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [neg_mul, neg_mul, mul_assoc, mul_assoc, mul_left_comm]
  have hmem : -(B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1) ∈ GlobalTheory.LatVac.latRat S T (colLat B : Set (Fin S.rank → D.host.E)) (colLat B' : Set (Fin T.rank → D.host.E)) := by
    rw [key]
    refine AddSubgroup.sum_mem _ fun l _ => AddSubgroup.sum_mem _ fun k _ => AddSubgroup.subset_closure ?_
    refine ⟨-M l k, Submodule.neg_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) (hM l k), _, ?_, _, ?_, rfl⟩
    · exact Submodule.subset_span ⟨k, rfl⟩
    · exact Submodule.subset_span ⟨l, rfl⟩
  exact GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) hmem

end GlobalTheory.FrameLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalFrameFinitePartMemCompletedLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalFrame_finitePart_mem_completedLattice : ∀ {D : D7} (S T : HSp D) (B : GL (Fin S.rank) D.host.E) (B' : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → ∀ M : Matrix (Fin T.rank) (Fin S.rank) D.host.E, (∀ i j, M i j ∈ D.host.AA) → GlobalTheory.VacUnique.finRat S T (-(B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1)) ∈ latO S T (colLat B : Set (Fin S.rank → D.host.E)) (colLat B' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  first | exact @GlobalTheory.FrameLat.frame_finRat_mem_latO | exact GlobalTheory.FrameLat.frame_finRat_mem_latO | (intros; apply GlobalTheory.FrameLat.frame_finRat_mem_latO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumRealRestrictionSatisfiesStandardThetaLaw
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacRealForm

theorem vacuum_real_law : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (σ : (D.what₂.Tau → ℂ) →+ AE D) (δ : ℂ), GlobalTheory.FockCompare.Chart W.θ σ → Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D (G.pS (.top t j)).rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D (G.pT (.top t j)).rank), ∀ Y, Formalism.MainNotions.TaylorLogMetric.al D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) x * Formalism.MainNotions.TaylorLogMetric.U D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) x (GlobalTheory.VacRealForm.thY σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f δ) Y = GlobalTheory.VacRealForm.thY σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f δ Y := by
  intro D T L sc G W U N σ δ hσ hcrv hδ t j hj f hf x hx Y
  obtain ⟨M, hM, rfl⟩ := GlobalTheory.T.torusLattice_standard_points_scaled_embedding δ x hx
  have hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (N.fr (.top j)).1 * (G.V (.top j)).gram * (N.fr (.top j)).1 = 1 :=
    N.fr_on (.top j) (show j ≤ D.R.m by omega)
  have hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (N.fr (.top (j + 1))).1 * (G.V (.top (j + 1))).gram *
      (N.fr (.top (j + 1))).1 = 1 := N.fr_on (.top (j + 1)) (show j + 1 ≤ D.R.m from hj)
  have hlat := GlobalTheory.T.orthonormalFrame_finitePart_mem_completedLattice (G.V (.top j)) (G.V (.top (j + 1))) (N.fr (.top j)) (N.fr (.top (j + 1))) hS M hM
  obtain ⟨k, hk, heig⟩ := GlobalTheory.T.heisenbergOperator_finitePart_latticeVacuum_sign W.ψ (G.V (.top j)) (G.V (.top (j + 1))) (colLat (N.fr (.top j))) (colLat (N.fr (.top (j + 1))))
    hf.1 (GlobalTheory.T.isSelfDualC_columnLattice_of_orthonormalFrame _ _ hS) (GlobalTheory.T.isSelfDualC_columnLattice_of_orthonormalFrame _ _ hT) f hf.2.lat _ hlat
  have hlaw := GlobalTheory.VacUnique.apply_add_infRat hσ hf.1 hf.2.theta _ heig
  rw [GlobalTheory.T.rationalPoint_finitePart_isotropic_pairing, neg_zero, AddChar.map_zero_eq_one, one_mul] at hlaw
  have hU := GlobalTheory.T.torusTranslate_thetaCoordinate_of_realPart_law σ (G.V (.top j)) (G.V (.top (j + 1))) (N.fr (.top j)) (N.fr (.top (j + 1))) hS hT δ hδ M f _ hlaw Y
  have hal := GlobalTheory.T.torusSemicharacter_eq_neg_one_pow_traceExponent (G.V (.top j)) (G.V (.top (j + 1))) (N.fr (.top j)) (N.fr (.top (j + 1))) hS hT δ hδ M k hk
  show Formalism.MainNotions.TaylorLogMetric.al D _ _ * Formalism.MainNotions.TaylorLogMetric.U D _ _ (thY σ (G.V (.top j)) (G.V (.top (j + 1))) (fun τ => (N.fr (.top j)).1.map (tauE D τ))
    (fun τ => (N.fr (.top (j + 1))).1.map (tauE D τ)) f δ) Y = _
  rw [hU, ← mul_assoc, hal, one_mul]
  rfl

end GlobalTheory.VacRealForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumRealRestrictionSatisfiesStandardThetaLawStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_realRestriction_satisfies_standardThetaLaw : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (σ : (D.what₂.Tau → ℂ) →+ AE D) (δ : ℂ), GlobalTheory.FockCompare.Chart W.θ σ → Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D (G.pS (.top t j)).rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D (G.pT (.top t j)).rank), ∀ Y, Formalism.MainNotions.TaylorLogMetric.al D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) x * Formalism.MainNotions.TaylorLogMetric.U D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) x (GlobalTheory.VacRealForm.thY σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f δ) Y = GlobalTheory.VacRealForm.thY σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f δ Y := by
  first | exact @GlobalTheory.VacRealForm.vacuum_real_law | exact GlobalTheory.VacRealForm.vacuum_real_law | (intros; apply GlobalTheory.VacRealForm.vacuum_real_law <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefinitePairUnitVacuumRealPointNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefinitePairUnitVacuumRealPointNeZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare

theorem vacuum_real_ne_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart W.θ σ → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∃ z : GlobalTheory.FockCompare.RW (G.pT (.top t j)) (G.pS (.top t j)), f (GlobalTheory.FockCompare.iotaW σ (G.pT (.top t j)) (G.pS (.top t j)) z) ≠ 0 := by
  classical
  intro D T L sc G W U N σ h t j hj f hf
  by_contra hcon
  push_neg at hcon
  have hψ := hf.1
  have hS : IsSelfDualC (G.pS (.top t j)) (N.latS (.top t j)) :=
    N.selfDual (X := .top j) (show j ≤ D.R.m by omega)
  have hT : IsSelfDualC (G.pT (.top t j)) (N.latT (.top t j)) :=
    N.selfDual (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega)
  obtain ⟨-, h2, h3⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D W.ψ _ _ _ _ hψ hS hT
  have hinf := fun u => GlobalTheory.VacUnique.latO_inf (u := u) (G.pS (.top t j)) (G.pT (.top t j))
    ((N.latS (.top t j) : Set _)) ((N.latT (.top t j) : Set _)) fun _ => True
  choose ε _ hε2 using h3 f hf.2.lat
  have e : f = 0 := by
    funext w
    obtain ⟨γ, z, u, hu, rfl⟩ := GlobalTheory.VacUnique.exists_decomp h h2 w
    rw [hf.2.theta.quasi, GlobalTheory.VacUnique.apply_real_add h hψ (hinf u hu) (hε2 u hu f hf.2.lat), hcon z]
    simp
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 := hn p hp
  rw [e] at n1
  simp [nrm2] at n1

end GlobalTheory.VacRealForm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefinitePairUnitVacuumRealPointNeZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definite_pair_unit_vacuum_real_point_ne_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart W.θ σ → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∃ z : GlobalTheory.FockCompare.RW (G.pT (.top t j)) (G.pS (.top t j)), f (GlobalTheory.FockCompare.iotaW σ (G.pT (.top t j)) (G.pS (.top t j)) z) ≠ 0 := by
  first | exact @GlobalTheory.VacRealForm.vacuum_real_ne_zero | exact GlobalTheory.VacRealForm.vacuum_real_ne_zero | (intros; apply GlobalTheory.VacRealForm.vacuum_real_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumRealRestrictionGaussianMulTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.FockCompare GlobalTheory.VacRealForm

namespace GlobalTheory.VacRealForm

theorem vacuum_real_form : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∃ θ : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.top t j)).rank (G.pT (.top t j)).rank → ℂ, θ ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) ∧ θ ≠ 0 ∧ ∀ w : WO (G.pS (.top t j)) (G.pT (.top t j)), w.map (finPart D) = 0 → f w = Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ) a b‖ ^ 2 : ℝ) : ℂ)) * θ (δ • (fun τ => (N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ)) := by
  intro D T L sc G W U N δ hC hδ t j hj f hf
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hf.2.inf
  have hU : ∀ X τ, IsUnit (N.frC X τ).det := fun X τ => by
    show IsUnit ((tauE D τ).mapMatrix (N.fr X).1).det
    rw [← RingHom.map_det]
    exact (Matrix.isUnits_det_units (N.fr X)).map _
  have hs : ∀ Z : D.what₂.Tau → Fin (G.pT (.top t j)).rank → Fin (G.pS (.top t j)).rank → ℂ, δ⁻¹ • δ • Z = Z :=
    fun Z => inv_smul_smul₀ hδ Z
  refine ⟨thY σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f δ,
    ⟨?_, ?_⟩, ?_, ?_⟩
  · exact (GlobalTheory.T.differentiable_fockVacuum_gaussian_definitePair W N σ hσ t j hj f hf).comp (differentiable_id.const_smul δ⁻¹)
  · exact GlobalTheory.T.vacuum_realRestriction_satisfies_standardThetaLaw W N σ δ hσ hC hδ t j hj f hf
  · obtain ⟨z, hz⟩ := GlobalTheory.T.definite_pair_unit_vacuum_real_point_ne_zero W N σ hσ t j hj f hf
    intro h0
    apply hz
    have e : thY σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f δ
        (δ • fun τ => ((N.frC (.top (j + 1)) τ)⁻¹ * Matrix.of (z τ) * N.frC (.top j) τ : Matrix _ _ ℂ)) = 0 :=
      congrFun h0 _
    unfold thY gZ at e
    erw [hs] at e
    rw [mul_eq_zero] at e
    rcases e with e | e
    · convert e using 3
      funext τ
      simp only [frPt, Matrix.of_apply]
      rw [show Matrix.of ((N.frC (.top (j + 1)) τ)⁻¹ * Matrix.of (z τ) * N.frC (.top j) τ) =
        (N.frC (.top (j + 1)) τ)⁻¹ * Matrix.of (z τ) * N.frC (.top j) τ from rfl,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.mul_one]
      rfl
    · exact absurd e (Complex.exp_ne_zero _)
  · intro w hw
    unfold thY gZ
    erw [hs]
    have e1 : frPt (N.frC (.top j)) (N.frC (.top (j + 1)))
        (fun τ => ((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ : Matrix _ _ ℂ)) =
        piW W.θ (G.pT (.top t j)) (G.pS (.top t j)) w := by
      funext τ
      simp only [frPt]
      rw [show Matrix.of ((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ) =
        (N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ from rfl,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.mul_one]
      rfl
    rw [e1, hσ.iota_pi hw, ← mul_assoc, mul_comm _ (f w), mul_assoc, ← Complex.exp_add]
    have e2 : -((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b,
        ((‖((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ) a b‖ ^ 2 : ℝ) : ℂ) +
        ((Real.pi * Formalism.L2.Pj.xiR D * sqSum (fun τ => ((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ : Matrix _ _ ℂ)) : ℝ) : ℂ) = 0 := by
      simp only [sqSum]
      push_cast
      ring
    rw [e2, Complex.exp_zero, mul_one]

end GlobalTheory.VacRealForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumRealRestrictionGaussianMulThetaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_real_restriction_gaussian_mul_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∃ θ : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.top t j)).rank (G.pT (.top t j)).rank → ℂ, θ ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) ∧ θ ≠ 0 ∧ ∀ w : WO (G.pS (.top t j)) (G.pT (.top t j)), w.map (finPart D) = 0 → f w = Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ) a b‖ ^ 2 : ℝ) : ℂ)) * θ (δ • (fun τ => (N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ)) := by
  first | exact @GlobalTheory.VacRealForm.vacuum_real_form | exact GlobalTheory.VacRealForm.vacuum_real_form | (intros; apply GlobalTheory.VacRealForm.vacuum_real_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetVacuumEqConstMulPeriodScaledJet
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj.TopJet

open Formalism.MainNotions.TaylorLogMetric in
theorem applyAt0_monomial (D : D7) {N N' : ℕ} (k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ) (G : VC D N N' → ℂ) :
    Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G = (k.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G k := by
  classical
  unfold Formalism.MainNotions.GL3Theta.applyAt0
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl,
    one_mul]

open Formalism.MainNotions.TaylorLogMetric in
theorem taylor_comp_smul (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ) (hG : Differentiable ℂ G) (a : ℂ) (α : Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (fun z => G (a • z)) α = a ^ (α.sum fun _ n => n) * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  unfold Formalism.MainNotions.TaylorLogMetric.taylor
  have key := iteratedFDeriv_comp_const_smul (𝕜 := ℂ) (i := Multiset.card (Finsupp.toMultiset α)) (f := G) a ((ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_diff hG).of_le (by exact_mod_cast le_top))
  rw [key]
  simp only [smul_zero, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]
  congr 2
  exact Finsupp.card_toMultiset α

open Formalism.MainNotions.TaylorLogMetric in
theorem taylor_const_smul (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ) (hG : Differentiable ℂ G) (c : ℂ) (α : Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (c • G) α = c * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  unfold Formalism.MainNotions.TaylorLogMetric.taylor
  have key := iteratedFDeriv_const_smul_apply (𝕜 := ℂ) (i := Multiset.card (Finsupp.toMultiset α)) (f := G) (x := 0) (a := c) (((ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_diff hG).of_le (by exact_mod_cast le_top)).contDiffAt)
  rw [key, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    mul_div_assoc]

theorem fockIn_vacuum_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0 → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ e0 : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.top t j)).rank (G.pT (.top t j)).rank → ℂ, Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ e0 → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∃ c : ℂˣ, ∀ k : FVar D (G.pT (.top t j)).rank (G.pS (.top t j)).rank →₀ ℕ, GlobalTheory.FunObj.fockIn W N.frC (.top t j) f (MvPolynomial.monomial k 1) 0 = c * ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e0) := by
  intro D T L sc G W U N δ t0 hC hδ hT t j hj e0 he0 f hf
  obtain ⟨θ, hθTh, hθ0, hreal⟩ := GlobalTheory.T.vacuum_real_restriction_gaussian_mul_theta W N δ hC hδ t j hj f hf
  have hG1 := (GlobalTheory.InducedType.induced_type D).1
  have he0ne : e0 ≠ 0 := by
    intro h
    have h1 := he0.2.2.1
    rw [h] at h1
    simp only [Formalism.MainNotions.TaylorLogMetric.normSq, Pi.zero_apply, norm_zero] at h1
    have h2 := h1.symm
    simp at h2
    exact GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D hG1 _ δ t0 hC hT h2.1
  obtain ⟨c, hc⟩ := (GlobalTheory.ThetaLine.theta_line D hG1 _ δ hC _ _ _
    (Or.inr ⟨_, _, GlobalTheory.FinWeil.Vacuum.sd_std D _, GlobalTheory.FinWeil.Vacuum.sd_std D _, rfl⟩)).1 θ hθTh e0 he0.1 he0ne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hθ0 (by rw [hc, zero_smul])
  refine ⟨Units.mk0 c hc0, fun k => ?_⟩
  have hdiff : Differentiable ℂ (fun z => θ (δ • z)) := hθTh.1.comp (differentiable_id.const_smul δ)
  rw [GlobalTheory.T.fockJet_gaussianEntire_origin_gridFrames W N t j hj f (fun z => θ (δ • z)) hdiff hreal k, applyAt0_monomial, applyAt0_monomial,
    taylor_comp_smul D θ hθTh.1, hc, taylor_const_smul D e0 he0.1.1]
  have hper : ∀ τ : D.what₂.Tau, GlobalTheory.FunObj.period δ τ = δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) := by
    intro τ
    rw [GlobalTheory.FunObj.period, GlobalTheory.AdTh.Fock.norm_embedding_hostFormConstant_eq, div_eq_mul_inv]
  have hprod : (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) =
      (δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹)) ^ (k.sum fun _ n => n) := by
    simp only [hper, Finsupp.prod, Finsupp.sum]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  rw [hprod, Units.val_mk0, mul_pow]
  ring

end GlobalTheory.FunObj.TopJet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetVacuumEqConstMulPeriodScaledJetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockJet_vacuum_eq_const_mul_periodScaledJet : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0 → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ e0 : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.top t j)).rank (G.pT (.top t j)).rank → ℂ, Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ e0 → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∃ c : ℂˣ, ∀ k : FVar D (G.pT (.top t j)).rank (G.pS (.top t j)).rank →₀ ℕ, GlobalTheory.FunObj.fockIn W N.frC (.top t j) f (MvPolynomial.monomial k 1) 0 = c * ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e0) := by
  first | exact @GlobalTheory.FunObj.TopJet.fockIn_vacuum_eq | exact GlobalTheory.FunObj.TopJet.fockIn_vacuum_eq | (intros; apply GlobalTheory.FunObj.TopJet.fockIn_vacuum_eq <;> assumption)
end
