module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralLiftCoprimeDerivative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoSelfIntersectionPowTensorDivPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPoints
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockPos

theorem differentiable_mul_of_cr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (G E : V → ℂ) (c : V → V → ℂ)
    (hG : Differentiable ℝ G) (hE : Differentiable ℝ E)
    (hGc : ∀ Z Y, fderiv ℝ G Z Y + Complex.I * fderiv ℝ G Z (Complex.I • Y) = -(c Z Y * G Z))
    (hEc : ∀ Z Y, fderiv ℝ E Z Y + Complex.I * fderiv ℝ E Z (Complex.I • Y) = c Z Y * E Z) :
    Differentiable ℂ (fun Z => G Z * E Z) := by
  intro Z
  have hL := (hG Z).hasFDerivAt.mul (hE Z).hasFDerivAt
  set L : V →L[ℝ] ℂ := G Z • fderiv ℝ E Z + E Z • fderiv ℝ G Z with hLdef
  have hI : ∀ Y, L (Complex.I • Y) = Complex.I * L Y := fun Y => by
    have h1 := hGc Z Y
    have h2 := hEc Z Y
    simp only [hLdef, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    linear_combination (-(Complex.I * E Z)) * h1 + (-(Complex.I * G Z)) * h2 +
      (E Z * fderiv ℝ G Z (Complex.I • Y) + G Z * fderiv ℝ E Z (Complex.I • Y)) * Complex.I_sq
  have hsm : ∀ (a : ℂ) (Y : V), L (a • Y) = a * L Y := fun a Y => by
    have e : a • Y = a.re • Y + a.im • (Complex.I • Y) := by
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul]
      congr 1
      exact (Complex.re_add_im a).symm
    rw [e, map_add L, L.map_smul, L.map_smul, hI, Complex.real_smul, Complex.real_smul]
    conv_rhs => rw [← Complex.re_add_im a]
    ring
  let g : V →L[ℂ] ℂ :=
    { toFun := fun Y => L Y
      map_add' := fun Y Y' => L.map_add Y Y'
      map_smul' := fun a Y => hsm a Y
      cont := L.continuous }
  exact (differentiableAt_iff_restrictScalars ℝ hL.differentiableAt).2 ⟨g, by rw [hL.fderiv]; ext Y; rfl⟩

theorem gauss_cr {ι : Type} [Fintype ι] {m n : ℕ} (r : ℝ) :
    Differentiable ℝ (fun Z : ι → Fin m → Fin n → ℂ =>
      Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) ∧
    ∀ Z Y : ι → Fin m → Fin n → ℂ,
      fderiv ℝ (fun Z : ι → Fin m → Fin n → ℂ =>
          Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) Z Y +
        Complex.I * fderiv ℝ (fun Z : ι → Fin m → Fin n → ℂ =>
          Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) Z (Complex.I • Y) =
      (2 * Real.pi * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) : ℂ) *
        Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ) := by
  let P : ι → Fin m → Fin n → ((ι → Fin m → Fin n → ℂ) →L[ℝ] ℂ) := fun τ a b =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) b).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => Fin m → Fin n → ℂ) τ))
  have hP : ∀ τ a b (Z : ι → Fin m → Fin n → ℂ), P τ a b Z = Z τ a b := fun _ _ _ _ => rfl
  have hq : ∀ Z : ι → Fin m → Fin n → ℂ, HasFDerivAt (fun Z : ι → Fin m → Fin n → ℂ => ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2)
      (∑ τ, ∑ a, ∑ b, (2 : ℕ) • (innerSL ℝ (Z τ a b)).comp (P τ a b)) Z := fun Z => by
    refine HasFDerivAt.fun_sum fun τ _ => HasFDerivAt.fun_sum fun a _ => HasFDerivAt.fun_sum fun b _ => ?_
    exact (P τ a b).hasFDerivAt.norm_sq
  have hE : ∀ Z : ι → Fin m → Fin n → ℂ, HasFDerivAt (fun Z : ι → Fin m → Fin n → ℂ =>
      Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ))
      (Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ) •
        Complex.ofRealCLM.comp ((Real.pi * r) • ∑ τ, ∑ a, ∑ b, (2 : ℕ) • (innerSL ℝ (Z τ a b)).comp (P τ a b))) Z :=
    fun Z => (Complex.ofRealCLM.hasFDerivAt.comp Z ((hq Z).const_mul (Real.pi * r))).cexp
  refine ⟨fun Z => (hE Z).differentiableAt, fun Z Y => ?_⟩
  rw [(hE Z).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_sum',
    Finset.sum_apply, smul_eq_mul, Complex.ofRealCLM_apply, innerSL_apply_apply, hP, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, nsmul_eq_mul]
  have key : ∀ z y : ℂ, z * starRingEnd ℂ y =
      ((inner ℝ z y : ℝ) : ℂ) + Complex.I * ((inner ℝ z (Complex.I * y) : ℝ) : ℂ) := by
    intro z y
    rw [Complex.inner, Complex.inner]
    apply Complex.ext <;> simp <;> ring
  simp_rw [key]
  push_cast
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem trace_frames {m n : ℕ} (GS B : Matrix (Fin n) (Fin n) ℂ) (GT B' : Matrix (Fin m) (Fin m) ℂ)
    (hB : Bᴴ * GS * B = 1) (hB' : B'ᴴ * GT * B' = 1) (Z Y : Matrix (Fin m) (Fin n) ℂ) :
    (GS⁻¹ * (B' * Y * B⁻¹)ᴴ * GT * (B' * Z * B⁻¹)).trace = ∑ a, ∑ b, Z a b * starRingEnd ℂ (Y a b) := by
  have e : GS⁻¹ * (B' * Y * B⁻¹)ᴴ * GT * (B' * Z * B⁻¹) = (GS⁻¹ * (B⁻¹)ᴴ) * (Yᴴ * Z) * B⁻¹ := by
    calc _ = GS⁻¹ * (B⁻¹)ᴴ * Yᴴ * (B'ᴴ * GT * B') * Z * B⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hB', Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have e2 : B⁻¹ * (GS⁻¹ * (B⁻¹)ᴴ) = 1 := by
    rw [Matrix.conjTranspose_nonsing_inv, ← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev, hB, inv_one]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, e2, Matrix.one_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

end GlobalTheory.FockPos

open GlobalTheory.FockCompare GlobalTheory.VacUnique

noncomputable section

namespace GlobalTheory.FockPos

variable {D : D7}

def frLin {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) :
    Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank →L[ℂ] RW T S :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Z τ => (frAt frT τ * Matrix.of (Z τ) * (frAt frS τ)⁻¹ : Matrix (Fin T.rank) (Fin S.rank) ℂ)
      map_add' := fun Y Z => by
        funext τ
        show (frAt frT τ * (Matrix.of (Y τ) + Matrix.of (Z τ)) * (frAt frS τ)⁻¹ : Matrix (Fin T.rank) (Fin S.rank) ℂ) = _ + _
        rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c Z => by
        funext τ
        show (frAt frT τ * (c • Matrix.of (Z τ)) * (frAt frS τ)⁻¹ : Matrix (Fin T.rank) (Fin S.rank) ℂ) = c • _
        rw [Matrix.mul_smul, Matrix.smul_mul] }

theorem frLin_apply {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank) (τ : D.what₂.Tau) :
    frLin frS frT Z τ = (frAt frT τ * Matrix.of (Z τ) * (frAt frS τ)⁻¹ : Matrix (Fin T.rank) (Fin S.rank) ℂ) := rfl

theorem norm_embedding_xi0_eq (D : D7) (τ : D.host.E →+* ℂ) : ‖τ D.host.xi0‖ = Formalism.L2.Pj.xiR D := by
  have hs : ∀ τ : D.host.E →+* ℂ, ‖τ D.host.sqrtMinusD‖ = Real.sqrt D.host.d := by
    intro τ
    have h0 : (τ D.host.sqrtMinusD) ^ 2 = -(D.host.d : ℂ) := by
      rw [← map_pow, Formalism.BasicNotions.Host.sqrtMinusD_sq D.host, map_neg, map_natCast]
    rw [← Real.sqrt_sq (norm_nonneg (τ D.host.sqrtMinusD)), ← norm_pow, h0, norm_neg, Complex.norm_natCast]
  unfold Formalism.L2.Pj.xiR Host.xi0
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul,
    Complex.norm_natCast, hs]

theorem xi_zero_eq_host (τ : D.what₂.Tau) : tauE D τ D.host.xi0 = Complex.I * (Formalism.L2.Pj.xiR D : ℂ) := by
  have h1 := GlobalTheory.RealSymplForm.realPlace_imaginaryGenerator_re_eq_zero D τ
  have h2 := Formalism.L2.Theta.xi_zero_im_pos D τ
  have h3 : ‖tauE D τ D.host.xi0‖ = Formalism.L2.Pj.xiR D := norm_embedding_xi0_eq D (tauE D τ)
  have h4 : (tauE D τ D.host.xi0).im = Formalism.L2.Pj.xiR D := by
    rw [← h3, Complex.norm_def, Complex.normSq_apply, h1, zero_mul, zero_add, Real.sqrt_mul_self_eq_abs,
      abs_of_pos h2]
  apply Complex.ext <;> simp [h1, h4]

theorem vacuum_real_entire : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) LS LT f → ∃ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Φ ∧ ∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w) := by
  intro D ψ θ S T frS frT LS LT hS hT f hf
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hf.2.inf
  obtain ⟨hF, hann⟩ := GlobalTheory.VacUnique.Ann.vacuum_annihilation D θ σ hσ ψ hf.1 S T (fun _ => 1) (fun _ => 1) f
    hf.2.theta hf.2.fock
  set F : RW T S → ℂ := fun z => f (iotaW σ T S z) with hFdef
  set X := frLin frS frT with hX
  set r := Formalism.L2.Pj.xiR D with hr
  set E : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ := fun Z =>
    Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ) with hE
  have hU : ∀ {k : ℕ} (fr : GL (Fin k) D.host.E) τ, IsUnit (frAt fr τ).det := fun fr τ =>
    isUnit_iff_ne_zero.2 (frAt_det_ne fr τ)
  have hG : Differentiable ℝ (fun Z => F (X Z)) := hF.comp (X.restrictScalars ℝ).differentiable
  have hdG : ∀ Z Y, fderiv ℝ (fun Z => F (X Z)) Z Y = fderiv ℝ F (X Z) (X Y) := fun Z Y => by
    have h : HasFDerivAt (fun Z => F (X Z)) ((fderiv ℝ F (X Z)).comp (X.restrictScalars ℝ)) Z :=
      (hF (X Z)).hasFDerivAt.comp Z (X.restrictScalars ℝ).hasFDerivAt
    rw [h.fderiv]
    rfl
  refine ⟨fun Z => F (X Z) * E Z,
    differentiable_mul_of_cr (fun Z => F (X Z)) E
      (fun Z Y => (2 * Real.pi * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) : ℂ))
      hG (gauss_cr r).1 (fun Z Y => ?_) (gauss_cr r).2, fun w hw => ?_⟩
  · rw [hdG, hdG]
    have hj : jO S T (fun _ => 1) (fun _ => 1) (X Y) = X (Complex.I • Y) := by
      rw [X.map_smul]
      funext τ
      rw [jO_apply]
      change Complex.I • ((1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) * Matrix.of (X Y τ) *
        (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) = _
      rw [Matrix.one_mul, Matrix.mul_one]
      rfl
    have h := hann (X Z) (X Y)
    rw [hj] at h
    have hom : ∀ Y' : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank, omO S T (X Z) (X Y') =
        ∑ τ, 2 * (Complex.I * (r : ℂ) * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y' τ a b)).re := by
      intro Y'
      rw [omO_apply]
      refine Finset.sum_congr rfl fun τ _ => ?_
      show 2 * (tauE D τ D.host.xi0 * hAt S T τ (X Z τ) (X Y' τ)).re = _
      unfold hAt
      rw [hX, frLin_apply, frLin_apply, trace_frames _ _ _ _ (frAt_on frS hS τ) (frAt_on frT hT τ), xi_zero_eq_host τ]
      rfl
    rw [hom, hom] at h
    have hs2 : ∀ τ, (∑ a, ∑ b, Z τ a b * starRingEnd ℂ ((Complex.I • Y) τ a b)) =
        -Complex.I * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) := fun τ => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    simp only [hs2] at h
    have key : ((∑ τ, 2 * (Complex.I * (r : ℂ) * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)).re : ℝ) : ℂ) +
        Complex.I * ((∑ τ, 2 * (Complex.I * (r : ℂ) * (-Complex.I * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b))).re : ℝ) : ℂ) =
        2 * Complex.I * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) := by
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      set s := ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)
      apply Complex.ext <;> simp <;> ring
    show _ = -((2 * Real.pi * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) : ℂ) * F (X Z))
    have h' : fderiv ℝ F (X Z) (X Y) - Real.pi * Complex.I * ((∑ τ, 2 * (Complex.I * (r : ℂ) * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)).re : ℝ) : ℂ) * F (X Z) +
      Complex.I * (fderiv ℝ F (X Z) (X (Complex.I • Y)) - Real.pi * Complex.I * ((∑ τ, 2 * (Complex.I * (r : ℂ) * (-Complex.I * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b))).re : ℝ) : ℂ) * F (X Z)) = 0 := h
    linear_combination h' + Real.pi * Complex.I * F (X Z) * key +
      2 * Real.pi * r * (∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)) * F (X Z) * Complex.I_sq
  · have e1 : X (zCo θ frS frT w) = piW θ T S w := by
      funext τ
      rw [hX, frLin_apply]
      change frAt frT τ * ((frAt frT τ)⁻¹ * compAt θ τ w * frAt frS τ) * (frAt frS τ)⁻¹ = _
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.mul_one]
      rfl
    show f w = gaussO θ frS frT w * (f (iotaW σ T S (X (zCo θ frS frT w))) * E (zCo θ frS frT w))
    rw [e1, hσ.iota_pi hw, ← mul_assoc, mul_comm _ (f w), mul_assoc, hE, gaussO, ← Complex.exp_add]
    have e2 : -((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖zCo θ frS frT w τ a b‖ ^ 2 : ℝ) : ℂ) +
        ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖zCo θ frS frT w τ a b‖ ^ 2 : ℝ) : ℂ) = 0 := by
      rw [hr]; push_cast; ring
    rw [e2, Complex.exp_zero, mul_one]

end GlobalTheory.FockPos

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntireStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacuum_real_restriction_gaussian_entire : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) LS LT f → ∃ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Φ ∧ ∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w) := by
  first | exact @GlobalTheory.FockPos.vacuum_real_entire | exact GlobalTheory.FockPos.vacuum_real_entire | (intros; apply GlobalTheory.FockPos.vacuum_real_entire <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieCombIffIsCombAt
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlagTan

section Comb

open DeRham Cris MonObj

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]

def lieComb {n : ℕ} (cf : Fin n → R) (v : Fin n → (epsR R ⟶ A)) : epsR R ⟶ A :=
  (List.ofFn fun i => GrpTangent.epsScale (cf i) ≫ v i).prod

theorem isLieComb_lieComb {n : ℕ} (cf : Fin n → R) (v : Fin n → (epsR R ⟶ A)) : IsLieComb cf v (lieComb cf v) :=
  ⟨_, fun _ => rfl, rfl⟩

theorem rel_lieComb {N : Type*} [AddCommMonoid N] [Module R N] {P : N → (epsR R ⟶ A) → Prop} (h0 : P 0 1)
    (ha : ∀ {f f' v v'}, P f v → P f' v' → P (f + f') (v * v'))
    (hs : ∀ {f v}, P f v → ∀ r : R, P (r • f) (GrpTangent.epsScale r ≫ v)) :
    ∀ {n : ℕ} (cf : Fin n → R) {f : Fin n → N} {v : Fin n → (epsR R ⟶ A)}, (∀ i, P (f i) (v i)) →
      P (∑ i, cf i • f i) (lieComb cf v)
  | 0, _, _, _, _ => by simpa [lieComb] using h0
  | n + 1, cf, f, v, h => by
    rw [Fin.sum_univ_succ, lieComb, List.ofFn_succ, List.prod_cons]
    exact ha (hs (h 0) _) (rel_lieComb h0 ha hs (fun i => cf i.succ) fun i => h i.succ)

theorem isLieImage_lieComb {n : ℕ} (cf : Fin n → R) {f : Fin n → HdR A} {v : Fin n → (epsR R ⟶ A)}
    (h : ∀ i, DeRham.IsLieImage (f i) (v i)) : DeRham.IsLieImage (∑ i, cf i • f i) (lieComb cf v) :=
  rel_lieComb (isLieImage_one_iff.2 (zero_mem _)) IsLieImage.add IsLieImage.smul cf h

theorem isKSValue_lieComb {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left}
    {h : IsGrpPullback A A' (DeRham.epsRed R) i} {n : ℕ} (cf : Fin n → R) {f : Fin n → HdR A} {v : Fin n → (epsR R ⟶ A)}
    (e : ∀ k, IsKSValue h (f k) (v k)) : IsKSValue h (∑ k, cf k • f k) (lieComb cf v) :=
  rel_lieComb ⟨0, ⟨0, zero_mem _, fun _ => (LinearMap.zero_apply _).trans (by simp)⟩, isLieImage_one_iff.2 (zero_mem _)⟩
    IsKSValue.add IsKSValue.smul cf e

end Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]

theorem isLieComb_iff_isCombAt {A : Over (Sp K)} [GrpObj A] {x : Sp K ⟶ Xo.X} {π : A.left ⟶ Xo.univ.t.G.left}
    (h : IsGrpPullback A Xo.univ.t.G x π) {n : ℕ} (cf : Fin n → K) (v : Fin n → (epsR K ⟶ A)) (w : epsR K ⟶ A) :
    IsLieComb cf v w ↔ IsCombAt x (fun i => (v i).left ≫ π) cf (w.left ≫ π) :=
  Chart.comb_push h cf v w

def ksChg (Φ : Finset (E →+* ℂ)) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) :
    (HIx Dw Φ → K) →ₗ[K] (HIx Dw Φ → K) where
  toFun M k := ∑ a', ∑ b', g (conjEmb k.1.1) a' k.2.1 * M ⟨k.1, a', b'⟩ * g k.1.1 b' k.2.2
  map_add' M M' := by ext k; simp [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' r M := by ext k; simp [Finset.mul_sum, mul_assoc, mul_left_comm]

theorem ksChg_apply (Φ : Finset (E →+* ℂ)) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (M : HIx Dw Φ → K) (k : HIx Dw Φ) :
    ksChg Φ g M k = ∑ a', ∑ b', g (conjEmb k.1.1) a' k.2.1 * M ⟨k.1, a', b'⟩ * g k.1.1 b' k.2.2 := rfl

theorem ksChg_eq_mul (Φ : Finset (E →+* ℂ)) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (M : HIx Dw Φ → K) (τ : Φ) : (Matrix.of fun a b => ksChg Φ g M ⟨τ, a, b⟩) =
      (g (conjEmb τ.1)).transpose * (Matrix.of fun a b => M ⟨τ, a, b⟩) * g τ.1 := by
  ext a b
  simp only [Matrix.of_apply, ksChg_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem ksChg_ksChg (Φ : Finset (E →+* ℂ)) (g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (M : HIx Dw Φ → K) : ksChg Φ g (ksChg Φ g' M) = ksChg Φ (fun τ => g' τ * g τ) M := by
  funext ⟨τ, a, b⟩
  have h : (Matrix.of fun a b => ksChg Φ g (ksChg Φ g' M) ⟨τ, a, b⟩) =
      Matrix.of fun a b => ksChg Φ (fun τ => g' τ * g τ) M ⟨τ, a, b⟩ := by
    simp only [ksChg_eq_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  exact congrFun (congrFun h a) b

theorem ksChg_one (Φ : Finset (E →+* ℂ)) (M : HIx Dw Φ → K) : ksChg Φ (fun _ => 1) M = M := by
  funext ⟨τ, a, b⟩
  have h := ksChg_eq_mul Φ (fun _ => 1) M τ
  rw [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at h
  exact congrFun (congrFun h a) b

theorem exists_frChg_inv {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K} {a : K}
    {y y' : FrPt Xo c K} (h : FrChg g a y y') :
    ∃ g' a', FrChg g' a' y' y ∧ (∀ τ, g' τ * g τ = 1) ∧ ∀ τ, g τ * g' τ = 1 := by
  obtain ⟨g', a', -, h'⟩ := (frChg_exists_unique E H Dw l Xo c K y' y).1 h.1.symm
  have C := frChg_calculus E H Dw l Xo c K
  have e := ((frChg_exists_unique E H Dw l Xo c K y y).2 _ _ _ _ ((C.1 _ _ _ _ _ _ _ h).1 h') (C.2.1 y)).1
  have e' := ((frChg_exists_unique E H Dw l Xo c K y' y').2 _ _ _ _ ((C.1 _ _ _ _ _ _ _ h').1 h) (C.2.1 y')).1
  exact ⟨g', a', h', congrFun e, congrFun e'⟩

theorem smul_sum_smul_sum {N α β γ : Type} [AddCommGroup N] [Module K N] [Fintype α] [Fintype β] [Fintype γ]
    (p : α → K) (M : α → β → K) (q : β → γ → K) (n : γ → N) :
    ∑ a, p a • ∑ b, M a b • ∑ k, q b k • n k = ∑ k, (∑ a, ∑ b, p a * M a b * q b k) • n k := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul, mul_assoc]
  exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm


open DeRham Cris in
theorem IsKS.of_frChg {Φ : Finset (E →+* ℂ)} {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K}
    {a : K} {y y' : FrPt Xo c K} (h : FrChg g a y y') {x' : Sp (DualNumber K) ⟶ Xo.X} {M' : HIx Dw Φ → K}
    (hM : IsKS Φ y' x' M') : IsKS Φ y x' (ksChg Φ g M') := by
  obtain ⟨g', a', h', e, -⟩ := exists_frChg_inv h
  obtain ⟨A, _, A', _, π, π', i, hi, ψ, ub, hb, hπ, hπ', hiπ, hψ, hub, hhb, hrow⟩ := hM
  rw [h.1] at hπ
  obtain ⟨N, _, _, v, -, -, htan, hcomb, -, -⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo K y.x
  choose n hn using fun σ k => (htan _).1 (y.tan σ k)
  have hn' : ∀ σ k, y'.u σ k = v (∑ j, g σ k j • n σ j) := fun σ k => by
    have := h.2.1 σ k
    rwa [show y.u σ = fun j => v (n σ j) from funext fun j => (hn σ j).symm, hcomb] at this
  have key : ∀ {m : ℕ} (cf : Fin m → K) (u : Fin m → (epsR K ⟶ A)) (b : Fin m → N) (w : epsR K ⟶ A),
      (∀ j, (u j).left ≫ π = v (b j)) → (IsLieComb cf u w ↔ w.left ≫ π = v (∑ j, cf j • b j)) :=
    fun cf u b w hu => by rw [isLieComb_iff_isCombAt hπ, funext hu, hcomb]
  have hub' : ∀ σ k, (ub σ k).left ≫ π = v (∑ j, g σ k j • n σ j) := fun σ k => (hub σ k).trans (hn' σ k)
  have hu : ∀ σ k, (lieComb (g' σ k) (ub σ)).left ≫ π = v (n σ k) := fun σ k => by
    rw [(key _ _ _ _ (hub' σ)).1 (isLieComb_lieComb _ _)]
    congr 1
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, e, Matrix.one_apply]
    simp
  refine ⟨A, _, A', _, π, π', i, hi, ψ, fun σ k => lieComb (g' σ k) (ub σ),
    fun q => ∑ j, g' q.1 q.2 j • hb ⟨q.1, j⟩, hπ, hπ', hiπ, hψ, fun σ k => (hu σ k).trans (hn σ k),
    fun σ k => isLieImage_lieComb _ (hhb σ), fun τ a => ?_⟩
  choose w hw f hf hd hv using hrow τ
  refine ⟨lieComb (fun a' => g (conjEmb τ.1) a' a) w, (key _ _ _ _ (hu τ.1)).2 ?_,
    ∑ a', g (conjEmb τ.1) a' a • f a', Submodule.sum_mem _ fun a' _ => Submodule.smul_mem _ _ (hf a'),
    fun ⟨σ, k⟩ => ?_, isKSValue_lieComb _ hv⟩
  · rw [(key _ _ _ _ fun a' => (key _ _ _ _ (hub' τ.1)).1 (hw a')).1 (isLieComb_lieComb _ _)]
    congr 1
    exact smul_sum_smul_sum _ (fun a' b' => M' ⟨τ, a', b'⟩) _ _
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hd, smul_eq_mul]
      by_cases hσ : σ = conjEmb τ.1
      · subst hσ
        have := congrFun (congrFun (e (conjEmb τ.1)) k) a
        simpa [Matrix.mul_apply, Matrix.one_apply] using this
      · simp [hσ]

theorem isKS_frChg_iff (Φ : Finset (E →+* ℂ)) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (a : K) (y y' : FrPt Xo c K) (h : FrChg g a y y') (x' : Sp (DualNumber K) ⟶ Xo.X) (M' : HIx Dw Φ → K) :
    IsKS Φ y' x' M' ↔ IsKS Φ y x'
      (fun k => ∑ a', ∑ b', g (conjEmb k.1.1) a' k.2.1 * M' ⟨k.1, a', b'⟩ * g k.1.1 b' k.2.2) := by
  refine ⟨fun k => k.of_frChg h, fun k => ?_⟩
  obtain ⟨g', a', h', -, e⟩ := exists_frChg_inv h
  have := IsKS.of_frChg h' (M' := ksChg Φ g M') k
  rwa [ksChg_ksChg, funext e, ksChg_one] at this

end GlobalTheory.FlagTan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolShapeOfOverK
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift.ProjLift

theorem exists_factor {A B X I : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup X] [Module ℂ X]
    (L₁ : A →ₗ[ℂ] X) (L₂ : B →ₗ[ℂ] X) (j : I → B) (hj : Submodule.span ℂ (Set.range j) = ⊤) (h : ∀ x, ∃ t, L₁ t = L₂ (j x)) :
    ∃ φ : B →ₗ[ℂ] A, ∀ y, L₁ (φ y) = L₂ y := by
  have h1 : ∀ y, L₂ y ∈ LinearMap.range L₁ := fun y =>
    (Submodule.span_le (p := (LinearMap.range L₁).comap L₂)).2 (by rintro _ ⟨x, rfl⟩; exact h x) (hj.ge Submodule.mem_top)
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property L₁.rangeRestrict (L₂.codRestrict _ h1) L₁.surjective_rangeRestrict
  exact ⟨φ, fun y => congrArg Subtype.val (LinearMap.congr_fun hφ y)⟩

section Low

open Matrix Formalism.MainNotions.S GlobalTheory.DefLift

variable {D : D7}


open Classical in
theorem eq_on_low {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} (h1 : LowSm M)
    (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : T ∈ Mult θ M J χ)
    {U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M} (hU : KEquiv θ M U) (e : ∀ τ, lowT M τ) (he : ∀ τ, e τ ≠ 0)
    (h : T (fun τ => (e τ : M.sm τ)) = U e) (v : ∀ τ, lowT M τ) : T (fun τ => (v τ : M.sm τ)) = U v := by
  have hT' : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
      (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
    intro τ g hg v w hw
    clear h
    induction hT using Submodule.span_induction with
    | mem T hT => exact hT.equiv τ g hg v w hw
    | zero => rfl
    | add x y _ _ hx hy => exact (congrArg₂ (· + ·) hx hy).trans rfl
    | smul a x _ hx => exact (congrArg (a • ·) hx).trans rfl
  have key := mem_of_translates h1 h2 (T.compLinearMap (fun τ => (lowT M τ).subtype) - U) ⊥ e he
    (by simpa [sub_eq_zero] using h) (fun τ k hk v u hu hv => ?_) v
  · simpa [sub_eq_zero] using key
  · have hv' : T (fun τ => (v τ : M.sm τ)) = U v := by simpa [sub_eq_zero] using hv
    have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    have hg : (M.fr τ)⁻¹ * k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
      have hk' : kᴴ * Formalism.REAL.Jm (M.ε τ) * k = Formalism.REAL.Jm (M.ε τ) := kset_uj hk
      have e1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
        rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
      change ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * k * M.fr τ) = gramAt D V τ
      calc ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * k * M.fr τ)
          = (M.fr τ)ᴴ * (kᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * k) *
              M.fr τ := by
            rw [← M.fr_gram τ]; simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = gramAt D V τ := by rw [e1, mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, hk', M.fr_gram]
    have e2 : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
        mul_nonsing_inv _ hd, Matrix.mul_one]
    have e3 := hT' τ _ hg (fun τ => (v τ : M.sm τ)) (u : M.sm τ) (by
      rw [hu, DSModel.rep, e2])
    have e4 : (fun ρ => ((Function.update v τ u ρ : lowT M ρ) : M.sm ρ)) =
        Function.update (fun ρ => (v ρ : M.sm ρ)) τ (u : M.sm τ) :=
      funext fun ρ => Function.apply_update (fun ρ (y : lowT M ρ) => (y : M.sm ρ)) v τ u ρ
    have e5 : T (fun ρ => ((Function.update v τ u ρ : lowT M ρ) : M.sm ρ)) = U (Function.update v τ u) := by
      rw [e4, e3, hv', hU τ k hk v u hu]
    simpa [sub_eq_zero] using e5

theorem kEquiv_thetaP {θ : InfFam D} {V W : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel W S} {c : CoefA V}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {pt : PolF D W.rank V.rank → (WO V W → ℂ)}
    {Δ : PolF D W.rank V.rank} {io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank} (hio : IsIoW θ M c ω pt Δ io)
    {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} {B : Submodule ℂ (GA D V → c.W)}
    {thP : B →ₗ[ℂ] (LowT M →ₗ[ℂ] (GA D W → ℂ))}
    (hth : Lift.IsThetaP ν 𝓕 (fun g h φ => thetaKO ω h g φ) pt io B thP) (y : B) :
    KEquiv θ M ((thP y).compMultilinearMap (PiTensorProduct.tprod ℂ)) := by
  intro τ k hk v u hu
  have hmul : ∀ h g k φ, thetaKO ω h (g * k) φ = thetaKO ω h g (ω (1, k) φ) := fun h g k φ => by
    unfold thetaKO
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  funext g
  simp only [LinearMap.compMultilinearMap_apply, rTr, hth.eq, Lift.thetaPInt, hmul, hio.2.1 τ k hk v u hu]

theorem exists_lift {θ : InfFam D} {W : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel W S} (h1 : LowSm M)
    (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {J : Set (GA D W)} {χ : GA D W → ℂ} {A B I : Type} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (e : A →ₗ[ℂ] MMap M) (he : ∀ t, e t ∈ Mult θ M J χ)
    (L : B →ₗ[ℂ] (LowT M →ₗ[ℂ] (GA D W → ℂ)))
    (hL : ∀ y, KEquiv θ M ((L y).compMultilinearMap (PiTensorProduct.tprod ℂ))) (j : I → B)
    (hj : Submodule.span ℂ (Set.range j) = ⊤) (v : ∀ τ, lowT M τ) (hv : ∀ τ, v τ ≠ 0)
    (h : ∀ x, ∃ t, e t (fun τ => (v τ : M.sm τ)) = L (j x) (PiTensorProduct.tprod ℂ v)) :
    ∃ φ : B →ₗ[ℂ] A, ∀ y (u : ∀ τ, lowT M τ), e (φ y) (fun τ => (u τ : M.sm τ)) = L y (PiTensorProduct.tprod ℂ u) := by
  let L₁ : A →ₗ[ℂ] ((∀ τ, lowT M τ) → GA D W → ℂ) :=
    { toFun := fun t u => e t (fun τ => (u τ : M.sm τ))
      map_add' := fun a b => by rw [map_add (f := _)]; rfl
      map_smul' := fun a b => by rw [map_smul]; rfl }
  let L₂ : B →ₗ[ℂ] ((∀ τ, lowT M τ) → GA D W → ℂ) :=
    { toFun := fun y u => L y (PiTensorProduct.tprod ℂ u)
      map_add' := fun a b => by rw [map_add (f := _)]; rfl
      map_smul' := fun a b => by rw [map_smul]; rfl }
  obtain ⟨φ, hφ⟩ := exists_factor L₁ L₂ j hj fun x => (h x).imp fun t ht =>
    funext fun u => eq_on_low h1 h2 (he t) (hL (j x)) v hv ht u
  exact ⟨φ, fun y u => congrFun (hφ y) u⟩

end Low

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem holShape_of_overK (R : RealDat D A Ks) (i : Fin D.R.m) {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) :
    GlobalTheory.HolDict.HolShape (R.MW i σ) := by
  have hs : ∀ ρ, (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := fun ρ => D.sp.W_sigval _ (inR i).1 (inR i).2 _
  have hr : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = (Wc D i).rank := by
    have := D.R.m_add_three_le_k
    have hi := i.2
    rw [rank_Wc i]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have key : ∀ ρ a, (R.MW i σ).lam ρ a = (Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) a : ℝ) ∧
      (R.MW i σ).ε ρ a = decide ((a : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1) := fun ρ a => by
    have he := (R.MW i σ).enum ρ
    unfold Links.parAt at he
    rw [if_pos (((labels_overK σ).1 hσ).2 ρ)] at he
    rw [← hs ρ]
    exact GlobalTheory.HolDict.isEnum_holPar_kapW _ (rank_Wc i) (by rw [hs ρ]; exact hr) he a
  have hc : ∀ ρ, Formalism.QuantumDeterminants.IsHCParam ((R.MW i σ).lam ρ) := fun ρ => by
    refine ⟨((R.MW i σ).enum ρ).1, fun a => ?_⟩
    obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int (D.hc (lab σ ρ)) a
    obtain ⟨s, hs'⟩ := Formalism.L2.NTheta.odd_r D.R
    refine ⟨z - s, ?_⟩
    have hn : (((Wc D i).rank : ℕ) : ℝ) = 2 * s + 1 := by rw [rank_Wc i, hs']; push_cast; rfl
    rw [(key ρ a).1, hz, hn]
    push_cast
    ring
  exact fun ρ => ⟨hc ρ, _, by omega, fun a => (key ρ a).2⟩

theorem proj_apply (R : RealDat D A Ks) (hg : R.models_gW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (t : (R.HW i σ).H)
    (v : (R.MW i σ).Vec) :
    (R.HW i σ).e ((∑ g, RealDat.eC (A := A) σ g • R.gW i σ g) t) v = R.eWf i σ ((R.HW i σ).e t v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [RealDat.eWf, gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, MultilinearMap.sum_apply,
    MultilinearMap.smul_apply, hg i σ, postOn_apply]
  rfl


end GlobalTheory.GalLift.ProjLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionCycleFormulaProjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionCycleFormulaProjective
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.RatSecCycle

open GlobalTheory.Cartier.CartierDiv

theorem exists_sec_divOfSec_eq {X : Scheme.{0}} [IsIntegral X] (E : CartierDiv X) (hE : E.Eff) :
    ∃ (s : (toLB E).Sec) (hs : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s),
      divOfSec (isLB_toLB E) s hs = E := by
  have h := presents_toLB E
  obtain ⟨s, hs1⟩ := h.exists_rat_eq (f := 1) (mem_sections.2 hE)
  have hs : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s :=
    (h.generatesAt_rat_iff s).1 (hs1 ▸ E.generatesAt_genericPoint one_ne_zero)
  refine ⟨s, hs, Presents.unique (presents_divOfRatSec (isLB_toLB E) _) ⟨isLB_toLB E,
    isRatSec_ratOfSec s hs, fun i x hx => ?_⟩⟩
  have e : ratOfSec s hs i = i.1.2 := Units.ext (by
    rw [val_ratOfSec (gen_mem hx), ← h.rat_mul s i (gen_mem hx), hs1, one_mul])
  rw [e]
  exact h.isEqn i x hx

end GlobalTheory.RatSecCycle


open GlobalTheory.Cartier.CartierDiv in
theorem GlobalTheory.ratSec_cycle_formula : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ (X := X)) → ∀ (n : ℕ), topologicalKrullDim X ≤ (n + 1 : ℕ) → ∀ (M : LB X) (hM : M.IsLB) (P : Fin n → LB X), (∀ i, (P i).IsLB) → ∀ (r : M.ι → X.functionFieldˣ) (hr : IsRatSec M r), interNum κ (structureModule X) (Fin.cons M P : Fin (n + 1) → LB X) = ∑ᶠ w, (divOfRatSec hM hr).mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  intro κ _ X _ _ _ hp n hn M hM P hP r hr
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  set D := divOfRatSec hM hr with hD
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hp
  obtain ⟨E, hE, hDE⟩ := GlobalTheory.T.exists_effective_cartierDivisor_add_effective X H hH D
  have key : ∀ E' : CartierDiv X, E'.Eff →
      interNum κ (structureModule X) (Fin.cons (toLB E') P : Fin (n + 1) → LB X) =
        ∑ᶠ w, E'.mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
    intro E' hE'
    obtain ⟨s, hs, e⟩ := GlobalTheory.RatSecCycle.exists_sec_divOfSec_eq E' hE'
    have := GlobalTheory.T.intersectionNumber_globalSection_eq_sum_cycle κ X hp n hn (toLB E') (isLB_toLB E') P hP s hs
    rw [e] at this
    exact this
  have hv := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom κ X) (structureModule X) hp
    (d := n + 1) (by rw [QCoh.suppDim_structureModule]; exact hn)
  have hc : CechPic.cls (toLB (D + E)) (isLB_toLB (D + E)) =
      CechPic.cls M hM + CechPic.cls (toLB E) (isLB_toLB E) := by
    rw [← toPic_apply, ← toPic_apply, map_add (f := _), (presents_divOfRatSec hM hr).toPic_eq]
  have ha := hv.interNum_cons_of_cls_eq_add le_rfl hP (isLB_toLB (D + E)) hM (isLB_toLB E) hc
  rw [key _ hDE, key _ hE] at ha
  have hfin : ∀ F : CartierDiv X, Function.HasFiniteSupport
      (fun w => F.mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P) :=
    fun F => (F.finite_support_mult).subset (Function.support_mul_subset_left _ _)
  have e2 : (∑ᶠ w, (D + E).mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P) =
      (∑ᶠ w, D.mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P) +
        ∑ᶠ w, E.mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
    simp only [mult_add, add_mul]
    exact finsum_add_distrib (hfin D) (hfin E)
  rw [e2] at ha
  linarith
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionCycleFormulaProjectiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_section_cycle_formula_projective : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ (X := X)) → ∀ (n : ℕ), topologicalKrullDim X ≤ (n + 1 : ℕ) → ∀ (M : LB X) (hM : M.IsLB) (P : Fin n → LB X), (∀ i, (P i).IsLB) → ∀ (r : M.ι → X.functionFieldˣ) (hr : IsRatSec M r), interNum κ (structureModule X) (Fin.cons M P : Fin (n + 1) → LB X) = ∑ᶠ w, (divOfRatSec hM hr).mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  first | exact @GlobalTheory.ratSec_cycle_formula | exact GlobalTheory.ratSec_cycle_formula | (intros; apply GlobalTheory.ratSec_cycle_formula <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMonomialAtOriginGaussianEntireOrthonormal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMonomialAtOriginGaussianEntireOrthonormal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockPos

theorem fock_monomial_zero_of_on : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), IsStdChar D ψ (-1) → IsInfFam θ → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ (F : WO S T → ℂ) (Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ), Differentiable ℂ Φ → (∀ w : WO S T, w.map (finPart D) = 0 → F w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.FockPos.frAt frS) (GlobalTheory.FockPos.frAt frT) F (MvPolynomial.monomial k 1) 0 = (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) ^ (k.sum fun _ n => n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Φ := by
  intro D ψ θ S T frS frT hψ hθ hS hT F Φ hΦ hF k
  have hS' : ∀ τ, (frAt frS τ)ᴴ * gramAt D S τ * frAt frS τ = 1 := frAt_on frS hS
  have hT' : ∀ τ, (frAt frT τ)ᴴ * gramAt D T τ * frAt frT τ = 1 := frAt_on frT hT
  exact GlobalTheory.FockJetOrigin.fock_monomial_zero θ hS' hT' hψ hθ F Φ hΦ (fun w hw => hF w hw) k

end GlobalTheory.FockPos
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMonomialAtOriginGaussianEntireOrthonormalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockMonomial_at_origin_gaussian_entire_orthonormal : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), IsStdChar D ψ (-1) → IsInfFam θ → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ (F : WO S T → ℂ) (Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ), Differentiable ℂ Φ → (∀ w : WO S T, w.map (finPart D) = 0 → F w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.FockPos.frAt frS) (GlobalTheory.FockPos.frAt frT) F (MvPolynomial.monomial k 1) 0 = (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) ^ (k.sum fun _ n => n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Φ := by
  first | exact @GlobalTheory.FockPos.fock_monomial_zero_of_on | exact GlobalTheory.FockPos.fock_monomial_zero_of_on | (intros; apply GlobalTheory.FockPos.fock_monomial_zero_of_on <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActLevOfLiftsOfEqOne
noncomputable section

namespace GlobalTheory.LevelActionOfLifts

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem levR_congr {f g k : Dw.La →ₗ[𝓞 E] Dw.La}
    (h : ∀ a, f a - g a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) {S : Type} [CommRing S] [Algebra c.F S]
    (y y' : FrPt Xo c S) : levR (f, k) y y' ↔ levR (g, k) y y' := by
  have e : ∀ a, Xo.univ.eta (f a) = Xo.univ.eta (g a) := fun a => GlobalTheory.LevelActionLaws.eta_congr Xo (h a)
  unfold levR IsLevMove
  simp only [e]

def modHalf (l : Level H) (f : Dw.La →ₗ[𝓞 E] Dw.La) : Module.End (𝓞 E) (LaMod Dw l) :=
  Submodule.mapQ _ _ f (by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)

end General

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

theorem actLev_of_lifts (Xo : Moduli Dw l) (c : Coeff l) {G : Type} [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M)
    (h1 : ∀ a, lev 1 a - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La))
    (hm : ∀ g h a, lev (g * h) a - lev g (lev h a) ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) :
    ActLev (Xo := Xo) c (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) := by
  let φ : G →* Module.End (𝓞 D.host.E) (LaMod Dw l) :=
    { toFun := fun g => modHalf l (lev g)
      map_one' := by
        refine LinearMap.ext fun q => ?_
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        exact (Submodule.Quotient.eq _).2 (h1 a)
      map_mul' := fun g h => by
        refine LinearMap.ext fun q => ?_
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        exact (Submodule.Quotient.eq _).2 (hm g h a) }
  let ψ : G →* (LaMod Dw l ≃ₗ[𝓞 D.host.E] LaMod Dw l) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (𝓞 D.host.E) (LaMod Dw l)).toMonoidHom.comp φ.toHomUnits
  have key : ∀ (g : G) {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S),
      levActR (Xo := Xo) (c := c) (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) g y y' ↔
        levActR (Xo := Xo) (c := c) (GlobalTheory.FormTies.levFull Dw l) (ψ g) y y' := by
    intro g S _ _ y y'
    refine levR_congr (fun a => (Submodule.Quotient.eq _).1 ?_) y y'
    exact (liftLa_spec (ψ g) a).symm
  have L := GlobalTheory.FullLevelAction.actLaws_levFull Xo c hpq hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g S _ _ y
    obtain ⟨y', h⟩ := L.total (ψ g) S y
    exact ⟨y', (key g y y').2 h⟩
  · intro g S _ _ y y' y'' h h'
    exact L.func (ψ g) S y y' y'' ((key _ _ _).1 h) ((key _ _ _).1 h')
  · intro S _ _ y
    refine (key 1 y y).2 ?_
    rw [map_one]
    exact L.one S y
  · intro g h S _ _ y y' y'' a b
    refine (key _ _ _).2 ?_
    rw [map_mul]
    exact L.mul _ _ S y y' y'' ((key _ _ _).1 a) ((key _ _ _).1 b)
  · intro g S T _ _ _ _ φ y y' z z' m a b
    exact L.nat (ψ g) S T φ y y' z z' m ((key _ _ _).1 a) ((key _ _ _).1 b)
  · intro g S _ _ t y y' z z' m a b
    exact L.bor (ψ g) S t y y' z z' m ((key _ _ _).1 a) ((key _ _ _).1 b)

theorem actLev_of_lifts_of_eq_one : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (G : Type) [Group G] (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La)), 1 ≤ Dw.p + Dw.q → l.A = 1 → (∀ a, lev 1 a - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) → (∀ g h a, lev (g * h) a - lev g (lev h a) ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) → ActLev (Xo := Xo) c (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) := by
  intro D H Dw l Xo c G _ lev hpq hA h1 hm
  exact actLev_of_lifts Xo c lev hpq (by rw [hA]; exact Nat.coprime_one_left _) h1 hm

end GlobalTheory.LevelActionOfLifts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharCMEtaLocalEqNegOnePowValInert
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharCMEtaLocalEqNegOnePowValInert
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.MuInert

theorem valuation_eq_uniformizer {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    {x : w.adicCompletion E} (hx : Valued.v x = WithZero.exp (-1 : ℤ)) :
    ValuativeRel.valuation (w.adicCompletion E) x = ValuativeRel.uniformizer (w.adicCompletion E) := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E)) Valued.v
  apply le_antisymm
  · rw [ValuativeRel.le_uniformizer_iff, he.lt_one_iff_lt_one, hx, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  · obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (ValuativeRel.uniformizer (w.adicCompletion E))
    rw [← hy]
    have h1 : Valued.v y < 1 := by
      rw [← he.lt_one_iff_lt_one, hy]; exact ValuativeRel.uniformizer_lt_one
    rw [he.le_iff_le, hx]
    by_cases hy0 : Valued.v y = 0
    · rw [hy0]; exact zero_le'
    · rw [← WithZero.exp_log hy0] at h1 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
      rw [WithZero.exp_le_exp]; omega

theorem valued_eq_one {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    {x : w.adicCompletion E} (hx : ValuativeRel.valuation (w.adicCompletion E) x = 1) : Valued.v x = 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E)) Valued.v).eq_one_iff_eq_one.1 hx

end GlobalTheory.MuInert

namespace GlobalTheory.MuInert

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (finiteCompletionMap ideleMap)

theorem loc_eq_unrChar_neg_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ μ : HChar E,
    (∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x) →
    (∀ (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ), ¬ IsSplitAt w → Valued.v (u : w.adicCompletion E) = 1 →
      μ.1 (Neutral.B1.localIdele E w u) = 1) →
    ∀ w : Pl E, ¬ IsSplitAt w → μ.loc w = GlobalTheory.SmGL.unrChar (w.adicCompletion E) (-1) := by
  intro E _ _ _ hU μ hres hunit w hw
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hns : ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E))) := by
    intro hs
    obtain ⟨a, b, hab, ha, hb⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
    apply hw
    rcases eq_or_ne a w with rfl | haw
    · exact ⟨b, hab.symm, hb⟩
    · exact ⟨a, haw, ha⟩
  have hun : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 (maximalRealSubfield E))) := by
    refine GlobalTheory.LFun.isUnram_iff.2 fun u hu => ?_
    obtain rfl := GlobalTheory.LFun.eq_of_not_isSplit hns hu rfl
    haveI := u.isPrime
    exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.1 (hU u)
  have he : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := GlobalTheory.LFun.isUnram_iff.1 hun w rfl
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.exists_isUniformiser (w.under (𝓞 (maximalRealSubfield E)))
  set ϖE : (w.adicCompletion E)ˣ := Units.map (finiteCompletionMap (maximalRealSubfield E) E w).toMonoidHom ϖ with hϖE
  have hvE : Valued.v (ϖE : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (finiteCompletionMap (maximalRealSubfield E) E w ϖ) = _
    rw [← GlobalTheory.CharTransport.locMap_eq, ← GlobalTheory.LFun.complMap_rfl, GlobalTheory.LFun.valued_complMap rfl ϖ.ne_zero, he, pow_one]
    exact hϖ
  have hid : ideleMap (maximalRealSubfield E) E (Neutral.B1.localIdele _ (w.under (𝓞 (maximalRealSubfield E))) ϖ) =
      Neutral.B1.localIdele E w ϖE := by
    refine Units.ext (Prod.ext ?_ (FiniteAdeleRing.ext _ fun u => ?_))
    · exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap (maximalRealSubfield E) E)
    · rw [GlobalTheory.ArtinTransfer.ideleMap_apply]
      by_cases hu : u = w
      · subst hu
        rw [GlobalTheory.ArtinTransfer.loc_same, GlobalTheory.ArtinTransfer.loc_same]
        rfl
      · have hu' : u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) :=
          fun e => hu (GlobalTheory.LFun.eq_of_not_isSplit hns e rfl)
        rw [GlobalTheory.ArtinTransfer.loc_ne hu', GlobalTheory.ArtinTransfer.loc_ne hu, map_one]
  have hq : (GlobalTheory.GalOfCusp.quadChar E).1 (Neutral.B1.localIdele _ (w.under (𝓞 (maximalRealSubfield E))) ϖ) = -1 := by
    change Units.map _ (GlobalTheory.IdeleNormChar.normSign E (Neutral.B1.localIdele _ _ ϖ)) = -1
    rw [GlobalTheory.LFun.normSign_localIdele]
    have hne := fun h => GlobalTheory.LFun.not_mem_normGroup_of_inert h2 hns hun hϖ (GlobalTheory.QuadSymbol.eta_eq_one_iff.1 h)
    rcases Int.units_eq_one_or (GlobalTheory.QuadSymbol.eta (maximalRealSubfield E) E _ ϖ) with h | h
    · exact absurd h hne
    · rw [h]; ext; simp
  have hval : μ.loc w ϖE = -1 := by
    change μ.1 (Neutral.B1.localIdele E w ϖE) = -1
    rw [← hid, hres, hq]
  have hunr : GlobalTheory.SplitWeil.IsUnram (μ.loc w) := fun x hx => hunit w x hw (valued_eq_one w hx)
  rw [GlobalTheory.SmGL.eq_unrChar hunr (valuation_eq_uniformizer w hvE), hval]

end GlobalTheory.MuInert
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharCMEtaLocalEqNegOnePowValInertStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharCM_eta_local_eq_neg_one_pow_val_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ μ : HChar E,
    (∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x) →
    (∀ (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ), ¬ IsSplitAt w → Valued.v (u : w.adicCompletion E) = 1 →
      μ.1 (Neutral.B1.localIdele E w u) = 1) →
    ∀ w : Pl E, ¬ IsSplitAt w → μ.loc w = GlobalTheory.SmGL.unrChar (w.adicCompletion E) (-1) := by
  first | exact @GlobalTheory.MuInert.loc_eq_unrChar_neg_one | exact GlobalTheory.MuInert.loc_eq_unrChar_neg_one | (intros; apply GlobalTheory.MuInert.loc_eq_unrChar_neg_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementMul
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory.IdTorus
theorem isIdTorusElt_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} {l l' : Fin r → (AF F ⊗[F] E)ˣ} {a b : GAd σ J}
    (ha : IsIdTorusElt σ J X Y l a) (hb : IsIdTorusElt σ J X Y l' b) : IsIdTorusElt σ J X Y (l * l') (a * b) := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  refine ⟨?_, ?_, fun z hz => ?_⟩
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, hb1, ← Matrix.mul_assoc, ha1, Matrix.mul_assoc, diagonal_mul_diagonal]
    exact congrArg _ (congrArg _ (funext fun k => by simp))
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, hb2, ← Matrix.mul_assoc, ha2, Matrix.mul_assoc, diagonal_mul_diagonal]
    exact congrArg _ (congrArg _ (funext fun k => by simp [map_mul, mul_inv, Units.val_mul, mul_comm]))
  · rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hb3 z hz, ha3 z hz]
end GlobalTheory.IdTorus
end
