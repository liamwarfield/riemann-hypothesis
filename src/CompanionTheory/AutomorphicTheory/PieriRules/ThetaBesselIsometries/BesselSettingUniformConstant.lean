module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaInfEqIntegralOfIntegrableCoefficient
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselPeriodAdjointPair
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormPlus
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSettingUniformConstant

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselFormalDegreeIdentity
section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselFormalDegreeIdentity
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselPhi

theorem hsInner_smul_smul {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (a b : ℂ) (A A' : Wq →L[ℂ] Wp) :
    B.hsInner (a • A) (b • A') = a * star b * B.hsInner A A' := by
  have h : ∀ (c : ℂ) (Y : Wq →L[ℂ] Wp), B.hsVec (c • Y) = c • B.hsVec Y := fun c Y => rfl
  unfold B.hsInner
  rw [h, h, inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply]
  ring

theorem isUnit_det_of_mem {k r : ℕ} {g : Mx k r} (hg : g ∈ GG k r) : IsUnit g.det := by
  have h : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have h1 : (Formalism.QuantumDeterminants.Hpk k r * (gᴴ * Formalism.QuantumDeterminants.Hpk k r)) * g = 1 := by
    rw [Matrix.mul_assoc, h]; exact PI.HwUniqW.Hpk_mul_self
  exact Matrix.isUnit_det_of_left_inverse h1

theorem haar_left {k r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} (h : B.IsHaarOn U μ) :
    PI.BesselPeriodGGP.IsHaarOn U μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  exact ⟨inferInstance, h.ne_zero, h.conc, h.left⟩

theorem Ph_coeff : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (dd : ℝ), R.IsDG ε mu → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ (x y x' y' : R.H) (X X' : Wq →L[ℂ] Wp) (p : B.SS k r), D.inSS p → Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => B.hsInner (B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) (Matrix.of g)) (⟪x', R.σ (Matrix.of g) y'⟫_ℂ • X')) D.μG ∧ B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p = ⟪y', R.σ (JF.sR p) y⟫_ℂ * ⟪R.σ (JF.sL p) x, x'⟫_ℂ / (dd : ℂ) * B.hsInner ((D.π (Matrix.of p.1.1)).comp (X.comp (D.π' (Matrix.of p.2.1)⁻¹))) X' := by
  intro hH k r ε mu R Wp _ _ _ _ Wq _ _ _ _ D dd hR hdd x y x' y' X X' p hp
  obtain ⟨hmul, hone, hinner, -, -, -, -, ⟨w, hw, -⟩, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hR
  obtain ⟨c, -, hc⟩ := GlobalTheory.BesselDegree.schur_fdeg hH k r ε D.μG (haar_left D.haarG)
  obtain ⟨hdeg, hS⟩ := hc mu R hR
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hd : c * Formalism.QuantumDeterminants.fdegHC mu = dd := (hdeg w hw0).symm.trans (hdd w hw0)
  obtain ⟨hI, hE⟩ := hS (R.σ (JF.sR p) y) (R.σ (JF.sL p) x) y' x'
  rw [hd] at hE
  have ha : (Matrix.of p.1.1 : Mx k r) ∈ GG k r := hp.1.1
  have hb : (Matrix.of p.1.2 : Mx k r) ∈ GG k r := hp.2.1.1
  have hc' : (Matrix.of p.2.1 : Mx k r) ∈ GG k r := hp.2.2.1.1
  have hd' : (Matrix.of p.2.2 : Mx k r) ∈ GG k r := hp.2.2.2.1
  have hL : JF.sL p ∈ GG k r := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hb ha
  have hRR : JF.sR p ∈ GG k r := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hd' hc'
  have hLi : (JF.sL p)⁻¹ ∈ GG k r := PI.HwUniqW.inv_mem_UH hL
  set Y := (D.π (Matrix.of p.1.1)).comp (X.comp (D.π' (Matrix.of p.2.1)⁻¹)) with hY
  have key : ∀ g ∈ GG k r, B.hsInner (B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) g) (⟪x', R.σ g y'⟫_ℂ • X') =
      ⟪R.σ (JF.sL p) x, R.σ g (R.σ (JF.sR p) y)⟫_ℂ * star ⟪x', R.σ g y'⟫_ℂ * B.hsInner Y X' := by
    intro g hg
    have e1 : B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) g = ⟪x, R.σ (B.sgs p g) y⟫_ℂ • Y := by
      unfold B.rho
      rw [hY, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    have e2 : B.sgs p g = (JF.sL p)⁻¹ * (g * JF.sR p) := by
      unfold B.sgs JF.sL JF.sR
      rw [Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
    have hgR : g * JF.sR p ∈ GG k r := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hg hRR
    have e3 : ⟪x, R.σ (B.sgs p g) y⟫_ℂ = ⟪R.σ (JF.sL p) x, R.σ g (R.σ (JF.sR p) y)⟫_ℂ := by
      rw [← hinner _ hL, e2, ← hmul _ hL _ (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hLi hgR), ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (isUnit_det_of_mem hL), Matrix.one_mul, hmul _ hg _ hRR]
    rw [e1, e3, hsInner_smul_smul]
  have hae : ∀ᵐ g ∂D.μG, (Matrix.of g : Mx k r) ∈ GG k r := by
    rw [ae_iff]; exact D.haarG.conc
  have hae2 : (fun g : Formalism.QuantumDeterminants.Mt k r => B.hsInner (B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) (Matrix.of g))
      (⟪x', R.σ (Matrix.of g) y'⟫_ℂ • X')) =ᵐ[D.μG] fun g => ⟪R.σ (JF.sL p) x, R.σ (Matrix.of g) (R.σ (JF.sR p) y)⟫_ℂ *
        star ⟪x', R.σ (Matrix.of g) y'⟫_ℂ * B.hsInner Y X' := hae.mono fun g hg => key _ hg
  refine ⟨(hI.mul_const _).congr hae2.symm, ?_⟩
  unfold B.Ph
  rw [integral_congr_ae hae2, integral_mul_const, hE]

end GlobalTheory.BesselPhi
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselFormalDegreeIdentityStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.bessel_formal_degree_identity : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (dd : ℝ), R.IsDG ε mu → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ (x y x' y' : R.H) (X X' : Wq →L[ℂ] Wp) (p : B.SS k r), D.inSS p → Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => B.hsInner (B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) (Matrix.of g)) (⟪x', R.σ (Matrix.of g) y'⟫_ℂ • X')) D.μG ∧ B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p = ⟪y', R.σ (JF.sR p) y⟫_ℂ * ⟪R.σ (JF.sL p) x, x'⟫_ℂ / (dd : ℂ) * B.hsInner ((D.π (Matrix.of p.1.1)).comp (X.comp (D.π' (Matrix.of p.2.1)⁻¹))) X' := by
  first | exact @GlobalTheory.BesselPhi.Ph_coeff | exact GlobalTheory.BesselPhi.Ph_coeff | (intros; apply GlobalTheory.BesselPhi.Ph_coeff <;> assumption)
end Gp91
end
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselFormalDegreePairing
section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselFormalDegreePairing
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

private theorem hsInner_add_left_theta_bessel_isometries {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A A' C : Wq →L[ℂ] Wp) :
    B.hsInner (A + A') C = B.hsInner A C + B.hsInner A' C := by
  unfold Formalism.FourierDecayAlt.B.hsInner
  rw [← inner_add_right]
  congr 1

private theorem hsInner_smul_lemma_2 {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (c : ℂ) (A C : Wq →L[ℂ] Wp) :
    B.hsInner (c • A) C = c * B.hsInner A C := by
  unfold Formalism.FourierDecayAlt.B.hsInner
  rw [← inner_smul_right]
  congr 1

theorem besPhInt_bilin {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (X X' : Wq →L[ℂ] Wp) :
    ∃ T : (Wp →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wq) →L[ℂ] ℂ, ∀ P Q, T P Q = B.hsInner (P.comp (X.comp Q)) X' := by
  let f : (Wp →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wq) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun P Q => B.hsInner (P.comp (X.comp Q)) X')
      (fun P₁ P₂ Q => by rw [ContinuousLinearMap.add_comp, hsInner_add_left_theta_bessel_isometries])
      (fun c P Q => by rw [ContinuousLinearMap.smul_comp, hsInner_smul_lemma_2, smul_eq_mul])
      (fun P Q₁ Q₂ => by
        rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_add, hsInner_add_left_theta_bessel_isometries])
      (fun c P Q => by
        rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul, hsInner_smul_lemma_2,
          smul_eq_mul])
  let g : (Wp →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wq) →L[ℂ] ℂ :=
    (LinearMap.toContinuousLinearMap : ((Wq →L[ℂ] Wq) →ₗ[ℂ] ℂ) ≃ₗ[ℂ] _).toLinearMap ∘ₗ f
  exact ⟨LinearMap.toContinuousLinearMap g, fun P Q => rfl⟩

theorem besPhInt_rank {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (X X' : Wq →L[ℂ] Wp)
    (a a' : Wp) (b b' : Wq) :
    B.hsInner (((innerSL ℂ a).smulRight a').comp (X.comp ((innerSL ℂ b').smulRight b))) X' =
      ⟪a, X b⟫_ℂ * star ⟪a', X' b'⟫_ℂ := by
  have key : ∀ i, ⟪X' (stdOrthonormalBasis ℂ Wq i),
      (((innerSL ℂ a).smulRight a').comp (X.comp ((innerSL ℂ b').smulRight b)))
        (stdOrthonormalBasis ℂ Wq i)⟫_ℂ =
      ⟪a, X b⟫_ℂ * (⟪b', stdOrthonormalBasis ℂ Wq i⟫_ℂ *
        ⟪stdOrthonormalBasis ℂ Wq i, (ContinuousLinearMap.adjoint X') a'⟫_ℂ) := by
    intro i
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      map_smul, inner_smul_right, ContinuousLinearMap.adjoint_inner_right, smul_eq_mul]
    ring
  unfold Formalism.FourierDecayAlt.B.hsInner Formalism.FourierDecayAlt.B.hsVec
  simp only [PiLp.inner_apply, PiLp.toLp_apply, key]
  rw [← Finset.mul_sum, OrthonormalBasis.sum_inner_mul_inner, ContinuousLinearMap.adjoint_inner_right]
  congr 1
  exact (inner_conj_symm (X' b') a').symm

theorem besPhInt_xi {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (p : B.SS k r) :
    B.xiTau D (1, 1) p = Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of p.1.2) *
      star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd (Matrix.of p.2.2)) := by
  unfold Formalism.FourierDecayAlt.B.xiTau Formalism.FourierDecayAlt.B.lam Formalism.QuantumDeterminants.psi
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

private theorem continuous_ell_matrix_of {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) :
    Continuous (fun q : Formalism.QuantumDeterminants.Mt k r => Formalism.QuantumDeterminants.ell k r z (Matrix.of q)) := by
  unfold Formalism.QuantumDeterminants.ell
  refine continuous_finsetSum _ (fun a _ => ?_)
  by_cases h : (a : ℕ) + 1 < r
  · simp only [dif_pos h, Matrix.of_apply]
    fun_prop
  · simp only [dif_neg h, Matrix.mulVec, dotProduct, Matrix.of_apply]
    exact continuous_finsetSum _ (fun j _ => by fun_prop)

theorem besPhInt_xi_cont {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) :
    Continuous (B.xiTau D (1, 1)) := by
  have h1 : Continuous (fun p : B.SS k r => Formalism.QuantumDeterminants.ell k r D.z (Matrix.of p.1.2)) :=
    (continuous_ell_matrix_of D.z).comp (continuous_snd.comp continuous_fst)
  have h2 : Continuous (fun p : B.SS k r => Formalism.QuantumDeterminants.ell k r D.z' (Matrix.of p.2.2)) :=
    (continuous_ell_matrix_of D.z').comp (continuous_snd.comp continuous_snd)
  unfold Formalism.FourierDecayAlt.B.xiTau Formalism.FourierDecayAlt.B.lam
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    ((continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul h1))).sub
      (continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul h2))))))

private theorem isUnit_det_of_mem_UH_Hpk_of_inv_mem {k r : ℕ} (hk : 1 ≤ k)
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hg' : g⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    IsUnit g.det := by
  by_contra hu
  rw [Matrix.nonsing_inv_apply_not_isUnit g hu] at hg'
  have h0 : Formalism.QuantumDeterminants.Hpk k r = 0 := by
    have h1 := hg'
    simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq, Matrix.conjTranspose_zero, Matrix.zero_mul] at h1
    exact h1.symm
  have hr : r < 2 * r + k + 1 := by omega
  have hk0 : k ≠ 0 := by omega
  have h2 := congrFun (congrFun h0 ⟨r, hr⟩) ⟨r, hr⟩
  simp [Formalism.QuantumDeterminants.Hpk, hk0] at h2

private theorem integrable_and_integral_prod_bilin_eq_apply_integrals {α β E F G : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
    (T : E →L[ℂ] F →L[ℂ] G) {u : α → E} {v : β → F} (hu : Integrable u μ) (hv : Integrable v ν) :
    Integrable (fun p : α × β => T (u p.1) (v p.2)) (μ.prod ν) ∧
      ∫ p, T (u p.1) (v p.2) ∂(μ.prod ν) = T (∫ a, u a ∂μ) (∫ b, v b ∂ν) := by
  have hint : Integrable (fun p : α × β => T (u p.1) (v p.2)) (μ.prod ν) := by
    refine Integrable.mono' ((MeasureTheory.Integrable.mul_prod hu.norm hv.norm).const_mul ‖T‖) ?_ ?_
    · exact T.continuous₂.comp_aestronglyMeasurable₂ hu.aestronglyMeasurable.comp_fst
        hv.aestronglyMeasurable.comp_snd
    · exact Filter.Eventually.of_forall (fun p => by
        have h1 := T.le_opNorm₂ (u p.1) (v p.2)
        simpa [mul_assoc] using h1)
  refine ⟨hint, ?_⟩
  rw [integral_prod _ hint]
  have h1 : ∀ a, ∫ b, T (u a) (v b) ∂ν = T (u a) (∫ b, v b ∂ν) :=
    fun a => (T (u a)).integral_comp_comm hv
  simp_rw [h1]
  have h2 := (T.flip (∫ b, v b ∂ν)).integral_comp_comm hu
  simpa using h2

theorem integral_xi_mul_Ph : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq) (dd : ℝ), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ x' ∈ R.TK, ∀ y' ∈ R.TK, ∀ X X' : Wq →L[ℂ] Wp, Integrable (B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X')) D.μSS ∧ ∫ p, B.xiTau D (1, 1) p * B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p ∂D.μSS = ⟪l x, X (l' y)⟫_ℂ * star ⟪l x', X' (l' y')⟫_ℂ / (dd : ℂ) := by
  intro hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ D l l' dd hDG _ _ hl hl' hdd x hx y hy x' hx' y' hy' X X'
  classical
  have hrep := rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hDG
  have hmul := hrep.1
  have hone := hrep.2.1
  have hunit := hrep.2.2.1
  have hTKsm := hrep.2.2.2.2.1
  have hWpi : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r D.z) D.μW :=
    ((_root_.GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μW).2.2 D.z D.z_mem D.T_pos D.k_pos).2 D.haarW
  have hNpi : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) D.μN :=
    (_root_.GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μN).2.1.2 D.haarN
  have hW'pi : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r D.z') D.μW' :=
    ((_root_.GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μW').2.2 D.z' D.z'_mem D.T'_pos D.k_pos).2 D.haarW'
  haveI : SigmaFinite D.μW := hWpi.1
  haveI : SigmaFinite D.μN := hNpi.1
  haveI : SigmaFinite D.μW' := hW'pi.1
  have h55 := _root_.GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z D.μW D.μN D.k_pos D.z_mem D.T_pos hWpi hNpi
  have h55' := _root_.GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z' D.μW' D.μN D.k_pos D.z'_mem D.T'_pos hW'pi hNpi
  have h54 := _root_.GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z Formalism.QuantumDeterminants.cStd D.z_mem
  have h54' := _root_.GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z' Formalism.QuantumDeterminants.cStd D.z'_mem
  obtain ⟨Φ, hΦ, hΦd⟩ : ∃ Φ : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      MeasurePreserving Φ (D.μW.prod D.μN) (D.μW.prod D.μN) ∧
        ∀ q, Φ q = ((fun i j => (Matrix.of q.1)⁻¹ i j), (fun i j => (Matrix.of q.2)⁻¹ i j)) :=
    ⟨_, h55.2.2.2.2.1, fun q => rfl⟩
  obtain ⟨Ψ, hΨ, hΨd⟩ : ∃ Ψ : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      MeasurePreserving Ψ (D.μW'.prod D.μN) (D.μW'.prod D.μN) ∧
        ∀ q, Ψ q = ((fun i j => Matrix.of q.1 i j),
          (fun i j => ((Matrix.of q.1)⁻¹ * Matrix.of q.2 * Matrix.of q.1) i j)) :=
    ⟨_, h55'.2.2.2.1, fun q => rfl⟩
  obtain ⟨U, hUd⟩ : ∃ U : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → Wp →L[ℂ] Wp, ∀ q, U q =
      (Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of q.2) *
        ⟪(R.σ (Matrix.of q.2 * Matrix.of q.1)) x, x'⟫_ℂ) • D.π (Matrix.of q.1) := ⟨_, fun q => rfl⟩
  obtain ⟨V, hVd⟩ : ∃ V : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → Wq →L[ℂ] Wq, ∀ q, V q =
      (star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd (Matrix.of q.2)) *
        ⟪y', (R.σ (Matrix.of q.2 * Matrix.of q.1)) y⟫_ℂ) • D.π' (Matrix.of q.1)⁻¹ := ⟨_, fun q => rfl⟩
  have hUeq : ∀ q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r, Matrix.of q.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z →
      Matrix.of q.2 ∈ Formalism.QuantumDeterminants.Nset k r →
      Formalism.FourierDecayAlt.ThreeDimData.beInt D.z Formalism.QuantumDeterminants.cStd D.π R.σ x' x (Φ q) = U q := by
    intro q hH hN
    obtain ⟨hNinv, hψinv⟩ := h54.2.2.1 _ hN
    have hHinv := (h54.2.2.2.2.1 _ hH _ hH).2.1
    have hHG := (h54.2.2.2.2.1 _ hH _ hH).2.2
    have hHinvG := (h54.2.2.2.2.1 _ hHinv _ hHinv).2.2
    have hNG := h54.2.2.2.2.2 _ hN
    have hNinvG := h54.2.2.2.2.2 _ hNinv
    have huH := isUnit_det_of_mem_UH_Hpk_of_inv_mem D.k_pos hH.1 hHinv.1
    have huN := isUnit_det_of_mem_UH_Hpk_of_inv_mem D.k_pos hN.1 hNinv.1
    have hin : ⟪x, (R.σ ((Matrix.of q.1)⁻¹ * (Matrix.of q.2)⁻¹)) x'⟫_ℂ =
        ⟪(R.σ (Matrix.of q.2 * Matrix.of q.1)) x, x'⟫_ℂ := by
      rw [hmul _ hNG _ hHG, hmul _ hHinvG _ hNinvG]
      calc ⟪x, (R.σ (Matrix.of q.1)⁻¹) ((R.σ (Matrix.of q.2)⁻¹) x')⟫_ℂ
          = ⟪(R.σ (Matrix.of q.1)) x,
              (R.σ (Matrix.of q.1)) ((R.σ (Matrix.of q.1)⁻¹) ((R.σ (Matrix.of q.2)⁻¹) x'))⟫_ℂ :=
            (hunit _ hHG _ _).symm
        _ = ⟪(R.σ (Matrix.of q.1)) x, (R.σ (Matrix.of q.2)⁻¹) x'⟫_ℂ := by
            rw [← hmul _ hHG _ hHinvG, Matrix.mul_nonsing_inv _ huH, hone]
        _ = ⟪(R.σ (Matrix.of q.2)) ((R.σ (Matrix.of q.1)) x),
              (R.σ (Matrix.of q.2)) ((R.σ (Matrix.of q.2)⁻¹) x')⟫_ℂ :=
            (hunit _ hNG _ _).symm
        _ = ⟪(R.σ (Matrix.of q.2)) ((R.σ (Matrix.of q.1)) x), x'⟫_ℂ := by
            rw [← hmul _ hNG _ hNinvG, Matrix.mul_nonsing_inv _ huN, hone]
    rw [hΦd, hUd]
    show (⟪x, (R.σ ((Matrix.of q.1)⁻¹ * (Matrix.of q.2)⁻¹)) x'⟫_ℂ *
        star (Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of q.2)⁻¹)) • D.π ((Matrix.of q.1)⁻¹)⁻¹ = _
    rw [hψinv, star_star, Matrix.nonsing_inv_nonsing_inv _ huH, hin]
    congr 1
    ring
  have hVeq : ∀ q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r, Matrix.of q.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z' →
      Matrix.of q.2 ∈ Formalism.QuantumDeterminants.Nset k r →
      Formalism.FourierDecayAlt.ThreeDimData.beInt D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ y y' (Ψ q) = V q := by
    intro q hH hN
    have hHinv := (h54'.2.2.2.2.1 _ hH _ hH).2.1
    have huH := isUnit_det_of_mem_UH_Hpk_of_inv_mem D.k_pos hH.1 hHinv.1
    have hψc := (h54'.2.2.2.1 _ hH _ hN).2.2.2
    have hm : Matrix.of q.1 * ((Matrix.of q.1)⁻¹ * Matrix.of q.2 * Matrix.of q.1) =
        Matrix.of q.2 * Matrix.of q.1 := by
      rw [← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ huH, one_mul]
    rw [hΨd, hVd]
    show (⟪y', (R.σ (Matrix.of q.1 * ((Matrix.of q.1)⁻¹ * Matrix.of q.2 * Matrix.of q.1))) y⟫_ℂ *
        star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd ((Matrix.of q.1)⁻¹ * Matrix.of q.2 * Matrix.of q.1))) •
        D.π' (Matrix.of q.1)⁻¹ = _
    rw [hm, hψc]
    congr 1
    ring
  have hbe := hl.2 x' (hTKsm x' hx') x hx
  have hbe' := hl'.2 y (hTKsm y hy) y' hy'
  have hUi : Integrable U (D.μW.prod D.μN) ∧
      ∫ q, U q ∂(D.μW.prod D.μN) = (innerSL ℂ (l x)).smulRight (l x') := by
    have hcomp : (fun q => Formalism.FourierDecayAlt.ThreeDimData.beInt D.z Formalism.QuantumDeterminants.cStd D.π R.σ x' x (Φ q))
        =ᵐ[D.μW.prod D.μN] U :=
      h55.2.2.2.2.2.mono (fun q hq => hUeq q hq.1 hq.2)
    have hint1 : Integrable (fun q => Formalism.FourierDecayAlt.ThreeDimData.beInt D.z Formalism.QuantumDeterminants.cStd D.π R.σ x' x (Φ q))
        (D.μW.prod D.μN) :=
      (hΦ.integrable_comp hbe.1.aestronglyMeasurable).mpr hbe.1
    refine ⟨hint1.congr hcomp, ?_⟩
    rw [← integral_congr_ae hcomp, ← integral_map hΦ.measurable.aemeasurable
      (by rw [hΦ.map_eq]; exact hbe.1.aestronglyMeasurable), hΦ.map_eq]
    exact hbe.2
  have hVi : Integrable V (D.μW'.prod D.μN) ∧
      ∫ q, V q ∂(D.μW'.prod D.μN) = (innerSL ℂ (l' y')).smulRight (l' y) := by
    have hcomp : (fun q => Formalism.FourierDecayAlt.ThreeDimData.beInt D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ y y' (Ψ q))
        =ᵐ[D.μW'.prod D.μN] V :=
      h55'.2.2.2.2.2.mono (fun q hq => hVeq q hq.1 hq.2)
    have hint1 : Integrable (fun q => Formalism.FourierDecayAlt.ThreeDimData.beInt D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ y y' (Ψ q))
        (D.μW'.prod D.μN) :=
      (hΨ.integrable_comp hbe'.1.aestronglyMeasurable).mpr hbe'.1
    refine ⟨hint1.congr hcomp, ?_⟩
    rw [← integral_congr_ae hcomp, ← integral_map hΨ.measurable.aemeasurable
      (by rw [hΨ.map_eq]; exact hbe'.1.aestronglyMeasurable), hΨ.map_eq]
    exact hbe'.2
  have haeSS : ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), D.inSS p := by
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := D.μW.prod D.μN)
      (ν := D.μW'.prod D.μN)).ae h55.2.2.2.2.2
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := D.μW.prod D.μN)
      (ν := D.μW'.prod D.μN)).ae h55'.2.2.2.2.2
    filter_upwards [h1, h2] with p hp1 hp2
    exact ⟨hp1.1, hp1.2, hp2.1, hp2.2⟩
  obtain ⟨T, hT⟩ := besPhInt_bilin X X'
  have hFub := integrable_and_integral_prod_bilin_eq_apply_integrals T hUi.1 hVi.1
  have hpt : ∀ p : B.SS k r, D.inSS p →
      B.xiTau D (1, 1) p * B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p =
        (1 / (dd : ℂ)) * T (U p.1) (V p.2) := by
    intro p hp
    rw [(Gp91.GlobalTheory.T.bessel_formal_degree_identity hH k r ε mu R Wp Wq D dd hDG hdd x y x' y' X X' p hp).2, besPhInt_xi, hT,
      hUd, hVd, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul, hsInner_smul_lemma_2, hsInner_smul_lemma_2]
    simp only [Formalism.FourierDecayAlt.JF.sL, Formalism.FourierDecayAlt.JF.sR]
    ring
  have hae : (fun p => B.xiTau D (1, 1) p *
      B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p)
      =ᵐ[D.μSS] fun p => (1 / (dd : ℂ)) * T (U p.1) (V p.2) :=
    haeSS.mono (fun p hp => hpt p hp)
  have hF1 : Integrable (fun p => T (U p.1) (V p.2)) D.μSS := hFub.1
  have hF2 : ∫ p, T (U p.1) (V p.2) ∂D.μSS =
      T (∫ q, U q ∂(D.μW.prod D.μN)) (∫ q, V q ∂(D.μW'.prod D.μN)) := hFub.2
  have hint2 : Integrable (fun p => B.xiTau D (1, 1) p *
      B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p) D.μSS :=
    (hF1.const_mul (1 / (dd : ℂ))).congr hae.symm
  have hxi := besPhInt_xi_cont D
  have hnorm : ∀ p, ‖B.xiTau D (1, 1) p‖ = 1 := by
    intro p
    unfold Formalism.FourierDecayAlt.B.xiTau
    exact Complex.norm_exp_I_mul_ofReal _
  refine ⟨?_, ?_⟩
  · have hint3 : Integrable (fun p => star (B.xiTau D (1, 1) p) * (B.xiTau D (1, 1) p *
        B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p)) D.μSS :=
      hint2.congr' ((hxi.star.aestronglyMeasurable).mul hint2.aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun p => by simp [hnorm]))
    refine hint3.congr (Filter.Eventually.of_forall (fun p => ?_))
    beta_reduce
    rw [← mul_assoc, Complex.star_def, Complex.conj_mul', hnorm]
    simp
  · rw [integral_congr_ae hae, integral_const_mul, hF2, hUi.2, hVi.2, hT,
      besPhInt_rank X X' (l x) (l x') (l' y) (l' y')]
    ring

end GlobalTheory
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselFormalDegreePairingStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.bessel_formal_degree_pairing : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq) (dd : ℝ), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ x' ∈ R.TK, ∀ y' ∈ R.TK, ∀ X X' : Wq →L[ℂ] Wp, Integrable (B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X')) D.μSS ∧ ∫ p, B.xiTau D (1, 1) p * B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p ∂D.μSS = ⟪l x, X (l' y)⟫_ℂ * star ⟪l x', X' (l' y')⟫_ℂ / (dd : ℂ) := by
  first | exact @GlobalTheory.integral_xi_mul_Ph | exact GlobalTheory.integral_xi_mul_Ph | (intros; apply GlobalTheory.integral_xi_mul_Ph <;> assumption)
end Gp91
end
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingUniformConstant
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselNormSq

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsInner_sum_sum {m : ℕ} (A C : Fin m → (Wq →L[ℂ] Wp)) :
    B.hsInner (∑ i, A i) (∑ j, C j) = ∑ i, ∑ j, B.hsInner (A i) (C j) := by
  have h : ∀ A : Fin m → (Wq →L[ℂ] Wp), B.hsVec (∑ i, A i) = ∑ i, B.hsVec (A i) := by
    intro A
    ext t
    simp [B.hsVec, ContinuousLinearMap.sum_apply]
  unfold B.hsInner
  rw [h, h, inner_sum]
  exact Finset.sum_congr rfl fun i _ => sum_inner _ _ _

theorem Ph_sum [FiniteDimensional ℂ Wp] (D : B.RealPlaceData k r Wp Wq) {m : ℕ} (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (f : Fin m → B.Mat k r → (Wq →L[ℂ] Wp)) (hF : ∀ g ∈ B.GV k r, F g = ∑ i, f i g) (p : B.SS k r)
    (hp : D.inSS p)
    (hint : ∀ i j, Integrable (fun g : Formalism.QuantumDeterminants.Mt k r =>
      B.hsInner (B.rho D p (f i) (Matrix.of g)) (f j (Matrix.of g))) D.μG) :
    B.Ph D F F p = ∑ i, ∑ j, B.Ph D (f i) (f j) p := _root_.GlobalTheory.BesselNormSq.Ph_sum (m := m) D F f hF p hp hint

theorem normSq_coef : HypsG → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∃ c : ℝ, 0 < c ∧ ∀ (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (l : R.H → Wp) (l' : R.H → Wq) (dd : ℝ), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ F s, IsCoef R l l' F s → B.normSq D F = ENNReal.ofReal (c * ‖s‖ ^ 2 / dd) := by
  intro H k r Wp _ _ _ _ Wq _ _ _ _ D
  obtain ⟨c, hc, hnb⟩ := GlobalTheory.T.besselNormSq_eq_const_mul_archPairing k r Wp Wq D
  refine ⟨c, hc, ?_⟩
  intro ε mu h R l l' dd hDS hgap hok hl hl' hdd F s hF
  have hA := (GlobalTheory.T.decayThresholds_of_spectralGapCondition k r h hok).2.1
  have hcc := (GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap H k r ε mu h R Wp Wq l l' F s hDS hgap hok hF).2
  obtain ⟨m, x, y, X, hxy, hFg, hs⟩ := hF
  set f : Fin m → B.Mat k r → (Wq →L[ℂ] Wp) := fun i g => ⟪x i, R.σ g (y i)⟫_ℂ • X i with hf
  have hI := fun i j => GlobalTheory.T.bessel_formal_degree_pairing H k r ε mu h R Wp Wq D l l' dd hDS hgap hok hl hl' hdd
    (x i) (hxy i).1 (y i) (hxy i).2 (x j) (hxy j).1 (y j) (hxy j).2 (X i) (X j)
  have hPh : B.Ph D F F =ᵐ[D.μSS] fun p => ∑ i, ∑ j, B.Ph D (f i) (f j) p :=
    (Formalism.FourierDecayAlt.P.B6.ae_inSS D).mono fun p hp => Ph_sum D F f hFg p hp fun i j =>
      (GlobalTheory.T.bessel_formal_degree_identity H k r ε mu R Wp Wq D dd hDS hdd (x i) (y i) (x j) (y j) (X i) (X j) p hp).1
  have hint : Integrable (B.Ph D F F) D.μSS :=
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hI i j).1).congr hPh.symm
  have hxi : ∀ i j, Integrable (fun p => B.xiTau D (1, 1) p * B.Ph D (f i) (f j) p) D.μSS := by
    intro i j
    refine Integrable.bdd_mul (c := 1) (hI i j).1 ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      have c1 : Continuous fun p : B.SS k r => B.lam k r D.z (Matrix.of p.1.2) :=
        (Formalism.FourierDecayAlt.P.B6.lam_continuous k r D.z).comp (continuous_snd.comp continuous_fst)
      have c2 : Continuous fun p : B.SS k r => B.lam k r D.z' (Matrix.of p.2.2) :=
        (Formalism.FourierDecayAlt.P.B6.lam_continuous k r D.z').comp (continuous_snd.comp continuous_snd)
      unfold B.xiTau
      exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        ((continuous_const.mul c1).sub (continuous_const.mul c2))))
    · unfold B.xiTau
      rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hb : B.betaInf D F F = ((‖s‖ ^ 2 / dd : ℝ) : ℂ) := by
    rw [GlobalTheory.T.betaInf_eq_integral_of_integrable_coefficient k r Wp Wq D _ F hA (hcc 4) hint]
    have e0 : ∫ p, B.xiTau D (1, 1) p * B.Ph D F F p ∂D.μSS =
        ∫ p, ∑ i, ∑ j, B.xiTau D (1, 1) p * B.Ph D (f i) (f j) p ∂D.μSS := by
      refine integral_congr_ae (hPh.mono fun p hp => ?_)
      simp only [hp, Finset.mul_sum]
    rw [e0, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hxi i j]
    have e1 : ∀ i, ∫ p, ∑ j, B.xiTau D (1, 1) p * B.Ph D (f i) (f j) p ∂D.μSS =
        ∑ j, ⟪l (x i), X i (l' (y i))⟫_ℂ * star ⟪l (x j), X j (l' (y j))⟫_ℂ / (dd : ℂ) := by
      intro i
      rw [integral_finsetSum _ fun j _ => hxi i j]
      exact Finset.sum_congr rfl fun j _ => (hI i j).2
    simp only [e1]
    have e2 : ((‖s‖ ^ 2 / dd : ℝ) : ℂ) = s * star s / (dd : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [e2, hs, star_sum, Finset.sum_mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_div]
  rw [hnb _ F hA (hcc 5), hb, ← Complex.ofReal_mul, Complex.ofReal_re, mul_div_assoc]

end GlobalTheory.BesselNormSq
end
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingUniformConstantStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.bessel_setting_uniform_constant : HypsG → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∃ c : ℝ, 0 < c ∧ ∀ (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (l : R.H → Wp) (l' : R.H → Wq) (dd : ℝ), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ F s, IsCoef R l l' F s → B.normSq D F = ENNReal.ofReal (c * ‖s‖ ^ 2 / dd) := by
  first | exact @GlobalTheory.BesselNormSq.normSq_coef | exact GlobalTheory.BesselNormSq.normSq_coef | (intros; apply GlobalTheory.BesselNormSq.normSq_coef <;> assumption)
end Gp91
end
