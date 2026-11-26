module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaInfEqIntegralOfIntegrableCoefficient
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselPeriodAdjointPair
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormPlus

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFormalDegreeIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFormalDegreeIdentity
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

theorem Ph_coeff : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (dd : ℝ), R.IsDS ε mu → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ (x y x' y' : R.H) (X X' : Wq →L[ℂ] Wp) (p : B.SS k r), D.inSS p → Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => B.hsInner (B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) (Matrix.of g)) (⟪x', R.σ (Matrix.of g) y'⟫_ℂ • X')) D.μG ∧ B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p = ⟪y', R.σ (JF.sR p) y⟫_ℂ * ⟪R.σ (JF.sL p) x, x'⟫_ℂ / (dd : ℂ) * B.hsInner ((D.π (Matrix.of p.1.1)).comp (X.comp (D.π' (Matrix.of p.2.1)⁻¹))) X' := by
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
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFormalDegreeIdentityStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_formal_degree_identity : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (dd : ℝ), R.IsDS ε mu → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ (x y x' y' : R.H) (X X' : Wq →L[ℂ] Wp) (p : B.SS k r), D.inSS p → Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => B.hsInner (B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) (Matrix.of g)) (⟪x', R.σ (Matrix.of g) y'⟫_ℂ • X')) D.μG ∧ B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p = ⟪y', R.σ (JF.sR p) y⟫_ℂ * ⟪R.σ (JF.sL p) x, x'⟫_ℂ / (dd : ℂ) * B.hsInner ((D.π (Matrix.of p.1.1)).comp (X.comp (D.π' (Matrix.of p.2.1)⁻¹))) X' := by
  first | exact @GlobalTheory.BesselPhi.Ph_coeff | exact GlobalTheory.BesselPhi.Ph_coeff | (intros; apply GlobalTheory.BesselPhi.Ph_coeff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFormalDegreePairing
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFormalDegreePairing
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem besPhInt_bilin {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (X X' : Wq →L[ℂ] Wp) :
    ∃ T : (Wp →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wq) →L[ℂ] ℂ, ∀ P Q, T P Q = B.hsInner (P.comp (X.comp Q)) X' := by
  refine ⟨∑ i, ((ContinuousLinearMap.compL ℂ (Wq →L[ℂ] Wq) Wp ℂ (innerSL ℂ (X' (stdOrthonormalBasis ℂ Wq i)))).comp
    ((ContinuousLinearMap.compL ℂ (Wq →L[ℂ] Wq) Wp Wp).flip
      (X.comp (ContinuousLinearMap.apply ℂ Wq (stdOrthonormalBasis ℂ Wq i))))), fun P Q => ?_⟩
  simp [B.hsInner, B.hsVec, PiLp.inner_apply]

theorem besPhInt_rank {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (X X' : Wq →L[ℂ] Wp)
    (a a' : Wp) (b b' : Wq) :
    B.hsInner (((innerSL ℂ a).smulRight a').comp (X.comp ((innerSL ℂ b').smulRight b))) X' =
      ⟪a, X b⟫_ℂ * star ⟪a', X' b'⟫_ℂ := by
  have hb : X' b' = ∑ i, ⟪stdOrthonormalBasis ℂ Wq i, b'⟫_ℂ • X' (stdOrthonormalBasis ℂ Wq i) := by
    conv_lhs => rw [← (stdOrthonormalBasis ℂ Wq).sum_repr' b']
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  have h2 : star ⟪a', X' b'⟫_ℂ = ⟪X' b', a'⟫_ℂ := inner_conj_symm _ _
  rw [h2, hb, sum_inner, Finset.mul_sum]
  simp only [B.hsInner, B.hsVec, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, map_smul,
    inner_smul_right, inner_smul_left, inner_conj_symm]
  ring

theorem besPhInt_xi {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (p : B.SS k r) :
    B.xiTau D (1, 1) p = Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of p.1.2) *
      star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd (Matrix.of p.2.2)) := by
  unfold B.xiTau Formalism.QuantumDeterminants.psi B.lam
  rw [show ∀ x : ℂ, star x = (starRingEnd ℂ) x from fun _ => rfl, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem besPhInt_xi_cont {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) :
    Continuous (B.xiTau D (1, 1)) := by
  have h : ∀ z, Continuous (fun m : Formalism.QuantumDeterminants.Mt k r => Formalism.QuantumDeterminants.ell k r z (Matrix.of m)) := by
    intro z
    unfold Formalism.QuantumDeterminants.ell
    refine continuous_finsetSum _ fun a _ => ?_
    split_ifs
    · simp only [Matrix.of_apply]
      fun_prop
    · simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
      fun_prop
  have h1 := (h D.z).comp (continuous_snd.comp (continuous_fst (X := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (Y := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)))
  have h2 := (h D.z').comp (continuous_snd.comp (continuous_snd (X := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (Y := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)))
  unfold B.xiTau B.lam
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  exact (continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul h1))).sub
    (continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul h2)))

theorem integral_xi_mul_Ph : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq) (dd : ℝ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ x' ∈ R.TK, ∀ y' ∈ R.TK, ∀ X X' : Wq →L[ℂ] Wp, Integrable (B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X')) D.μSS ∧ ∫ p, B.xiTau D (1, 1) p * B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p ∂D.μSS = ⟪l x, X (l' y)⟫_ℂ * star ⟪l x', X' (l' y')⟫_ℂ / (dd : ℂ) := by
  intro hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ D l l' dd hDS _ _ hl hl' hdd x hx y hy x' hx' y' hy' X X'
  obtain ⟨hmul, hone, hinn, -, hTK, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hDS
  have hsf : ∀ {U : Set (B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)}, B.IsHaarOn U μ → SigmaFinite μ := by
    intro U μ h
    have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
    infer_instance
  haveI := hsf D.haarW
  haveI := hsf D.haarN
  haveI := hsf D.haarW'
  have hN := (GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μN).2.1.2 D.haarN
  have hW := ((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μW).2.2 D.z D.z_mem D.T_pos D.k_pos).2 D.haarW
  have hW' := ((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μW').2.2 D.z' D.z'_mem D.T'_pos D.k_pos).2 D.haarW'
  obtain ⟨-, -, -, -, mA, aeA⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z D.μW D.μN D.k_pos D.z_mem D.T_pos hW hN
  obtain ⟨-, -, -, mB, -, aeB⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z' D.μW' D.μN D.k_pos D.z'_mem D.T'_pos hW' hN
  obtain ⟨psn, -, psinv, -, -, -⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z Formalism.QuantumDeterminants.cStd D.z_mem
  obtain ⟨psn', -, -, pscj, -, -⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z' Formalism.QuantumDeterminants.cStd D.z'_mem
  obtain ⟨iA, eA⟩ := hl.2 x' (hTK x' hx') x hx
  obtain ⟨iB, eB⟩ := hl'.2 y (hTK y hy) y' hy'
  have iA' := mA.integrable_comp_of_integrable iA
  have iB' := mB.integrable_comp_of_integrable iB
  have eA' := integral_map mA.measurable.aemeasurable (mA.map_eq.symm ▸ iA.aestronglyMeasurable)
  have eB' := integral_map mB.measurable.aemeasurable (mB.map_eq.symm ▸ iB.aestronglyMeasurable)
  rw [mA.map_eq] at eA'
  rw [mB.map_eq] at eB'
  unfold be at eA eB
  rw [eA] at eA'
  rw [eB] at eB'
  obtain ⟨T, hT⟩ := besPhInt_bilin X X'
  have hI := integral_prod_bilin T iA' iB'
  have hInt := iA'.op_fst_snd (op := fun P Q => T P Q) (by fun_prop) ⟨‖T‖, T.le_opNorm₂⟩ iB'
  simp only [Function.comp_apply] at hI hInt
  rw [← eA', ← eB', hT, besPhInt_rank] at hI
  have hae : ∀ᵐ p ∂D.μSS, D.inSS p := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := D.μW.prod D.μN) (ν := D.μW'.prod D.μN)).ae aeA,
      (Measure.quasiMeasurePreserving_snd (μ := D.μW.prod D.μN) (ν := D.μW'.prod D.μN)).ae aeB] with p h1 h2
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩
  have key : ∀ p : B.SS k r, D.inSS p →
      B.xiTau D (1, 1) p * B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p =
      T (beInt D.z Formalism.QuantumDeterminants.cStd D.π R.σ x' x
          (((fun i j => ((Matrix.of p.1.1)⁻¹ : Mx k r) i j), (fun i j => ((Matrix.of p.1.2)⁻¹ : Mx k r) i j))))
        (beInt D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ y y'
          (((fun i j => (Matrix.of p.2.1 : Mx k r) i j),
            (fun i j => ((Matrix.of p.2.1)⁻¹ * Matrix.of p.2.2 * Matrix.of p.2.1 : Mx k r) i j)))) / (dd : ℂ) := by
    intro p hp
    rw [(GlobalTheory.T.bessel_formal_degree_identity hH k r ε mu R Wp Wq D dd hDS hdd x y x' y' X X' p hp).2, besPhInt_xi, ← hT]
    obtain ⟨h1, h2, h3, h4⟩ := hp
    have hof : ∀ M : Mx k r, Matrix.of (fun i j => M i j) = M := fun M => rfl
    unfold beInt JF.sL JF.sR
    simp only [hof]
    generalize Matrix.of p.1.1 = a at *
    generalize Matrix.of p.1.2 = n at *
    generalize Matrix.of p.2.1 = a' at *
    generalize Matrix.of p.2.2 = n' at *
    obtain ⟨ai, aa, aa'⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv h1.1
    obtain ⟨ni, nn, nn'⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv h2.1
    obtain ⟨bi, bb, bb'⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv h3.1
    have e1 : a⁻¹⁻¹ = a := Matrix.inv_eq_right_inv aa'
    have e2 : a' * (a'⁻¹ * n' * a') = n' * a' := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, bb, Matrix.one_mul]
    have e3 : ⟪x, R.σ (a⁻¹ * n⁻¹) x'⟫_ℂ = ⟪R.σ (n * a) x, x'⟫_ℂ := by
      have hna := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul h2.1 h1.1
      have hna' := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul ai ni
      rw [← hinn _ hna, ← hmul _ hna _ hna']
      have : n * a * (a⁻¹ * n⁻¹) = 1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc a, aa, Matrix.one_mul, nn]
      rw [this, hone]
    rw [e1, e2, e3, (psinv n h2).2, (pscj a' h3 n' h4).2.2.2, star_star]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hae' := hae.mono key
  have hInt' : Integrable (fun p => B.xiTau D (1, 1) p *
      B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p) D.μSS :=
    (hInt.div_const (dd : ℂ)).congr (hae'.mono fun p hp => hp.symm)
  have hn : ∀ p, ‖B.xiTau D (1, 1) p‖ = 1 := by
    intro p
    rw [besPhInt_xi, norm_mul, norm_star, psn, psn', one_mul]
  refine ⟨?_, ?_⟩
  · have := hInt'.bdd_mul (c := 1) (f := fun p => star (B.xiTau D (1, 1) p))
      (besPhInt_xi_cont D).star.aestronglyMeasurable (Filter.Eventually.of_forall fun p => by rw [norm_star, hn])
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    have h1 : star (B.xiTau D (1, 1) p) * B.xiTau D (1, 1) p = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hn]; simp
    simp only
    rw [← mul_assoc, h1, one_mul]
  · rw [integral_congr_ae hae', integral_div]
    exact congrArg (· / (dd : ℂ)) hI

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFormalDegreePairingStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_formal_degree_pairing : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq) (dd : ℝ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ x' ∈ R.TK, ∀ y' ∈ R.TK, ∀ X X' : Wq →L[ℂ] Wp, Integrable (B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X')) D.μSS ∧ ∫ p, B.xiTau D (1, 1) p * B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p ∂D.μSS = ⟪l x, X (l' y)⟫_ℂ * star ⟪l x', X' (l' y')⟫_ℂ / (dd : ℂ) := by
  first | exact @GlobalTheory.integral_xi_mul_Ph | exact GlobalTheory.integral_xi_mul_Ph | (intros; apply GlobalTheory.integral_xi_mul_Ph <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSettingUniformConstant
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
    B.Ph D F F p = ∑ i, ∑ j, B.Ph D (f i) (f j) p := by
  have hae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ B.GV k r := D.haarG.conc
  unfold B.Ph
  have e1 : ∀ i, ∑ j, ∫ g, B.hsInner (B.rho D p (f i) (Matrix.of g)) (f j (Matrix.of g)) ∂D.μG =
      ∫ g, ∑ j, B.hsInner (B.rho D p (f i) (Matrix.of g)) (f j (Matrix.of g)) ∂D.μG :=
    fun i => (integral_finsetSum _ fun j _ => hint i j).symm
  simp only [e1]
  rw [← integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  refine integral_congr_ae (hae.mono fun g hg => ?_)
  have h1 : B.rho D p F (Matrix.of g) = ∑ i, B.rho D p (f i) (Matrix.of g) := by
    unfold B.rho
    rw [hF _ (Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group D hp hg)]
    ext v
    simp [ContinuousLinearMap.sum_apply]
  simp only
  rw [h1, hF _ hg, hsInner_sum_sum]

theorem normSq_coef : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∃ c : ℝ, 0 < c ∧ ∀ (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (l : R.H → Wp) (l' : R.H → Wq) (dd : ℝ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ F s, IsCoef R l l' F s → B.normSq D F = ENNReal.ofReal (c * ‖s‖ ^ 2 / dd) := by
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
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSettingUniformConstantStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_setting_uniform_constant : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∃ c : ℝ, 0 < c ∧ ∀ (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (l : R.H → Wp) (l' : R.H → Wq) (dd : ℝ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ F s, IsCoef R l l' F s → B.normSq D F = ENNReal.ofReal (c * ‖s‖ ^ 2 / dd) := by
  first | exact @GlobalTheory.BesselNormSq.normSq_coef | exact GlobalTheory.BesselNormSq.normSq_coef | (intros; apply GlobalTheory.BesselNormSq.normSq_coef <;> assumption)
end
