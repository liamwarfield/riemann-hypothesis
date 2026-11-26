module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousOnMajorantFlagLengths
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
public import Formalism.LocalRingCardinality.DataTies
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarBallGrowthUnitaryJ
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasFDerivAtOfContinuousPartials

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiPositiveDefiniteCholeskyFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiPositiveDefiniteCholeskyFormula
open Matrix Finset Formalism.MainNotions.S
open scoped ComplexOrder

namespace GlobalTheory.Dec

private lemma blockTriangular_toDual_of_isLo {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : IsLo b) :
    b.BlockTriangular OrderDual.toDual :=
  fun i j hij => hb i j (OrderDual.toDual_lt_toDual.mp hij)

private lemma isLo_of_blockTriangular_toDual {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.BlockTriangular OrderDual.toDual) : IsLo b :=
  fun _ _ hij => hb (OrderDual.toDual_lt_toDual.mpr hij)

theorem exists_isLo_mul_conjTranspose {n : ℕ} {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    ∃ b : Matrix (Fin n) (Fin n) ℂ, IsLo b ∧ x = b * bᴴ := by
  classical

  have hLi : (LDL.lowerInv hx).BlockTriangular OrderDual.toDual :=
    LDL.isLowerTriangular_lowerInv hx
  have hL : (LDL.lower hx).BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular hLi

  have hD : (LDL.diag hx).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    refine hx.mul_mul_conjTranspose_same ?_
    intro v w hvw
    have h := congrArg (fun u => u ᵥ* (LDL.lowerInv hx)⁻¹) hvw
    simpa [Matrix.vecMul_vecMul, Matrix.mul_inv_of_invertible] using h
  have hd : ∀ i, 0 < LDL.diagEntries hx i := fun i => by
    simpa [LDL.diag] using hD.diag_pos (i := i)
  let s : Fin n → ℂ := fun i => ((Real.sqrt (LDL.diagEntries hx i).re : ℝ) : ℂ)
  have hs : ∀ i, s i * star (s i) = LDL.diagEntries hx i := fun i => by
    obtain ⟨hre, him⟩ := Complex.pos_iff.mp (hd i)
    have hsq := Real.mul_self_sqrt hre.le
    apply Complex.ext
    · simp [s, Complex.mul_re, hsq]
    · simp [s, Complex.mul_im, ← him]
  refine ⟨LDL.lower hx * Matrix.diagonal s,
    isLo_of_blockTriangular_toDual (hL.mul (Matrix.blockTriangular_diagonal s)), ?_⟩
  have hDs : LDL.diag hx = Matrix.diagonal s * (Matrix.diagonal s)ᴴ := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    unfold LDL.diag
    congr 1
    funext i
    exact (hs i).symm
  conv_lhs => rw [← LDL.lower_conj_diag hx, hDs]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem one_mem_Omega_leadMinor (n : ℕ) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Omega n := by
  intro i
  simp [leadMinor, Matrix.submatrix_one _ (Fin.castLE_injective _)]

theorem diag_ne_zero_of_posDef_mul_conjTranspose {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : IsLo b)
    (hx : (b * bᴴ).PosDef) (l : Fin n) : b l l ≠ 0 := by
  classical
  have hdet : (b * bᴴ).det ≠ 0 := hx.det_pos.ne'
  have hb' : b.det ≠ 0 := fun h => hdet (by rw [Matrix.det_mul, h, zero_mul])
  rw [Matrix.det_of_isLowerTriangular b (blockTriangular_toDual_of_isLo hb)] at hb'
  exact Finset.prod_ne_zero_iff.mp hb' l (Finset.mem_univ l)

private lemma phi_mul_conjTranspose_of_isLo (hT : PhiTri) {n : ℕ} (lam : Fin n → ℝ)
    {b : Matrix (Fin n) (Fin n) ℂ} (hb : IsLo b) (hd : ∀ l, b l l ≠ 0) :
    b * bᴴ ∈ Omega n ∧ Phi lam (b * bᴴ) = ((∏ l, ‖b l l‖ ^ (-(2 * muInt lam l)) : ℝ) : ℂ) := by
  have hup : IsUp bᴴ := fun i j hji => by
    simp [Matrix.conjTranspose_apply, hb j i hji]
  have h := hT n lam b 1 bᴴ hb hup
    (fun l => ⟨hd l, by simpa [Matrix.conjTranspose_apply] using hd l⟩) (one_mem_Omega_leadMinor n)
  rw [Matrix.mul_one] at h
  refine ⟨h.1, ?_⟩
  rw [h.2, Phi_at_one, mul_one, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj', Complex.ofReal_zpow,
    ← zpow_natCast, ← _root_.zpow_mul]
  congr 1
  push_cast
  ring

theorem phiPos_of_phiTri (hT : PhiTri) : PhiPos := by
  intro n lam x hx
  obtain ⟨b, hb, rfl⟩ := exists_isLo_mul_conjTranspose hx
  have hd := fun l => diag_ne_zero_of_posDef_mul_conjTranspose hb hx l
  obtain ⟨hΩ, hΦ⟩ := phi_mul_conjTranspose_of_isLo hT lam hb hd
  refine ⟨hΩ, ?_, ⟨b, hb, rfl⟩, fun b' hb' hx' => ?_⟩
  · rw [hΦ, Complex.zero_lt_real]
    exact Finset.prod_pos fun l _ => zpow_pos (norm_pos_iff.mpr (hd l)) _
  · have hx2 : (b' * b'ᴴ).PosDef := hx' ▸ hx
    rw [hx']
    exact (phi_mul_conjTranspose_of_isLo hT lam hb'
      (fun l => diag_ne_zero_of_posDef_mul_conjTranspose hb' hx2 l)).2

theorem phiPos : PhiPos := phiPos_of_phiTri GlobalTheory.PhiTriangular.phiTri

end GlobalTheory.Dec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiPositiveDefiniteCholeskyFormulaStatement
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_positive_definite_cholesky_formula : PhiPos := by
  first | exact @GlobalTheory.Dec.phiPos | exact GlobalTheory.Dec.phiPos | (intros; apply GlobalTheory.Dec.phiPos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianSpacesSameSignatureIsometric
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianSpacesSameSignatureIsometric
open NumberField Matrix

namespace GlobalTheory.FlagMeas

open ReciprocityTheory.ChartRestriction.G.FD

theorem exists_congr_of_hasSignature {n p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.UG.HasSignature M p q) (f : Fin n ≃ Fin p ⊕ Fin q) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ, A.det ≠ 0 ∧
      Aᵀ * Mᵀ * A.map (starRingEnd ℂ) = ((Formalism.UG.Jpq p q).submatrix f f)ᵀ := by
  obtain ⟨e, P, hP⟩ := h
  have hPu : IsUnit (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 P.isUnit
  refine ⟨(P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e f, ?_, ?_⟩
  · have hσ : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e f =
        ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix f f).submatrix (e.trans f.symm) id := by
      ext i j; simp
    rw [hσ, Matrix.det_permute, Matrix.det_submatrix_equiv_self]
    exact mul_ne_zero (by simp) hPu.ne_zero
  · have hM : M = (M.reindex e e).submatrix e e := by ext i j; simp
    have hA : ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e f)ᴴ * M *
        (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e f = (Formalism.UG.Jpq p q).submatrix f f := by
      rw [hM, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ← hP]
      congr 1
    rw [← hA]
    simp [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.conjTranspose]
    rfl

theorem sameKindIsometric : SameKindIsometric := by
  intro E _ _ _ hE n J J' hJ hJ' hd hd' hΛ hΛ' hsig
  obtain ⟨hTC, hφ, hun⟩ := hE
  have hne : ∃ z : E, star z ≠ z := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have hc := hTC.isComplex w
    rw [InfinitePlace.isComplex_iff] at hc
    apply hc
    rw [ComplexEmbedding.isReal_iff]
    ext z
    rw [ComplexEmbedding.conjugate_coe_eq, ← hφ, hcon]
  obtain ⟨hcm, hst⟩ := (GlobalTheory.LeastExponentCompare.conj_iff E star).1
    ⟨fun φ z => by rw [hφ]; rfl, hne⟩
  have := hcm
  have hcc : ∀ z : E, star z = cc z := fun z => congrFun hst z
  have : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := by
    refine Formalism.L2.Pj.unramBridge_holds E fun P hP => ?_
    obtain ⟨θ, t, ht, hθ⟩ := hun P hP
    refine ⟨θ, ?_⟩
    convert hθ using 2
    ext
    simp [ht, hcc, cc]
  have hform : ∀ (M : Matrix (Fin n) (Fin n) E) (x y : Fin n → E),
      ReciprocityTheory.ChartRestriction.G.FD.herm Mᵀ x y = star y ⬝ᵥ (M *ᵥ x) := by
    intro M x y
    simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.transpose_apply, Pi.star_apply, hcc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hone : ∀ z : E, z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ↔ z ∈ (algebraMap (𝓞 E) E).range := by
    intro z
    rw [FractionalIdeal.mem_one_iff, RingHom.mem_range]
  have hmod : ∀ (M : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)),
      (∀ x, x ∈ L ↔ ∀ y ∈ L, star y ⬝ᵥ (M *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) →
      ∀ x, x ∈ L ↔ ∀ y ∈ L, ReciprocityTheory.ChartRestriction.G.FD.herm Mᵀ x y ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    intro M L h x
    simp only [hone, hform]
    exact h x
  have hherm : ∀ M : Matrix (Fin n) (Fin n) E, Mᴴ = M → ∀ a b, cc (Mᵀ a b) = Mᵀ b a := by
    intro M hM a b
    rw [← hcc]
    have := congrFun (congrFun hM a) b
    simpa [Matrix.conjTranspose_apply] using this
  have hc : ∀ z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), cc z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    intro z hz
    rw [FractionalIdeal.mem_one_iff] at hz ⊢
    obtain ⟨x, rfl⟩ := hz
    exact ⟨IsCMField.ringOfIntegersComplexConj E x, by simp [cc]⟩
  have hs : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧
      J'ᵀ.map τ = Qᵀ * Jᵀ.map τ * Q.map (starRingEnd ℂ) := by
    intro τ
    obtain ⟨p, q, h1, h2⟩ := hsig τ
    obtain ⟨e, -, -⟩ := id h1
    obtain ⟨A, hA, hA'⟩ := exists_congr_of_hasSignature h1 e
    obtain ⟨B, hB, hB'⟩ := exists_congr_of_hasSignature h2 e
    have hBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.2 hB)
    refine ⟨A * B⁻¹, by simp [Matrix.det_nonsing_inv, hA, hB], ?_⟩
    rw [Matrix.transpose_map, Matrix.transpose_map]
    have h1' : (B⁻¹)ᵀ * Bᵀ = 1 := by rw [← Matrix.transpose_mul, hBi, Matrix.transpose_one]
    have h2' : B.map (starRingEnd ℂ) * (B⁻¹).map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, hBi]
      simp
    have hY : (J'.map τ)ᵀ = (B⁻¹)ᵀ * (Bᵀ * (J'.map τ)ᵀ * B.map (starRingEnd ℂ)) *
        (B⁻¹).map (starRingEnd ℂ) := by
      simp only [← Matrix.mul_assoc]
      rw [h1', Matrix.one_mul, Matrix.mul_assoc, h2', Matrix.mul_one]
    rw [hY, hB', ← hA', Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  obtain ⟨Λ, hΛl, hΛm⟩ := hΛ
  obtain ⟨Λ', hΛl', hΛm'⟩ := hΛ'
  have hspan : ∀ (M : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)),
      Submodule.IsLattice E L →
      (∀ x, x ∈ L ↔ ∀ y ∈ L, star y ⬝ᵥ (M *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) →
      Submodule.span E (L : Set (Fin n → E)) = ⊤ := by
    intro M L hl hm
    classical
    obtain ⟨s, hs⟩ := hl.fg
    apply eq_top_iff.mpr
    intro z _
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E))
      (s.image fun y => star y ⬝ᵥ (M *ᵥ z))
    have hd0 : (algebraMap (𝓞 E) E d) ≠ 0 :=
      (IsFractionRing.injective (𝓞 E) E).ne (nonZeroDivisors.ne_zero d.2)
    have hdz : (algebraMap (𝓞 E) E d) • z ∈ L := by
      apply (hm _).2
      intro y hy
      rw [← hs] at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, ha⟩ := hd _ (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
        refine ⟨a, ?_⟩
        rw [Matrix.mulVec_smul, dotProduct_smul]
        simpa only [smul_eq_mul, Algebra.smul_def] using ha
      | zero => simp
      | add x y hx hy ihx ihy =>
        simpa [star_add, add_dotProduct] using add_mem ihx ihy
      | smul a x hx ih =>
        have ha : star (algebraMap (𝓞 E) E a) ∈ (algebraMap (𝓞 E) E).range := by
          rw [hcc]
          exact ⟨IsCMField.ringOfIntegersComplexConj E a, by simp [cc]⟩
        have he : star (a • x) = star (algebraMap (𝓞 E) E a) • star x := by
          ext i
          simp [Algebra.smul_def]
        rw [he, smul_dotProduct]
        simpa only [smul_eq_mul] using mul_mem ha ih
    have hz : z = (algebraMap (𝓞 E) E d)⁻¹ • ((algebraMap (𝓞 E) E d) • z) := by
      rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hdz)
  obtain ⟨P, hPd, hP⟩ := GlobalTheory.SelfDualGenus.congr_of_modular
    (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt
    (by
      intro h
      have h1 : (1 : E) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
        rw [FractionalIdeal.mem_one_iff]
        exact ⟨1, map_one _⟩
      rw [h, FractionalIdeal.mem_zero_iff] at h1
      exact one_ne_zero h1) hc (hherm J hJ) (hherm J' hJ') (by rwa [Matrix.det_transpose])
    (by rwa [Matrix.det_transpose]) ⟨hΛl.fg, hspan J Λ hΛl hΛm⟩
    ⟨hΛl'.fg, hspan J' Λ' hΛl' hΛm'⟩
    (hmod J Λ hΛm) (hmod J' Λ' hΛm') hs
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero P hPd, ?_⟩
  have hT := congrArg Matrix.transpose hP
  rw [Matrix.transpose_transpose, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_transpose] at hT
  change Pᴴ * J * P = J'
  rw [hT, Matrix.mul_assoc]
  congr 1
  ext i j
  simp [Matrix.conjTranspose_apply, hcc]

end GlobalTheory.FlagMeas
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianSpacesSameSignatureIsometricStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_spaces_same_signature_isometric : SameKindIsometric := by
  first | exact @GlobalTheory.FlagMeas.sameKindIsometric | exact GlobalTheory.FlagMeas.sameKindIsometric | (intros; apply GlobalTheory.FlagMeas.sameKindIsometric <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeProportional
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeProportional
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.DegreeTie

open Formalism.FourierDecayAlt.P.HaarUniquenessConjugation

theorem map_phi_eq {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P Q : MatKR k r} (hP : IsCayley k r ε P)
    (hQ : IsCayley k r ε Q) : (Formalism.REAL.muG ε).map (phi ε P) = (Formalism.REAL.muG ε).map (phi ε Q) := by
  obtain ⟨hPu, hPJ⟩ := hP
  obtain ⟨hQu, hQJ⟩ := hQ

  set Pu := hPu.unit with hPu_def
  set Qu := hQu.unit with hQu_def
  have hQQ : Q * Q⁻¹ = 1 := by
    rw [← hQu.unit_spec, ← Matrix.coe_units_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hmJ : (P * Q⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * Q⁻¹) = Formalism.REAL.Jm ε := by
    have h1 : (Q⁻¹)ᴴ * Qᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hQQ, Matrix.conjTranspose_one]
    calc (P * Q⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * Q⁻¹) = (Q⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * Q⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((Q⁻¹)ᴴ * Qᴴ) * Formalism.REAL.Jm ε * (Q * Q⁻¹) := by
          rw [hPJ, ← hQJ]; simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h1, hQQ, Matrix.one_mul, Matrix.mul_one]
  have hmem : Pu * Qu⁻¹ ∈ Formalism.REAL.UJ ε := by
    have hv : ((Pu * Qu⁻¹ : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) :
        Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = P * Q⁻¹ := by
      rw [Units.val_mul, Matrix.coe_units_inv, hPu_def, hQu_def, hPu.unit_spec, hQu.unit_spec]
    show Formalism.REAL.inUJ ε _
    rw [hv]
    exact hmJ
  set m : Formalism.REAL.UJ ε := ⟨Pu * Qu⁻¹, hmem⟩ with hm_def
  have hval : ∀ (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hA : IsUnit A)
      (u : Formalism.REAL.UJ ε), phi ε A u = ((hA.unit⁻¹ * (u : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) * hA.unit :
        (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := by
    intro A hA u
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, hA.unit_spec]
    rfl
  have hconj : phi ε Q = phi ε P ∘ (fun u => m * u * m⁻¹) := by
    funext u
    rw [Function.comp_apply, hval Q hQu, hval P hPu]
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hm_def]
    rw [hPu_def, hQu_def]
    group <;> rfl
  have hcont : ∀ A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Continuous (phi ε A) := by
    intro A
    have : Continuous (fun u : Formalism.REAL.UJ ε =>
        ((u : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
      Units.continuous_val.comp continuous_subtype_val
    exact (continuous_const.matrix_mul this).matrix_mul continuous_const
  have hinv : (Formalism.REAL.muG ε).map (fun u => m * u * m⁻¹) = Formalism.REAL.muG ε := by
    have hL : Measurable (fun u : Formalism.REAL.UJ ε => m * u) := measurable_const_mul m
    have hR : Measurable (fun u : Formalism.REAL.UJ ε => u * m⁻¹) := measurable_mul_const m⁻¹
    calc (Formalism.REAL.muG ε).map (fun u => m * u * m⁻¹)
        = ((Formalism.REAL.muG ε).map (fun u => m * u)).map (fun u => u * m⁻¹) := by
          rw [Measure.map_map hR hL]; rfl
      _ = (Formalism.REAL.muG ε).map (fun u => u * m⁻¹) := by
          rw [MeasureTheory.map_mul_left_eq_self (Formalism.REAL.muG ε) m]
      _ = Formalism.REAL.muG ε := Formalism.REAL.indefinite_unitary_unimodular _ ε m⁻¹
  rw [hconj, ← Measure.map_map (hcont P).measurable (by
    exact (measurable_const_mul m).mul_const m⁻¹), hinv]

theorem deg_eq_mul_fdegH : Hyps → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS), cdScaleTie D → GoodW D τ w w' θ W → ∃ κ : ℝ, 0 < κ ∧ ∀ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A → ∀ v : A.H, v ≠ 0 → A.deg = κ * PI.BesselPeriodGGP.fdegH W.μG A.σ v ∧ 0 < A.deg := by
  intro _ D τ w w' θ W _ hW

  by_cases hC : ∃ P0 : MatKR D.R.k D.R.rS, IsCayley D.R.k D.R.rS (epsSH D.R) P0
  swap
  · refine ⟨1, one_pos, ?_⟩
    intro lam A hA
    obtain ⟨P, hP, -⟩ := hA.2.2.2.2.2.2.2.2.2.2
    exact absurd ⟨P, hP⟩ hC
  obtain ⟨P0, hP0⟩ := hC
  have hP0det : IsUnit P0.det := (Matrix.isUnit_iff_isUnit_det P0).1 hP0.1
  obtain ⟨c, hc0, hctop, hμ⟩ :=
    GlobalTheory.BesselDegree.haar_eq_smul (ε := epsSH D.R) hP0det hP0.2 W.μG hW.2.2.2.2.2.2.1
  set cd : NNReal := D.s.cdScale _ (epsSH D.R) with hcd_def

  have hI : ∀ (P : MatKR D.R.k D.R.rS), IsCayley D.R.k D.R.rS (epsSH D.R) P →
      ∀ (F : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → ℝ),
        ∫ x, F x ∂W.μG = c.toReal * ∫ u, F (phi (epsSH D.R) P u) ∂(Formalism.REAL.muG (epsSH D.R)) := by
    intro P hP F
    have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).1 hP.1)
    have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).1 hP.1)
    let h : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ ≃ₜ
        Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
      { toFun := fun x => P⁻¹ * x * P
        invFun := fun x => P * x * P⁻¹
        left_inv := fun x => by
          simp only [← Matrix.mul_assoc, hPP, Matrix.one_mul]
          rw [Matrix.mul_assoc, hPP, Matrix.mul_one]
        right_inv := fun x => by
          simp only [← Matrix.mul_assoc, hPP', Matrix.one_mul]
          rw [Matrix.mul_assoc, hPP', Matrix.mul_one]
        continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
        continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
    have hemb : Topology.IsClosedEmbedding (phi (epsSH D.R) P) :=
      h.isClosedEmbedding.comp (Formalism.REAL.isClosedEmbeddingMatrix _ (epsSH D.R)).1
    rw [hμ, map_phi_eq hP0 hP, integral_smul_measure, smul_eq_mul,
      hemb.measurableEmbedding.integral_map]
  by_cases hcd : cd = 0
  · refine ⟨1, one_pos, ?_⟩
    intro lam A hA v hv
    obtain ⟨P, -, hF⟩ := hA.2.2.2.2.2.2.2.2.2.2
    have h2 := (hF.2 v v v v).2
    rw [← hcd_def] at h2
    rw [hcd, ENNReal.coe_zero, zero_smul, integral_zero_measure] at h2
    have hv' : (⟪v, v⟫_ℂ : ℂ) ≠ 0 := inner_self_ne_zero.2 hv
    have hd : (A.deg : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hF.1.ne'
    exact absurd h2.symm (div_ne_zero (mul_ne_zero hv' hv') hd)
  have hcpos : 0 < c.toReal := ENNReal.toReal_pos hc0 hctop
  have hcdpos : (0 : ℝ) < cd := by
    rw [NNReal.coe_pos]; exact pos_iff_ne_zero.2 hcd
  refine ⟨c.toReal / cd, div_pos hcpos hcdpos, ?_⟩
  intro lam A hA v hv
  obtain ⟨P, hP, hF⟩ := hA.2.2.2.2.2.2.2.2.2.2
  refine ⟨?_, hF.1⟩
  have h2 := (hF.2 v v v v).2
  rw [← hcd_def] at h2

  set J := ∫ u, ‖⟪v, A.σ (P⁻¹ * ((u : (Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)ˣ) :
      Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) * P) v⟫_ℂ‖ ^ 2
      ∂(Formalism.REAL.muG (epsSH D.R)) with hJ
  have hJc : ((cd : ℝ) * J : ℂ) = (‖v‖ ^ 4 / A.deg : ℝ) := by
    have hin : (⟪v, v⟫_ℂ : ℂ) = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    have hint : ∫ g, coefOn (fun g => A.σ (P⁻¹ * g * P)) v v g * star (coefOn (fun g => A.σ (P⁻¹ * g * P)) v v g)
        ∂(Formalism.REAL.muG (epsSH D.R)) = ((J : ℝ) : ℂ) := by
      rw [hJ, ← integral_complex_ofReal]
      congr 1
      funext g
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    rw [integral_smul_measure, hint, hin, ENNReal.coe_toReal, Complex.real_smul] at h2
    rw [h2]
    push_cast
    ring
  have hJr : (cd : ℝ) * J = ‖v‖ ^ 4 / A.deg := by exact_mod_cast hJc
  have hIv := hI P hP (fun x => ‖⟪v, A.σ (Matrix.of x) v⟫_ℂ‖ ^ 2)
  have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hdeg := hF.1
  unfold PI.BesselPeriodGGP.fdegH
  rw [hIv]
  change A.deg = c.toReal / cd * (‖v‖ ^ 4 / (c.toReal * J))
  have hJ' : J = ‖v‖ ^ 4 / A.deg / cd := by
    rw [← hJr]; field_simp
  rw [hJ']
  field_simp

end GlobalTheory.DegreeTie

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeProportionalStatement
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_degree_proportional : Hyps → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS), cdScaleTie D → GoodW D τ w w' θ W → ∃ κ : ℝ, 0 < κ ∧ ∀ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A → ∀ v : A.H, v ≠ 0 → A.deg = κ * PI.BesselPeriodGGP.fdegH W.μG A.σ v ∧ 0 < A.deg := by
  first | exact @GlobalTheory.DegreeTie.deg_eq_mul_fdegH | exact GlobalTheory.DegreeTie.deg_eq_mul_fdegH | (intros; apply GlobalTheory.DegreeTie.deg_eq_mul_fdegH <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalVolumeGrowth
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalVolumeGrowth
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff Pointwise

namespace GlobalTheory.RadVol

private theorem measure_slice_le_measure_mul_inv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] {N : Set G} {ν : Measure G} (hnull : ν Nᶜ = 0)
    (hleft : ∀ m ∈ N, Measure.map (fun x => m * x) ν = ν) {K S : Set G} (hK : IsCompact K) (g : G) :
    ν {s | s ∈ S ∧ s⁻¹ * g ∈ K} ≤ ν (K * K⁻¹) := by
  by_cases h0 : ∃ s₀ ∈ N, s₀⁻¹ * g ∈ K
  · obtain ⟨s₀, hs₀, hk₀⟩ := h0
    have hKK : MeasurableSet (K * K⁻¹) := (hK.mul hK.inv).isClosed.measurableSet
    have hpre : MeasurableSet ((fun x => s₀⁻¹ * x) ⁻¹' (K * K⁻¹)) := hKK.preimage (measurable_const_mul _)
    calc ν {s | s ∈ S ∧ s⁻¹ * g ∈ K} ≤ ν ((fun x => s₀⁻¹ * x) ⁻¹' (K * K⁻¹)) := by
          apply measure_mono
          intro s hs
          simp only [Set.mem_preimage]
          rw [show s₀⁻¹ * s = (s₀⁻¹ * g) * (s⁻¹ * g)⁻¹ by group]
          exact Set.mul_mem_mul hk₀ (Set.inv_mem_inv.mpr hs.2)
      _ = Measure.map (fun x => s₀ * x) ν ((fun x => s₀⁻¹ * x) ⁻¹' (K * K⁻¹)) := by
          rw [hleft s₀ hs₀]
      _ = ν ((fun x => s₀ * x) ⁻¹' ((fun x => s₀⁻¹ * x) ⁻¹' (K * K⁻¹))) :=
          Measure.map_apply (measurable_const_mul _) hpre
      _ = ν (K * K⁻¹) := by
          congr 1
          ext x
          simp
  · push_neg at h0
    have hsub : {s | s ∈ S ∧ s⁻¹ * g ∈ K} ⊆ Nᶜ := fun s hs hsN => h0 s hsN hs.2
    calc ν {s | s ∈ S ∧ s⁻¹ * g ∈ K} ≤ ν Nᶜ := measure_mono hsub
      _ = 0 := hnull
      _ ≤ ν (K * K⁻¹) := bot_le

theorem measure_mul_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    {N : Set G} {ν : Measure G} (hν : IsHaarSub N ν) {K S T : Set G} (hK : IsCompact K) (hS : MeasurableSet S)
    (hT : MeasurableSet T) (h : ∀ s ∈ S, ∀ k ∈ K, s * k ∈ T) : ν S * μ K ≤ ν (K * K⁻¹) * μ T := by
  classical
  obtain ⟨-, hfc, hnull, hleft⟩ := hν
  haveI : IsFiniteMeasureOnCompacts ν := hfc
  haveI : SigmaFinite ν := inferInstance
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set E : Set (G × G) := {p | p.1 ∈ S ∧ p.1⁻¹ * p.2 ∈ K} with hEd
  have hE : MeasurableSet E :=
    (measurable_fst hS).inter ((measurable_fst.inv.mul measurable_snd) hKm)

  have h1 : ν.prod μ E = ν S * μ K := by
    rw [Measure.prod_apply hE]
    have hsl : ∀ s, μ (Prod.mk s ⁻¹' E) = S.indicator (fun _ => μ K) s := by
      intro s
      by_cases hs : s ∈ S
      · rw [Set.indicator_apply, if_pos hs, ← measure_preimage_mul μ s⁻¹ K]
        congr 1
        ext x
        simp [hEd, hs]
      · rw [Set.indicator_apply, if_neg hs]
        have h0 : Prod.mk s ⁻¹' E = ∅ := by
          ext x
          simp [hEd, hs]
        rw [h0, measure_empty]
    simp_rw [hsl]
    rw [lintegral_indicator_const hS, mul_comm]

  have h2 : ν.prod μ E ≤ ν (K * K⁻¹) * μ T := by
    rw [Measure.prod_apply_symm hE]
    calc ∫⁻ g, ν ((fun s => (s, g)) ⁻¹' E) ∂μ
        ≤ ∫⁻ g, T.indicator (fun _ => ν (K * K⁻¹)) g ∂μ := by
          apply lintegral_mono
          intro g
          by_cases hg : g ∈ T
          · rw [Set.indicator_apply, if_pos hg]
            exact (le_of_eq (by rw [hEd]; rfl)).trans
              (measure_slice_le_measure_mul_inv (S := S) hnull hleft hK g)
          · rw [Set.indicator_apply, if_neg hg]
            have h0 : (fun s => (s, g)) ⁻¹' E = ∅ := by
              ext s
              simp only [hEd, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
                not_and]
              intro hs hk
              apply hg
              simpa using h s hs _ hk
            exact le_of_eq (by show ν ((fun s => (s, g)) ⁻¹' E) = 0; rw [h0, measure_empty])
      _ = ν (K * K⁻¹) * μ T := lintegral_indicator_const hT _
  calc ν S * μ K = ν.prod μ E := h1.symm
    _ ≤ ν (K * K⁻¹) * μ T := h2

private theorem dOp_nonneg_subadditive_continuous {n : ℕ} (ε : Fin n → Bool) :
    (∀ g : UJ ε, 0 ≤ dOp (umat g)) ∧
      (∀ g g' : UJ ε, dOp (umat (g * g')) ≤ dOp (umat g) + dOp (umat g')) ∧
      Continuous (fun g : UJ ε => dOp (umat g)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : ∀ g : Matrix (Fin 0) (Fin 0) ℂ, dOp g = 0 := by
      intro g
      have hz : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)‖ = 0 := by
        refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ le_rfl fun x => ?_) (norm_nonneg _)
        rw [zero_mul, EuclideanSpace.norm_eq]
        simp
      simp only [dOp, hz, Real.log_zero]
    simp only [h0]
    exact ⟨fun _ => le_rfl, fun _ _ => by norm_num, continuous_const⟩
  · obtain ⟨-, h2, -, -, h5⟩ := GlobalTheory.Count.Cartan.cartan_distances n ε
    exact ⟨fun g => (h2 g 1 hn).1, fun g g' => (h2 g g' hn).2.2.1, h5⟩

theorem radical_volume_growth : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)),
    IsIsoC ε W → IsHaarSub (NW ε W) ν →
    (∃ C : ℝ, ∀ r : ℝ, 0 ≤ r →
      ν {m | dOp (umat m) ≤ r} ≤ ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * r))) ∧
    ∀ b : ℝ, 4 * n * rkR ε < b → Integrable (fun m : UJ ε => Real.exp (-(b * dOp (umat m)))) ν := by
  intro n ε W ν _ hν
  obtain ⟨hP, hM, hD⟩ := dOp_nonneg_subadditive_continuous ε
  haveI : (muG ε).IsHaarMeasure := by
    first
    | infer_instance
    | (unfold muG; infer_instance)
  have hgrowth : ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r →
      ν {m | dOp (umat m) ≤ r} ≤ ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * r)) := by
    obtain ⟨C, -, hball⟩ := GlobalTheory.BallVol.ballVol n ε
    obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : UJ ε)
    have hμK : 0 < muG ε K := by
      first
      | exact measure_pos_of_mem_nhds (μ := muG ε) hK1
      | exact (muG ε).measure_pos_of_mem_nhds hK1
      | exact Measure.measure_pos_of_mem_nhds (muG ε) hK1
    have hμKt : muG ε K < ⊤ := by
      first
      | exact hKc.measure_lt_top (μ := muG ε)
      | exact IsCompact.measure_lt_top hKc
    have hνKK : ν (K * K⁻¹) < ⊤ := by
      haveI : IsFiniteMeasureOnCompacts ν := hν.2.1
      exact (hKc.mul hKc.inv).measure_lt_top
    obtain ⟨B, hB⟩ := hKc.bddAbove_image hD.continuousOn
    refine ⟨(ν (K * K⁻¹)).toReal * C * Real.exp (4 * n * rkR ε * max B 0) / (muG ε K).toReal,
      fun r hr => ?_⟩

    have hmul : ∀ s ∈ {m : UJ ε | dOp (umat m) ≤ r}, ∀ k ∈ K,
        s * k ∈ {m : UJ ε | dOp (umat m) ≤ r + max B 0} := by
      intro s hs k hk
      have hkB : dOp (umat k) ≤ B := hB (Set.mem_image_of_mem _ hk)
      have hs' : dOp (umat s) ≤ r := hs
      show dOp (umat (s * k)) ≤ r + max B 0
      linarith [hM s k, le_max_left B 0]
    have key := measure_mul_le (muG ε) hν (S := {m : UJ ε | dOp (umat m) ≤ r})
      (T := {m : UJ ε | dOp (umat m) ≤ r + max B 0}) hKc (measurableSet_le hD.measurable measurable_const)
      (measurableSet_le hD.measurable measurable_const) hmul
    have hT : muG ε {m : UJ ε | dOp (umat m) ≤ r + max B 0} ≤
        ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * (r + max B 0))) :=
      hball _ (add_nonneg hr (le_max_right B 0))
    have hm : 0 < (muG ε K).toReal := ENNReal.toReal_pos hμK.ne' hμKt.ne
    have key2 : ν {m : UJ ε | dOp (umat m) ≤ r} * ENNReal.ofReal (muG ε K).toReal ≤
        ENNReal.ofReal ((ν (K * K⁻¹)).toReal * (C * Real.exp (4 * n * rkR ε * (r + max B 0)))) := by
      rw [ENNReal.ofReal_toReal hμKt.ne, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hνKK.ne]
      exact key.trans (by gcongr)
    have key3 := (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hm).ne')
      (Or.inl ENNReal.ofReal_ne_top)).mpr key2
    rw [← ENNReal.ofReal_div_of_pos hm] at key3
    refine key3.trans (le_of_eq (congrArg ENNReal.ofReal ?_))
    rw [mul_add, Real.exp_add]
    ring
  refine ⟨hgrowth, fun b hb => ?_⟩
  obtain ⟨C, hC⟩ := hgrowth
  exact GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth (UJ ε) ν (fun m => dOp (umat m)) (4 * n * rkR ε) b C
    hD.measurable hP hC hb

end GlobalTheory.RadVol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalVolumeGrowthStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadical_volume_growth : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → (∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → ν {m | dOp (umat m) ≤ r} ≤ ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * r))) ∧ ∀ b : ℝ, 4 * n * rkR ε < b → Integrable (fun m : UJ ε => Real.exp (-(b * dOp (umat m)))) ν := by
  first | exact @GlobalTheory.RadVol.radical_volume_growth | exact GlobalTheory.RadVol.radical_volume_growth | (intros; apply GlobalTheory.RadVol.radical_volume_growth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtCompletedTensorOrbitSmoothAverage
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtCompletedTensorOrbitSmoothAverage
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.AverageDeriv

theorem hasDerivAt_average {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : G → (H →L[ℂ] H)} (hσ : IsURep σ) (w : H) {a : ℝ → G} (ha : Continuous a) (ha0 : a 0 = 1)
    {f f' : G → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (hf' : Continuous f')
    (hfc' : HasCompactSupport f')
    (hd : ∀ g t, HasDerivAt (fun s => f ((a s)⁻¹ * g)) (f' ((a t)⁻¹ * g)) t) :
    HasDerivAt (fun t => σ (a t) (∫ g, f g • σ g w ∂μ)) (∫ g, f' g • σ g w ∂μ) 0 := by
  obtain ⟨-, hmul, hnorm, hcont⟩ := hσ
  have hcw : Continuous fun g => σ g w := hcont w

  have key : ∀ t, σ (a t) (∫ g, f g • σ g w ∂μ) = ∫ g, f ((a t)⁻¹ * g) • σ g w ∂μ := by
    intro t
    have hint : Integrable (fun g => f g • σ g w) μ :=
      (hf.smul hcw).integrable_of_hasCompactSupport (hfc.smul_right)
    rw [← (σ (a t)).integral_comp_comm hint]
    rw [← integral_mul_left_eq_self (fun g => f ((a t)⁻¹ * g) • σ g w) (a t)]
    congr 1
    funext g
    rw [map_smul, inv_mul_cancel_left, hmul]
    rfl

  obtain ⟨C, hC⟩ := hf'.bounded_above_of_compact_support hfc'
  set K : Set G := (fun p : ℝ × G => a p.1 * p.2) '' (Set.Icc (-1 : ℝ) 1 ×ˢ tsupport f') with hK
  have hKc : IsCompact K :=
    (isCompact_Icc.prod hfc').image ((ha.comp continuous_fst).mul continuous_snd)
  have hsupp : ∀ s ∈ Metric.ball (0 : ℝ) 1, ∀ g, g ∉ K → f' ((a s)⁻¹ * g) = 0 := by
    intro s hs g hg
    by_contra h
    apply hg
    refine ⟨(s, (a s)⁻¹ * g), ⟨?_, subset_tsupport _ h⟩, by simp⟩
    rw [Real.ball_eq_Ioo, zero_sub, zero_add] at hs
    exact Set.Ioo_subset_Icc_self hs
  have hbound_int : Integrable (K.indicator fun _ => C * ‖w‖) μ :=
    (continuousOn_const.integrableOn_compact hKc).integrable_indicator hKc.isClosed.measurableSet
  have hcont_tr : ∀ (k : G → ℂ), Continuous k → ∀ s : ℝ, Continuous fun g => k ((a s)⁻¹ * g) • σ g w :=
    fun k hk s => (hk.comp (continuous_const.mul continuous_id)).smul hcw
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun s g => f ((a s)⁻¹ * g) • σ g w) (F' := fun s g => f' ((a s)⁻¹ * g) • σ g w)
    (bound := K.indicator fun _ => C * ‖w‖) (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun s => (hcont_tr f hf s).aestronglyMeasurable)
    (by
      simp only [ha0, inv_one, one_mul]
      exact (hf.smul hcw).integrable_of_hasCompactSupport (hfc.smul_right))
    (hcont_tr f' hf' 0).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g s hs => by
      by_cases hg : g ∈ K
      · rw [Set.indicator_of_mem hg, norm_smul, hnorm]
        exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
      · rw [Set.indicator_of_notMem hg, hsupp s hs g hg, zero_smul, norm_zero])
    hbound_int
    (Filter.Eventually.of_forall fun g s _ => (hd g s).smul_const (σ g w))
  have hfun : (fun t => σ (a t) (∫ g, f g • σ g w ∂μ)) = fun t => ∫ g, f ((a t)⁻¹ * g) • σ g w ∂μ :=
    funext key
  rw [hfun]
  simpa only [ha0, inv_one, one_mul] using hder.2

theorem expU_zero {n : ℕ} {ε : Fin n → Bool} : expU (0 : gLie ε) = 1 := by
  apply Subtype.ext
  apply Units.ext
  refine (uMat_expU _).trans ?_
  simp

theorem expU_add {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (a b : ℝ) :
    expU ((a + b) • X) = expU (a • X) * expU (b • X) := by
  apply Subtype.ext
  apply Units.ext
  refine (uMat_expU _).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (uMat_expU (a • X)).symm (uMat_expU (b • X)).symm)
  rw [Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left a).smul_right b)

theorem expU_inv {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (t : ℝ) : (expU (t • X))⁻¹ = expU ((-t) • X) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← expU_add, add_neg_cancel, zero_smul, expU_zero]

theorem continuous_expU {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) : Continuous fun t : ℝ => expU (t • X) := by
  have hcexp : ∀ A : Matrix (Fin n) (Fin n) ℂ, Continuous fun t : ℝ => NormedSpace.exp (t • A) := by
    intro A
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    exact (differentiable_exp_smul_const ℝ A).continuous
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · have e : (fun t : ℝ => (((expU (t • X) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) = fun t : ℝ => NormedSpace.exp (t • X.1) := by
      funext t
      rw [← Submodule.coe_smul]
      exact uMat_expU (t • X)
    have h := hcexp X.1
    rw [← e] at h
    exact h
  · have e : (fun t : ℝ => ((((expU (t • X) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ :
        (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) =
        fun t : ℝ => NormedSpace.exp (t • (-X.1)) := by
      funext t
      have h1 := congrArg (fun g : Formalism.REAL.UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) (expU_inv X t)
      refine h1.trans ((uMat_expU _).trans ?_)
      rw [Submodule.coe_smul, neg_smul, smul_neg]
    have h := hcexp (-X.1)
    rw [← e] at h
    exact h

theorem hasDerivAt_exp_mul_entry {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) * Y) i j) ((X * (NormedSpace.exp (t • X) * Y)) i j) t := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X t).mul_const Y
  let l : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h2 := (LinearMap.toContinuousLinearMap l).hasFDerivAt.comp_hasDerivAt t h
  have h3 : HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) * Y) i j)
      ((X * NormedSpace.exp (t • X) * Y) i j) t := h2
  rw [← mul_assoc]
  exact h3

theorem uMat_inv_mul {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (t : ℝ) (g : UJ ε) :
    uMat ((expU (t • X))⁻¹ * g) = NormedSpace.exp (t • (-X.1)) * uMat g := by
  rw [expU_inv]
  show uMat (expU ((-t) • X)) * uMat g = _
  rw [uMat_expU, Submodule.coe_smul, neg_smul, smul_neg]

theorem hasDerivAt_orbit_average : ∀ (B : RowsAut) (F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ) (E : gInf B) (w : B.Hs), IsURep B.σs → ContDiff ℝ ∞ F → HasCompactSupport F → ∃ F' : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F' ∧ HasCompactSupport F' ∧ HasDerivAt (orbit B E (∫ g, F (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I))) (∫ g, F' (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I)) 0 := by
  intro B F E w hσ hF hFc

  have hμ : muInf B.I = Measure.pi (fun v => Formalism.REAL.muG (B.I.ε v)) := rfl
  haveI : (muInf B.I).IsMulLeftInvariant := by rw [hμ]; infer_instance
  haveI : IsFiniteMeasureOnCompacts (muInf B.I) := by rw [hμ]; infer_instance
  let c : B.I.Ginf → (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) :=
    fun g v i j => uMat (g v) i j
  have hc : Topology.IsClosedEmbedding c :=
    Topology.IsClosedEmbedding.piMap fun v => (Formalism.REAL.isClosedEmbeddingMatrix B.I.n (B.I.ε v)).1

  let Lm : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) →ₗ[ℝ]
      (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) :=
    { toFun := fun M v i j => ∑ k, (-(E v).1) i k * M v k j
      map_add' := by
        intro M N
        funext v i j
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r M
        funext v i j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Complex.real_smul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _ }
  let L := LinearMap.toContinuousLinearMap Lm
  let F' : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ := fun M => fderiv ℝ F M (L M)
  have hF's : ContDiff ℝ ∞ F' := (contDiff_infty_iff_fderiv.1 hF).2.clm_apply L.contDiff
  have hF'c : HasCompactSupport F' := by
    refine (hFc.fderiv (𝕜 := ℝ)).mono' fun M hM => subset_tsupport _ ?_
    intro h0
    apply hM
    show fderiv ℝ F M (L M) = 0
    rw [h0]
    rfl
  refine ⟨F', hF's, hF'c, ?_⟩
  let a : ℝ → B.I.Ginf := fun t v => expU (t • E v)
  have ha : Continuous a := continuous_pi fun v => continuous_expU (E v)
  have ha0 : a 0 = 1 := by
    funext v
    show expU ((0 : ℝ) • E v) = 1
    rw [zero_smul, expU_zero]
  have hcc : Continuous c := hc.continuous
  have hd : ∀ g t, HasDerivAt (fun s => F (c ((a s)⁻¹ * g))) (F' (c ((a t)⁻¹ * g))) t := by
    intro g t
    let p : ℝ → (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) :=
      fun s v i j => (NormedSpace.exp (s • (-(E v).1)) * uMat (g v)) i j
    have hp : ∀ s, c ((a s)⁻¹ * g) = p s := by
      intro s
      funext v i j
      show uMat ((expU (s • E v))⁻¹ * g v) i j = _
      rw [uMat_inv_mul]
    have hp' : HasDerivAt p (L (p t)) t := by
      refine hasDerivAt_pi.2 fun v => hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
      exact hasDerivAt_exp_mul_entry _ _ t i j
    have hFd : HasFDerivAt F (fderiv ℝ F (p t)) (p t) :=
      (hF.differentiable (by simp)).differentiableAt.hasFDerivAt
    have h := hFd.comp_hasDerivAt t hp'
    simp only [hp]
    exact h
  have main := hasDerivAt_average (muInf B.I) hσ w (a := a) ha ha0 (f := fun g => F (c g))
    (f' := fun g => F' (c g)) (hF.continuous.comp hcc) (hFc.comp_isClosedEmbedding hc)
    (hF's.continuous.comp hcc) (hF'c.comp_isClosedEmbedding hc) hd
  exact main

end GlobalTheory.AverageDeriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtCompletedTensorOrbitSmoothAverageStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_completedTensorOrbit_smoothAverage : ∀ (B : RowsAut) (F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ) (E : gInf B) (w : B.Hs), IsURep B.σs → ContDiff ℝ ∞ F → HasCompactSupport F → ∃ F' : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F' ∧ HasCompactSupport F' ∧ HasDerivAt (orbit B E (∫ g, F (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I))) (∫ g, F' (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I)) 0 := by
  first | exact @GlobalTheory.AverageDeriv.hasDerivAt_orbit_average | exact GlobalTheory.AverageDeriv.hasDerivAt_orbit_average | (intros; apply GlobalTheory.AverageDeriv.hasDerivAt_orbit_average <;> assumption)
end
end
