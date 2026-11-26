module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundInfinitePlaces
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundInfinitePlaces
noncomputable section

open Matrix PositivityTheory.Rg.BcB.D1
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Wedge

variable {ι κ κ' : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

theorem gram_det_nonneg (A : Matrix ι κ ℂ) : 0 ≤ (Aᴴ * A).det := by
  exact (Matrix.posSemidef_conjTranspose_mul_self A).det_nonneg

theorem gram_det_im (A : Matrix ι κ ℂ) : (Aᴴ * A).det.im = 0 := by
  exact (Complex.nonneg_iff.1 (gram_det_nonneg A)).2.symm

theorem nI_nonneg (A : Matrix ι κ ℂ) : 0 ≤ nI A := by
  exact (Complex.nonneg_iff.1 (gram_det_nonneg A)).1

theorem nI_ne_zero_iff_det (A : Matrix ι κ ℂ) : nI A ≠ 0 ↔ (Aᴴ * A).det ≠ 0 := by
  have him := gram_det_im A
  show (Aᴴ * A).det.re ≠ 0 ↔ _
  constructor
  · intro h h0
    apply h
    rw [h0, Complex.zero_re]
  · intro h h0
    apply h
    exact Complex.ext (by rw [h0, Complex.zero_re]) (by rw [him, Complex.zero_im])

theorem gram_det_ne_zero_iff (A : Matrix ι κ ℂ) :
    (Aᴴ * A).det ≠ 0 ↔ LinearIndependent ℂ Aᵀ := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit,
    ← Matrix.coe_mulVecLin, ← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_conjTranspose_mul_self,
    LinearMap.ker_eq_bot, Matrix.coe_mulVecLin]
  exact Matrix.mulVec_injective_iff

theorem nI_submatrix (e : κ' ≃ κ) (A : Matrix ι κ ℂ) : nI (A.submatrix id e) = nI A := by
  show ((A.submatrix id e)ᴴ * A.submatrix id e).det.re = (Aᴴ * A).det.re
  rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul Aᴴ A (⇑e) id (⇑e) Function.bijective_id,
    Matrix.det_submatrix_equiv_self]

theorem nI_fromCols_of_orth (B : Matrix ι κ ℂ) (D : Matrix ι κ' ℂ) (h : Bᴴ * D = 0) :
    nI (fromCols B D) = nI B * nI D := by
  have h' : Dᴴ * B = 0 := by
    have h2 := congrArg Matrix.conjTranspose h
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] at h2
    exact h2
  show ((fromCols B D)ᴴ * fromCols B D).det.re = (Bᴴ * B).det.re * (Dᴴ * D).det.re
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul_fromCols, h, h',
    Matrix.det_fromBlocks_zero₂₁, Complex.mul_re, gram_det_im B, gram_det_im D, mul_zero, sub_zero]

theorem exists_proj (B : Matrix ι κ ℂ) (hB : LinearIndependent ℂ Bᵀ) :
    ∃ Y : Matrix κ ι ℂ, Y * B = 1 ∧ (B * Y)ᴴ = B * Y := by
  have hu : IsUnit (Bᴴ * B).det := isUnit_iff_ne_zero.2 ((gram_det_ne_zero_iff B).2 hB)
  have hG : (Bᴴ * B)ᴴ = Bᴴ * B := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  refine ⟨(Bᴴ * B)⁻¹ * Bᴴ, ?_, ?_⟩
  · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_nonsing_inv, hG, Matrix.mul_assoc]

theorem commGroup_mul_mul_eq_mul_inv_mul_mul_mul [DecidableEq ι] (hD : DetMono) (hM : MulI) (B : Matrix ι κ ℂ) (Y : Matrix κ ι ℂ)
    (hYB : Y * B = 1) (hQ : (B * Y)ᴴ = B * Y) (C : Matrix ι κ' ℂ) :
    nI (fromCols B C) = nI B * nI ((1 - B * Y) * C) ∧ nI ((1 - B * Y) * C) ≤ nI C ∧
      (1 - B * Y) * B = 0 := by
  have hPP : B * Y * (B * Y) = B * Y := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Y, hYB, Matrix.one_mul]
  have hQB : (1 - B * Y) * B = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hYB, Matrix.mul_one, sub_self]
  have hQh : (1 - B * Y)ᴴ = 1 - B * Y := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQ]
  have hQQ : (1 - B * Y) * (1 - B * Y) = 1 - B * Y := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self, sub_zero]
  have hPh : (B * Y)ᴴ * (B * Y) = B * Y := by
    rw [hQ, hPP]
  refine ⟨?_, ?_, hQB⟩
  · have hcols : fromCols B C = (fromCols B ((1 - B * Y) * C) : Matrix ι (κ ⊕ κ') ℂ) *
        (fromBlocks (1 : Matrix κ κ ℂ) (Y * C) (0 : Matrix κ' κ ℂ) (1 : Matrix κ' κ' ℂ)) := by
      rw [Matrix.fromCols_mul_fromBlocks]
      congr 1
      · rw [Matrix.mul_one, Matrix.mul_zero, add_zero]
      · rw [Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
        abel
    have horth : Bᴴ * ((1 - B * Y) * C) = 0 := by
      rw [← Matrix.mul_assoc, ← hQh, ← Matrix.conjTranspose_mul, hQB, Matrix.conjTranspose_zero,
        Matrix.zero_mul]
    rw [hcols, (hM ι ι (κ ⊕ κ') (fromCols B ((1 - B * Y) * C))).2.1, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, Matrix.det_one, mul_one, norm_one, one_pow, mul_one, nI_fromCols_of_orth B _ horth]
  · have hX : ((1 - B * Y) * C)ᴴ * ((1 - B * Y) * C) = Cᴴ * ((1 - B * Y) * C) := by
      rw [Matrix.conjTranspose_mul, hQh, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - B * Y), hQQ]
    have hYX : Cᴴ * C - ((1 - B * Y) * C)ᴴ * ((1 - B * Y) * C) = (B * Y * C)ᴴ * (B * Y * C) := by
      rw [hX, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (B * Y)ᴴ, hPh,
        Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, sub_sub_cancel]
    exact hD κ' (((1 - B * Y) * C)ᴴ * ((1 - B * Y) * C)) (Cᴴ * C)
      (Matrix.posSemidef_conjTranspose_mul_self _)
      (by rw [hYX]; exact Matrix.posSemidef_conjTranspose_mul_self _)

theorem wedgeI_of_detMono_mulI : DetMono → MulI → WedgeI := by
  intro hD hM ι _ _
  refine ⟨fun κ _ _ A => nI_nonneg A, fun κ _ _ A => (nI_ne_zero_iff_det A).trans (gram_det_ne_zero_iff A),
    fun κ κ' _ _ _ _ e A => nI_submatrix e A, fun κ _ _ B hB => ?_⟩
  obtain ⟨Y, hYB, hQ⟩ := exists_proj B hB
  exact ⟨Y, fun κ' _ _ C => commGroup_mul_mul_eq_mul_inv_mul_mul_mul hD hM B Y hYB hQ C⟩

end GlobalTheory.CompanionTheory.Wedge

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundInfinitePlacesStatement
open Matrix PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wedgeI_of_detMono_mulI_var : DetMono → MulI → WedgeI := by
  first | exact @GlobalTheory.CompanionTheory.Wedge.wedgeI_of_detMono_mulI | exact GlobalTheory.CompanionTheory.Wedge.wedgeI_of_detMono_mulI | (intros; apply GlobalTheory.CompanionTheory.Wedge.wedgeI_of_detMono_mulI <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovOfAlgHom
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.CovMono

theorem cov_self (p : ℕ) (A : Type) [CommRing A] (r : ℕ → A) : Cov p r A := by
  intro K₁ K₀ _ _ _ _ _ _ d _ z hz k
  obtain ⟨w, hw⟩ := hz
  have key : z = d (TensorProduct.lid A K₁ w) := by
    have h1 : TensorProduct.lid A K₀ (d.lTensor A w) = d (TensorProduct.lid A K₁ w) := by
      clear hw
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [hw] at h1
    simpa using h1
  rw [key, ← map_smul]
  exact ⟨_, rfl⟩

theorem cov_of_algHom (p : ℕ) (A : Type) [CommRing A] (r : ℕ → A)
    (B : Type) [CommRing B] [Algebra A B] (B₁ : Type) [CommRing B₁] [Algebra A B₁]
    (φ : B →ₐ[A] B₁) (h : Cov p r B₁) : Cov p r B := by
  intro K₁ K₀ _ _ _ _ hK₁ hK₀ d hd z hz k
  obtain ⟨w, hw⟩ := hz
  refine h K₁ K₀ hK₁ hK₀ d hd z ⟨φ.toLinearMap.rTensor K₁ w, ?_⟩ k
  have h1 : φ.toLinearMap.rTensor K₀ (d.lTensor B w) = d.lTensor B₁ (φ.toLinearMap.rTensor K₁ w) := by
    clear hw
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [← h1, hw]
  simp

theorem cov_mono : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A), Cov p r A ∧ ∀ (B : Type) [CommRing B] [Algebra A B] (B₁ : Type) [CommRing B₁] [Algebra A B₁] (φ : B →ₐ[A] B₁), Cov p r B₁ → Cov p r B := by
  intro p _ A _ r
  exact ⟨cov_self p A r, fun B _ _ B₁ _ _ φ h => cov_of_algHom p A r B B₁ φ h⟩

end GlobalTheory.CompanionTheory.CovMono
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftCommLTensorNatural
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Dblock.AmiBc

theorem leftComm_lTensor_natural {A B C M N : Type} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup C] [Module A C] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (d : M →ₗ[A] N) (c : C) (w : B ⊗[A] M) :
    (d.lTensor C).lTensor B (TensorProduct.leftComm A C B M (c ⊗ₜ[A] w)) =
      TensorProduct.leftComm A C B N (c ⊗ₜ[A] (d.lTensor B w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul b m => simp [TensorProduct.leftComm_tmul]
  | add x y hx hy =>
    simp only [TensorProduct.tmul_add, map_add (f := _), hx, hy]

theorem contraction_lTensor :
    ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (C : Type) [AddCommGroup C] [Module A C] (K : ℕ → Type) [∀ n, AddCommGroup (K n)] [∀ n, Module A (K n)] (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n), ((∀ z, H 0 (d 0 z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, (d n).lTensor B (H n z) + H (n + 1) (d (n + 1) z) = (1 : B) ⊗ₜ[A] z) → ∃ H₁ : ∀ n, C ⊗[A] K (n + 1) →ₗ[A] B ⊗[A] (C ⊗[A] K n), (∀ z, H₁ 0 ((d 0).lTensor C z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, ((d n).lTensor C).lTensor B (H₁ n z) + H₁ (n + 1) ((d (n + 1)).lTensor C z) = (1 : B) ⊗ₜ[A] z := by
  intro A _ B _ _ C _ _ K _ _ d H ⟨h0, hS⟩
  refine ⟨fun n => (TensorProduct.leftComm A C B (K n)).toLinearMap ∘ₗ (H n).lTensor C, ?_, ?_⟩
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c k =>
      simp [h0, TensorProduct.leftComm_tmul]
    | add x y hx hy =>
      simp only [map_add (f := _), hx, hy, TensorProduct.tmul_add]
  · intro n z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c k =>
      have key := congrArg (fun t => TensorProduct.leftComm A C B (K (n + 1)) (c ⊗ₜ[A] t)) (hS n k)
      simp only [TensorProduct.tmul_add, map_add (f := _)] at key
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lTensor_tmul]
      rw [leftComm_lTensor_natural, key, TensorProduct.leftComm_tmul]
    | add x y hx hy =>
      simp only [map_add (f := _), TensorProduct.tmul_add]
      rw [← hx, ← hy]
      abel

end GlobalTheory.CompanionTheory.Dblock.AmiBc
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparableQuotientOfValuation
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.ValQuot

theorem valuation_comparable_quotient : ∀ {S : Type} [CommRing S] (π : S), Val π → Val0 (S := S ⧸ Ideal.span {π}) := by
  intro S _ π hV f' g'
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f'
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g'
  have hpi : ∀ x : S, ∃ N : ℕ, π ^ N ∈ Ideal.span {x, π} := fun x =>
    ⟨1, Ideal.mem_span_pair.mpr ⟨0, 1, by ring⟩⟩
  obtain ⟨e₁, he1, h1f, h1π⟩ := hV f π (hpi f)
  obtain ⟨e₂, he2, h2g, h2π⟩ := hV g π (hpi g)
  obtain ⟨a1, ha1⟩ := Ideal.mem_span_singleton'.mp h1f
  obtain ⟨b1, hb1⟩ := Ideal.mem_span_singleton'.mp h1π
  obtain ⟨a2, ha2⟩ := Ideal.mem_span_singleton'.mp h2g
  have he1' : e₁ * e₁ = e₁ := he1
  have he2' : e₂ * e₂ = e₂ := he2
  obtain ⟨u, hu⟩ : ∃ u : S, u = (1 - e₁) * (1 - e₂) := ⟨_, rfl⟩
  have hu2 : u * u = u := by subst hu; linear_combination (1 - e₂) ^ 2 * he1' + (1 - e₁) * he2'
  have he1u : e₁ * u = 0 := by subst hu; linear_combination (-(1 - e₂)) * he1'
  have huπ : u * π = (1 - e₂) * b1 * f := by subst hu; linear_combination (-(1 - e₂)) * hb1
  obtain ⟨e₃, he3, h3, h3'⟩ := hV (u * f + (1 - u)) (u * g + (1 - u))
    ⟨1, Ideal.mem_span_pair.mpr ⟨(1 - e₂) * b1 * u + π * (1 - u), 0, by
      linear_combination ((1 - e₂) * b1 * f - (1 - e₂) * b1 - π * f + 2 * π) * hu2 - u * huπ⟩⟩
  have he3' : e₃ * e₃ = e₃ := he3
  obtain ⟨c3, hc3⟩ := Ideal.mem_span_singleton'.mp h3
  obtain ⟨d3, hd3⟩ := Ideal.mem_span_singleton'.mp h3'
  refine ⟨Ideal.Quotient.mk _ (e₁ + u * e₃), ?_, ?_, ?_⟩
  · show Ideal.Quotient.mk _ (e₁ + u * e₃) * Ideal.Quotient.mk _ (e₁ + u * e₃) =
      Ideal.Quotient.mk _ (e₁ + u * e₃)
    rw [← map_mul]
    exact congrArg (Ideal.Quotient.mk _)
      (by linear_combination he1' + 2 * e₃ * he1u + e₃ ^ 2 * hu2 + u * he3')
  · refine Ideal.mem_span_singleton'.mpr ⟨Ideal.Quotient.mk _ (c3 * u), ?_⟩
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton']
    exact ⟨-a1, by linear_combination -ha1 - u * hc3 + (c3 * g - c3 - e₃ * f + e₃) * hu2⟩
  · refine Ideal.mem_span_singleton'.mpr ⟨Ideal.Quotient.mk _ (d3 * u), ?_⟩
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {π})), ← map_sub, ← map_mul, ← map_mul, Ideal.Quotient.eq,
      Ideal.mem_span_singleton']
    exact ⟨-((1 - e₁) * a2), by
      linear_combination -(1 - e₁) * ha2 - g * hu - u * hd3 + (d3 * f - d3 - (1 - e₃) * g + (1 - e₃)) * hu2⟩

end GlobalTheory.CompanionTheory.ValQuot
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodBaseChange
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.GoodBaseChange

theorem good_baseChange : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (r : ℕ → A) (K₁ K₀ : Type) [AddCommGroup K₁] [Module A K₁] [AddCommGroup K₀] [Module A K₀] (d : K₁ →ₗ[A] K₀), Good p r d → Good p (fun k => algebraMap A B (r k)) (d.baseChange B) := by
  intro p _ A _ B _ _ r K₁ K₀ _ _ _ _ d hd
  intro C _ _ hC w hw k
  letI : Algebra A C := Algebra.compHom C (algebraMap A B)
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let e₁ := AlgebraTensorModule.cancelBaseChange A B C C K₁
  let e₀ := AlgebraTensorModule.cancelBaseChange A B C C K₀
  have hnat : ∀ v, e₀ ((d.baseChange B).lTensor C v) = d.lTensor C (e₁ v) := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b x =>
        simp [e₀, e₁, LinearMap.baseChange_tmul, AlgebraTensorModule.cancelBaseChange_tmul]
      | add y y' h h' => simp only [tmul_add, map_add (f := _), h, h']
    | add v v' h h' => simp only [map_add (f := _), h, h']
  have hw' : d.lTensor C (e₁ w) = 0 := by rw [← hnat, hw, map_zero]
  have hmem := hd C hC (e₁ w) hw' k
  have hsmul : r k • e₁ w = e₁ (algebraMap A B (r k) • w) := by
    rw [← algebraMap_smul C (algebraMap A B (r k)) w, map_smul, algebraMap_smul]
    rfl
  have key : ∀ u : C ⊗[A] LinearMap.ker d,
      e₁.symm ((LinearMap.ker d).subtype.lTensor C u) ∈
        LinearMap.range ((LinearMap.ker (d.baseChange B)).subtype.lTensor C) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul c x =>
      have hx : (1 : B) ⊗ₜ[A] (x : K₁) ∈ LinearMap.ker (d.baseChange B) := by
        simp [LinearMap.baseChange_tmul, x.2]
      refine ⟨c ⊗ₜ ⟨_, hx⟩, ?_⟩
      simp [e₁, AlgebraTensorModule.cancelBaseChange_symm_tmul]
    | add u u' h h' => rw [map_add (f := _), map_add (f := _)]; exact Submodule.add_mem _ h h'
  obtain ⟨u, hu⟩ := hmem
  have := key u
  rw [hu, hsmul, LinearEquiv.symm_apply_apply] at this
  exact this

end GlobalTheory.CompanionTheory.GoodBaseChange
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectivePreservesClosednessComparability
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectivePreservesClosednessComparability
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.SurjPass

theorem aic_of_surjective {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T)
    (hφ : Function.Surjective φ) (h : Aic (S := S)) : Aic (S := T) := by
  intro P hP hdeg
  rcases subsingleton_or_nontrivial T with hT | hT
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨Q, hQ, hQdeg, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.lifts_iff_coeff_lifts P).mpr fun n => hφ (P.coeff n)) hP
  obtain ⟨x, hx⟩ := h Q hQm (hQdeg ▸ hdeg)
  refine ⟨φ x, ?_⟩
  rw [← hQ, Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_hom, hx.eq_zero, map_zero]

theorem comparable_of_surjective {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T)
    (hφ : Function.Surjective φ) (h : Val0 (S := S)) : Val0 (S := T) := by
  intro f g
  obtain ⟨f', rfl⟩ := hφ f
  obtain ⟨g', rfl⟩ := hφ g
  obtain ⟨e, he, h1, h2⟩ := h f' g'
  refine ⟨φ e, ?_, ?_, ?_⟩
  · unfold IsIdempotentElem
    rw [← map_mul, he.eq]
  · rw [Ideal.mem_span_singleton] at h1 ⊢
    rw [← map_mul]
    exact map_dvd φ h1
  · rw [Ideal.mem_span_singleton] at h2 ⊢
    rw [← map_one φ, ← map_sub, ← map_mul]
    exact map_dvd φ h2

theorem absolutely_closed_comparable_surjective : ∀ {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T),
    Function.Surjective φ → (Aic (S := S) → Aic (S := T)) ∧ (Val0 (S := S) → Val0 (S := T)) := by
  intro S _ T _ φ hφ
  exact ⟨aic_of_surjective φ hφ, comparable_of_surjective φ hφ⟩

end GlobalTheory.CompanionTheory.SurjPass
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectivePreservesClosednessComparabilityStatement
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_preserves_closedness_comparability : ∀ {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T), Function.Surjective φ → (Aic (S := S) → Aic (S := T)) ∧ (Val0 (S := S) → Val0 (S := T)) := by
  first | exact @GlobalTheory.CompanionTheory.SurjPass.absolutely_closed_comparable_surjective | exact GlobalTheory.CompanionTheory.SurjPass.absolutely_closed_comparable_surjective | (intros; apply GlobalTheory.CompanionTheory.SurjPass.absolutely_closed_comparable_surjective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyClosedPolynomialSplits
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyClosedPolynomialSplits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.MonicSplit

open Polynomial

theorem exists_multiset_of_natDegree_eq {S : Type} [CommRing S] (hS : Aic (S := S)) (d : ℕ) :
    ∀ P : Polynomial S, P.Monic → P.natDegree = d →
      ∃ s : Multiset S, P = (s.map fun b => X - C b).prod := by
  rcases subsingleton_or_nontrivial S with hS' | hS'
  · intro P _ _
    exact ⟨0, Subsingleton.elim _ _⟩
  · induction d with
    | zero =>
      intro P hP hd
      refine ⟨0, ?_⟩
      rw [Multiset.map_zero, Multiset.prod_zero]
      exact Polynomial.eq_one_of_monic_natDegree_zero hP hd
    | succ d ih =>
      intro P hP hd
      obtain ⟨x, hx⟩ := hS P hP (by omega)
      have hmul : (X - C x) * (P /ₘ (X - C x)) = P := Polynomial.mul_divByMonic_eq_iff_isRoot.2 hx
      have hQ : (P /ₘ (X - C x)).Monic :=
        Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C x) (by rw [hmul]; exact hP)
      have hQd : (P /ₘ (X - C x)).natDegree = d := by
        have h := (Polynomial.monic_X_sub_C x).natDegree_mul hQ
        rw [hmul, Polynomial.natDegree_X_sub_C, hd] at h
        omega
      obtain ⟨s, hs⟩ := ih _ hQ hQd
      refine ⟨x ::ₘ s, ?_⟩
      rw [Multiset.map_cons, Multiset.prod_cons, ← hs, hmul]

theorem monic_splits : ∀ {S : Type} [CommRing S], Aic (S := S) → ∀ P : Polynomial S, P.Monic →
    ∃ s : Multiset S, P = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by
  intro S _ hS P hP
  exact exists_multiset_of_natDegree_eq hS _ P hP rfl

end GlobalTheory.CompanionTheory.MonicSplit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyClosedPolynomialSplitsStatement
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absolutely_closed_polynomial_splits : ∀ {S : Type} [CommRing S] , Aic (S := S) → ∀ P : Polynomial S, P.Monic → ∃ s : Multiset S, P = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by
  first | exact @GlobalTheory.CompanionTheory.MonicSplit.monic_splits | exact GlobalTheory.CompanionTheory.MonicSplit.monic_splits | (intros; apply GlobalTheory.CompanionTheory.MonicSplit.monic_splits <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsComplNonZeroDivisor
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonZeroDivisorOfDenseOfStrict
namespace GlobalTheory.CompanionTheory.ComplReg

theorem nonZeroDivisor_of_dense_of_strict {B T : Type} [CommRing B] [CommRing T] (π : B)
    (g : B →+* T) (hH : IsHausdorff (Ideal.span {g π}) T)
    (hd : ∀ (M : ℕ) (y : T), ∃ x, y - g x ∈ Ideal.span {g π ^ M})
    (hk : ∀ (M : ℕ) (x : B), g x ∈ Ideal.span {g π ^ M} → x ∈ Ideal.span {π ^ M})
    (hπ : π ∈ nonZeroDivisors B) : g π ∈ nonZeroDivisors T := by
  have key : ∀ t : T, t * g π = 0 → ∀ M : ℕ, t ∈ Ideal.span {g π ^ M} := by
    intro t ht M
    obtain ⟨x, hx⟩ := hd M t
    rw [Ideal.mem_span_singleton] at hx
    obtain ⟨d, hd'⟩ := hx
    have hxπ : x * π ∈ Ideal.span {π ^ (M + 1)} := by
      apply hk (M + 1) (x * π)
      rw [Ideal.mem_span_singleton]
      exact ⟨-d, by rw [map_mul]; linear_combination ht - g π * hd'⟩
    rw [Ideal.mem_span_singleton] at hxπ
    obtain ⟨c, hc⟩ := hxπ
    have h0 : (x - π ^ M * c) * π = 0 := by
      rw [sub_mul, hc]
      ring
    have hxeq : x = π ^ M * c := sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hπ).2 _ h0)
    have hgx : g x = g π ^ M * g c := by
      rw [hxeq, map_mul, map_pow]
    rw [Ideal.mem_span_singleton]
    exact ⟨d + g c, by linear_combination hd' + hgx⟩
  have main : ∀ t : T, t * g π = 0 → t = 0 := by
    intro t ht
    refine IsHausdorff.haus hH t (fun n => ?_)
    rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact key t ht n
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun t ht => main t (by rwa [mul_comm] at ht), main⟩

end GlobalTheory.CompanionTheory.ComplReg
end

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.ComplReg

theorem isCompl_nonZeroDivisor : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T),
    IsCompl π g → π ∈ nonZeroDivisors B → g π ∈ nonZeroDivisors T := by
  intro B _ T _ π g hC hπ
  exact nonZeroDivisor_of_dense_of_strict π g hC.compl.toIsHausdorff hC.surj hC.inj hπ

end GlobalTheory.CompanionTheory.ComplReg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompletionComplete
set_option autoImplicit false

noncomputable section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.AdicCompl

theorem completion_complete (B : Type) [CommRing B] (π : B) :
    IsAdicComplete (Ideal.span {algebraMap B (AdicCompletion (Ideal.span {π}) B) π})
      (AdicCompletion (Ideal.span {π}) B) := by
  have h := AdicCompletion.isAdicComplete (R := B) (I := Ideal.span {π}) (M := B)
    (Submodule.fg_span_singleton _)
  rw [← IsAdicComplete.map_algebraMap_iff (S := AdicCompletion (Ideal.span {π}) B)] at h
  simpa [Ideal.map_span] using h

theorem completion_surj (B : Type) [CommRing B] (π : B) (M : ℕ)
    (y : AdicCompletion (Ideal.span {π}) B) :
    ∃ x : B, y - algebraMap B (AdicCompletion (Ideal.span {π}) B) x ∈
      Ideal.span {algebraMap B (AdicCompletion (Ideal.span {π}) B) π ^ M} := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (y.1 M)
  refine ⟨a, ?_⟩
  have hx : y - algebraMap B (AdicCompletion (Ideal.span {π}) B) a ∈
      ((Ideal.span {π}) ^ M).map (algebraMap B (AdicCompletion (Ideal.span {π}) B)) := by
    rw [← Submodule.restrictScalars_mem B, ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton π),
      AdicCompletion.algebraMap_apply]
    simpa [AdicCompletion.eval, sub_eq_zero] using ha.symm
  rwa [Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow] at hx

theorem completion_inj (B : Type) [CommRing B] (π : B) (M : ℕ) (x : B)
    (h : algebraMap B (AdicCompletion (Ideal.span {π}) B) x ∈
      Ideal.span {algebraMap B (AdicCompletion (Ideal.span {π}) B) π ^ M}) :
    x ∈ Ideal.span {π ^ M} := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  have h1 := congrArg (AdicCompletion.evalₐ (Ideal.span {π}) M) hz
  have hf : Ideal.Quotient.mk (Ideal.span {π} ^ M) (π ^ M) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (by
      rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
  rw [map_mul, map_pow, AlgHom.commutes, ← map_pow, AlgHom.commutes, Ideal.Quotient.algebraMap_eq,
    hf, mul_zero] at h1
  rw [← Ideal.span_singleton_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1.symm

theorem exists_isCompl : ∀ (B : Type) [CommRing B] (π : B),
    ∃ (T : Type) (_ : CommRing T) (g : B →+* T), IsCompl π g := by
  intro B _ π
  exact ⟨AdicCompletion (Ideal.span {π}) B, inferInstance,
    algebraMap B (AdicCompletion (Ideal.span {π}) B),
    { compl := completion_complete B π
      surj := completion_surj B π
      inj := completion_inj B π }⟩

end GlobalTheory.CompanionTheory.AdicCompl
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerIdealTorsionFree
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.DivPow

theorem exists_gamma {S : Type} [CommRing S] (I : Ideal S) (z : S)
    (h : ∀ k : ℕ, k ≠ 0 → ∃ y ∈ I, (k.factorial : S) * y = z ^ k) :
    ∃ γ : ℕ → S, (∀ i, i ≠ 0 → γ i ∈ I) ∧ ∀ i, (i.factorial : S) * γ i = z ^ i := by
  classical
  refine ⟨fun i => if hi : i = 0 then 1 else (h i hi).choose, ?_, ?_⟩
  · intro i hi
    simpa [hi] using (h i hi).choose_spec.1
  · intro i
    by_cases hi : i = 0
    · subst hi
      simp
    · simpa [hi] using (h i hi).choose_spec.2

theorem pdI_span : ∀ {S : Type} [CommRing S], TF (S := S) → ∀ s : Set S,
    (∀ x ∈ s, ∀ k : ℕ, k ≠ 0 → ∃ y ∈ Ideal.span s, (k.factorial : S) * y = x ^ k) →
    PdI (Ideal.span s) := by
  intro S _ _ s h x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    intro k hk
    exact ⟨0, Ideal.zero_mem _, by simp [zero_pow hk]⟩
  | smul a x _ ih =>
    intro k hk
    obtain ⟨y, hy, e⟩ := ih k hk
    refine ⟨a ^ k * y, Ideal.mul_mem_left _ _ hy, ?_⟩
    rw [smul_eq_mul, mul_pow, ← e]
    ring
  | add x x' _ _ ih ih' =>
    intro k hk
    obtain ⟨γ, hγ, e⟩ := exists_gamma _ x ih
    obtain ⟨γ', hγ', e'⟩ := exists_gamma _ x' ih'
    refine ⟨∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, γ p.1 * γ' p.2, ?_, ?_⟩
    · refine Ideal.sum_mem _ ?_
      rintro ⟨i, j⟩ hij
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      by_cases hi : i = 0
      · have hj : j ≠ 0 := by
          rintro rfl
          exact hk (by omega)
        exact Ideal.mul_mem_left _ _ (hγ' j hj)
      · exact Ideal.mul_mem_right _ _ (hγ i hi)
    · rw [Finset.mul_sum, (Commute.all x x').add_pow']
      refine Finset.sum_congr rfl ?_
      rintro ⟨i, j⟩ hij
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      subst hij
      rw [← e i, ← e' j, nsmul_eq_mul, Nat.choose_symm_add, ← Nat.add_choose_mul_factorial_mul_factorial i j]
      push_cast
      ring

end GlobalTheory.CompanionTheory.DivPow
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfLTensorSubtypeEqZero
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Dblock

theorem smul_eq_zero_of_lTensor_subtype_eq_zero :
    ∀ (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] (r : ℕ → R) (N : Type)
      [AddCommGroup N] [Module R N] (K : Type) [AddCommGroup K] [Module R K] (I : Submodule R K),
      (∀ (a : R) (x : K), a ≠ 0 → a • x ∈ I → ∀ k, r k • x ∈ I) →
      ∀ w : N ⊗[R] I, I.subtype.lTensor N w = 0 → ∀ k, r k • w = 0 := by
  intro R _ _ _ r N _ _ K _ _ I hI w hw k
  let I' : Submodule R K :=
    { carrier := {x | ∃ a : R, a ≠ 0 ∧ a • x ∈ I}
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      add_mem' := by
        rintro x y ⟨a, ha, hax⟩ ⟨b, hb, hby⟩
        refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
        rw [smul_add]
        refine I.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact I.smul_mem _ hax
        · rw [mul_smul]; exact I.smul_mem _ hby
      smul_mem' := by
        rintro c x ⟨a, ha, hax⟩
        refine ⟨a, ha, ?_⟩
        rw [smul_comm]; exact I.smul_mem _ hax }
  have hle : I ≤ I' := fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩
  have hflat : Module.Flat R (K ⧸ I') := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := I'.mkQ_surjective y
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hy
    have hax : (a : R) • x ∈ I' := by
      rw [← Submodule.Quotient.mk_eq_zero]
      simpa [Submonoid.smul_def] using ha
    obtain ⟨b, hb, hbx⟩ := hax
    have hx : x ∈ I' := ⟨b * a, mul_ne_zero hb (nonZeroDivisors.ne_zero a.2), by
      rw [mul_smul]; exact hbx⟩
    simpa using (Submodule.Quotient.mk_eq_zero I').2 hx
  have hinj : Function.Injective (I'.subtype.lTensor N) :=
    LinearMap.lTensor_injective_of_exact_of_flat I'.mkQ I'.mkQ_surjective I'.subtype
      I'.injective_subtype (LinearMap.exact_subtype_mkQ I') N
  let ι : I →ₗ[R] I' := Submodule.inclusion hle
  let φ : I' →ₗ[R] I := LinearMap.codRestrict I (r k • I'.subtype) (fun x => by
    obtain ⟨a, ha, hax⟩ := x.2
    exact hI a x ha hax k)
  have h1 : ι.lTensor N w = 0 := by
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    exact hw
  have hcomp : φ ∘ₗ ι = r k • LinearMap.id := by
    ext x
    rfl
  have h2 : φ.lTensor N (ι.lTensor N w) = r k • w := by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hcomp, LinearMap.lTensor_smul,
      LinearMap.lTensor_id]
    rfl
  rw [← h2, h1, map_zero]

end GlobalTheory.CompanionTheory.Dblock
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleOfPerm
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleOfPerm
open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.ShuffleWords

variable {T : Type u}

theorem interleave_exchange {u v w : List T} (h : Interleave u v w) :
    ∀ {u' x : List T}, Interleave u' x v →
      ∃ v', Interleave u' v' w ∧ Interleave u x v' := by
  induction h with
  | nil =>
    intro u' x h'
    cases h'
    exact ⟨[], Interleave.nil, Interleave.nil⟩
  | @left a u v w _ ih =>
    intro u' x h'
    obtain ⟨v', h₁, h₂⟩ := ih h'
    exact ⟨a :: v', Interleave.right h₁, Interleave.left h₂⟩
  | @right a u v w _ ih =>
    intro u' x h'
    cases h' with
    | left h' =>
      obtain ⟨v', h₁, h₂⟩ := ih h'
      exact ⟨v', Interleave.left h₁, h₂⟩
    | right h' =>
      obtain ⟨v', h₁, h₂⟩ := ih h'
      exact ⟨a :: v', Interleave.right h₁, Interleave.right h₂⟩

theorem shuffle_swap {a b : List T} {us : List (List T)} {w : List T}
    (h : Shuffle (a :: b :: us) w) : Shuffle (b :: a :: us) w := by
  cases h with
  | cons hv hw =>
    cases hv with
    | cons hx hv =>
      obtain ⟨v', h₁, h₂⟩ := interleave_exchange hw hv
      exact Shuffle.cons (Shuffle.cons hx h₂) h₁

theorem shuffle_perm {T : Type u} (us us' : List (List T)) (w : List T)
    (h : Shuffle us w) (hp : us.Perm us') : Shuffle us' w := by
  induction hp generalizing w with
  | nil => exact h
  | cons a _ ih =>
    cases h with
    | cons hv hw => exact Shuffle.cons (ih _ hv) hw
  | swap a b l => exact shuffle_swap h
  | trans _ _ ih₁ ih₂ => exact ih₂ _ (ih₁ _ h)

end GlobalTheory.CompanionTheory.ShuffleWords
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleOfPermStatement
open Zc.Comb
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shuffle_of_perm : ∀ {T : Type u} (us us' : List (List T)) (w : List T), Shuffle us w → us.Perm us' → Shuffle us' w := by
  first | exact @GlobalTheory.CompanionTheory.ShuffleWords.shuffle_perm | exact GlobalTheory.CompanionTheory.ShuffleWords.shuffle_perm | (intros; apply GlobalTheory.CompanionTheory.ShuffleWords.shuffle_perm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingHermitianSimultaneousDiag
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingHermitianSimultaneousDiag
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.SimDiag

theorem exists_unitary_isDiag {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) ℂ))
    (hH : ∀ A ∈ S, Aᴴ = A) (hC : ∀ A ∈ S, ∀ B ∈ S, A * B = B * A) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A ∈ S, (Uᴴ * A * U).IsDiag := by
  classical
  let L : Matrix (Fin n) (Fin n) ℂ → (EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :=
    fun M => Matrix.toEuclideanLin M
  have hL : ∀ M v, L M v = WithLp.toLp 2 (M *ᵥ WithLp.ofLp v) := fun _ _ => rfl
  obtain ⟨m, b, hb⟩ := Formalism.IndefR.EigenDecomposition.exists_onb_of_commuting (L '' S)
    (by
      rintro _ ⟨M, hM, rfl⟩ _ ⟨N, hN, rfl⟩
      refine LinearMap.ext fun v => ?_
      change L M (L N v) = L N (L M v)
      simp only [hL, Matrix.mulVec_mulVec, hC M hM N hN])
    (by
      rintro _ ⟨M, hM, rfl⟩
      refine ⟨M, hM, ?_⟩
      change Matrix.toEuclideanLin M = LinearMap.adjoint (Matrix.toEuclideanLin M)
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hH M hM])
  have hm : m = n := by
    have := Module.finrank_eq_card_basis b.toBasis
    simpa [finrank_euclideanSpace] using this.symm
  subst hm
  have hinner : ∀ j k, ∑ i, star (WithLp.ofLp (b j) i) * WithLp.ofLp (b k) i =
      if j = k then 1 else 0 := by
    intro j k
    have := orthonormal_iff_ite.1 b.orthonormal j k
    rw [PiLp.inner_apply] at this
    simpa [RCLike.inner_apply, mul_comm] using this
  let U : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i k => WithLp.ofLp (b k) i
  refine ⟨U, ?_, fun A hA => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    ext j k
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, U, Matrix.of_apply]
    exact hinner j k
  · intro j k hjk
    obtain ⟨μ, hμ⟩ := hb k (L A) ⟨A, hA, rfl⟩
    have hv : A *ᵥ WithLp.ofLp (b k) = μ • WithLp.ofLp (b k) := by
      have := congrArg WithLp.ofLp hμ
      simpa [hL] using this
    have hAU : ∀ i, (A * U) i k = μ * WithLp.ofLp (b k) i := by
      intro i
      have := congrFun hv i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, U] using this
    have h0 := hinner j k
    rw [if_neg hjk] at h0
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp_rw [hAU]
    calc ∑ i, Uᴴ j i * (μ * WithLp.ofLp (b k) i)
        = μ * ∑ i, star (WithLp.ofLp (b j) i) * WithLp.ofLp (b k) i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Matrix.conjTranspose_apply, U, Matrix.of_apply]
          ring
      _ = 0 := by rw [h0, mul_zero]

end GlobalTheory.CompanionTheory.SimDiag
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingHermitianSimultaneousDiagStatement
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_hermitian_simultaneous_diag : ∀ {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) ℂ)), (∀ A ∈ S, Aᴴ = A) → (∀ A ∈ S, ∀ B ∈ S, A * B = B * A) → ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A ∈ S, (Uᴴ * A * U).IsDiag := by
  first | exact @GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag | exact GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag | (intros; apply GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.TubeFourier

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def pt (x y : ℝ × ℝ) : ℂ × ℂ := (⟨x.1, y.1⟩, ⟨x.2, y.2⟩)

def dot (l : ℂ × ℂ) (t : ℝ × ℝ) : ℂ := l.1 * t.1 + l.2 * t.2

def rdot (x t : ℝ × ℝ) : ℝ := x.1 * t.1 + x.2 * t.2

def phi (G : ℂ × ℂ → X) (x t : ℝ × ℝ) : X :=
  ∫ y : ℝ × ℝ, Complex.exp (-dot (pt x y) t) • G (pt x y)

def inv (φ : ℝ × ℝ → X) (l : ℂ × ℂ) : X :=
  (((2 * Real.pi) ^ 2 : ℂ)⁻¹) • ∫ t : ℝ × ℝ, Complex.exp (dot l t) • φ t

def gauss (F : ℂ × ℂ → X) (l : ℂ × ℂ) : X := Complex.exp (l.1 ^ 2 + l.2 ^ 2) • F l

structure GaussTube (G : ℂ × ℂ → X) (Ω : Set (ℝ × ℝ)) : Prop where
  hol : LineHol G (tube Ω)
  cont : ContinuousOn G (tube Ω)
  decay : ∀ C ⊆ Ω, IsCompact C → ∃ M : ℝ, ∀ l ∈ tube C,
    ‖G l‖ ≤ M * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2))

def ExpDecay {T : Type} [TopologicalSpace T] (φ : ℝ × ℝ → T → X) : Prop :=
  ∀ (x₀ : ℝ × ℝ) (g : T), ∃ ε : ℝ, 0 < ε ∧ ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ x : ℝ × ℝ, |x.1 - x₀.1| ≤ ε → |x.2 - x₀.2| ≤ ε →
    ∀ g' ∈ U, ∀ t : ℝ × ℝ, ‖φ t g'‖ ≤ M * Real.exp (-rdot x t) * Real.exp (-ε * (|t.1| + |t.2|))

theorem norm_exp_sq (l : ℂ × ℂ) : ‖Complex.exp (l.1 ^ 2 + l.2 ^ 2)‖ =
    Real.exp (l.1.re ^ 2 + l.2.re ^ 2) * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp [sq]
  ring

theorem gauss_bound {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω C : Set (ℝ × ℝ)} (h : TubeGood F Ω)
    (hC : C ⊆ Ω) (hc : IsCompact C) (g : T) : ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ g' ∈ U, ∀ l ∈ tube C,
      ‖gauss (F · g') l‖ ≤ M * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by
  obtain ⟨U, hU, M, hM⟩ := h.bdd C hC hc g
  obtain ⟨B, hB⟩ := (hc.image (f := fun x : ℝ × ℝ => x.1 ^ 2 + x.2 ^ 2) (by fun_prop)).bddAbove
  refine ⟨U, hU, Real.exp B * |M|, fun g' hg' l hl => ?_⟩
  have h1 : l.1.re ^ 2 + l.2.re ^ 2 ≤ B := hB ⟨(l.1.re, l.2.re), hl, rfl⟩
  have h2 : ‖F l g'‖ ≤ |M| := (hM l hl g' hg').trans (le_abs_self M)
  simp only [gauss]
  rw [norm_smul, norm_exp_sq]
  have h3 : Real.exp (l.1.re ^ 2 + l.2.re ^ 2) ≤ Real.exp B := Real.exp_le_exp.2 h1
  have h4 := Real.exp_pos (-(l.1.im ^ 2 + l.2.im ^ 2))
  calc _ = Real.exp (l.1.re ^ 2 + l.2.re ^ 2) * ‖F l g'‖ * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by ring
    _ ≤ Real.exp B * |M| * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by gcongr

theorem gaussTube_of_tubeGood {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω : Set (ℝ × ℝ)}
    (h : TubeGood F Ω) (g : T) : GaussTube (gauss (F · g)) Ω := by
  refine ⟨?_, ?_, ?_⟩
  · intro p v
    have h1 : Differentiable ℂ fun τ : ℂ => Complex.exp ((p + τ • v).1 ^ 2 + (p + τ • v).2 ^ 2) := by
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      fun_prop
    exact h1.differentiableOn.smul (h.hol g p v)
  · have h1 : ContinuousOn (fun l : ℂ × ℂ => F l g) (tube Ω) :=
      h.cont.comp (f := fun l : ℂ × ℂ => (l, g)) (by fun_prop) fun l hl => ⟨hl, trivial⟩
    exact ContinuousOn.smul (by fun_prop) h1
  · intro C hC hc
    obtain ⟨U, hU, M, hM⟩ := gauss_bound h hC hc g
    exact ⟨M, fun l hl => hM g (mem_of_mem_nhds hU) l hl⟩

end GlobalTheory.CompanionTheory.TubeFourier
end
end
