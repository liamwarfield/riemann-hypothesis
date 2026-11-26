module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.RealMetaplecticRepresentationHolds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticHolPartDetNeZeroAndIsSymm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticHolPartDetNeZeroAndIsSymm
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory.SympBlocks

open scoped ComplexOrder

theorem herm_identity {l : Type} [Fintype l] [DecidableEq l] (A B C D : Matrix l l ℂ)
    (h1 : Aᵀ * C = Cᵀ * A) (h2 : Bᵀ * D = Dᵀ * B) (h3 : Aᵀ * D - Cᵀ * B = 1) :
    (Aᵀ + I • Bᵀ) * (C - I • D) - (Cᵀ + I • Dᵀ) * (A - I • B) = (-(2 * I)) • (1 : Matrix l l ℂ) := by
  have h4 : Dᵀ * A - Bᵀ * C = 1 := by
    simpa [transpose_sub, transpose_mul] using congrArg Matrix.transpose h3
  have e3 : Aᵀ * D = 1 + Cᵀ * B := by rw [← h3]; abel
  have e4 : Dᵀ * A = 1 + Bᵀ * C := by rw [← h4]; abel
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul,
    I_mul_I]
  rw [← h1, ← h2, e3, e4]
  module

theorem symm_identity {l : Type} [Fintype l] [DecidableEq l] (A B C D : Matrix l l ℂ)
    (h1 : Aᵀ * C = Cᵀ * A) (h2 : Bᵀ * D = Dᵀ * B) (h3 : Aᵀ * D - Cᵀ * B = 1) :
    (A - I • B)ᵀ * (C - I • D) = (C - I • D)ᵀ * (A - I • B) := by
  have h4 : Dᵀ * A - Bᵀ * C = 1 := by
    simpa [transpose_sub, transpose_mul] using congrArg Matrix.transpose h3
  have e3 : Aᵀ * D = 1 + Cᵀ * B := by rw [← h3]; abel
  have e4 : Dᵀ * A = 1 + Bᵀ * C := by rw [← h4]; abel
  simp only [transpose_sub, transpose_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rw [← h1, ← h2, e3, e4]
  module

end GlobalTheory.SympBlocks

namespace GlobalTheory.SympBlocks

open scoped ComplexOrder

theorem det_ne_zero_and_isSymm : ∀ (l : Type) [Fintype l] [DecidableEq l]
    (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ),
    (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) →
    (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) →
    s ∈ Matrix.symplecticGroup l ℝ → P.det ≠ 0 ∧ (-(Q * P⁻¹)).IsSymm := by
  intro l _ _ s P Q hP hQ hs
  have hs' : fromBlocks s.toBlocks₁₁ s.toBlocks₁₂ s.toBlocks₂₁ s.toBlocks₂₂ ∈
      Matrix.symplecticGroup l ℝ := by rwa [fromBlocks_toBlocks]
  obtain ⟨r1, r2, r3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 hs'
  set A := s.toBlocks₁₁.map Complex.ofRealHom
  set B := s.toBlocks₁₂.map Complex.ofRealHom
  set C := s.toBlocks₂₁.map Complex.ofRealHom
  set D := s.toBlocks₂₂.map Complex.ofRealHom
  have h1 : Aᵀ * C = Cᵀ * A := by
    simp only [A, C, ← transpose_map, ← Matrix.map_mul, r1]
  have h2 : Bᵀ * D = Dᵀ * B := by
    simp only [B, D, ← transpose_map, ← Matrix.map_mul, r2]
  have h3 : Aᵀ * D - Cᵀ * B = 1 := by
    simp only [A, B, C, D, ← transpose_map, ← Matrix.map_mul]
    rw [← Matrix.map_sub _ (fun a b => map_sub Complex.ofRealHom a b), r3]; simp
  have ePQ : P = A - I • B ∧ Q = C - I • D := by
    constructor <;> ext a b <;> simp [A, B, C, D, hP, hQ, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁,
      toBlocks₂₂]
  obtain ⟨eP, eQ⟩ := ePQ
  have hPc : Pᴴ = Aᵀ + I • Bᵀ := by
    rw [eP]; ext a b; simp [A, B, conjTranspose_apply, transpose_apply]
  have hQc : Qᴴ = Cᵀ + I • Dᵀ := by
    rw [eQ]; ext a b; simp [C, D, conjTranspose_apply, transpose_apply]
  have hH : Pᴴ * Q - Qᴴ * P = (-(2 * I)) • (1 : Matrix l l ℂ) := by
    rw [hPc, hQc, eP, eQ]; exact herm_identity A B C D h1 h2 h3
  have hS : Pᵀ * Q = Qᵀ * P := by
    rw [eP, eQ]; exact symm_identity A B C D h1 h2 h3
  have hdet : P.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    have key : star v ⬝ᵥ ((Pᴴ * Q - Qᴴ * P) *ᵥ v) = 0 := by
      rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv,
        Matrix.mulVec_zero, dotProduct_zero, sub_zero, dotProduct_mulVec, ← star_mulVec, hv,
        star_zero, zero_dotProduct]
    rw [hH, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at key
    have h2I : (-(2 * I)) ≠ 0 := by simp [I_ne_zero]
    have : star v ⬝ᵥ v = 0 := (mul_eq_zero.1 key).resolve_left h2I
    exact hv0 (dotProduct_star_self_eq_zero.1 this)
  refine ⟨hdet, ?_⟩
  have hu : IsUnit P.det := isUnit_iff_ne_zero.2 hdet
  have huT : IsUnit Pᵀ.det := by rwa [det_transpose]
  apply Matrix.IsSymm.neg
  unfold Matrix.IsSymm
  rw [transpose_mul, transpose_nonsing_inv]
  calc Pᵀ⁻¹ * Qᵀ = Pᵀ⁻¹ * (Qᵀ * P) * P⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = Pᵀ⁻¹ * (Pᵀ * Q) * P⁻¹ := by rw [hS]
    _ = Q * P⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ huT, Matrix.one_mul]

end GlobalTheory.SympBlocks
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticHolPartDetNeZeroAndIsSymmStatement
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_holPart_det_ne_zero_and_isSymm : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → s ∈ Matrix.symplecticGroup l ℝ → P.det ≠ 0 ∧ (-(Q * P⁻¹)).IsSymm := by
  first | exact @GlobalTheory.SympBlocks.det_ne_zero_and_isSymm | exact GlobalTheory.SympBlocks.det_ne_zero_and_isSymm | (intros; apply GlobalTheory.SympBlocks.det_ne_zero_and_isSymm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticCoverWeilRepresentation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticGaussianNormalised
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticGaussianNormalised
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory

theorem metaplecticGaussianNormalised : ∀ (l : Type) [Fintype l] [DecidableEq l], ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G) (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l)) (φ : Sch l), IsCoveringMap pr ∧ Function.Surjective pr ∧ (∃ ε : G, ε ≠ 1 ∧ (∀ g, pr g = 1 ↔ g = 1 ∨ g = ε) ∧ ∀ f, om ε f = -f) ∧ (∀ f : L2 l, Continuous fun g => om g f) ∧ (∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l), om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) ∧ (∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) ∧ (∀ x : EuclideanSpace ℝ l, φ x = cexp (-π * ((x.ofLp ⬝ᵥ x.ofLp : ℝ) : ℂ))) ∧ (∀ j : l, dRho (Pi.single (.inl j) 1) φ = I • dRho (Pi.single (.inr j) 1) φ) ∧ ∀ (g : G) (P : Matrix l l ℂ), (∀ a b, P a b = ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) → omS g φ 0 ^ 2 * P.det = 1 := by
  intro l _ _
  have hS : CompanionTheory.ThKR.Mp.SecEx l := CompanionTheory.ThKR.Mp.secEx_of CompanionTheory.ThKR.Mp.mkElt CompanionTheory.ThKR.Mp.nrmUp
  have hO : CompanionTheory.ThKR.Mp.Surj l := CompanionTheory.ThKR.Mp.surj_of CompanionTheory.ThKR.Mp.ddNe hS
  have hC : CompanionTheory.ThKR.Mp.Cover l :=
    CompanionTheory.ThKR.Mp.cover_of CompanionTheory.ThKR.Mp.topG hO CompanionTheory.ThKR.Mp.ker hS CompanionTheory.ThKR.Mp.secDer
  haveI : IsTopologicalGroup (CompanionTheory.ThKR.Mp.G l) := CompanionTheory.ThKR.Mp.topG
  refine ⟨CompanionTheory.ThKR.Mp.G l, inferInstance, inferInstance, inferInstance, CompanionTheory.ThKR.Mp.pr, CompanionTheory.ThKR.Mp.om,
    CompanionTheory.ThKR.Mp.omS, CompanionTheory.ThKR.Mp.MpA.gs l, hC, hO, CompanionTheory.ThKR.Mp.ker, CompanionTheory.ThKR.Mp.continuous_om,
    CompanionTheory.ThKR.Mp.om_rho, CompanionTheory.ThKR.Mp.om_sch, ?_, ?_, ?_⟩
  · intro x
    rw [CompanionTheory.ThKR.Mp.MpA.gs, GroundTheory.Global.gaussianSchwartz_apply]
    have e : ‖x‖ ^ 2 = x.ofLp ⬝ᵥ x.ofLp := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [dotProduct, sq]
    rw [e, Complex.ofReal_exp]
    push_cast
    ring_nf
  · intro j
    have h := CompanionTheory.ThKR.Mp.MpA.ann_gs (l := l) j
    have e1 : ((1 : CompanionTheory.ThKR.Mp.Sp l) : CompanionTheory.ThKR.Mp.Mat l) = 1 := rfl
    rw [e1, one_mulVec, one_mulVec] at h
    exact h
  · intro g P hP
    have h := CompanionTheory.ThKR.Mp.omS_nrm g 1 (CompanionTheory.ThKR.Mp.MpA.gs l) CompanionTheory.ThKR.Mp.MpA.ann_gs
    have e1 : ((1 : CompanionTheory.ThKR.Mp.Sp l) : CompanionTheory.ThKR.Mp.Mat l) = 1 := rfl
    rw [e1, Matrix.mul_one, CompanionTheory.ThKR.Mp.MpA.gs_zero, CompanionTheory.ThKR.Mp.MpA.dd_one, one_pow, one_mul] at h
    have eP : P = CompanionTheory.ThKR.Mp.upperParabolic (CompanionTheory.ThKR.Mp.pr g).1 := by
      ext a b; rw [hP]; rfl
    rw [eP]
    exact h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticGaussianNormalisedStatement
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metaplecticGaussianNormalisedAlt : ∀ (l : Type) [Fintype l] [DecidableEq l], ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G) (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l)) (φ : Sch l), IsCoveringMap pr ∧ Function.Surjective pr ∧ (∃ ε : G, ε ≠ 1 ∧ (∀ g, pr g = 1 ↔ g = 1 ∨ g = ε) ∧ ∀ f, om ε f = -f) ∧ (∀ f : L2 l, Continuous fun g => om g f) ∧ (∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l), om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) ∧ (∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) ∧ (∀ x : EuclideanSpace ℝ l, φ x = cexp (-π * ((x.ofLp ⬝ᵥ x.ofLp : ℝ) : ℂ))) ∧ (∀ j : l, dRho (Pi.single (.inl j) 1) φ = I • dRho (Pi.single (.inr j) 1) φ) ∧ ∀ (g : G) (P : Matrix l l ℂ), (∀ a b, P a b = ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) → omS g φ 0 ^ 2 * P.det = 1 := by
  first | exact @GlobalTheory.metaplecticGaussianNormalised | exact GlobalTheory.metaplecticGaussianNormalised | (intros; apply GlobalTheory.metaplecticGaussianNormalised <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzEqGaussianOfFderivEqMulVec
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzEqGaussianOfFderivEqMulVec
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory

theorem schwartz_eq_gaussian_of_fderiv_eq_mulVec :
    ∀ (l : Type) [Fintype l] [DecidableEq l] (τ : Matrix l l ℂ) (f : Sch l), τ.IsSymm →
      (∀ (a : l) (x : EuclideanSpace ℝ l),
        fderiv ℝ f x (EuclideanSpace.single a 1) = 2 * π * I * (τ *ᵥ fun i => (x i : ℂ)) a * f x) →
      ∀ x : EuclideanSpace ℝ l,
        f x = f 0 * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) := by
  intro l _ _ τ f _hτ H x
  set v : l → ℂ := fun i => (x i : ℂ) with hv
  set c : ℂ := v ⬝ᵥ τ *ᵥ v with hc
  have hx : x = ∑ a, x a • EuclideanSpace.single a (1 : ℝ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun l ℝ).toBasis.sum_repr x]
    simp
  have hD : ∀ t : ℝ, fderiv ℝ f (t • x) x = 2 * π * I * (t * c) * f (t • x) := by
    intro t
    rw [show fderiv ℝ f (t • x) x = fderiv ℝ f (t • x) (∑ a, x a • EuclideanSpace.single a (1 : ℝ)) from
      congrArg _ hx]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, H, Complex.real_smul]
    have hvt : (fun i => ((t • x) i : ℂ)) = (t : ℂ) • v := by
      funext i; simp [hv]
    rw [hvt, Matrix.mulVec_smul, hc, dotProduct]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, hv]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  set φ : ℝ → ℂ := fun t => f (t • x) * cexp (-(π * I * c) * ((t ^ 2 : ℝ) : ℂ)) with hφ
  have hφd : ∀ t : ℝ, HasDerivAt φ 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => f (t • x)) (fderiv ℝ f (t • x) ((1 : ℝ) • x)) t :=
      (f.differentiableAt (x := t • x)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const x)
    have h2 : HasDerivAt (fun t : ℝ => cexp (-(π * I * c) * ((t ^ 2 : ℝ) : ℂ)))
        (cexp (-(π * I * c) * ((t ^ 2 : ℝ) : ℂ)) * (-(π * I * c) * (((2 : ℕ) * t ^ (2 - 1) : ℝ) : ℂ))) t :=
      (((hasDerivAt_pow 2 t).ofReal_comp).const_mul _).cexp
    refine (h1.mul h2).congr_deriv ?_
    rw [one_smul, hD]
    push_cast
    ring
  have hconst := is_const_of_deriv_eq_zero (fun t => (hφd t).differentiableAt) (fun t => (hφd t).deriv) 1 0
  simp only [hφ, one_smul, zero_smul, one_pow, ofReal_one, mul_one] at hconst
  norm_num at hconst
  rw [← hconst, mul_assoc, ← Complex.exp_add]
  simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzEqGaussianOfFderivEqMulVecStatement
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_eq_gaussian_of_fderiv_eq_mulVec_of_isSymm : ∀ (l : Type) [Fintype l] [DecidableEq l] (τ : Matrix l l ℂ) (f : Sch l), τ.IsSymm → (∀ (a : l) (x : EuclideanSpace ℝ l), fderiv ℝ f x (EuclideanSpace.single a 1) = 2 * π * I * (τ *ᵥ fun i => (x i : ℂ)) a * f x) → ∀ x : EuclideanSpace ℝ l, f x = f 0 * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) := by
  first | exact @GlobalTheory.schwartz_eq_gaussian_of_fderiv_eq_mulVec | exact GlobalTheory.schwartz_eq_gaussian_of_fderiv_eq_mulVec | (intros; apply GlobalTheory.schwartz_eq_gaussian_of_fderiv_eq_mulVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FderivEqMulVecOfSchrodingerAnnihilated
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FderivEqMulVecOfSchrodingerAnnihilated
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory.RealWeil

theorem dRho_apply_basis {l : Type} [Fintype l] [DecidableEq l] (w : l ⊕ l → ℝ) (f : Sch l)
    (x : EuclideanSpace ℝ l) :
    dRho w f x = ∑ b, (w (.inl b) : ℂ) * fderiv ℝ f x (EuclideanSpace.single b 1) +
      2 * π * I * (∑ b, (w (.inr b) : ℂ) * (x b : ℂ)) * f x := by
  rw [dRho_apply]
  have h1 : pPart w = ∑ b, w (.inl b) • EuclideanSpace.single b (1 : ℝ) := by
    ext i
    simp [pPart, PiLp.single_apply, Pi.single_apply]
  have h2 : inner ℝ (qPart w) x = ∑ b, w (.inr b) * x b := by
    simp [qPart, PiLp.inner_apply, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, map_sum, h2]
  simp [Complex.real_smul, ofReal_sum]

theorem fderiv_eq_of_annihilated : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) →
    (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → P.det ≠ 0 →
    ∀ f : Sch l, (∀ j : l, dRho (s *ᵥ Pi.single (.inl j) 1) f = I • dRho (s *ᵥ Pi.single (.inr j) 1) f) →
    ∀ (a : l) (x : EuclideanSpace ℝ l), fderiv ℝ f x (EuclideanSpace.single a 1) =
      2 * π * I * ((-(Q * P⁻¹))ᵀ *ᵥ fun i => (x i : ℂ)) a * f x := by
  intro l _ _ s P Q hP hQ hdet f hf a x
  set u : l → ℂ := fun b => fderiv ℝ f x (EuclideanSpace.single b 1) with hu
  set xC : l → ℂ := fun i => (x i : ℂ) with hxC
  have hj : ∀ j, ∑ b, P b j * u b + 2 * π * I * (∑ b, Q b j * xC b) * f x = 0 := by
    intro j
    have e := congrArg (fun g : Sch l => g x) (hf j)
    simp only [SchwartzMap.smul_apply, smul_eq_mul, dRho_apply_basis] at e
    simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at e
    simp only [hP, hQ, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    simp only [hu, hxC]
    linear_combination e
  have hv : Pᵀ *ᵥ u = -(2 * π * I * f x) • (Qᵀ *ᵥ xC) := by
    funext j
    simp only [mulVec, dotProduct, transpose_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination hj j
  have hunit : IsUnit Pᵀ.det := by rw [det_transpose]; exact isUnit_iff_ne_zero.mpr hdet
  have hu' : u = (Pᵀ)⁻¹ *ᵥ (Pᵀ *ᵥ u) := by rw [mulVec_mulVec, nonsing_inv_mul _ hunit, one_mulVec]
  have key : u a = ((Pᵀ)⁻¹ *ᵥ (-(2 * π * I * f x) • (Qᵀ *ᵥ xC))) a := by rw [← hv, ← hu']
  change u a = _
  rw [key, mulVec_smul, mulVec_mulVec, ← transpose_nonsing_inv, ← transpose_mul, Matrix.transpose_neg,
    Matrix.neg_mulVec]
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

end GlobalTheory.RealWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FderivEqMulVecOfSchrodingerAnnihilatedStatement
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fderiv_eq_mulVec_of_schrodinger_annihilated : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → P.det ≠ 0 → ∀ f : Sch l, (∀ j : l, dRho (s *ᵥ Pi.single (.inl j) 1) f = I • dRho (s *ᵥ Pi.single (.inr j) 1) f) → ∀ (a : l) (x : EuclideanSpace ℝ l), fderiv ℝ f x (EuclideanSpace.single a 1) = 2 * π * I * ((-(Q * P⁻¹))ᵀ *ᵥ fun i => (x i : ℂ)) a * f x := by
  first | exact @GlobalTheory.RealWeil.fderiv_eq_of_annihilated | exact GlobalTheory.RealWeil.fderiv_eq_of_annihilated | (intros; apply GlobalTheory.RealWeil.fderiv_eq_of_annihilated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMetaplecticSchwartzActionProd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMetaplecticSchwartzActionProd
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

noncomputable section

namespace GlobalTheory.RealWeil

theorem continuous_omS_prod (l : Type) [Fintype l] [DecidableEq l] (G : Type) [Group G] [TopologicalSpace G]
    (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l))
    (hpr : Continuous pr) (hom : ∀ f : L2 l, Continuous fun g => om g f)
    (h3 : ∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
      om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f))
    (h4 : ∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) :
    Continuous fun x : G × Sch l => omS x.1 x.2 := by

  have hjoint : Continuous fun x : G × L2 l => om x.1 x.2 :=
    continuous_prod_of_continuous_lipschitzWith' (fun x : G × L2 l => om x.1 x.2) 1
      (fun g => (om g).isometry.lipschitz) hom
  have hentry : ∀ a b, Continuous fun g => (pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b := fun a b =>
    by
    have hv : Continuous fun g => (pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
      (continuous_subtype_val (p := fun M => M ∈ Matrix.symplecticGroup l ℝ)).comp hpr
    exact (continuous_apply b).comp ((continuous_apply a).comp hv)

  have key : ∀ {A : Sch l →L[ℂ] Sch l}, A ∈ weylAlg l →
      Continuous fun x : G × Sch l => schwartzToL2 l (A (omS x.1 x.2)) := by
    intro A hA
    refine weylAlg_induction (P := fun A => Continuous fun x : G × Sch l => schwartzToL2 l (A (omS x.1 x.2)))
      ?_ ?_ ?_ ?_ ?_ hA
    · have e : (fun x : G × Sch l => schwartzToL2 l ((1 : Sch l →L[ℂ] Sch l) (omS x.1 x.2))) =
          fun x => om x.1 (schwartzToL2 l x.2) := by
        funext x
        simp only [ContinuousLinearMap.one_apply, schwartzToL2_apply, h4]
      rw [e]
      exact hjoint.comp (continuous_fst.prodMk ((schwartzToL2 l).continuous.comp continuous_snd))
    · intro A w ih
      simp only [toLp_dRho_omS h3 h4]
      refine continuous_finsetSum _ fun a _ => ?_
      have hih : Continuous fun x : G × Sch l => schwartzToL2 l (A (omS x.1 (dRho (Pi.single a 1) x.2))) :=
        ih.comp (continuous_fst.prodMk ((dRho (Pi.single a 1)).continuous.comp continuous_snd))
      refine Continuous.smul (M := ℂ) ?_ hih
      refine continuous_ofReal.comp ?_
      simp only [mulVec, dotProduct, Matrix.neg_apply, Matrix.mul_apply, transpose_apply]
      exact continuous_finsetSum _ fun b _ => Continuous.mul (Continuous.neg (continuous_finsetSum _ fun c _ =>
        Continuous.mul (continuous_finsetSum _ fun d _ => continuous_const.mul
          ((hentry _ _).comp continuous_fst)) continuous_const)) continuous_const
    · simp only [ContinuousLinearMap.zero_apply, map_zero]
      exact continuous_const
    · intro A B hA hB
      simp only [ContinuousLinearMap.add_apply, map_add (f := _)]
      exact hA.add hB
    · intro c A hA
      simp only [ContinuousLinearMap.smul_apply, map_smul]
      exact hA.const_smul c
  rw [continuous_iff_continuousAt]
  intro x0
  unfold ContinuousAt
  rw [(schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨A, hA, hb⟩ := exists_seminorm_le (l := l) k n
  have ht : Filter.Tendsto (fun x : G × Sch l => ∑ r, ‖schwartzToL2 l (A r (omS x.1 x.2)) - schwartzToL2 l (A r (omS x0.1 x0.2))‖)
      (nhds x0) (nhds 0) := by
    have : (0 : ℝ) = ∑ r : Fin n → l, ‖schwartzToL2 l (A r (omS x0.1 x0.2)) - schwartzToL2 l (A r (omS x0.1 x0.2))‖ := by simp
    rw [this]
    exact tendsto_finsetSum _ fun r _ => ((((key (hA r)).sub continuous_const).norm).tendsto x0)
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with x hx
  refine lt_of_le_of_lt ?_ hx
  rw [SchwartzMap.schwartzSeminormFamily_apply]
  refine (hb _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← schwartzToL2_apply, map_sub, map_sub]

end GlobalTheory.RealWeil
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMetaplecticSchwartzActionProdStatement
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_metaplectic_schwartz_action_prod : ∀ (l : Type) [Fintype l] [DecidableEq l] (G : Type) [Group G] [TopologicalSpace G] (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l)), Continuous pr → (∀ f : L2 l, Continuous fun g => om g f) → (∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l), om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) → (∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) → Continuous fun x : G × Sch l => omS x.1 x.2 := by
  first | exact @GlobalTheory.RealWeil.continuous_omS_prod | exact GlobalTheory.RealWeil.continuous_omS_prod | (intros; apply GlobalTheory.RealWeil.continuous_omS_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticCoverWeilRepresentation
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

theorem GlobalTheory.metaplectic_euclidean_gaussian : ∀ (l : Type) [Fintype l] [DecidableEq l], ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G) (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l)) (φ : Sch l), IsCoveringMap pr ∧ Function.Surjective pr ∧ (∃ ε : G, ε ≠ 1 ∧ (∀ g, pr g = 1 ↔ g = 1 ∨ g = ε) ∧ ∀ f, om ε f = -f) ∧ (∀ f : L2 l, Continuous fun g => om g f) ∧ (∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l), om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) ∧ (∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) ∧ (∀ x : EuclideanSpace ℝ l, φ x = cexp (-π * ((x.ofLp ⬝ᵥ x.ofLp : ℝ) : ℂ))) ∧ (Continuous fun x : G × Sch l => omS x.1 x.2) ∧ ∀ (g : G) (P Q : Matrix l l ℂ), (∀ a b, P a b = ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) → ∃ c : ℂ, c ^ 2 * P.det = 1 ∧ ∀ x : EuclideanSpace ℝ l, omS g φ x = c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) := by
  intro l _ _
  obtain ⟨G, iG, tG, hG, pr, om, omS, φ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := GlobalTheory.T.metaplecticGaussianNormalisedAlt l
  refine ⟨G, iG, tG, hG, pr, om, omS, φ, h1, h2, h3, h4, h5, h6, h7,
    GlobalTheory.T.continuous_metaplectic_schwartz_action_prod l G pr om omS h1.continuous h4 h5 h6, ?_⟩
  intro g P Q hP hQ
  refine ⟨omS g φ 0, h9 g P hP, ?_⟩
  obtain ⟨hdet, hS⟩ := GlobalTheory.T.symplectic_holPart_det_ne_zero_and_isSymm l (pr g).1 P Q hP hQ (pr g).2
  have hann : ∀ j : l, dRho ((pr g).1 *ᵥ Pi.single (.inl j) 1) (omS g φ) =
      I • dRho ((pr g).1 *ᵥ Pi.single (.inr j) 1) (omS g φ) := fun j => by
    rw [← omS_dRho h5 h6, ← omS_dRho h5 h6, h8 j, map_smul]
  have hd := GlobalTheory.T.fderiv_eq_mulVec_of_schrodinger_annihilated l (pr g).1 P Q hP hQ hdet (omS g φ) hann
  rw [hS.eq] at hd
  exact GlobalTheory.T.schwartz_eq_gaussian_of_fderiv_eq_mulVec_of_isSymm l (-(Q * P⁻¹)) (omS g φ) hS hd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticCoverWeilRepresentationStatement
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metaplectic_cover_weil_representation : ∀ (l : Type) [Fintype l] [DecidableEq l], ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G) (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l)) (φ : Sch l), IsCoveringMap pr ∧ Function.Surjective pr ∧ (∃ ε : G, ε ≠ 1 ∧ (∀ g, pr g = 1 ↔ g = 1 ∨ g = ε) ∧ ∀ f, om ε f = -f) ∧ (∀ f : L2 l, Continuous fun g => om g f) ∧ (∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l), om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) ∧ (∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) ∧ (∀ x : EuclideanSpace ℝ l, φ x = cexp (-π * ((x.ofLp ⬝ᵥ x.ofLp : ℝ) : ℂ))) ∧ (Continuous fun x : G × Sch l => omS x.1 x.2) ∧ ∀ (g : G) (P Q : Matrix l l ℂ), (∀ a b, P a b = ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) → ∃ c : ℂ, c ^ 2 * P.det = 1 ∧ ∀ x : EuclideanSpace ℝ l, omS g φ x = c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) := by
  first | exact @GlobalTheory.metaplectic_euclidean_gaussian | exact GlobalTheory.metaplectic_euclidean_gaussian | (intros; apply GlobalTheory.metaplectic_euclidean_gaussian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumMatrixCoefficientSq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelGaussianPairStandardGaussian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelGaussianPairStandardGaussian
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory

theorem siegelGauss_pair_standard (l : Type) [Fintype l] [DecidableEq l] (τ : Matrix l l ℂ) (c : ℂ) (hτ : GlobalTheory.IsSiegel τ) :
    (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 * (1 - I • τ).det = c ^ 2 := by
  set σ : Matrix l l ℂ := τ + I • (1 : Matrix l l ℂ) with hσdef
  have hσ : GlobalTheory.IsSiegel σ := by
    refine ⟨?_, ?_⟩
    · exact hτ.1.add (by simp [Matrix.IsSymm, Matrix.transpose_smul])
    · have : σ.map Complex.im = τ.map Complex.im + 1 := by
        ext i j
        by_cases hij : i = j
        · subst hij; simp [σ, Matrix.one_apply]
        · simp [σ, Matrix.one_apply, hij]
      rw [this]
      exact hτ.2.add_posSemidef Matrix.PosSemidef.one
  have hint : ∀ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))
      = c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (σ *ᵥ fun i => (x i : ℂ)))) := by
    intro x
    rw [← Complex.exp_conj, mul_assoc, ← Complex.exp_add]
    congr 2
    have e : ((x ⬝ᵥ x : ℝ) : ℂ) = (fun i => (x i : ℂ)) ⬝ᵥ (fun i => (x i : ℂ)) := by
      simp [dotProduct]
    rw [e, hσdef, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
    simp only [map_mul, map_neg, conj_ofReal, smul_eq_mul]
    have : conj ((fun i => (x i : ℂ)) ⬝ᵥ (fun i => (x i : ℂ))) = (fun i => (x i : ℂ)) ⬝ᵥ (fun i => (x i : ℂ)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [dotProduct, map_sum]
    rw [this]
    ring_nf
    simp [I_sq]
    ring
  have hdet : (1 - I • τ) = -I • σ := by
    rw [hσdef, smul_add, smul_smul]
    simp [neg_smul, sub_eq_add_neg, add_comm]
  simp_rw [hint]
  rw [integral_const_mul, hdet, mul_pow, mul_assoc]
  have := hσ.siegelGaussIntegral_sq_mul_det
  rw [siegelGaussIntegral] at this
  rw [this, mul_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelGaussianPairStandardGaussianStatement
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelGaussian_pair_standardGaussian : ∀ (l : Type) [Fintype l] [DecidableEq l] (τ : Matrix l l ℂ) (c : ℂ), GlobalTheory.IsSiegel τ → (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 * (1 - I • τ).det = c ^ 2 := by
  first | exact @GlobalTheory.siegelGauss_pair_standard | exact GlobalTheory.siegelGauss_pair_standard | (intros; apply GlobalTheory.siegelGauss_pair_standard <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumMatrixCoefficientSq
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

theorem GlobalTheory.vacuum_coef_sq : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → P.det ≠ 0 → GlobalTheory.IsSiegel (-(Q * P⁻¹)) → ∀ c : ℂ, c ^ 2 * P.det = 1 → (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 * (GlobalTheory.Published.Metaplectic.holPart s).det = (∫ x : l → ℝ, cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 := by
  intro l _ _ s P Q hP hQ hdet hS c hc
  set K := (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ))))
  set J := (∫ x : l → ℝ, cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ))))
  have h1 := GlobalTheory.T.siegelGaussian_pair_standardGaussian l (-(Q * P⁻¹)) c hS
  have hSI : GlobalTheory.IsSiegel ((I • (1 : Matrix l l ℂ))) := by
    refine ⟨?_, ?_⟩
    · simp [Matrix.IsSymm]
    · have : ((I • (1 : Matrix l l ℂ)).map Complex.im) = 1 := by
        ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]
      rw [this]; exact Matrix.PosDef.one
  have h2 := GlobalTheory.T.siegelGaussian_pair_standardGaussian l (I • (1 : Matrix l l ℂ)) 1 hSI
  have hJ : (∫ x : l → ℝ, (1:ℂ) * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (I • (1 : Matrix l l ℂ)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) = J := by
    congr 1; ext x
    congr 2
    rw [one_mul]; congr 1
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
    simp only [dotProduct, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul]
    rw [← mul_assoc, mul_assoc _ I I, I_mul_I]; ring
  rw [hJ] at h2
  have hdet2 : (1 - I • (I • (1 : Matrix l l ℂ))).det = 2 ^ Fintype.card l := by
    have : (1 - I • (I • (1 : Matrix l l ℂ))) = (2:ℂ) • (1 : Matrix l l ℂ) := by
      rw [smul_smul, I_mul_I]; ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]; norm_num
    rw [this, det_smul, det_one, mul_one]
  rw [hdet2, one_pow] at h2
  have hprod : (1 - I • (-(Q * P⁻¹))) * P = (2:ℂ) • GlobalTheory.Published.Metaplectic.holPart s := by
    have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
    rw [sub_mul, one_mul, smul_mul_assoc, neg_mul, Matrix.mul_assoc, nonsing_inv_mul _ hu, mul_one]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul, hP, hQ, GlobalTheory.Published.Metaplectic.holPart]
    push_cast
    ring_nf; rw [I_sq]; ring
  have h3 : K ^ 2 * ((2:ℂ) ^ Fintype.card l * (GlobalTheory.Published.Metaplectic.holPart s).det) = 1 := by
    rw [← det_smul, ← hprod, det_mul, ← mul_assoc, h1, hc]
  have h2ne : (2:ℂ) ^ Fintype.card l ≠ 0 := pow_ne_zero _ two_ne_zero
  apply mul_left_cancel₀ h2ne
  linear_combination h3 - h2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumMatrixCoefficientSqStatement
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_matrix_coefficient_sq : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → P.det ≠ 0 → GlobalTheory.IsSiegel (-(Q * P⁻¹)) → ∀ c : ℂ, c ^ 2 * P.det = 1 → (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 * (GlobalTheory.Published.Metaplectic.holPart s).det = (∫ x : l → ℝ, cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 := by
  first | exact @GlobalTheory.vacuum_coef_sq | exact GlobalTheory.vacuum_coef_sq | (intros; apply GlobalTheory.vacuum_coef_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerProductEuclideanModelsAgree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerProductEuclideanModelsAgree
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

theorem GlobalTheory.Proof.schrodinger_models_agree : ∀ (l : Type) [Fintype l] [DecidableEq l] (w : (l → ℝ) × (l → ℝ)) (φ : 𝓢(l → ℝ, ℂ)) (f f₁ : Sch l), (∀ x : EuclideanSpace ℝ l, f x = φ x.ofLp) → (∀ x : EuclideanSpace ℝ l, f₁ x = GlobalTheory.Published.Metaplectic.rho w φ x.ofLp) → f₁.toLp 2 = rho (Sum.elim w.1 w.2) (f.toLp 2) := by
  intro l _ _ w φ f f₁ hf hf₁
  obtain ⟨p, q⟩ := w
  have h : ⇑f₁ = rhoFun (Sum.elim p q) ⇑f := by
    funext x
    rw [hf₁, GlobalTheory.Published.Metaplectic.rho_apply, rhoFun, hf]
    simp only [phase, pPart, qPart, Sum.elim_inl, Sum.elim_inr, PiLp.inner_apply, WithLp.ofLp_add]
    congr 1
    · congr 1
      push_cast
      simp only [dotProduct, RCLike.inner_apply, conj_trivial, Finset.sum_div]
      push_cast
      ring_nf
      rw [Finset.sum_congr rfl fun i _ => mul_comm ((q i : ℝ) : ℂ) ((p i : ℝ) : ℂ)]
      ring
  refine Lp.ext ((f₁.coeFn_toLp 2 volume).trans ?_)
  rw [h]
  exact ((coeFn_rho _ _).trans (rhoFun_congr _ (f.coeFn_toLp 2 volume))).symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerProductEuclideanModelsAgreeStatement
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_product_euclidean_models_agree : ∀ (l : Type) [Fintype l] [DecidableEq l] (w : (l → ℝ) × (l → ℝ)) (φ : 𝓢(l → ℝ, ℂ)) (f f₁ : Sch l), (∀ x : EuclideanSpace ℝ l, f x = φ x.ofLp) → (∀ x : EuclideanSpace ℝ l, f₁ x = GlobalTheory.Published.Metaplectic.rho w φ x.ofLp) → f₁.toLp 2 = rho (Sum.elim w.1 w.2) (f.toLp 2) := by
  first | exact @GlobalTheory.Proof.schrodinger_models_agree | exact GlobalTheory.Proof.schrodinger_models_agree | (intros; apply GlobalTheory.Proof.schrodinger_models_agree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSiegelUpperHalfSpaceNegMulInvSymplectic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSiegelUpperHalfSpaceNegMulInvSymplectic
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

open scoped ComplexOrder

namespace GlobalTheory

theorem IsSiegel.neg_mul_inv_of_symplectic (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (P Q : Matrix l l ℂ)
    (hP : ∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ))
    (hQ : ∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ))
    (hs : s ∈ Matrix.symplecticGroup l ℝ) (hdet : P.det ≠ 0) (hsym : (-(Q * P⁻¹)).IsSymm) :
    GlobalTheory.IsSiegel (-(Q * P⁻¹)) := by
  refine ⟨hsym, ?_⟩
  set A : Matrix l l ℂ := fun a b => (s (.inl a) (.inl b) : ℂ) with hA
  set B : Matrix l l ℂ := fun a b => (s (.inl a) (.inr b) : ℂ) with hB
  set C : Matrix l l ℂ := fun a b => (s (.inr a) (.inl b) : ℂ) with hC
  set D : Matrix l l ℂ := fun a b => (s (.inr a) (.inr b) : ℂ) with hD
  have hPe : P = A - I • B := by ext a b; simp only [hP]; rfl
  have hQe : Q = C - I • D := by ext a b; simp only [hQ]; rfl
  have hsc : s.map (Complex.ofRealHom : ℝ →+* ℂ) = fromBlocks A B C D := by
    ext (a|a) (b|b) <;> rfl
  have hJ : (J l ℝ).map (Complex.ofRealHom : ℝ →+* ℂ) = J l ℂ := by
    ext (a|a) (b|b) <;> simp [J, Matrix.one_apply] <;> split_ifs <;> simp
  have hc : (fromBlocks A B C D)ᵀ * J l ℂ * fromBlocks A B C D = J l ℂ := by
    have h1 := congrArg (fun M => M.map (Complex.ofRealHom : ℝ →+* ℂ)) (SymplecticGroup.mem_iff'.mp hs)
    simp only [Matrix.map_mul, transpose_map, hJ, hsc] at h1
    exact h1
  rw [J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at hc
  obtain ⟨h11, h12, h21, h22⟩ := hc
  simp at h11 h12 h21 h22
  have star_real : ∀ X : Matrix l l ℂ, (∀ a b, star (X a b) = X a b) → Xᴴ = Xᵀ := by
    intro X hX; ext a b; simp [conjTranspose_apply, hX]
  have hAs : Aᴴ = Aᵀ := star_real A (fun a b => by simp [A])
  have hBs : Bᴴ = Bᵀ := star_real B (fun a b => by simp [B])
  have hCs : Cᴴ = Cᵀ := star_real C (fun a b => by simp [C])
  have hDs : Dᴴ = Dᵀ := star_real D (fun a b => by simp [D])
  have key : Pᴴ * Q - Qᴴ * P = -(2 * I) • (1 : Matrix l l ℂ) := by
    rw [hPe, hQe]
    simp only [conjTranspose_sub, conjTranspose_smul, hAs, hBs, hCs, hDs, Complex.star_def, conj_I,
      sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
    linear_combination (norm := (match_scalars <;> ring_nf <;> (try simp only [I_sq]) <;> ring_nf)) -h11 - h22 + I • h12 - I • h21
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
  set τ := -(Q * P⁻¹) with hτ
  have hτP : τ * P = -Q := by rw [hτ, neg_mul, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
  have hsymm : ∀ a b, τ b a = τ a b := fun a b => by
    have := congrFun (congrFun hsym a) b
    simpa [transpose_apply] using this
  set M : Matrix l l ℝ := τ.map im with hM
  set Mc : Matrix l l ℂ := M.map (Complex.ofRealHom : ℝ →+* ℂ) with hMc
  have hdiff : τ - τᴴ = (2 * I) • Mc := by
    ext a b
    simp only [Matrix.sub_apply, conjTranspose_apply, hsymm a b, Matrix.smul_apply, smul_eq_mul, Mc, M, map_apply,
      Complex.ofRealHom_eq_coe, Complex.star_def, Complex.sub_conj]
    push_cast
    ring
  have hQP : Pᴴ * τᴴ = -Qᴴ := by rw [← conjTranspose_mul, hτP, conjTranspose_neg]
  have h2 : Pᴴ * Mc * P = 1 := by
    have e : Pᴴ * (τ - τᴴ) * P = (2 * I) • (1 : Matrix l l ℂ) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hτP, hQP]
      rw [Matrix.mul_neg, Matrix.neg_mul]
      linear_combination (norm := (match_scalars <;> ring_nf <;> (try simp only [I_sq]) <;> ring_nf)) -key
    rw [hdiff, Matrix.mul_smul, Matrix.smul_mul] at e
    exact smul_right_injective _ (by simp [I_ne_zero] : (2 * I) ≠ 0) e
  have e1 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ hu, conjTranspose_one]
  have e2 : P * P⁻¹ = 1 := mul_nonsing_inv _ hu
  have hMcf : Mc = (P⁻¹)ᴴ * P⁻¹ := by
    calc Mc = ((P⁻¹)ᴴ * Pᴴ) * Mc * (P * P⁻¹) := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
      _ = (P⁻¹)ᴴ * (Pᴴ * Mc * P) * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * P⁻¹ := by rw [h2, Matrix.mul_one]
  have hinj : Function.Injective (P⁻¹).mulVec := by
    intro u v h
    have := congrArg P.mulVec h
    simpa [mulVec_mulVec, e2] using this
  have hpd : Mc.PosDef := hMcf ▸ PosDef.conjTranspose_mul_self _ hinj
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext a b
    simp [conjTranspose_apply, M, hsymm a b]
  · intro x hx
    set xc : l → ℂ := fun i => (x i : ℂ) with hxc
    have hxc0 : xc ≠ 0 := by
      intro h; apply hx; ext i
      have := congrFun h i
      simpa [xc] using this
    have e : star xc ⬝ᵥ Mc *ᵥ xc = ((star x ⬝ᵥ M *ᵥ x : ℝ) : ℂ) := by
      simp [dotProduct, mulVec, Mc, xc, Complex.ofReal_sum, Complex.ofReal_mul]
    have := hpd.dotProduct_mulVec_pos hxc0
    rw [e] at this
    exact zero_lt_real.mp this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSiegelUpperHalfSpaceNegMulInvSymplecticStatement
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSiegelUpperHalfSpace_neg_mul_inv_symplectic : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → s ∈ Matrix.symplecticGroup l ℝ → P.det ≠ 0 → (-(Q * P⁻¹)).IsSymm → GlobalTheory.IsSiegel (-(Q * P⁻¹)) := by
  first | exact @GlobalTheory.IsSiegel.neg_mul_inv_of_symplectic | exact GlobalTheory.IsSiegel.neg_mul_inv_of_symplectic | (intros; apply GlobalTheory.IsSiegel.neg_mul_inv_of_symplectic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzL2EuclideanIdentification
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzL2EuclideanIdentification
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

noncomputable section

namespace GlobalTheory.EuclidTransport

variable (l : Type) [Fintype l]

theorem volume_preserving_ofLp' : MeasurePreserving (@WithLp.ofLp 2 (l → ℝ)) volume volume :=
  PiLp.volume_preserving_ofLp l

theorem volume_preserving_toLp' : MeasurePreserving (@WithLp.toLp 2 (l → ℝ)) volume volume :=
  PiLp.volume_preserving_toLp l

def schwartzTransport : 𝓢(l → ℝ, ℂ) ≃L[ℂ] Sch l :=
  ContinuousLinearEquiv.equivOfInverse
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv l ℝ))
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv l ℝ).symm)
    (fun φ => by ext x; rfl) (fun φ => by ext x; rfl)

variable {l}

theorem schwartzTransport_apply (φ : 𝓢(l → ℝ, ℂ)) (x : EuclideanSpace ℝ l) :
    schwartzTransport l φ x = φ x.ofLp := rfl

variable (l)

def l2TransportIsometry : Lp ℂ 2 (volume : Measure (l → ℝ)) →ₗᵢ[ℂ] L2 l :=
  Lp.compMeasurePreservingₗᵢ ℂ (@WithLp.ofLp 2 (l → ℝ)) (volume_preserving_ofLp' l)

theorem l2TransportIso_apply (f : Lp ℂ 2 (volume : Measure (l → ℝ))) :
    l2TransportIsometry l f = Lp.compMeasurePreserving _ (volume_preserving_ofLp' l) f := rfl

theorem l2TransportIso_surjective : Function.Surjective (l2TransportIsometry l) := by
  intro h
  refine ⟨Lp.compMeasurePreserving (@WithLp.toLp 2 (l → ℝ)) (volume_preserving_toLp' l) h, ?_⟩
  rw [l2TransportIso_apply]
  ext1
  refine (Lp.coeFn_compMeasurePreserving _ (volume_preserving_ofLp' l)).trans ?_
  refine ((volume_preserving_ofLp' l).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_compMeasurePreserving h (volume_preserving_toLp' l))).trans ?_
  exact Filter.Eventually.of_forall fun x => rfl

def l2Transport : Lp ℂ 2 (volume : Measure (l → ℝ)) ≃ₗᵢ[ℂ] L2 l :=
  LinearIsometryEquiv.ofSurjective (l2TransportIsometry l) (l2TransportIso_surjective l)

variable {l}

theorem l2Transport_apply (f : Lp ℂ 2 (volume : Measure (l → ℝ))) :
    l2Transport l f = Lp.compMeasurePreserving _ (volume_preserving_ofLp' l) f := rfl

theorem l2Transport_toLp (φ : 𝓢(l → ℝ, ℂ)) : l2Transport l (φ.toLp 2) = (schwartzTransport l φ).toLp 2 := by
  rw [l2Transport_apply]
  have h4 : ((φ.toLp 2 : Lp ℂ 2 (volume : Measure (l → ℝ))) : (l → ℝ) → ℂ) =ᵐ[volume] (φ : (l → ℝ) → ℂ) :=
    φ.coeFn_toLp 2 volume
  have h5 : (((schwartzTransport l φ).toLp 2 : L2 l) : EuclideanSpace ℝ l → ℂ) =ᵐ[volume]
      (schwartzTransport l φ : EuclideanSpace ℝ l → ℂ) :=
    (schwartzTransport l φ).coeFn_toLp 2 volume
  refine Lp.ext (Filter.EventuallyEq.trans ?_ h5.symm)
  refine (Lp.coeFn_compMeasurePreserving _ (volume_preserving_ofLp' l)).trans ?_
  refine ((volume_preserving_ofLp' l).quasiMeasurePreserving.ae_eq_comp h4).trans ?_
  exact Filter.Eventually.of_forall fun x => (schwartzTransport_apply φ x).symm

theorem exists_schwartz_L2_transport (l : Type) [Fintype l] [DecidableEq l] :
    ∃ (e : 𝓢(l → ℝ, ℂ) ≃L[ℂ] Sch l) (u : Lp ℂ 2 (volume : Measure (l → ℝ)) ≃ₗᵢ[ℂ] L2 l),
      (∀ φ (x : EuclideanSpace ℝ l), e φ x = φ x.ofLp) ∧ ∀ φ : 𝓢(l → ℝ, ℂ), u (φ.toLp 2) = (e φ).toLp 2 :=
  ⟨schwartzTransport l, l2Transport l, schwartzTransport_apply, l2Transport_toLp⟩

end GlobalTheory.EuclidTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzL2EuclideanIdentificationStatement
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_L2_euclidean_identification : ∀ (l : Type) [Fintype l] [DecidableEq l], ∃ (e : 𝓢(l → ℝ, ℂ) ≃L[ℂ] Sch l) (u : Lp ℂ 2 (volume : Measure (l → ℝ)) ≃ₗᵢ[ℂ] L2 l), (∀ φ (x : EuclideanSpace ℝ l), e φ x = φ x.ofLp) ∧ ∀ φ : 𝓢(l → ℝ, ℂ), u (φ.toLp 2) = (e φ).toLp 2 := by
  first | exact @GlobalTheory.EuclidTransport.exists_schwartz_L2_transport | exact GlobalTheory.EuclidTransport.exists_schwartz_L2_transport | (intros; apply GlobalTheory.EuclidTransport.exists_schwartz_L2_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalSymplecticFixesSiegelPointI
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalSymplecticFixesSiegelPointI
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory

theorem holPart_eq_and_gaussian_of_orthogonal_symplectic (l : Type) [Fintype l] [DecidableEq l]
    (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ)
    (hP : ∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ))
    (hQ : ∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ))
    (hs : s ∈ Matrix.symplecticGroup l ℝ) (ho : sᵀ * s = 1) (hd : P.det ≠ 0) :
    GlobalTheory.Published.Metaplectic.holPart s = P ∧ ∀ x : l → ℝ,
      cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) =
        cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) := by
  have hJ : s * J l ℝ = J l ℝ * s := by
    have h2 : s * J l ℝ * sᵀ = J l ℝ := SymplecticGroup.mem_iff.mp hs
    calc s * J l ℝ = s * J l ℝ * (sᵀ * s) := by rw [ho, Matrix.mul_one]
      _ = (s * J l ℝ * sᵀ) * s := by simp only [Matrix.mul_assoc]
      _ = J l ℝ * s := by rw [h2]
  have e1 : ∀ a b, s (.inl a) (.inr b) = - s (.inr a) (.inl b) := by
    intro a b
    have := congrFun (congrFun hJ (.inl a)) (.inl b)
    simpa [J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] using this
  have e2 : ∀ a b, s (.inr a) (.inr b) = s (.inl a) (.inl b) := by
    intro a b
    have := congrFun (congrFun hJ (.inl a)) (.inr b)
    simp [J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] at this
    linarith
  have hh : GlobalTheory.Published.Metaplectic.holPart s = P := by
    ext a b
    simp only [GlobalTheory.Published.Metaplectic.holPart, hP, e2, e1]
    push_cast; ring
  have hQP : Q = (-I) • P := by
    ext a b
    simp only [hP, hQ, e2, e1, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring_nf; rw [I_sq]; ring
  have hinv : -(Q * P⁻¹) = I • (1 : Matrix l l ℂ) := by
    rw [hQP, Matrix.smul_mul, mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hd), neg_smul, neg_neg]
  refine ⟨hh, fun x => ?_⟩
  rw [hinv, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  simp only [dotProduct]
  push_cast
  ring_nf; rw [I_sq]; ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalSymplecticFixesSiegelPointIStatement
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_symplectic_fixes_siegel_point_i : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → s ∈ Matrix.symplecticGroup l ℝ → sᵀ * s = 1 → P.det ≠ 0 → GlobalTheory.Published.Metaplectic.holPart s = P ∧ ∀ x : l → ℝ, cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) = cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.holPart_eq_and_gaussian_of_orthogonal_symplectic | exact GlobalTheory.holPart_eq_and_gaussian_of_orthogonal_symplectic | (intros; apply GlobalTheory.holPart_eq_and_gaussian_of_orthogonal_symplectic <;> assumption)
end
end

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory

theorem metaplecticRepresentation_holds : GlobalTheory.Published.MetaplecticRepresentation := by
  intro ι _ _
  obtain ⟨G, iG, tG, tgG, pr, om, omS, φ, hcov, hsurj, ⟨ε, hε1, hker, hεf⟩, hcont, hint, hcompat, hφ, hjc,
    hgauss⟩ := GlobalTheory.T.metaplectic_cover_weil_representation ι
  obtain ⟨e, u, he, hu⟩ := GlobalTheory.T.schwartz_L2_euclidean_identification ι
  have hes : ∀ (ψ : Sch ι) (x : ι → ℝ), e.symm ψ x = ψ (WithLp.toLp 2 x) := by
    intro ψ x
    simpa using (he (e.symm ψ) (WithLp.toLp 2 x)).symm
  have inj : ∀ ψ₁ ψ₂ : Sch ι, ψ₁.toLp 2 = ψ₂.toLp 2 → ψ₁ = ψ₂ := fun ψ₁ ψ₂ h =>
    SchwartzMap.injective_toLp (E := EuclideanSpace ℝ ι) (F := ℂ) 2 volume h
  let Ω : G →* (Lp ℂ 2 (volume : Measure (ι → ℝ)) →L[ℂ] Lp ℂ 2 (volume : Measure (ι → ℝ))) :=
    { toFun := fun g => ((u.symm.toContinuousLinearEquiv : L2 ι →L[ℂ] Lp ℂ 2 (volume : Measure (ι → ℝ))).comp
          ((om g).toContinuousLinearEquiv : L2 ι →L[ℂ] L2 ι)).comp
          (u.toContinuousLinearEquiv : Lp ℂ 2 (volume : Measure (ι → ℝ)) →L[ℂ] L2 ι)
      map_one' := by ext1 f; simp
      map_mul' := fun g h => by ext1 f; simp }
  have hΩ : ∀ g f, Ω g f = u.symm (om g (u f)) := fun g f => rfl
  let ω : G →* (𝓢(ι → ℝ, ℂ) →L[ℂ] 𝓢(ι → ℝ, ℂ)) :=
    { toFun := fun g => ((e.symm : Sch ι →L[ℂ] 𝓢(ι → ℝ, ℂ)).comp (omS g)).comp (e : 𝓢(ι → ℝ, ℂ) →L[ℂ] Sch ι)
      map_one' := by ext1 f; simp
      map_mul' := fun g h => by ext1 f; simp }
  have hω : ∀ g f, ω g f = e.symm (omS g (e f)) := fun g f => rfl
  have heω : ∀ g f, e (ω g f) = omS g (e f) := fun g f => by rw [hω, e.apply_symm_apply]
  have hφ₀ : ∀ x : ι → ℝ, e.symm φ x = cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) := by
    intro x
    rw [hes, hφ]
  refine ⟨G, iG, tG, tgG, pr, Ω, ω, e.symm φ, hsurj, hcov, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hφ₀, ?_, ?_⟩
  · have hk : (pr.ker : Set G) = {1, ε} := by
      ext g
      simp [MonoidHom.mem_ker, hker]
    rw [← SetLike.coe_sort_coe, hk, Nat.card_coe_set_eq, Set.ncard_pair hε1.symm]
  · intro g f
    rw [hΩ, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
  · intro f
    exact u.symm.continuous.comp (hcont (u f))
  · intro g ψ
    rw [hΩ, LinearIsometryEquiv.symm_apply_eq, hu, hu, heω, hcompat]
  · have : (fun x : G × 𝓢(ι → ℝ, ℂ) => ω x.1 x.2) =
        (fun y : Sch ι => e.symm y) ∘ (fun y : G × Sch ι => omS y.1 y.2) ∘ (fun x : G × 𝓢(ι → ℝ, ℂ) => (x.1, e x.2)) := by
      funext x; rfl
    rw [this]
    exact e.symm.continuous.comp (hjc.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd)))
  · intro g w ψ
    apply e.injective
    apply inj
    rw [heω, ← hcompat]
    rw [GlobalTheory.T.schrodinger_product_euclidean_models_agree ι w ψ (e ψ) (e (GlobalTheory.Published.Metaplectic.rho w ψ)) (he ψ) (he _)]
    rw [hint, hcompat]
    rw [GlobalTheory.T.schrodinger_product_euclidean_models_agree ι (GlobalTheory.Published.Metaplectic.act (pr g).1 w) (ω g ψ) (e (ω g ψ))
      (e (GlobalTheory.Published.Metaplectic.rho (GlobalTheory.Published.Metaplectic.act (pr g).1 w) (ω g ψ))) (he _) (he _)]
    rw [heω]
    congr 2
    simp [GlobalTheory.Published.Metaplectic.act, Sum.elim_comp_inl_inr]
  · intro g hg1 hg ψ
    have hgε : g = ε := ((hker g).1 hg1).resolve_left hg
    subst hgε
    have h1 : omS g (e ψ) = -(e ψ) := by
      apply inj
      have hn := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))).map_neg (e ψ)
      simp only [SchwartzMap.toLpCLM_apply] at hn
      rw [← hcompat, hεf, hn]
    rw [hω, h1, map_neg, e.symm_apply_apply]
  · intro g
    obtain ⟨c, hc, hcx⟩ := hgauss g (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ))
      (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ))
      (fun a b => rfl) (fun a b => rfl)
    have hdet : (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)).det ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hc; exact zero_ne_one hc
    obtain ⟨-, hsymm⟩ := GlobalTheory.T.symplectic_holPart_det_ne_zero_and_isSymm ι (pr g).1 (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) (fun a b => rfl) (fun a b => rfl) (pr g).2
    have hsieg := GlobalTheory.T.isSiegelUpperHalfSpace_neg_mul_inv_symplectic ι (pr g).1 (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) (fun a b => rfl) (fun a b => rfl) (pr g).2 hdet hsymm
    have hωx : ∀ x : ι → ℝ, ω g (e.symm φ) x = c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ
        (-((Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) *
          (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ))⁻¹)) *ᵥ
          fun i => (x i : ℂ))) := by
      intro x
      rw [hω, e.apply_symm_apply, hes, hcx]
    simp only [hωx, hφ₀]
    exact GlobalTheory.T.vacuum_matrix_coefficient_sq ι (pr g).1 (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) (fun a b => rfl) (fun a b => rfl) hdet hsieg c hc
  · intro g horth
    obtain ⟨c, hc, hcx⟩ := hgauss g (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ))
      (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ))
      (fun a b => rfl) (fun a b => rfl)
    have hdet : (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)).det ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hc; exact zero_ne_one hc
    obtain ⟨hP, hq⟩ := GlobalTheory.T.orthogonal_symplectic_fixes_siegel_point_i ι (pr g).1 (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) (fun a b => rfl) (fun a b => rfl) (pr g).2 horth hdet
    refine ⟨c, by rw [hP]; exact hc, ?_⟩
    ext x
    rw [hω, e.apply_symm_apply, hes, hcx, SchwartzMap.smul_apply, smul_eq_mul, hφ₀]
    simp only [PiLp.toLp_apply]
    rw [hq x]

end GlobalTheory
