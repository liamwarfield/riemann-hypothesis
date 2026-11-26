module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.PacketConditionsClosed
set_option autoImplicit false

noncomputable section

open NumberField Matrix
open scoped ComplexOrder

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem mulVec_injective_map {E : Type*} [Field E] {n j : ℕ} (f : E →+* ℂ)
    (Bm : Matrix (Fin n) (Fin j) E) (hB : Function.Injective Bm.mulVec) :
    Function.Injective (Bm.map f).mulVec := by
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' Bm)
    (by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      apply hB
      simpa [Matrix.toLin'_apply] using hxy)
  have hC : LinearMap.toMatrix' g * Bm = 1 := by
    have h1 := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] at h1
  have h2 : (LinearMap.toMatrix' g).map f * Bm.map f = 1 := by
    rw [← Matrix.map_mul, hC]
    exact Matrix.map_one f (map_zero f) (map_one f)
  intro x y hxy
  have h3 := congrArg ((LinearMap.toMatrix' g).map f).mulVec hxy
  simp only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] at h3
  exact h3

theorem gram_det_re_pos (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ}
    (b : Fin j → Fin I.n → I.E) (hb : LinearIndependent I.E b) : 0 < (gramV I x v b).det.re := by
  classical
  set A : Matrix (Fin I.n) (Fin I.n) ℂ := uMat (x.1 v)⁻¹ * (I.P v)⁻¹ with hA
  set Bm : Matrix (Fin I.n) (Fin j) I.E := Matrix.of fun i a => b a i with hBm
  have hgram : gramV I x v b = (A * Bm.map (I.φ v))ᴴ * (A * Bm.map (I.φ v)) := by
    ext a c
    have e : ∀ a i, coordV I x v (b a) i = (A * Bm.map (I.φ v)) i a := by
      intro a i
      simp [coordV, A, Bm, Matrix.mulVec, dotProduct, Matrix.mul_apply]
    simp only [gramV, e, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hB : Function.Injective Bm.mulVec := by
    intro c c' h
    have hs : ∑ a, (c a - c' a) • b a = 0 := by
      ext i
      have := congrFun h i
      simp only [Bm, Matrix.mulVec, dotProduct, Matrix.of_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
        Pi.zero_apply]
      rw [sub_eq_zero]
      simpa only [mul_comm] using this
    funext a
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hb _ hs a)
  have hAu : IsUnit A := (Units.isUnit _).mul (Matrix.isUnit_nonsing_inv_iff.2 (I.P_unit v))
  have hC : Function.Injective (A * Bm.map (I.φ v)).mulVec := by
    intro w w' h
    simp only [← Matrix.mulVec_mulVec] at h
    exact mulVec_injective_map (I.φ v) Bm hB (Matrix.mulVec_injective_iff_isUnit.2 hAu h)
  have hpos := (Matrix.PosDef.conjTranspose_mul_self _ hC).det_pos
  rw [hgram]
  exact (Complex.pos_iff.1 hpos).1

theorem packet_conditions_closed (h1 : LatticeFinitelyGenerated) (h2 : ExistsBoundedBasis) : HeightsPositive := by
  unfold HeightsPositive
  intro I x s
  unfold ht
  obtain ⟨M, hMfg, hM⟩ := h1 I x
  cases s
  apply div_pos
  · apply Finset.prod_pos
    intro v _
    apply gram_det_re_pos
    assumption
  · rw [Nat.cast_pos]
    refine @Nat.card_pos _ _ (h2 _ _ _ M _ _ hMfg ?_ ?_ ?_ ?_)
    all_goals first
      | assumption
      | (intro y hy; rw [← SetLike.mem_coe, hM]; aesop)
      | aesop

end Formalism.L2.SG.Pf.Tau
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.ExistsMulMulConjTransposeEqOne
set_option autoImplicit false

noncomputable section

open Matrix

open scoped ComplexOrder

namespace Formalism.L2.SG.Pf.Tau

theorem re_star_dotProduct_self {m : ℕ} (z : Fin m → ℂ) :
    (star z ⬝ᵥ z).re = ∑ i, ‖z i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

theorem star_dotProduct_gram {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℂ) (z : Fin k → ℂ) :
    star z ⬝ᵥ ((Aᴴ * A) *ᵥ z) = star (A *ᵥ z) ⬝ᵥ (A *ᵥ z) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem det_bounds_of_rayleigh {j : ℕ} (M : Matrix (Fin j) (Fin j) ℂ) (hM : M.IsHermitian) (a b : ℝ)
    (ha : 0 ≤ a)
    (h : ∀ z : Fin j → ℂ, a * ∑ i, ‖z i‖ ^ 2 ≤ (star z ⬝ᵥ (M *ᵥ z)).re ∧
      (star z ⬝ᵥ (M *ᵥ z)).re ≤ b * ∑ i, ‖z i‖ ^ 2) :
    ∃ μ : ℝ, M.det = μ ∧ a ^ j ≤ μ ∧ μ ≤ b ^ j := by
  have key : ∀ i, a ≤ hM.eigenvalues i ∧ hM.eigenvalues i ≤ b := by
    intro i
    set v : Fin j → ℂ := (hM.eigenvectorBasis i).ofLp with hv_def
    have hnorm : ∑ k, ‖v k‖ ^ 2 = 1 := by
      have h1 := (hM.eigenvectorBasis).norm_eq_one i
      rw [EuclideanSpace.norm_eq] at h1
      have h2 := congrArg (fun t : ℝ => t ^ 2) h1
      simp only [one_pow] at h2
      rwa [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h2
    have e : (star v ⬝ᵥ (M *ᵥ v)).re = hM.eigenvalues i := by
      rw [hv_def, hM.mulVec_eigenvectorBasis i, dotProduct_smul, Complex.smul_re, smul_eq_mul,
        ← hv_def, re_star_dotProduct_self, hnorm, mul_one]
    have := h v
    rw [e, hnorm, mul_one, mul_one] at this
    exact this
  refine ⟨∏ i, hM.eigenvalues i, ?_, ?_, ?_⟩
  · rw [hM.det_eq_prod_eigenvalues]
    norm_cast
  · calc a ^ j = ∏ _i : Fin j, a := by simp
      _ ≤ ∏ i, hM.eigenvalues i := Finset.prod_le_prod₀ (fun _ _ => ha) (fun i _ => (key i).1)
  · calc ∏ i, hM.eigenvalues i ≤ ∏ _i : Fin j, b :=
          Finset.prod_le_prod₀ (fun i _ => ha.trans (key i).1) (fun i _ => (key i).2)
      _ = b ^ j := by simp

theorem exists_mul_mul_conjTranspose_eq_one {j : ℕ} {G : Matrix (Fin j) (Fin j) ℂ} (hG : G.PosDef) :
    ∃ S : Matrix (Fin j) (Fin j) ℂ, S * G * Sᴴ = 1 := by
  have hH := hG.isHermitian
  set U : Matrix (Fin j) (Fin j) ℂ := (hH.eigenvectorUnitary : Matrix (Fin j) (Fin j) ℂ) with hU_def
  have hU : star U * U = 1 := by simp [U]
  have hspec : G = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := by
    have := hH.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at this
  have hpos : ∀ i, 0 < hH.eigenvalues i := hG.eigenvalues_pos
  refine ⟨diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U, ?_⟩
  rw [show (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U) * G *
      (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U)ᴴ =
      (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U) *
      (U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U) *
      (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U)ᴴ by rw [← hspec]]
  rw [conjTranspose_mul, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose,
    ← Matrix.star_eq_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star U) U, hU, Matrix.one_mul, ← Matrix.mul_assoc (star U) U, hU, Matrix.one_mul,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  have hs : 0 < Real.sqrt (hH.eigenvalues i) := Real.sqrt_pos.2 (hpos i)
  have hsq : Real.sqrt (hH.eigenvalues i) ^ 2 = hH.eigenvalues i := Real.sq_sqrt (hpos i).le
  have h1 : (Real.sqrt (hH.eigenvalues i))⁻¹ * hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i))⁻¹ = 1 := by
    rw [show (Real.sqrt (hH.eigenvalues i))⁻¹ * hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i))⁻¹
        = hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i) ^ 2)⁻¹ by ring, hsq, mul_inv_cancel₀ (hpos i).ne']
  simp only [Function.comp, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
  rw [← mul_assoc]
  have h2 := congrArg (fun t : ℝ => (t : ℂ)) h1
  push_cast at h2
  simpa using h2

theorem det_gram_mul_eq_zero {n j : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin j) ℂ)
    (hd : (Cᴴ * C).det = 0) : ((Y * C)ᴴ * (Y * C)).det = 0 := by
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have hCz : C *ᵥ z = 0 := by
    have h1 : star z ⬝ᵥ ((Cᴴ * C) *ᵥ z) = 0 := by rw [hz, dotProduct_zero]
    rw [star_dotProduct_gram] at h1
    exact dotProduct_star_self_eq_zero.mp h1
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨z, hz0, ?_⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hCz, Matrix.mulVec_zero, Matrix.mulVec_zero]

theorem t5 : GramDistortionBound := by
  intro n j Y C a b ha hY
  by_cases hd : (Cᴴ * C).det = 0
  · rw [hd, det_gram_mul_eq_zero Y C hd]
    simp
  have hPS : (Cᴴ * C).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self C
  have hPD : (Cᴴ * C).PosDef := hPS.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
  obtain ⟨S, hS⟩ := exists_mul_mul_conjTranspose_eq_one hPD
  set V := C * Sᴴ with hV_def
  have hV : Vᴴ * V = 1 := by
    rw [hV_def, conjTranspose_mul, conjTranspose_conjTranspose]
    rw [show S * Cᴴ * (C * Sᴴ) = S * (Cᴴ * C) * Sᴴ by simp only [Matrix.mul_assoc]]
    exact hS
  set M := (Y * V)ᴴ * (Y * V) with hM_def
  have hMH : M.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self _
  have hray : ∀ z : Fin j → ℂ, a * ∑ i, ‖z i‖ ^ 2 ≤ (star z ⬝ᵥ (M *ᵥ z)).re ∧
      (star z ⬝ᵥ (M *ᵥ z)).re ≤ b * ∑ i, ‖z i‖ ^ 2 := by
    intro z
    have e1 : (star z ⬝ᵥ (M *ᵥ z)).re = ∑ i, ‖((Y * V) *ᵥ z) i‖ ^ 2 := by
      rw [hM_def, star_dotProduct_gram, re_star_dotProduct_self]
    have e2 : ∑ i, ‖(V *ᵥ z) i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
      rw [← re_star_dotProduct_self, ← star_dotProduct_gram, hV, Matrix.one_mulVec, re_star_dotProduct_self]
    have := hY (V *ᵥ z)
    rw [Matrix.mulVec_mulVec, e2] at this
    rw [e1]
    exact this
  obtain ⟨μ, hμ, h1, h2⟩ := det_bounds_of_rayleigh M hMH a b ha hray
  have hMeq : M = S * ((Y * C)ᴴ * (Y * C)) * Sᴴ := by
    simp only [hM_def, hV_def, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hdet1 : S.det * (Cᴴ * C).det * Sᴴ.det = 1 := by
    rw [← det_mul, ← det_mul, hS, det_one]
  have hdY : ((Y * C)ᴴ * (Y * C)).det = μ * (Cᴴ * C).det := by
    calc ((Y * C)ᴴ * (Y * C)).det
        = ((Y * C)ᴴ * (Y * C)).det * (S.det * (Cᴴ * C).det * Sᴴ.det) := by rw [hdet1, mul_one]
      _ = (S.det * ((Y * C)ᴴ * (Y * C)).det * Sᴴ.det) * (Cᴴ * C).det := by ring
      _ = μ * (Cᴴ * C).det := by rw [← det_mul, ← det_mul, ← hMeq, hμ]
  have hG0 := hPS.det_nonneg
  rw [Complex.nonneg_iff] at hG0
  have hre : ((Y * C)ᴴ * (Y * C)).det.re = μ * (Cᴴ * C).det.re := by
    rw [hdY, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hre]
  exact ⟨mul_le_mul_of_nonneg_right h1 hG0.1, mul_le_mul_of_nonneg_right h2 hG0.1⟩

end Formalism.L2.SG.Pf.Tau
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.EmbeddingLinearIndependent
set_option autoImplicit false

noncomputable section

open NumberField Matrix Module
open scoped ComplexOrder

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem complex_embedding_cases (I : AutInst) (σ : I.E →+* ℂ) :
    ∃ v, σ = I.φ v ∨ σ = (starRingEnd ℂ).comp (I.φ v) := by
  classical
  haveI := I.cm.totReal
  let ψ : I.F →+* ℂ := σ.comp (algebraMap I.F I.E)
  let v : InfinitePlace I.F := InfinitePlace.mk ψ
  have hreal : ComplexEmbedding.IsReal ψ := InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal v)
  have hemb : v.embedding = ψ := InfinitePlace.embedding_mk_eq_of_isReal hreal
  have hagree : ∀ x : I.F, σ (algebraMap I.F I.E x) = I.φ v (algebraMap I.F I.E x) := by
    intro x
    rw [I.φ_over, hemb]
    rfl
  have hF : ∀ t : I.E, star t = t → σ t = I.φ v t := by
    intro t ht
    obtain ⟨x, rfl⟩ := (I.cm.fixed t).mp ht
    exact hagree x
  have key : ∀ a : I.E, σ a = I.φ v a ∨ σ a = starRingEnd ℂ (I.φ v a) := by
    intro a
    have ht := hF (a + star a) (by rw [star_add, star_star, add_comm])
    have hm := hF (a * star a) (by rw [star_mul, star_star])
    rw [map_add (f := _), map_add (f := _)] at ht
    rw [map_mul, map_mul] at hm
    have hprod : (σ a - I.φ v a) * (σ a - I.φ v (star a)) = 0 := by
      linear_combination (σ a) * ht - hm
    rcases mul_eq_zero.mp hprod with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · right
      rw [sub_eq_zero.mp h]
      exact I.cm.cmUnram.2.1 (I.φ v) a
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon v
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ I.φ v a := by
    by_contra h
    push_neg at h
    exact h1 (RingHom.ext h)
  obtain ⟨b, hb⟩ : ∃ b, σ b ≠ starRingEnd ℂ (I.φ v b) := by
    by_contra h
    push_neg at h
    exact h2 (RingHom.ext h)
  have ha' := (key a).resolve_left ha
  have hb' := (key b).resolve_right hb
  rcases key (a + b) with h | h
  · apply ha
    rw [map_add (f := _), map_add (f := _)] at h
    linear_combination h - hb'
  · apply hb
    rw [map_add (f := _), map_add (f := _), map_add (f := _)] at h
    linear_combination h - ha'

theorem embedding_linear_independent (I : AutInst) :
    LinearIndependent ℝ (fun i : Free.ChooseBasisIndex ℤ (𝓞 I.E) =>
      fun v : InfinitePlace I.F => I.φ v (integralBasis I.E i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 I.E)) = Fintype.card (I.E →ₐ[ℚ] ℂ) := by
    rw [AlgHom.card, ← NumberField.RingOfIntegers.rank, Module.finrank_eq_card_chooseBasisIndex]
  let e := Fintype.equivOfCardEq hcard
  have hdet : (Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis I.E) e).det ≠ 0 := by
    intro h0
    have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ (integralBasis I.E) e
    rw [h0] at h1
    exact Algebra.discr_not_zero_of_basis ℚ (integralBasis I.E)
      ((map_eq_zero_iff (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective).mp (by rw [h1]; ring))
  have hall : ∀ σ : I.E →+* ℂ, ∑ i, (g i : ℂ) * σ (integralBasis I.E i) = 0 := by
    intro σ
    obtain ⟨v, hv | hv⟩ := complex_embedding_cases I σ
    · have := congrFun hg v
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Complex.real_smul] at this
      rw [hv]
      exact this
    · have := congrArg (starRingEnd ℂ) (congrFun hg v)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Complex.real_smul, map_sum, map_mul,
        Complex.conj_ofReal, map_zero] at this
      rw [hv]
      simp only [RingHom.coe_comp, Function.comp_apply]
      exact this
  have hvec : (fun i => (g i : ℂ)) ᵥ* Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis I.E) e = 0 := by
    funext j
    simp only [Matrix.vecMul, dotProduct, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix,
      Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply, Equiv.symm_symm,
      Matrix.of_apply, Pi.zero_apply]
    exact hall (e j).toRingHom
  have h0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hvec
  intro i
  have hi := congrFun h0 i
  simp only [Pi.zero_apply] at hi
  exact_mod_cast hi

theorem card_infinite_places (I : AutInst) : Fintype.card (InfinitePlace I.F) = I.f := by
  haveI := I.cm.totReal
  have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.F
  rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, add_zero] at h
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, h]
  rfl

theorem card_integral_basis (I : AutInst) : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 I.E)) = 2 * I.f := by
  rw [← Module.finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank,
    ← Module.finrank_mul_finrank ℚ I.F I.E, I.cm.deg2]
  show Module.finrank ℚ I.F * 2 = 2 * Module.finrank ℚ I.F
  ring

theorem finrank_places_complex (I : AutInst) : finrank ℝ (InfinitePlace I.F → ℂ) = 2 * I.f := by
  rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
    card_infinite_places, smul_eq_mul]
  ring

def embeddingBasis (I : AutInst) : Basis (Free.ChooseBasisIndex ℤ (𝓞 I.E)) ℝ (InfinitePlace I.F → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank (embedding_linear_independent I)
    (by rw [card_integral_basis, finrank_places_complex])

theorem embeddingBasis_apply (I : AutInst) (i : Free.ChooseBasisIndex ℤ (𝓞 I.E)) :
    embeddingBasis I i = fun v => I.φ v (integralBasis I.E i) := by
  unfold embeddingBasis
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]

def complexToEuclidean {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ} (e : Fin 2 × ι ≃ Fin d) :
    (ι → ℂ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  ((Complex.basisOneI.smulTower (Pi.basisFun ℂ ι)).reindex e).equivFun.trans
    (EuclideanSpace.equiv (Fin d) ℝ).toLinearEquiv.symm


open scoped MatrixOrder in
theorem gram_factor_invertible {n j : ℕ} (C : Matrix (Fin n) (Fin j) ℂ) (hC : Function.Injective C.mulVec) :
    ∃ R : Matrix (Fin j) (Fin j) ℂ, Cᴴ * C = Rᴴ * R ∧ R.det ≠ 0 := by
  have hpd : (Cᴴ * C).PosDef := Matrix.PosDef.conjTranspose_mul_self C hC
  have h0 : 0 ≤ Cᴴ * C := Matrix.nonneg_iff_posSemidef.mpr hpd.posSemidef
  refine ⟨CFC.sqrt (Cᴴ * C), ?_, ?_⟩
  · have hsa : (CFC.sqrt (Cᴴ * C))ᴴ = CFC.sqrt (Cᴴ * C) := by
      have := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (Cᴴ * C))).star_eq
      rwa [Matrix.star_eq_conjTranspose] at this
    rw [hsa, CFC.sqrt_mul_sqrt_self _ h0]
  · intro hdet
    have hd : (Cᴴ * C).det ≠ 0 := (hpd.posSemidef.posDef_iff_det_ne_zero).mp hpd
    rw [← CFC.sqrt_mul_sqrt_self _ h0, Matrix.det_mul, hdet, zero_mul] at hd
    exact hd rfl

theorem norm_sq_eq_of_gram_eq {n j : ℕ} (C : Matrix (Fin n) (Fin j) ℂ) (R : Matrix (Fin j) (Fin j) ℂ)
    (h : Cᴴ * C = Rᴴ * R) (z : Fin j → ℂ) :
    ∑ i, ‖(C *ᵥ z) i‖ ^ 2 = ∑ k, ‖(R *ᵥ z) k‖ ^ 2 := by
  have key : ∀ {m : Type} [Fintype m] (M : Matrix m (Fin j) ℂ),
      ((∑ i, ‖(M *ᵥ z) i‖ ^ 2 : ℝ) : ℂ) = star z ⬝ᵥ ((Mᴴ * M) *ᵥ z) := by
    intro m _ M
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  apply Complex.ofReal_injective
  rw [key C, key R, h]

end Formalism.L2.SG.Pf.Tau
end
end
