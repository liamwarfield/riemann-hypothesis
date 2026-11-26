module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetSmulDirection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertTwistedLatticeJetsModularFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiPeriodNormalisedJetModularTransform
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeJetSl2IntSmul
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbFam.JetModular

def rowEquiv (F : Type) [Field F] (γ : SL(2, ℤ)) : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) :=
  LinearEquiv.ofLinear
    (Matrix.vecMulLinear ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → F)))
    (Matrix.vecMulLinear (((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → F)))
    (by
      refine LinearMap.ext fun x ↦ ?_
      simp only [LinearMap.comp_apply, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, LinearMap.id_apply]
      rw [← Matrix.map_mul_intCast, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
      simp)
    (by
      refine LinearMap.ext fun x ↦ ?_
      simp only [LinearMap.comp_apply, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, LinearMap.id_apply]
      rw [← Matrix.map_mul_intCast, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
      simp)

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
set_option autoImplicit false in
private lemma iterD_const_mul {I : Type} [Fintype I] [DecidableEq I] (u : List I)
    (h : (I → ℂ) → ℂ) (A : ℂ) (z : I → ℂ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u (fun z ↦ A * h z) z =
      A * _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u h z := by
  simpa using _root_.GlobalTheory.HilbFam.iterD_const_mul_reindex I I (Equiv.refl I) u h A z

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
set_option autoImplicit false in
private lemma mem_iff_sl2_equiv_mem_mulMat (F : Type) [Field F] [NumberField F] (L : _root_.GlobalTheory.HilbFam.Lat F)
    (γ : SL(2, ℤ)) (x : Fin 2 → F) :
    x ∈ L ↔ _root_.GlobalTheory.HilbFam.JetModular.rowEquiv F γ x ∈ _root_.GlobalTheory.HilbFam.mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  unfold _root_.GlobalTheory.HilbFam.mulMat
  rw [Submodule.mem_map]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    rwa [(_root_.GlobalTheory.HilbFam.JetModular.rowEquiv F γ).injective (a₁ := y) (a₂ := x) hxy] at hy

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
set_option autoImplicit false in
private lemma embeddingCoord_sl2_smul_lemma_3 (F : Type) [Field F] [NumberField F] (γ : SL(2, ℤ)) (τ : ℍ)
    (c t : ℂ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (x : Fin 2 → F) (i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) :
    _root_.GlobalTheory.HilbFam.coord (fun i ↦ ((γ • τ : ℍ) : ℂ) + z i * (c * ((γ • τ : ℍ) : ℂ) + t)) (fun i ↦ 1 + z i * c) x i =
      (fun _ ↦ (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1))⁻¹) i *
      _root_.GlobalTheory.HilbFam.coord
        (fun i ↦ (τ : ℂ) + z i * ((c - t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)) * τ + t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ^ 2))
        (fun i ↦ 1 + z i * (c - t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)))
        (_root_.GlobalTheory.HilbFam.JetModular.rowEquiv F γ x) i := by
  have hj : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ≠ 0 := by
    have h := denom_ne_zero (γ : GL (Fin 2) ℝ) τ
    rw [denom] at h
    simpa using h
  have hdet : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  simp only [_root_.GlobalTheory.HilbFam.coord, _root_.GlobalTheory.HilbFam.JetModular.rowEquiv, LinearEquiv.ofLinear_apply,
    Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.map_apply, map_add,
    map_mul, map_intCast, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast,
    specialLinearGroup_apply, coe_mk, eq_intCast]
  set j := ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) with hj_def
  have hji : j * j⁻¹ = 1 := mul_inv_cancel₀ hj
  rw [div_eq_mul_inv]
  linear_combination (-(((i (x 0) : ℝ) : ℂ) * z i * t + ((i (x 1) : ℝ) : ℂ) * (1 + z i * c))) * hji -
    ((i (x 0) : ℝ) : ℂ) * z i * t * j * j⁻¹ * hdet

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
set_option autoImplicit false in
private lemma card_realEmbeddings_eq_finrank (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Fintype.card (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) = Module.finrank ℚ F := by
  rw [← NumberField.Embeddings.card F ℂ]
  refine Fintype.card_of_bijective (f := fun φ : F →+* ℝ ↦ Complex.ofRealHom.comp φ) ⟨?_, ?_⟩
  · intro φ ψ h
    ext x
    simpa using congrArg (fun f : F →+* ℂ ↦ f x) h
  · intro ψ
    have hψ : ComplexEmbedding.IsReal ψ := InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal _)
    exact ⟨hψ.embedding, by ext x; simp [hψ.coe_embedding_apply]⟩


open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
set_option autoImplicit false in
theorem _root_.GlobalTheory.HilbFam.JetModular.jet_smul : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (γ : SL(2, ℤ)) (τ : ℍ) (c t : ℂ), Even k → _root_.GlobalTheory.HilbFam.jet k L κ ((γ • τ : ℍ) : ℂ) c t = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ (k * Module.finrank ℚ F) * _root_.GlobalTheory.HilbFam.jet k (_root_.GlobalTheory.HilbFam.mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ)) κ τ (c - t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)) (t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ^ 2) := by
  intro F _ _ _ k L κ γ τ c t hk
  have hj : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ≠ 0 := by
    have h := denom_ne_zero (γ : GL (Fin 2) ℝ) τ
    rw [denom] at h
    simpa using h
  unfold _root_.GlobalTheory.HilbFam.jet
  rw [← iterD_const_mul]
  congr 1
  funext z
  rw [_root_.GlobalTheory.HilbFam.gval_linear_change F k L (_root_.GlobalTheory.HilbFam.mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ))
    (_root_.GlobalTheory.HilbFam.JetModular.rowEquiv F γ) _ _ _ _ (fun _ ↦ ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)⁻¹) hk
    (mem_iff_sl2_equiv_mem_mulMat F L γ) (fun _ ↦ inv_ne_zero hj)
    (fun x i ↦ embeddingCoord_sl2_smul_lemma_3 F γ τ c t z x i)]
  rw [Finset.prod_const, Finset.card_univ, card_realEmbeddings_eq_finrank]
  simp only [inv_pow, inv_inv, ← pow_mul, mul_comm (Module.finrank ℚ F) k]
  ring

end GlobalTheory.HilbFam.JetModular
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiPeriodNormalisedJetModularTransform
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma length_word_eq_sum {I : Type} [Fintype I] (κ : I → ℕ) :
    (_root_.GlobalTheory.HilbFam.word κ).length = ∑ i, κ i := by
  unfold _root_.GlobalTheory.HilbFam.word
  simp [List.length_flatMap, Finset.sum_toList]

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma lineDeriv_const_mul_comp_smul {I : Type} (f : (I → ℂ) → ℂ) (a c : ℂ)
    (z v : I → ℂ) :
    lineDeriv ℂ (fun z => a * f (c • z)) z v = a * c * lineDeriv ℂ f (c • z) v := by
  simp only [lineDeriv]
  have h : (fun t : ℂ => a * f (c • (z + t • v))) =
      fun t => a * (fun s : ℂ => f (c • z + s • v)) (c * t) := by
    funext t
    simp only [smul_add, smul_smul, mul_comm c t]
  rw [h]
  calc deriv (fun t => a * (fun s : ℂ => f (c • z + s • v)) (c * t)) 0
      = a * deriv (fun t => (fun s : ℂ => f (c • z + s • v)) (c * t)) 0 := by
        rw [deriv_const_mul_field']
    _ = a * (c • deriv (fun s : ℂ => f (c • z + s • v)) (c * 0)) :=
        congrArg (a * ·) (deriv_comp_mul_left c (fun s : ℂ => f (c • z + s • v)) 0)
    _ = a * c * deriv (fun t : ℂ => f (c • z + t • v)) 0 := by
        rw [mul_zero, smul_eq_mul, mul_assoc]

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma iterD_comp_smul {I : Type} [DecidableEq I] (c : ℂ)
    (u : List I) (f : (I → ℂ) → ℂ) (z : I → ℂ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u (fun z => f (c • z)) z =
      c ^ u.length * _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u f (c • z) := by
  induction u generalizing z with
  | nil => simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD]
  | cons i u ih =>
    simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD, List.foldr_cons] at ih ⊢
    rw [show List.foldr _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.partialD (fun z => f (c • z)) u =
      fun z => c ^ u.length * List.foldr _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.partialD f u (c • z) from funext ih]
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.partialD
    rw [lineDeriv_const_mul_comp_smul, List.length_cons, pow_succ]

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma jet_mul_eq_pow_sum_mul {F : Type} [Field F] [NumberField F] (k : ℕ)
    (L : _root_.GlobalTheory.HilbFam.Lat F) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (τ c t lam : ℂ) :
    _root_.GlobalTheory.HilbFam.jet k L κ τ (lam * c) (lam * t) =
      lam ^ (∑ i, κ i) * _root_.GlobalTheory.HilbFam.jet k L κ τ c t := by
  unfold _root_.GlobalTheory.HilbFam.jet
  rw [← length_word_eq_sum κ, ← smul_zero lam,
    ← iterD_comp_smul]
  congr 1
  · funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 2 <;> funext i <;> ring
  · exact smul_zero lam


open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.hfun_slash : _root_.GlobalTheory.LatJet.EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F), 1 ≤ s → 0 < N → _root_.GlobalTheory.HilbFam.HasLevel N L → ∀ (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (γ : SL(2, ℤ)) (Ch Ch' : ℍ → ℂ) (τ : ℍ), (∃ L', _root_.GlobalTheory.HilbFam.HasLevel N L' ∧ L' = _root_.GlobalTheory.HilbFam.mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ)) → Ch (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ 2 * Ch' τ - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) / (2 * Real.pi * Complex.I) → _root_.GlobalTheory.HilbFam.hfun (2 * s) L κ Ch (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ _root_.GlobalTheory.HilbFam.wt (2 * s) κ * _root_.GlobalTheory.HilbFam.hfun (2 * s) (_root_.GlobalTheory.HilbFam.mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ)) κ Ch' τ := by
  intro _ F _ _ _ _ s N L _ _ _ κ γ Ch Ch' τ _ hCh
  have hP : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  simp only [_root_.GlobalTheory.HilbFam.hfun]
  rw [_root_.GlobalTheory.HilbFam.JetModular.jet_smul F (2 * s) L κ γ τ _ _ (even_two_mul s)]
  set j : ℂ := ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) with hj
  set P : ℂ := 2 * Real.pi * Complex.I with hPdef
  have hc : P ^ 2 * Ch (γ • τ) - -P * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * j =
      j ^ 2 * (P ^ 2 * Ch' τ) := by
    rw [hCh]
    field_simp
    ring
  rw [hc, show -P * j ^ 2 = j ^ 2 * -P by ring, jet_mul_eq_pow_sum_mul,
    _root_.GlobalTheory.HilbFam.wt, ← pow_mul, pow_add j]
  ring

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiPeriodNormalisedJetModularTransformStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiPeriod_normalised_jet_modular_transform : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (κ : Emb F → ℕ) (γ : SL(2, ℤ)) (Ch Ch' : ℍ → ℂ) (τ : ℍ), (∃ L', HasLevel N L' ∧ L' = mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ)) → Ch (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ 2 * Ch' τ - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) / (2 * Real.pi * Complex.I) → hfun (2 * s) L κ Ch (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ wt (2 * s) κ * hfun (2 * s) (mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ)) κ Ch' τ := by
  first | exact @GlobalTheory.HilbFam.hfun_slash | exact GlobalTheory.HilbFam.hfun_slash | (intros; apply GlobalTheory.HilbFam.hfun_slash <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistByMatrixModNMulSL2Z
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistByMatrixModNMulSL2Z
set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam.TwistSL

theorem vecMul_mem_stdLat {F : Type} [Field F] [NumberField F] (B : Matrix (Fin 2) (Fin 2) ℤ) {w : Fin 2 → F}
    (hw : w ∈ stdLat F) : Matrix.vecMul w (B.map (Int.cast : ℤ → F)) ∈ stdLat F := by
  intro j _
  have h0 := hw 0 (Set.mem_univ _)
  have h1 := hw 1 (Set.mem_univ _)
  have e : Matrix.vecMul w (B.map (Int.cast : ℤ → F)) j = B 0 j • w 0 + B 1 j • w 1 := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  change Matrix.vecMul w (B.map (Int.cast : ℤ → F)) j ∈ (1 : Submodule (𝓞 F) F)
  rw [e]
  exact Submodule.add_mem _ (zsmul_mem h0 _) (zsmul_mem h1 _)

theorem map_cast_mul (R : Type) [CommRing R] (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * B).map (Int.cast : ℤ → R) = A.map (Int.cast : ℤ → R) * B.map (Int.cast : ℤ → R) :=
  Matrix.map_mul (f := Int.castRingHom R)

theorem twist_mul_sl : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F) (α : Matrix (Fin 2) (Fin 2) (ZMod N)) (γ : SL(2, ℤ)), L ≤ stdLat F → twist N L (α * (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)) = mulMat (twist N L α) (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  intro F _ _ _ N L α γ hL
  obtain ⟨A, rfl⟩ : ∃ A : Matrix (Fin 2) (Fin 2) ℤ, α = A.map (Int.cast : ℤ → ZMod N) :=
    ⟨α.map (ZMod.cast : ZMod N → ℤ), by ext i j; simp⟩
  rw [← map_cast_mul]
  have hinv : ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → F) *
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → F) = 1 := by
    rw [← map_cast_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    exact Matrix.map_one _ Int.cast_zero Int.cast_one
  ext v
  rw [GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L _ v hL]
  constructor
  · rintro ⟨y, hy, w, hw, rfl⟩
    refine ⟨Matrix.vecMul y (A.map (Int.cast : ℤ → F)) +
      (N : F) • Matrix.vecMul w (((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → F)), ?_, ?_⟩
    · exact (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A _ hL).2 ⟨y, hy, _, vecMul_mem_stdLat _ hw, rfl⟩
    · rw [LinearMap.restrictScalars_apply, Matrix.vecMulLinear_apply, Matrix.add_vecMul, Matrix.smul_vecMul, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hinv,
        Matrix.vecMul_one, map_cast_mul]
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨y, hy, w, hw, rfl⟩ := (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A _ hL).1 hu
    refine ⟨y, hy, _, vecMul_mem_stdLat (γ : Matrix (Fin 2) (Fin 2) ℤ) hw, ?_⟩
    rw [LinearMap.restrictScalars_apply, Matrix.vecMulLinear_apply, Matrix.add_vecMul, Matrix.smul_vecMul, Matrix.vecMul_vecMul, map_cast_mul]

end GlobalTheory.HilbFam.TwistSL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistByMatrixModNMulSL2ZStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertLatticeTwistByMatrixModN_mul_SL2Z : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F) (α : Matrix (Fin 2) (Fin 2) (ZMod N)) (γ : SL(2, ℤ)), L ≤ stdLat F → twist N L (α * (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)) = mulMat (twist N L α) (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  first | exact @GlobalTheory.HilbFam.TwistSL.twist_mul_sl | exact GlobalTheory.HilbFam.TwistSL.twist_mul_sl | (intros; apply GlobalTheory.HilbFam.TwistSL.twist_mul_sl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertTwistedLatticeJetsModularFamily
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem isFam_hfun_twist : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (ι : Type) (act : ι → SL(2, ℤ) → ι) (α : ι → Matrix (Fin 2) (Fin 2) (ZMod N)) (Ch : ι → ℍ → ℂ) (κ : Emb F → ℕ), (∀ i γ, α (act i γ) = α i * (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)) → (∀ i (γ : SL(2, ℤ)) (τ : ℍ), Ch i (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ 2 * Ch (act i γ) τ - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) / (2 * Real.pi * Complex.I)) → IsFam act (wt (2 * s) κ : ℕ) (fun i ↦ hfun (2 * s) (twist N L (α i)) κ (Ch i)) := by
  intro hE F _ _ _ hF s N L hs hN hL ι act α Ch κ hα hC
  rw [GlobalTheory.T.isSLTwoPermutedModularFamily_iff_values]
  intro i γ τ
  have htw : twist N L (α (act i γ)) = mulMat (twist N L (α i)) (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [hα]; exact GlobalTheory.T.hilbertLatticeTwistByMatrixModN_mul_SL2Z F N L (α i) γ hL.2
  have h := GlobalTheory.T.quasiPeriod_normalised_jet_modular_transform hE F hF s N (twist N L (α i)) hs hN (GlobalTheory.T.hilbertLatticeTwist_hasLevel F N L (α i) hL) κ γ (Ch i)
    (Ch (act i γ)) τ ⟨_, GlobalTheory.T.hilbertLatticeTwist_hasLevel F N L (α (act i γ)) hL, htw⟩ (hC i γ τ)
  rw [zpow_natCast]
  beta_reduce
  rw [h, htw]

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertTwistedLatticeJetsModularFamilyStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertTwistedLattice_jets_modular_family : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (ι : Type) (act : ι → SL(2, ℤ) → ι) (α : ι → Matrix (Fin 2) (Fin 2) (ZMod N)) (Ch : ι → ℍ → ℂ) (κ : Emb F → ℕ), (∀ i γ, α (act i γ) = α i * (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)) → (∀ i (γ : SL(2, ℤ)) (τ : ℍ), Ch i (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ 2 * Ch (act i γ) τ - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) / (2 * Real.pi * Complex.I)) → IsFam act (wt (2 * s) κ : ℕ) (fun i ↦ hfun (2 * s) (twist N L (α i)) κ (Ch i)) := by
  first | exact @GlobalTheory.HilbFam.isFam_hfun_twist | exact GlobalTheory.HilbFam.isFam_hfun_twist | (intros; apply GlobalTheory.HilbFam.isFam_hfun_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassModularTransformationLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassModularTransformationLevel
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem wB_smul_transform : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ), wB N x (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ 2 * wB N (vact N x γ) τ - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) / (2 * Real.pi * Complex.I) := by
  intro N _ x γ τ
  have h := congrFun (EisensteinSeries.G2_slash_action γ) τ
  rw [ModularForm.SL_slash_apply, Pi.sub_apply, EisensteinSeries.D2] at h
  have hj : UpperHalfPlane.denom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  have hd : UpperHalfPlane.denom γ τ = ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
    simp [ModularGroup.denom_apply]
  have hG : EisensteinSeries.G2 (γ • τ) = UpperHalfPlane.denom γ τ ^ 2 * EisensteinSeries.G2 τ
      - 2 * Real.pi * Complex.I * ((γ 1 0 : ℤ) : ℂ) * UpperHalfPlane.denom γ τ := by
    rw [zpow_neg, zpow_ofNat] at h
    field_simp at h
    linear_combination h
  have hwp := ((GlobalTheory.QFam.isFam_iff_values _ _ _ _).1 (GlobalTheory.T.weierstrassP_torsion_isModularFamily N).1) x γ τ
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [zpow_ofNat] at hwp
  rw [wB, wB, gN, gN, hwp, hG, hd]
  field_simp
  ring
end GlobalTheory.WpFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassModularTransformationLevelStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrass_modular_transformation_level : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ), wB N x (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ 2 * wB N (vact N x γ) τ - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) / (2 * Real.pi * Complex.I) := by
  first | exact @GlobalTheory.WpFam.wB_smul_transform | exact GlobalTheory.WpFam.wB_smul_transform | (intros; apply GlobalTheory.WpFam.wB_smul_transform <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertFamilyWeierstrassTwist
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam

namespace GlobalTheory.HilbFam

theorem famGL_coe_redGL (N : ℕ) (γ : SL(2, ℤ)) :
    ((redGL N γ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) := rfl

theorem famGL_vmul_gact (N : ℕ) (y : Fin 2 → ZMod N) (α : GL (Fin 2) (ZMod N)) (γ : SL(2, ℤ)) :
    vmul y (gact N 1 α γ) = vact N (vmul y α) γ := by
  rw [gact_one, vact, vmul, vmul, vmul, Matrix.vecMul_vecMul, Units.val_mul]

theorem isFam_hfun_GL : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ (y : Fin 2 → ZMod N) (κ : Emb F → ℕ), IsFam (gact N 1) (wt (2 * s) κ : ℕ) (fun α ↦ hfun (2 * s) (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ (wB N (vmul y (α)))) := by
  intro hE F _ _ _ hF s N _ L hs hL y κ
  refine GlobalTheory.T.hilbertTwistedLattice_jets_modular_family hE F hF s N L hs (Nat.pos_of_ne_zero (NeZero.ne N)) hL (GL (Fin 2) (ZMod N)) (gact N 1)
    (fun α ↦ (α : Matrix (Fin 2) (Fin 2) (ZMod N))) (fun α ↦ wB N (vmul y α)) κ ?_ ?_
  · intro α γ
    simp only [gact_one, Units.val_mul, famGL_coe_redGL]
  · intro α γ τ
    simp only [famGL_vmul_gact]
    exact GlobalTheory.T.weierstrass_modular_transformation_level N (vmul y α) γ τ

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertFamilyWeierstrassTwistStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_family_weierstrass_twist : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ (y : Fin 2 → ZMod N) (κ : Emb F → ℕ), IsFam (gact N 1) (wt (2 * s) κ : ℕ) (fun α ↦ hfun (2 * s) (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ (wB N (vmul y (α)))) := by
  first | exact @GlobalTheory.HilbFam.isFam_hfun_GL | exact GlobalTheory.HilbFam.isFam_hfun_GL | (intros; apply GlobalTheory.HilbFam.isFam_hfun_GL <;> assumption)
end
