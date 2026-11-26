module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConstantTermEqZeroOfIsCuspidal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.ExistsCompactFundamentalSetOfHeightLe
open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

theorem UpperTheory.exists_compact_fundamental_set_of_height_le :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (R : ℝ), ∃ C : Set (G1 K n), IsCompact C ∧
        ∀ x : G1 K n, qht x ≤ R → ∃ g ∈ Gam K n, ∃ y ∈ C, x = g * y := by
  intro K _ _ n R
  obtain ⟨c, N, hc, h⟩ := UpperTheory.adelicNorm_vecMul_ge_of_height K n
  have hR : 0 < max 1 R + 1 := by positivity
  obtain ⟨C, hC, hC'⟩ := Reduction.exists_isCompact_forall_of_pos_le_height (K := K) (n := n)
    (ε := (c * (max 1 R + 1) ^ N)⁻¹) (by positivity)
  refine ⟨Subtype.val ⁻¹' C, isClosed_normOneGL.isClosedEmbedding_subtypeVal.isCompact_preimage hC, fun x hx => ?_⟩
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt (hx.trans_lt ((le_max_right 1 R).trans_lt (lt_add_one _)))
  obtain ⟨δ, hδ, y, hy, e⟩ := hC' ((γ : G1 K n) * x : G1 K n) ((γ : G1 K n) * x).2 fun v hv => by
      rw [inv_le_iff_one_le_mul₀' (by positivity)]
      have h0 := h ((γ : G1 K n) * x : G1 K n) v hv
      have hq := AutomorphicForm.height_pos (K := K) ((γ : G1 K n) * x : G1 K n).1
      have hp : 0 ≤ Reduction.height ((γ : G1 K n) * x : G1 K n).1 v := by
        by_contra hn
        have : 0 ≤ c * AutomorphicForm.height (K := K) ((γ : G1 K n) * x : G1 K n).1 ^ N := by
          positivity
        nlinarith [not_le.1 hn]
      exact h0.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hq.le hγ.le N) hc.le) hp)
  let d : G1 K n := ⟨δ, rationalGL_le_normOneGL hδ⟩
  have hd : d ∈ Gam K n := hδ
  refine ⟨(γ : G1 K n)⁻¹ * d, mul_mem (inv_mem γ.2) hd, d⁻¹ * ((γ : G1 K n) * x), ?_, by group⟩
  have e' : δ * y = ((γ : G1 K n) * x : G1 K n).1 := e
  change δ⁻¹ * ((γ : G1 K n) * x : G1 K n).1 ∈ C
  rw [← e', inv_mul_cancel_left]
  exact hy
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.AdelicGLGaloisBaseChangeDiagonalCompat
open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem galAd_alg (σ : E ≃ₐ[F] E) (x : E) :
    galAd σ (algebraMap E 𝔸[E] x) = algebraMap E 𝔸[E] (σ x) := by
  have h : (adeleTensorEquiv F E).symm (algebraMap E 𝔸[E] x) = x ⊗ₜ[F] 1 := by
    rw [AlgEquiv.symm_apply_eq, adeleTensorEquiv_tmul, map_one, mul_one]
  change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
    ((adeleTensorEquiv F E).symm (algebraMap E 𝔸[E] x))) = _
  rw [h, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul, map_one, map_one, mul_one]
  rfl

private theorem rat_of_map (a : 𝔸[F]) (x : E) (h : adeleMap F E a = algebraMap E 𝔸[E] x) :
    ∃ y : F, algebraMap F 𝔸[F] y = a := by
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F E)
    (LinearMap.ker_eq_bot.2 (algebraMap F E).injective)
  have h1 : φ 1 = 1 := by simpa using LinearMap.congr_fun hφ 1
  have h2 : (1 : E) ⊗ₜ[F] a = x ⊗ₜ[F] (1 : 𝔸[F]) := by
    apply (adeleTensorEquiv F E).injective
    rw [adeleTensorEquiv_tmul, adeleTensorEquiv_tmul, map_one, map_one, one_mul, mul_one, h]
  have h3 := congrArg (fun z => TensorProduct.lid F 𝔸[F] (LinearMap.rTensor 𝔸[F] φ z)) h2
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, h1, one_smul] at h3
  exact ⟨φ x, by rw [h3, Algebra.algebraMap_eq_smul_one]⟩

private theorem mat_rat {n : ℕ} (t : AdelicGLn.AdelicGL F n) (h : GL (Fin n) E)
    (e : mapGL n (adeleMap F E) t = AdelicGLn.diagonal E n h) :
    ∃ M : Matrix (Fin n) (Fin n) F, (algebraMap F 𝔸[F]).mapMatrix M = (t : Matrix (Fin n) (Fin n) 𝔸[F]) := by
  have : ∀ i j, ∃ y : F, algebraMap F 𝔸[F] y = (t : Matrix (Fin n) (Fin n) 𝔸[F]) i j := fun i j =>
    rat_of_map _ ((h : Matrix (Fin n) (Fin n) E) i j)
      (congrArg (fun u : AdelicGLn.AdelicGL E n => (u : Matrix (Fin n) (Fin n) 𝔸[E]) i j) e)
  choose M hM using this
  exact ⟨Matrix.of M, Matrix.ext hM⟩
end

theorem UpperTheory.adelicGL_galois_baseChange_diagonal_compat :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ),
        (∀ h : GL (Fin n) E, mapGL n (galAd σ) (AdelicGLn.diagonal E n h) = AdelicGLn.diagonal E n (sigmaGL σ h)) ∧
        (∀ g : GL (Fin n) F, mapGL n (adeleMap F E) (AdelicGLn.diagonal F n g) = AdelicGLn.diagonal E n (incl g)) ∧
        ∀ (t : AdelicGLn.AdelicGL F n) (h : GL (Fin n) E), mapGL n (adeleMap F E) t = AdelicGLn.diagonal E n h →
          ∃ g : GL (Fin n) F, t = AdelicGLn.diagonal F n g := by
  intro F E _ _ _ _ _ σ n
  refine ⟨fun h => ?_, fun g => ?_, fun t h e => ?_⟩
  · refine Units.ext (Matrix.ext fun i j => ?_)
    exact galAd_alg σ (h.1 i j)
  · refine Units.ext (Matrix.ext fun i j => ?_)
    exact adeleMap_algebraMap (K := F) (L := E) (g.1 i j)
  · obtain ⟨M, hM⟩ := mat_rat t h e
    obtain ⟨N, hN⟩ := mat_rat t⁻¹ h⁻¹ (by rw [map_inv, map_inv, e])
    have hinj : Function.Injective ((algebraMap F 𝔸[F]).mapMatrix : Matrix (Fin n) (Fin n) F →+* _) :=
      Matrix.map_injective (AdeleRing.algebraMap_injective (𝓞 F) F)
    refine ⟨⟨M, N, hinj ?_, hinj ?_⟩, Units.ext hM.symm⟩
    · rw [map_mul, hM, hN, map_one, Units.mul_inv]
    · rw [map_mul, hM, hN, map_one, Units.inv_mul]
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.TwNormConjDiagonalEqConjNormGL
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing TensorProduct

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem galAd_apply (σ : E ≃ₐ[F] E) (y : 𝔸[E]) : galAd σ y = σ • y := by
  have h : galAd σ = MulSemiringAction.toRingHom (E ≃ₐ[F] E) 𝔸[E] σ := by
    refine adeleRingHom_ext (K := F) (fun l => ?_) (fun a => ?_)
    · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
        ((adeleTensorEquiv F E).symm (algebraMap E 𝔸[E] l))) = σ • algebraMap E 𝔸[E] l
      rw [adeleTensorEquiv_symm_algebraMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
        AdeleBaseChange.smul_algebraMap, map_one, map_one, mul_one]
      rfl
    · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
        ((adeleTensorEquiv F E).symm (adeleMap F E a))) = σ • adeleMap F E a
      rw [adeleTensorEquiv_symm_adeleMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
        smul_adeleMap, map_one, map_one, one_mul]
      rfl
  rw [h]
  rfl

private theorem gal_diag (σ : E ≃ₐ[F] E) (n : ℕ) (h : GL (Fin n) E) :
    mapGL n (galAd σ) (AdelicGLn.diagonal E n h) = AdelicGLn.diagonal E n (sigmaGL σ h) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change galAd σ (algebraMap E 𝔸[E] (h.1 i j)) = algebraMap E 𝔸[E] (σ (h.1 i j))
  rw [galAd_apply, AdeleBaseChange.smul_algebraMap]

private noncomputable def thetaE (σ : E ≃ₐ[F] E) (n : ℕ) : Monoid.End (AdelicGLn.AdelicGL E n) :=
  mapGL n (galAd σ)

private theorem theta_pow_val (σ : E ≃ₐ[F] E) (n m : ℕ) (g : AdelicGLn.AdelicGL E n) (i j : Fin n) :
    ((((thetaE σ n ^ m) g :
        AdelicGLn.AdelicGL E n) : Matrix (Fin n) (Fin n) 𝔸[E]) i j) =
      (σ ^ m) • ((g : Matrix (Fin n) (Fin n) 𝔸[E]) i j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ_apply', pow_succ', mul_smul, ← ih, ← galAd_apply]
    rfl

private theorem theta_pow_eq_one [IsGalois F E] (σ : E ≃ₐ[F] E) (n : ℕ) :
    thetaE σ n ^ Module.finrank F E = 1 := by
  have hσ : σ ^ Module.finrank F E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank F E]
    exact pow_card_eq_one'
  have key : ∀ g : AdelicGLn.AdelicGL E n, (thetaE σ n ^ Module.finrank F E) g = g :=
    fun g => Units.ext (Matrix.ext fun i j => by rw [theta_pow_val, hσ, one_smul])
  exact MonoidHom.ext key

private theorem theta_pow_diag (σ : E ≃ₐ[F] E) (n m : ℕ) (h : GL (Fin n) E) :
    (thetaE σ n ^ m) (AdelicGLn.diagonal E n h) =
      AdelicGLn.diagonal E n (((sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ m) h) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ_apply', pow_succ_apply', ih]
    exact gal_diag σ n _

private theorem twNorm_diag (σ : E ≃ₐ[F] E) (n m : ℕ) (h : GL (Fin n) E) :
    twNorm (thetaE σ n) m (AdelicGLn.diagonal E n h) =
      AdelicGLn.diagonal E n (twNorm (sigmaGL σ) m h) := by
  induction m with
  | zero => rw [twNorm_zero, twNorm_zero, map_one]
  | succ m ih => rw [twNorm_succ, twNorm_succ, ih, theta_pow_diag, map_mul]

end

theorem UpperTheory.twNorm_conj_diagonal_eq_conj_normGL :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E) (n : ℕ) (δ : GL (Fin n) E) (x : AdelicGLn.AdelicGL E n),
        twNorm (G := AdelicGLn.AdelicGL E n) (mapGL n (galAd σ)) (Module.finrank F E) (x⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) x) =
          x⁻¹ * AdelicGLn.diagonal E n (normGL σ δ) * x := by
  intro F E _ _ _ _ _ _ σ n δ x
  have h := twNorm_twConj_of_pow_eq_one (thetaE σ n) (theta_pow_eq_one σ n) x
    (AdelicGLn.diagonal E n δ)
  rw [twNorm_diag] at h
  exact h
end
