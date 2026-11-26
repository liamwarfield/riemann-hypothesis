module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.ResidualAutomorphyOfLinkedEnds
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.SideGLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinKTest
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.FinG
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ThetaThetaAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.NormPosPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsHermitianConjugationOfUnitaryTau
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HermitianDatumUniqueUpToScalar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsStarFixedRotationBasisOfCharpoly
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.BasePt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsLinearEquivSpOfIsUnitDetBasis
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

private theorem vecMul_of_three {R : Type} [CommRing R] (a b c : R) (e v w : Fin 3 → R) :
    ![a, b, c] ᵥ* (Matrix.of ![e, v, w]) = a • e + b • v + c • w := by
  ext j
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three]

theorem UpperTheory.exists_linearEquiv_sp_of_isUnit_det_basis :
    ∀ (K : Type) [Field K] (Δ τ : K) (e v w : Fin 3 → Lsq K Δ), IsUnit (Matrix.of ![e, v, w]).det →
        ∃ P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ), ∀ x : Sp Δ τ, P x = x.1 • e + x.2.re • v + x.2.im • w := by
  intro K _ Δ τ e v w h
  set M : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := Matrix.of ![e, v, w] with hM
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M h
  have h2 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M h
  refine ⟨{ toFun := fun x => x.1 • e + x.2.re • v + x.2.im • w
            map_add' := ?_
            map_smul' := ?_
            invFun := fun y => ((y ᵥ* M⁻¹) 0, ⟨(y ᵥ* M⁻¹) 1, (y ᵥ* M⁻¹) 2⟩)
            left_inv := ?_
            right_inv := ?_ }, fun x => rfl⟩
  · intro x y
    simp only [Prod.fst_add, Prod.snd_add, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, add_smul]
    abel
  · intro r x
    simp [mul_smul, smul_add]
  · intro x
    have : (x.1 • e + x.2.re • v + x.2.im • w) ᵥ* M⁻¹ = ![x.1, x.2.re, x.2.im] := by
      rw [← vecMul_of_three, ← hM, Matrix.vecMul_vecMul, h1, Matrix.vecMul_one]
    simp only [this]
    ext <;> simp
  · intro y
    have : ((y ᵥ* M⁻¹) 0) • e + ((y ᵥ* M⁻¹) 1) • v + ((y ᵥ* M⁻¹) 2) • w = (y ᵥ* M⁻¹) ᵥ* M := by
      rw [hM, ← vecMul_of_three]
      congr 1
      funext i; fin_cases i <;> rfl
    simp only [this]
    rw [Matrix.vecMul_vecMul, h2, Matrix.vecMul_one]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CubicCharpolyDiscriminant
open Matrix Polynomial UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

namespace UpperTheory.Reformulated.B.CubicCharpolyDiscriminant

private lemma charpoly_three {R : Type} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) :
    M.charpoly = X ^ 3 - C M.trace * X ^ 2 + C M.adjugate.trace * X - C M.det := by
  simp [Matrix.charpoly, Matrix.det_fin_three, Matrix.trace_fin_three, Matrix.adjugate_fin_three,
    Matrix.charmatrix_apply_eq, Matrix.charmatrix_apply_ne]
  ring

private lemma charpoly_tw {R : Type} [CommRing R] [StarRing R] (A M : Matrix (Fin 3) (Fin 3) R)
    (hA : A * star A = 1) (hM : M * star M = 1) (h : M = A * A.map star) :
    star M.trace = M.trace ∧ M.charpoly = (X - 1) * (X ^ 2 - C (M.trace - 1) * X + 1) := by
  have h1 : star M.trace = M.trace := by
    subst h
    simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply,
      star_add, star_mul', star_star]
    ring
  have h2 : M.det = 1 := by
    have e : A.map star = (star A)ᵀ := by
      ext i j
      simp [Matrix.star_apply]
    rw [h, det_mul, e, det_transpose, ← det_mul, hA, det_one]
  have h3 : M.adjugate = star M := by
    calc M.adjugate = M.adjugate * (M * star M) := by rw [hM, Matrix.mul_one]
      _ = star M := by rw [← Matrix.mul_assoc, adjugate_mul, h2, one_smul, Matrix.one_mul]
  refine ⟨h1, ?_⟩
  rw [charpoly_three, h3, h2, star_eq_conjTranspose, trace_conjTranspose, h1]
  simp only [map_sub, map_one]
  ring

open scoped Matrix.Norms.L2Operator in
private lemma disc_nonpos (M : Matrix (Fin 3) (Fin 3) ℂ) (hM : M ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ)) (t : ℝ)
    (h : M.charpoly = (X - 1) * (X ^ 2 - C (t : ℂ) * X + 1)) : t ^ 2 - 4 ≤ 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s ^ 2 = t ^ 2 - 4 := ⟨√(t ^ 2 - 4), Real.sq_sqrt hc.le⟩
  set r : ℝ := (t + s) / 2 with hr
  have e : r ^ 2 - t * r + 1 = 0 := by rw [hr]; linarith
  have hroot : (r : ℂ) ∈ spectrum ℂ M := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, h]
    have e' : (r : ℂ) ^ 2 - t * r + 1 = 0 := by exact_mod_cast e
    simp [e']
  have hn := spectrum.norm_eq_one_of_unitary hM hroot
  rw [Complex.norm_real, Real.norm_eq_abs] at hn
  have h2 : r ^ 2 = 1 := by rw [← sq_abs, hn]; norm_num
  have h3 : t * r = 2 := by linarith
  have h4 : t ^ 2 = 4 := by
    calc t ^ 2 = (t * r) ^ 2 := by rw [mul_pow, h2, mul_one]
      _ = 4 := by rw [h3]; norm_num
  linarith

private lemma exists_emb {F : Type} [Field F] (Δ : F) (σ : F →+* ℝ) (h : σ Δ < 0) :
    ∃ φ : Lsq F Δ →+* ℂ, (∀ x, φ (star x) = star (φ x)) ∧ ∀ a, φ (algebraMap F _ a) = σ a := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s * s = -σ Δ := ⟨√(-σ Δ), Real.mul_self_sqrt (by linarith)⟩
  refine ⟨{ toFun := fun x => ⟨σ x.re, σ x.im * s⟩
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩
  · apply Complex.ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · intro x y
    apply Complex.ext
    · simp
      linear_combination (σ x.im * σ y.im) * hs
    · simp
      ring
  · apply Complex.ext <;> simp
  · intro x y
    apply Complex.ext
    · simp
    · simp
      ring
  · intro x
    apply Complex.ext <;> simp
  · intro a
    apply Complex.ext <;> simp

end UpperTheory.Reformulated.B.CubicCharpolyDiscriminant

theorem UpperTheory.Reformulated.B.CubicCharpolyDiscriminant.tauEx :
    UpperTheory.V.Z.Sym.Glob.TauEx := by
  intro F _ _ Δ D hD δ
  set M : U3 Δ := δ * theta Δ δ with hMdef
  obtain ⟨h1, h2⟩ := charpoly_tw (δ : Matrix (Fin 3) (Fin 3) (Lsq F Δ)) (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ))
    δ.2.2 M.2.2 rfl
  have him : (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).trace.im = 0 := by
    have := congrArg QuadraticAlgebra.im h1
    rw [QuadraticAlgebra.im_star] at this
    linear_combination (-1 / 2 : F) * this
  have hτ : algebraMap F (Lsq F Δ) ((M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).trace.re - 1) =
      (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).trace - 1 := by
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, him]
  rw [← hτ] at h2
  generalize (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).trace.re - 1 = τ at h2
  refine ⟨τ, h2, fun hne σ => ?_⟩
  obtain ⟨φ, hφ, hφa⟩ := exists_emb Δ σ (hD.neg σ)
  have hs : star ((M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).map φ) = (star (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ))).map φ := by
    ext i j
    simp only [Matrix.star_apply, Matrix.map_apply, hφ]
  have hu : (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).map φ ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ) := by
    constructor
    · rw [hs, ← Matrix.map_mul, M.2.1, Matrix.map_one _ (map_zero φ) (map_one φ)]
    · rw [hs, ← Matrix.map_mul, M.2.2, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hle := disc_nonpos _ hu (σ τ) (by
    rw [Matrix.charpoly_map, h2]
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add (f := _), Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_one, Polynomial.map_C, hφa])
  have hne' : σ (τ ^ 2 - 4) ≠ 0 := (map_ne_zero σ).2 hne
  have e : σ (τ ^ 2 - 4) = σ τ ^ 2 - 4 := by
    rw [map_sub, map_pow, map_ofNat]
  exact lt_of_le_of_ne (e ▸ hle) hne'
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ClassG
open Matrix

namespace UpperTheory.V.Z.Sym.Glob

open Loc

private theorem unitary_form' {K : Type} [Field K] {Δ : K} (g : U3 Δ) (v w : Fin 3 → Lsq K Δ) :
    ∑ i, ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ v) i * star (((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ w) i) =
      ∑ i, v i * star (w i) := by
  have hu : (g : Matrix (Fin 3) (Fin 3) (Lsq K Δ))ᴴ * (g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = 1 := by
    have := g.2
    rw [Matrix.mem_unitaryGroup_iff'] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  have e1 : ∀ a b : Fin 3 → Lsq K Δ, ∑ i, a i * star (b i) = star b ⬝ᵥ a := by
    intro a b
    simp [dotProduct, mul_comm]
  rw [e1, e1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]

end UpperTheory.V.Z.Sym.Glob

private theorem map_star_mul_divisor {R : Type} [CommRing R] [StarRing R] (A : Matrix (Fin 3) (Fin 3) R) :
    (A * A.map star).map star = A.map star * A := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Matrix.mul_apply, star_sum, star_mul', star_star]

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc in
theorem UpperTheory.V.Z.Sym.Glob.classG :
    UpperTheory.V.Z.Sym.Glob.ClassG := by
  unfold ClassG
  intro K _ _ Δ τ d m hΔ hD δ hδ
  have hreg := hD.reg
  have hnorm := hD.d_norm
  obtain ⟨B, hBB, hNB, hBw⟩ := UpperTheory.exists_hermitian_conjugation_of_unitary_tau K Δ τ hreg d hnorm δ hδ _ rfl
  have hchar := hδ
  rw [HasTau.eq_1] at hchar
  obtain ⟨e, v, hBe, hBv, hNe, hNv, hdet⟩ := UpperTheory.exists_star_fixed_rotation_basis_of_charpoly K Δ τ hΔ hreg B _ hBB hNB hchar
  set N : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) with hN
  have hδe : (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star e = e := (hBw e hBe).1 hNe
  have hδv : (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star v = d.re • v + d.im • N *ᵥ v := (hBw v hBv).2 hNv
  obtain ⟨c, m', hm'u, hm's, hform⟩ := UpperTheory.exists_hermitian_form_of_unitary_rotation_basis K Δ τ hreg N (δ * theta Δ δ).property e v hNe hNv hdet
  obtain ⟨P, hP⟩ := UpperTheory.exists_linearEquiv_sp_of_isUnit_det_basis K Δ τ e v (N *ᵥ v) hdet
  have hform' : ∀ x y : Sp Δ τ, herm (c : K) m' x y = ∑ i, P x i * star (P y i) := by
    intro x y
    rw [hform, hP, hP]
  have h1 : N = (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map star := by
    rw [hN]
    rfl
  have hA : (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * N.map star = N * δ := by
    rw [h1, map_star_mul_divisor, Matrix.mul_assoc]
  have hsemi : ∀ x, P (semi d x) = (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star (P x) := by
    intro x
    rw [hP, hP]
    exact UpperTheory.semilinear_coords_eq_mulVec_star K Δ τ d δ N e v hA hδe hδv hNv x
  have hinv : ∀ x y, herm (c : K) m' (semi d x) (semi d y) = star (herm (c : K) m' x y) := by
    intro x y
    rw [hform', hform', hsemi, hsemi, unitary_form']
    simp [star_sum, mul_comm]
  have hsig := UpperTheory.sigL_eq_of_herm_semilinear_eq_star K Δ τ (c : K) d m' hreg hinv
  have hD' : IsDat (c : K) d m' := ⟨hreg, c.ne_zero, hnorm, hm'u, hm's, hsig⟩
  obtain ⟨t, ht⟩ := UpperTheory.hermitian_datum_unique_up_to_scalar K Δ τ 1 (c : K) d m m' hD hD'
  obtain ⟨δ', ι, hM⟩ := exG_models hD' P hform'
  refine ⟨c, t, ι, P, ?_⟩
  rw [← ht]
  exact ⟨hform', hsemi, hM.tor⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.MapStarMulVec
noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open QuadraticAlgebra Matrix Loc

section Vec

variable {R : Type} [CommRing R] [StarRing R]

private theorem map_star_mulVec (M : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R) :
    M.map star *ᵥ star v = star (M *ᵥ v) := by
  ext i
  simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]

private theorem dot_unitary {X : Matrix (Fin 3) (Fin 3) R} (hX : star X * X = 1) (p q : Fin 3 → R) :
    ∑ i, (X *ᵥ p) i * star ((X *ᵥ q) i) = ∑ i, p i * star (q i) := by
  have h1 : (X *ᵥ p) ⬝ᵥ star (X *ᵥ q) = p ⬝ᵥ star q := by
    rw [dotProduct_comm, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.star_eq_conjTranspose, hX, Matrix.one_mulVec, dotProduct_comm]
  simpa [dotProduct] using h1

private theorem unitary_of_map (T : (Fin 3 → R) →ₗ[R] (Fin 3 → R))
    (h : ∀ p q, ∑ i, T p i * star (T q i) = ∑ i, p i * star (q i)) :
    ∃ M ∈ Matrix.unitaryGroup (Fin 3) R, ∀ p, M *ᵥ p = T p := by
  classical
  have hM : ∀ p, LinearMap.toMatrix' T *ᵥ p = T p := fun p => by
    simpa using congrFun (congrArg DFunLike.coe (Matrix.toLin'_toMatrix' T)) p
  refine ⟨LinearMap.toMatrix' T, ?_, hM⟩
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  simp only [← hM, Matrix.mulVec_single_one] at this
  simpa [Matrix.mul_apply, Matrix.star_apply, mul_comm, Pi.single_apply, Matrix.one_apply, eq_comm, apply_ite (star : R → R)] using this

end Vec

section Shape

variable {K : Type} [Field K] {Δ τ : K}

private theorem semi_semi {d : EL Δ τ} (hd : d * sigL d = ofE Δ (ω : Etau K τ)) (x : Sp Δ τ) :
    semi d (semi d x) = (x.1, ofE Δ (ω : Etau K τ) * x.2) := by
  refine Prod.ext (by simp [semi]) ?_
  change d * sigL (d * sigL x.2) = _
  rw [sigL_mul, sigL_sigL, ← mul_assoc, hd]

private theorem omega_sub_inv (hτ : τ ^ 2 - 4 ≠ 0) : ∃ u : EL Δ τ, (ofE Δ (ω : Etau K τ) - 1) * u = 1 := by
  have h2 : 2 - τ ≠ 0 := fun h => hτ (by linear_combination (-(2 + τ)) * h)
  refine ⟨ofE Δ ⟨(τ - 1) / (2 - τ), -1 / (2 - τ)⟩, ?_⟩
  have e : ofE Δ (ω : Etau K τ) - 1 = ofE Δ ((ω : Etau K τ) - 1) := by
    ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  rw [e, ← ofE_mul, ← ofE_one (Δ := Δ) (τ := τ)]
  congr 1
  ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring

private theorem eq_of_star_eq [CharZero K] {x : Lsq K Δ} (h : star x = x) : x = algebraMap K _ x.re := by
  have := congrArg QuadraticAlgebra.im h
  simp at this
  have h2 : (2 : K) * x.im = 0 := by linear_combination -this
  have h3 : x.im = 0 := by simpa using h2
  ext
  · simp
  · simpa using h3

private theorem alg_inj {x y : K} (h : algebraMap K (Lsq K Δ) x = algebraMap K _ y) : x = y := by
  simpa using congrArg QuadraticAlgebra.re h

private theorem isUnit_of_norm {d : EL Δ τ} (hd : d * sigL d = ofE Δ (ω : Etau K τ)) : IsUnit d := by
  have h : (ω : Etau K τ) * star ω = 1 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    simp [QuadraticAlgebra.norm_def]
  have : d * (sigL d * ofE Δ (star (ω : Etau K τ))) = 1 := by
    rw [← mul_assoc, hd, ← ofE_mul, h, ofE_one]
  exact IsUnit.of_mul_eq_one _ this

private theorem shape [CharZero K] {c₁ c₂ t₁ t₂ : K} {d m n : EL Δ τ} (hτ : τ ^ 2 - 4 ≠ 0)
    (hd : d * sigL d = ofE Δ (ω : Etau K τ)) (hn : m * n = 1)
    (Q : Sp Δ τ →ₗ[Lsq K Δ] Sp Δ τ) (hs : ∀ v, Q (semi d v) = semi d (Q v))
    (hf : ∀ v w, herm c₂ (t₂ • m) (Q v) (Q w) = herm c₁ (t₁ • m) v w) :
    ∃ (s : K) (z : Etau K τ), c₁ = c₂ * s ^ 2 ∧ t₁ = t₂ * QuadraticAlgebra.norm z := by
  set W : EL Δ τ := ofE Δ (ω : Etau K τ) with hW
  obtain ⟨u, hu⟩ := omega_sub_inv (Δ := Δ) hτ
  rw [← hW] at hu
  have hN : ∀ v, Q (v.1, W * v.2) = ((Q v).1, W * (Q v).2) := fun v => by
    rw [← semi_semi hd, hs, hs, semi_semi hd]

  have h1 : (Q (1, 0)).2 = 0 := by
    have := congrArg Prod.snd (hN (1, 0))
    simp only [mul_zero] at this
    have h' : (W - 1) * (Q (1, 0)).2 = 0 := by linear_combination -this
    calc (Q (1, 0)).2 = u * ((W - 1) * (Q (1, 0)).2) := by linear_combination (-(Q (1, 0)).2) * hu
      _ = 0 := by rw [h', mul_zero]

  have h2 : ∀ y : EL Δ τ, (Q (0, y)).1 = 0 := fun y => by
    have e : ((0 : Lsq K Δ), y) = (0, W * (u * y)) - (0, u * y) := by
      refine Prod.ext (by simp) ?_
      change y = W * (u * y) - u * y
      linear_combination (-y) * hu
    rw [e, map_sub, Prod.fst_sub, hN (0, u * y)]
    simp
  set e : EL Δ τ := (Q (0, 1)).2 with he
  have yy : ∀ y : EL Δ τ, y = y.re • (1 : EL Δ τ) + y.im • W := fun y => by
    ext <;> simp [hW, ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have h3 : ∀ y : EL Δ τ, (Q (0, y)).2 = e * y := fun y => by
    have ey : ((0 : Lsq K Δ), y) = y.re • ((0 : Lsq K Δ), (1 : EL Δ τ)) + y.im • (0, W * 1) := by
      refine Prod.ext (by simp) ?_
      simpa using yy y
    have hw := congrArg Prod.snd (hN (0, 1))
    rw [ey, map_add (f := _), map_smul, map_smul, Prod.snd_add, Prod.smul_snd, Prod.smul_snd, hw]
    change y.re • e + y.im • (W * e) = _
    calc _ = e * (y.re • (1 : EL Δ τ) + y.im • W) := by
          rw [mul_add, mul_smul_comm, mul_smul_comm, mul_one, mul_comm e W]
      _ = e * y := by rw [← yy]
  have hdu := isUnit_of_norm hd
  have hsig : sigL e = e := by
    have e1 : semi d ((0 : Lsq K Δ), (1 : EL Δ τ)) = (0, d) := Prod.ext (by simp [semi]) (by simp [semi, sigL_one])
    have h := congrArg Prod.snd (hs (0, 1))
    rw [e1, h3] at h
    change e * d = d * sigL e at h
    exact hdu.mul_left_cancel (by rw [← h, mul_comm])
  have hz : e = ofE Δ ⟨e.re.re, e.im.re⟩ := by
    have a1 : star e.re = e.re := congrArg QuadraticAlgebra.re hsig
    have a2 : star e.im = e.im := congrArg QuadraticAlgebra.im hsig
    ext1
    · exact eq_of_star_eq a1
    · exact eq_of_star_eq a2
  set z : Etau K τ := ⟨e.re.re, e.im.re⟩ with hzdef
  set a : Lsq K Δ := (Q (1, 0)).1 with ha
  have hQ1 : Q (1, 0) = (a, 0) := Prod.ext rfl h1
  have hstar : star a = a := by
    have e1 : semi d ((1 : Lsq K Δ), (0 : EL Δ τ)) = (1, 0) := Prod.ext (by simp [semi]) (by
      have s0 : sigL (0 : EL Δ τ) = 0 := by ext <;> simp [sigL]
      simp [semi, s0])
    have h := congrArg Prod.fst (hs (1, 0))
    rw [e1, hQ1] at h
    exact h.symm
  refine ⟨a.re, z, ?_, ?_⟩
  · have h := hf (1, 0) (1, 0)
    rw [hQ1] at h
    simp only [herm, mul_zero, zero_mul, map_zero, add_zero, star_one, mul_one, hstar] at h
    rw [eq_of_star_eq hstar] at h
    simp only [← map_mul] at h
    linear_combination -alg_inj h
  · have ht : ∀ k : K, QuadraticAlgebra.trace (k • (1 : EL Δ τ)) = 2 * algebraMap K (Lsq K Δ) k := fun k => by
      have : (k • (1 : EL Δ τ)).re = algebraMap K (Lsq K Δ) k := by
        simp [QuadraticAlgebra.re_one, Algebra.algebraMap_eq_smul_one]
      have h0 : (k • (1 : EL Δ τ)).im = 0 := by simp [QuadraticAlgebra.im_one]
      rw [QuadraticAlgebra.trace_def, this, h0, mul_zero, add_zero]
    have hee : e * star (sigL e) = QuadraticAlgebra.norm z • (1 : EL Δ τ) := by
      rw [hsig, hz, ← ofE_star, ← ofE_mul, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
      ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, Algebra.algebraMap_eq_smul_one]
    have h := hf (0, n) (0, 1)
    have q1 : Q (0, n) = (0, e * n) := Prod.ext (h2 n) (h3 n)
    have q2 : Q (0, 1) = (0, e) := Prod.ext (h2 1) (by rw [h3, mul_one])
    rw [q1, q2] at h
    simp only [herm, mul_zero, zero_mul, star_zero, zero_add, sigL_one, star_one, mul_one] at h
    have l1 : t₂ • m * (e * n) * star (sigL e) = (t₂ * QuadraticAlgebra.norm z) • (1 : EL Δ τ) := by
      rw [mul_smul, ← hee]
      simp only [smul_mul_assoc]
      congr 1
      linear_combination (e * star (sigL e)) * hn
    have l2 : t₁ • m * n = t₁ • (1 : EL Δ τ) := by rw [smul_mul_assoc, hn]
    rw [l1, l2, ht, ht] at h
    have h4 : 2 * (t₂ * QuadraticAlgebra.norm z) = 2 * t₁ := alg_inj (Δ := Δ) (by
      rw [map_mul (algebraMap K (Lsq K Δ)) 2, map_mul (algebraMap K (Lsq K Δ)) 2, map_ofNat]
      exact h)
    exact (mul_left_cancel₀ two_ne_zero h4).symm

end Shape

section Main

variable {K : Type} [Field K] {Δ τ : K}

private theorem star_alg (r : K) : star (algebraMap K (Lsq K Δ) r) = algebraMap K _ r := by
  ext <;> simp

private theorem ofE_norm (z : Etau K τ) :
    ofE Δ z * star (ofE Δ z) = QuadraticAlgebra.norm z • (1 : EL Δ τ) := by
  rw [← ofE_star, ← ofE_mul, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, Algebra.algebraMap_eq_smul_one]

private def scaleMap (r : K) (y : EL Δ τ) : Sp Δ τ →ₗ[Lsq K Δ] Sp Δ τ where
  toFun x := (algebraMap K _ r * x.1, y * x.2)
  map_add' a b := by simp [mul_add]
  map_smul' a b := Prod.ext (by simp; ring) (mul_smul_comm _ _ _)

private theorem fwd {c c' : K} {d m m' : EL Δ τ} {δ δ' x : U3 Δ} {ι ι' P P'}
    (h : Models c d m δ ι P) (h' : Models c' d m' δ' ι' P') (hx : δ' = x⁻¹ * δ * theta Δ x) :
    ∃ Q : Sp Δ τ →ₗ[Lsq K Δ] Sp Δ τ, (∀ v, Q (semi d v) = semi d (Q v)) ∧
      ∀ v w, herm c' m' (Q v) (Q w) = herm c m v w := by
  set X : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := ((x⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) with hX
  have hXu : star X * X = 1 := (Matrix.mem_unitaryGroup_iff').1 (x⁻¹ : U3 Δ).2
  let Q : Sp Δ τ →ₗ[Lsq K Δ] Sp Δ τ := P'.symm.toLinearMap ∘ₗ X.mulVecLin ∘ₗ P.toLinearMap
  have hQ : ∀ v, P' (Q v) = X *ᵥ P v := fun v => by simp [Q]
  refine ⟨Q, fun v => P'.injective ?_, fun v w => ?_⟩
  · rw [hQ, h'.semi, hQ, h.semi, hx]
    have e : ((x⁻¹ * δ * theta Δ x : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) =
        X * (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * (x : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map star := rfl
    have e2 : (x : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * X = 1 := by
      rw [hX]; exact congrArg Subtype.val (mul_inv_cancel x)
    rw [e, ← Matrix.mulVec_mulVec, map_star_mulVec, Matrix.mulVec_mulVec _ (x : Matrix (Fin 3) (Fin 3) (Lsq K Δ)), e2,
      Matrix.one_mulVec, Matrix.mulVec_mulVec]
  · rw [h'.form, h.form, hQ, hQ]
    exact dot_unitary hXu _ _

private theorem bwd {c c' : K} {d m m' : EL Δ τ} {δ δ' : U3 Δ} {ι ι' P P'}
    (h : Models c d m δ ι P) (h' : Models c' d m' δ' ι' P')
    (Q : Sp Δ τ →ₗ[Lsq K Δ] Sp Δ τ) (hs : ∀ v, Q (semi d v) = semi d (Q v))
    (hf : ∀ v w, herm c m (Q v) (Q w) = herm c' m' v w) :
    ∃ x, δ' = x⁻¹ * δ * theta Δ x := by
  obtain ⟨M, hM, hMv⟩ := unitary_of_map (P.toLinearMap ∘ₗ Q ∘ₗ P'.symm.toLinearMap) (fun p q => by
    have e := hf (P'.symm p) (P'.symm q)
    rw [h.form, h'.form] at e
    simpa using e)
  have hMP : ∀ v, M *ᵥ P' v = P (Q v) := fun v => by simp [hMv]
  refine ⟨⟨M, hM⟩, ?_⟩
  have key : (⟨M, hM⟩ : U3 Δ) * δ' = δ * theta Δ ⟨M, hM⟩ := by
    apply Subtype.ext
    change M * (δ' : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * M.map star
    have hall : ∀ u, (M * (δ' : Matrix (Fin 3) (Fin 3) (Lsq K Δ))) *ᵥ u =
        ((δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * M.map star) *ᵥ u := fun u => by
      obtain ⟨v, rfl⟩ : ∃ v, u = star (P' v) := ⟨P'.symm (star u), by simp⟩
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← h'.semi, hMP, hs, h.semi, map_star_mulVec, hMP]
    exact Matrix.ext_of_mulVec_single fun i => hall _
  rw [mul_assoc, ← key]
  simp

end Main

theorem conjG : ConjG := by
  intro K _ _ Δ τ d m hΔ hD c c' t t' δ δ' ι ι' P P' h h'
  obtain ⟨n, hn⟩ : ∃ n, m * n = 1 := hD.m_unit.exists_right_inv
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨Q, q1, q2⟩ := fwd h h' hx
    obtain ⟨s, z, e1, e2⟩ := shape hD.reg hD.d_norm hn Q q1 q2
    have hs0 : s ≠ 0 := fun h0 => c.ne_zero (by rw [e1, h0]; simp)
    have hN0 : QuadraticAlgebra.norm z ≠ 0 := fun h0 => t.ne_zero (by rw [e2, h0, mul_zero])
    have hzu : IsUnit z := QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (isUnit_iff_ne_zero.2 hN0)
    refine ⟨⟨Units.mk0 s⁻¹ (inv_ne_zero hs0), Units.ext ?_⟩, hzu.unit⁻¹, ?_⟩
    · simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_mk0]
      rw [e1]
      have := c'.ne_zero
      field_simp
    · rw [map_inv]
      apply Units.ext
      simp only [Units.val_inv_eq_inv_val, Units.coe_map, IsUnit.unit_spec, Units.val_div_eq_div_val, MonoidHom.coe_coe]
      rw [e2]
      have := t'.ne_zero
      field_simp
  · rintro ⟨⟨r, hr⟩, ⟨z, hz⟩⟩
    have C : (c' : K) = c * r * r := by
      have := congrArg Units.val hr
      simp only [Units.val_div_eq_div_val, Units.val_mul] at this
      rw [mul_assoc, ← this]
      have := c.ne_zero
      field_simp
    have T : (t' : K) = t * QuadraticAlgebra.norm (z : Etau K τ) := by
      have := congrArg Units.val hz
      simp only [Units.val_div_eq_div_val, Units.coe_map, MonoidHom.coe_coe] at this
      rw [this]
      have := t.ne_zero
      field_simp
    refine bwd h h' (scaleMap r (ofE Δ z)) (fun v => Prod.ext ?_ ?_) (fun v w => ?_)
    · change algebraMap K (Lsq K Δ) r * star v.1 = star (algebraMap K (Lsq K Δ) r * v.1)
      rw [star_mul', star_alg]
    · change ofE Δ (z : Etau K τ) * (d * sigL v.2) = d * sigL (ofE Δ (z : Etau K τ) * v.2)
      rw [sigL_mul, sigL_ofE]
      ring
    · change herm (c : K) ((t : K) • m) (algebraMap K (Lsq K Δ) r * v.1, ofE Δ (z : Etau K τ) * v.2)
        (algebraMap K (Lsq K Δ) r * w.1, ofE Δ (z : Etau K τ) * w.2) = _
      simp only [herm, sigL_mul, sigL_ofE, star_mul', star_alg]
      congr 1
      · rw [C]
        simp only [map_mul]
        ring
      · congr 1
        simp only [smul_mul_assoc]
        rw [show m * (ofE Δ (z : Etau K τ) * v.2) * (star (ofE Δ (z : Etau K τ)) * star (sigL w.2)) =
          (ofE Δ (z : Etau K τ) * star (ofE Δ (z : Etau K τ))) * (m * v.2 * star (sigL w.2)) by ring,
          ofE_norm, smul_mul_assoc, one_mul, smul_smul, ← T]

end UpperTheory.V.Z.Sym.Glob
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.CharpolyThree
noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open Matrix Polynomial Loc

private theorem charpoly_three {R : Type} [CommRing R] (N : Matrix (Fin 3) (Fin 3) R) :
    N.charpoly = X ^ 3 - C N.trace * X ^ 2 + C N.adjugate.trace * X - C N.det := by
  simp only [Matrix.charpoly, Matrix.det_fin_three, Matrix.charmatrix_apply, Matrix.adjugate_fin_three,
    Matrix.trace_fin_three]
  simp [Matrix.diagonal_apply, Matrix.det_fin_three]
  ring

end UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Glob.tauEx :
    UpperTheory.V.Z.Sym.Glob.TauEx :=
  _root_.UpperTheory.Reformulated.B.CubicCharpolyDiscriminant.tauEx
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.PosLaw
namespace UpperTheory.V.Z.Sym.Glob

open Loc

section

variable {F : Type} [Field F] {Δ τ : F}

private theorem re_mul_star (x : Lsq F Δ) : (x * star x).re = x.re ^ 2 - Δ * x.im ^ 2 := by
  simp
  ring

private theorem nrm_nonneg (σ : F →+* ℝ) (h : σ Δ < 0) (x : Lsq F Δ) : 0 ≤ σ (x * star x).re := by
  rw [re_mul_star]
  simp only [map_sub, map_mul, map_pow]
  nlinarith [sq_nonneg (σ x.re), sq_nonneg (σ x.im)]

private theorem nrm_pos (σ : F →+* ℝ) (h : σ Δ < 0) (x : Lsq F Δ) (hx : x ≠ 0) : 0 < σ (x * star x).re := by
  rw [re_mul_star, map_sub, map_mul, map_pow, map_pow]
  have hne : x.re ≠ 0 ∨ x.im ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx (QuadraticAlgebra.ext (by simp [hc.1]) (by simp [hc.2]))
  have ha := mul_nonneg (neg_nonneg.mpr h.le) (sq_nonneg (σ x.im))
  have hb := sq_nonneg (σ x.re)
  rcases hne with h1 | h1
  · have h2 : σ x.re ≠ 0 := (map_ne_zero σ).mpr h1
    have h3 : 0 < σ x.re ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h2))
    nlinarith
  · have h2 : σ x.im ≠ 0 := (map_ne_zero σ).mpr h1
    have h3 : 0 < σ x.im ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h2))
    have h4 := mul_pos (neg_pos.mpr h) h3
    nlinarith

private theorem herm_re (c t : F) (m : EL Δ τ) (x : Sp Δ τ) :
    (herm c (t • m) x x).re = c * (x.1 * star x.1).re + t * (herm 1 m (0, x.2) (0, x.2)).re := by
  simp [herm]
  ring

private theorem sum_pos (σ : F →+* ℝ) (h : σ Δ < 0) (y : Fin 3 → Lsq F Δ) (hy : y ≠ 0) :
    0 < σ (∑ i, y i * star (y i)).re := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
  have h0 := nrm_nonneg σ h (y 0)
  have h1 := nrm_nonneg σ h (y 1)
  have h2 := nrm_nonneg σ h (y 2)
  have hp := nrm_pos σ h (y i) hi
  rw [Fin.sum_univ_three, QuadraticAlgebra.re_add, QuadraticAlgebra.re_add, map_add (f := _), map_add (f := _)]
  fin_cases i
  · exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hp h1) h2
  · exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos h0 hp) h2
  · exact add_pos_of_nonneg_of_pos (add_nonneg h0 h1) hp

end

end UpperTheory.V.Z.Sym.Glob

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob in
theorem UpperTheory.V.Z.Sym.Glob.posLaw :
    UpperTheory.V.Z.Sym.Glob.PosLaw := by
  intro F _ _ Δ D hD τ d m hm c t
  have hneg := hD.neg
  refine ⟨fun hc ht x hx σ => ?_, fun δ ι P hM => ?_⟩
  · rw [herm_re, map_add (f := _), map_mul, map_mul]
    have h1 := nrm_nonneg σ (hneg σ) x.1
    by_cases h2 : x.2 = 0
    · have hx1 : x.1 ≠ 0 := by
        intro h1'
        exact hx (Prod.ext h1' h2)
      have h4 := nrm_pos σ (hneg σ) x.1 hx1
      have h3 : (herm 1 m (0, x.2) (0, x.2)).re = 0 := by
        rw [h2]
        simp [herm]
      rw [h3, map_zero, mul_zero, add_zero]
      exact mul_pos (hc σ) h4
    · have hx2 : ((0 : Lsq F Δ), x.2) ≠ 0 := by
        intro h'
        exact h2 (congrArg Prod.snd h')
      have h4 := hm _ hx2 σ
      nlinarith [hc σ, ht σ, mul_nonneg (hc σ).le h1, mul_pos (ht σ) h4]
  · have key : ∀ x : Sp Δ τ, x ≠ 0 → TPos (herm c (t • m) x x).re := by
      intro x hx σ
      rw [hM.form x x]
      apply sum_pos σ (hneg σ)
      intro h0
      exact hx (P.injective (h0.trans (map_zero P).symm))
    refine ⟨fun σ => ?_, fun σ => ?_⟩
    · have h1 := key ((1 : Lsq F Δ), 0) (by simp) σ
      simpa [herm] using h1
    · have hx : ((0 : Lsq F Δ), (1 : EL Δ τ)) ≠ 0 := by simp
      have h1 := key _ hx σ
      have h2 : 0 < σ (herm 1 m (0, ((0 : Lsq F Δ), (1 : EL Δ τ)).2) (0, ((0 : Lsq F Δ), (1 : EL Δ τ)).2)).re := hm _ hx σ
      have hz : ((0 : Lsq F Δ) * star (0 : Lsq F Δ)).re = 0 := by simp
      rw [herm_re, map_add (f := _), map_mul, map_mul] at h1
      simp only [hz, map_zero, mul_zero, zero_add] at h1
      nlinarith
end

namespace UpperTheory.V.Z.Sym.Glob

open NumberField Loc

private theorem sum_sub {α : Type} (p : α → Prop) (f : α → ℂ) :
    ∑ᶠ i : {a // p a}, f i.1 = ∑ᶠ a, one (p a) * f a := by
  rw [show (∑ᶠ i : {a // p a}, f i.1) = ∑ᶠ a ∈ {a | p a}, f a from
    finsum_set_coe_eq_finsum_mem (f := f) {a | p a}, finsum_mem_def]
  congr 1
  ext a
  by_cases h : p a <;> simp [one, Set.indicator, h]

private theorem const_sum {α : Type} (c : ℂ) (f : α → ℂ) : ∑ᶠ i, c * f i = c * ∑ᶠ i, f i := by
  exact (mul_finsum f c).symm

variable {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ)

private theorem aux_statement_10 (hD : D.Ok) (t : Dat.Par F) (ht : D.Cone t) (τ : F) (h : D.admitted t τ) : τ ^ 2 - 4 ≠ 0 := by
  intro h0
  obtain ⟨v, hv⟩ := hD.ne
  refine ((hD.sig v hv).reg (t v) (ht v hv) _ (h v hv)).2 ?_
  have h2 : IsIntegral (Ov v) (2 : Kv v) := by
    have := isIntegral_algebraMap (R := Ov v) (A := Kv v) (x := 2)
    rwa [map_ofNat] at this
  have h1 : (τ - 2) * (τ + 2) = 0 := by rw [← h0]; ring
  rcases mul_eq_zero.mp h1 with h1 | h1
  · rw [sub_eq_zero.mp h1, map_ofNat]; exact h2
  · rw [eq_neg_of_add_eq_zero_left h1, map_neg, map_ofNat]; exact h2.neg

private theorem delta_ne (hD : D.Ok) : Δ ≠ 0 := by
  intro h0
  haveI := hD.real
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hw : w.IsReal := IsTotallyReal.isReal w
  have := hD.neg (InfinitePlace.embedding_of_isReal hw)
  rw [h0, map_zero] at this
  exact lt_irrefl _ this

private def GI (t : Dat.Par F) (τ : F) : Prop := D.Good t τ ∧ ∀ v ∉ D.Sg, cv v τ ∈ (algebraMap (Ov v) (Kv v)).range

private theorem sum_GI (hD : D.Ok) (t : Dat.Par F) (ht : D.Cone t) (ch : F → ℂ) (e : ℂ) :
    ∑ᶠ τ : {τ // GI D t τ}, ch τ.1 * ms τ.1 * (D.nS τ.1 + e * D.nK τ.1) = D.sumS ch t + e * D.sumK ch t := by
  have key : ∀ (h : F → ℂ) (τ : F),
      (D.Good t τ → ¬ (∀ v ∉ D.Sg, (cv v) τ ∈ (algebraMap (Ov v) (Kv v)).range) → h τ = 0) →
      one (D.Good t τ) * h τ = one (GI D t τ) * h τ := by
    intro h τ hh
    by_cases hg : D.Good t τ
    · by_cases hi : ∀ v ∉ D.Sg, (cv v) τ ∈ (algebraMap (Ov v) (Kv v)).range
      · have hG : GI D t τ := ⟨hg, hi⟩
        simp only [one, if_pos hg, if_pos hG]
      · rw [hh hg hi, mul_zero, mul_zero]
    · have hG : ¬ GI D t τ := fun h' => hg h'.1
      simp only [one, if_neg hg, if_neg hG]
  have van : ∀ τ, D.Good t τ → ¬ (∀ v ∉ D.Sg, (cv v) τ ∈ (algebraMap (Ov v) (Kv v)).range) →
      D.nS τ = 0 ∧ D.nK τ = 0 := fun τ hg hi => sg_vanish D hD (aux_statement_10 D hD t ht τ hg.2) hi
  have kS : ∀ τ, one (D.Good t τ) * (ch τ * ms τ * D.nS τ) = one (GI D t τ) * (ch τ * ms τ * D.nS τ) :=
    fun τ => key (fun τ => ch τ * ms τ * D.nS τ) τ (fun hg hi => by
      show ch τ * ms τ * D.nS τ = 0
      rw [(van τ hg hi).1, mul_zero])
  have kK : ∀ τ, one (D.Good t τ) * (ch τ * ms τ * D.nK τ) = one (GI D t τ) * (ch τ * ms τ * D.nK τ) :=
    fun τ => key (fun τ => ch τ * ms τ * D.nK τ) τ (fun hg hi => by
      show ch τ * ms τ * D.nK τ = 0
      rw [(van τ hg hi).2, mul_zero])
  have hfin := finSupp F Δ D hD t ht
  have sup : ∀ h : F → ℂ, (Function.support fun τ => one (GI D t τ) * h τ).Finite := fun h =>
    hfin.subset (fun τ hτ => by
      by_contra hn
      exact hτ (by simp only [one, if_neg (show ¬ GI D t τ from hn), zero_mul]))
  have sup' : ∀ h : F → ℂ, (Function.support fun τ => e * (one (GI D t τ) * h τ)).Finite := fun h =>
    hfin.subset (fun τ hτ => by
      by_contra hn
      exact hτ (by simp only [one, if_neg (show ¬ GI D t τ from hn), zero_mul, mul_zero]))
  rw [sum_sub (GI D t) (fun τ => ch τ * ms τ * (D.nS τ + e * D.nK τ))]
  simp only [Dat.sumS, Dat.sumK]
  rw [finsum_congr kS, finsum_congr kK, ← const_sum, ← finsum_add_distrib (sup _) (sup' _)]
  exact finsum_congr (fun τ => by ring)

set_option maxHeartbeats 800000 in
private theorem term_eq (hD : D.Ok) {V : Type} [AddCommGroup V] [Module ℂ V] {ch : F → ℂ} {B : Base (U3 Δ) (GA Δ) V} {s : B.Tw}
    (hB : D.IsBG ch B s) {t : Dat.Par F} (ht : D.Cone t) {τ c : F} {d m : EL Δ τ} {δ i P} (hτ : D.Good t τ) (hd : IsDat c d m)
    (h : Models c d m δ i P) :
    s.term (D.FG t) δ = (1 / 2 * ∏ v ∈ D.Sg, ((D.S v).cG : ℂ)) * (ch τ * ms τ * D.nL c d m) := by
  obtain ⟨h1, h2, h3, h4⟩ := modelFacts F Δ τ c d m δ i P (delta_ne D hD) hd h
  obtain ⟨hF, hT⟩ := finG F Δ D hD V ch B s hB
  have a := sideGTerm _ _ V _ B hF s (D.FG t) (hT t ht) hB.ω hB.Γ₀ δ (negU Δ) i h3
    (fun x => by rw [hB.θΓ]; exact h4 x) D.UG (scalE τ) hB.U h2
  have b := gqG F Δ D hD B.ι hB.ι s.θ.toMonoidHom hB.θ t ht τ c d m δ i P hτ.1 hd h
  have o : one (D.admitted t τ) = 1 := if_pos hτ.2
  have a' := a.trans (congrArg₂ (fun x y : ℂ => x * y) (hB.tr δ τ h1) b)
  simp only [o] at a'
  linear_combination (1 / 2 : ℂ) * a'

private theorem weight_eq (hD : D.Ok) {τ : F} {d m : EL Δ τ} (hd : IsDat 1 d m) (hp : PosF 1 m)
    (c : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) (u : Fˣ) (A : ℂ) :
    one (∃ δ ι P, Models (c.out : F) d ((u : F) • m) δ ι P) * (A * D.nL (c.out : F) d ((u : F) • m)) =
      A * (one (c ∈ D.Sel (2 - τ)) * (one (TPos (u : F)) * D.nL (c.out : F) d ((u : F) • m))) := by
  have hd' : IsDat (c.out : F) d ((u : F) • m) := by
    have h1 := datSmul F Δ τ 1 d m hd u
    exact ⟨h1.reg, Units.ne_zero _, h1.d_norm, h1.m_unit, h1.m_star, h1.m_sig⟩
  by_cases hn : D.nL (c.out : F) d ((u : F) • m) = 0
  · rw [hn]
    simp
  · have hev := sg_ev D hD hd' hn
    by_cases hm : ∃ δ ι P, Models (c.out : F) d ((u : F) • m) δ ι P
    · obtain ⟨δ, ι, P, hM⟩ := hm
      have hq := (posLaw F Δ D hD τ d m hp (c.out : F) (u : F)).2 δ ι P hM
      have hS : c ∈ D.Sel (2 - τ) := ⟨hq.1, hev⟩
      simp only [one, if_pos (show ∃ δ ι P, Models (c.out : F) d ((u : F) • m) δ ι P from ⟨δ, ι, P, hM⟩),
        if_pos hS, if_pos hq.2]
      ring
    · have hno : ¬ (c ∈ D.Sel (2 - τ) ∧ TPos (u : F)) := by
        rintro ⟨hS, hu⟩
        exact hm (exG F Δ D hD τ (c.out : F) d _ hd'
          ((posLaw F Δ D hD τ d m hp (c.out : F) (u : F)).1 hS.1 hu) hev)
      by_cases hS : c ∈ D.Sel (2 - τ)
      · have hu : ¬ TPos (u : F) := fun hu => hno ⟨hS, hu⟩
        simp only [one, if_neg hm, if_pos hS, if_neg hu]
        ring
      · simp only [one, if_neg hm, if_neg hS]
        ring

private theorem cls_eq {K : Type} [Field K] {τ : K} {x y : (Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) × (Kˣ ⧸ NE τ)}
    (h : IsSquare (y.1.out / x.1.out) ∧ y.2.out / x.2.out ∈ NE τ) : x = y := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  simp only at h1 h2
  rw [Prod.mk.injEq]
  constructor
  · rw [← QuotientGroup.out_eq' x1, ← QuotientGroup.out_eq' y1, QuotientGroup.eq]
    obtain ⟨r, hr⟩ := h1
    exact ⟨r, by rw [powMonoidHom_apply, pow_two, ← hr, div_eq_inv_mul]⟩
  · rw [← QuotientGroup.out_eq' x2, ← QuotientGroup.out_eq' y2, QuotientGroup.eq, ← div_eq_inv_mul]
    exact h2

set_option maxHeartbeats 1600000 in
theorem sideG : SideG := by
  intro F _ _ Δ D hD
  obtain ⟨e, he⟩ := basePt F Δ D hD
  obtain ⟨hS1f, hS1n, -⟩ := selCard F Δ D hD
  have hΔ := delta_ne D hD
  have hp : 0 < ∏ v ∈ D.Sg, (D.S v).cG := Finset.prod_pos (fun v hv => (hD.sig v hv).cG)
  have hn : 0 < (D.Sel 1).ncard := (Set.ncard_pos hS1f).mpr hS1n
  refine ⟨(∏ v ∈ D.Sg, (D.S v).cG) * (D.Sel 1).ncard / 4, e,
    div_pos (mul_pos hp (Nat.cast_pos.mpr hn)) (by norm_num), ?_⟩
  intro V _ _ _ ch B s hB t ht
  obtain ⟨hFin, hTest⟩ := finG F Δ D hD V ch B s hB
  have spl : ∀ τ : {τ // GI D t τ}, D.Spl τ.1 := fun τ v hv =>
    ((hD.sig v hv).reg (t v) (ht v hv) (cv v τ.1) (τ.2.1.2 v hv)).1
  have bp : ∀ τ : {τ // GI D t τ}, ∃ d m : EL Δ τ.1, IsDat 1 d m ∧ PosF 1 m ∧
      ∀ (c : F), TPos c → D.Ev (c * (2 - τ.1)) →
        ∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), kapSum (Ov v) ((cv v) c) (elmap (cv v) d) (elmap (cv v) m) =
          (e : ℂ) * D.nK τ.1 :=
    fun τ => he τ.1 τ.2.1.1 (spl τ) τ.2.2
  choose d m hdm using bp
  have hex : ∀ (τ : {τ // GI D t τ})
      (x : {x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ.1) //
        ∃ δ ι P, Models (x.1.out : F) (d τ) ((x.2.out : F) • m τ) δ ι P}),
      ∃ δ ι P, Models (x.1.1.out : F) (d τ) ((x.1.2.out : F) • m τ) δ ι P := fun τ x => x.2
  choose δf ιf Pf hM using hex
  have isD : ∀ (τ : {τ // GI D t τ}) (c u : Fˣ), IsDat (c : F) (d τ) ((u : F) • m τ) := by
    intro τ c u
    have h1 := datSmul F Δ τ.1 1 (d τ) (m τ) (hdm τ).1 u
    exact ⟨h1.reg, Units.ne_zero _, h1.d_norm, h1.m_unit, h1.m_star, h1.m_sig⟩
  have inj : ∀ i j : (Σ τ : {τ // GI D t τ}, {x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ.1) //
        ∃ δ ι P, Models (x.1.out : F) (d τ) ((x.2.out : F) • m τ) δ ι P}),
      s.Rel (δf i.1 i.2) (δf j.1 j.2) → i = j := by
    rintro ⟨τ, x⟩ ⟨τ', x'⟩ ⟨g, z, hz, hrel⟩
    rw [hB.Γ₀, Subgroup.mem_bot] at hz
    subst hz
    rw [mul_one, hB.θΓ] at hrel
    have h1 := (modelFacts F Δ τ.1 _ _ _ _ _ _ hΔ (isD τ _ _) (hM τ x)).1
    have h2 := (modelFacts F Δ τ'.1 _ _ _ _ _ _ hΔ (isD τ' _ _) (hM τ' x')).1
    have heq : τ.1 = τ'.1 := sideGTau.2.1 F Δ (δf τ' x') τ.1 τ'.1
      (by rw [hrel]; exact sideGTau.1 F Δ _ g τ.1 h1) h2
    obtain ⟨τ, hτ⟩ := τ
    obtain ⟨τ', hτ'⟩ := τ'
    simp only at heq
    subst heq
    have hc := (conjG F Δ τ (d ⟨τ, hτ⟩) (m ⟨τ, hτ⟩) hΔ (hdm ⟨τ, hτ⟩).1 x.1.1.out x'.1.1.out x.1.2.out x'.1.2.out
      _ _ _ _ _ _ (hM ⟨τ, hτ⟩ x) (hM ⟨τ, hτ'⟩ x')).mp ⟨g, hrel⟩
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext (cls_eq hc)))
  have surj : ∀ γ : U3 Δ, (∃ y, s.ker (D.FG t) γ y ≠ 0) →
      ∃ i : (Σ τ : {τ // GI D t τ}, {x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ.1) //
        ∃ δ ι P, Models (x.1.out : F) (d τ) ((x.2.out : F) • m τ) δ ι P}), s.Rel (δf i.1 i.2) γ := by
    rintro γ ⟨y, hy⟩
    obtain ⟨τ, hγτ, hcm⟩ := tauEx F Δ D hD γ
    have hsupp := sideGSupp F Δ D hD B.ι hB.ι s.θ.toMonoidHom hB.θ t ht γ τ y.out hγτ hy
    have hG : GI D t τ := ⟨⟨hcm (aux_statement_10 D hD t ht τ hsupp.1), hsupp.1⟩, hsupp.2⟩
    obtain ⟨c, u, ι, P, hMod⟩ := classG F Δ τ (d ⟨τ, hG⟩) (m ⟨τ, hG⟩) hΔ (hdm ⟨τ, hG⟩).1 γ hγτ
    obtain ⟨x, P', hx⟩ := sg_out hMod
    refine ⟨⟨⟨τ, hG⟩, ⟨x, γ, ι, P', hx⟩⟩, ?_⟩
    obtain ⟨g, hg⟩ := (conjG F Δ τ (d ⟨τ, hG⟩) (m ⟨τ, hG⟩) hΔ (hdm ⟨τ, hG⟩).1 x.1.out x.1.out x.2.out x.2.out
      _ γ _ ι _ P' (hM ⟨τ, hG⟩ ⟨x, γ, ι, P', hx⟩) hx).mpr
      ⟨by rw [div_self']; exact ⟨1, (mul_one 1).symm⟩, by rw [div_self']; exact one_mem _⟩
    exact ⟨g, 1, by rw [hB.Γ₀]; exact one_mem _, by rw [mul_one, hB.θΓ]; exact hg⟩
  have htr := UpperTheory.V.Z.Sym.Tf.trace (U3 Δ) (GA Δ) V B hFin s (D.FG t) (hTest t ht)
    (Σ τ : {τ // GI D t τ}, {x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ.1) //
        ∃ δ ι P, Models (x.1.out : F) (d τ) ((x.2.out : F) • m τ) δ ι P})
    (fun i => δf i.1 i.2) inj surj
  rw [htr.2]
  have indicator_eq_one_of_true : ∀ {p : Prop}, p → one p = 1 := fun h => if_pos h
  have hterm : ∀ i : (Σ τ : {τ // GI D t τ}, {x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ.1) //
        ∃ δ ι P, Models (x.1.out : F) (d τ) ((x.2.out : F) • m τ) δ ι P}),
      s.term (D.FG t) (δf i.1 i.2) = (1 / 2 * ∏ v ∈ D.Sg, ((D.S v).cG : ℂ)) * (ch i.1.1 * ms i.1.1) *
        D.nL (i.2.1.1.out : F) (d i.1) ((i.2.1.2.out : F) • m i.1) := fun i => by
    rw [term_eq D hD hB ht i.1.2.1 (isD i.1 _ _) (hM i.1 i.2)]
    ring
  haveI : Finite {τ // GI D t τ} := (finSupp F Δ D hD t ht).to_subtype
  have hinner : ∀ τ : {τ // GI D t τ},
      (Function.support fun x : {x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ.1) //
        ∃ δ ι P, Models (x.1.out : F) (d τ) ((x.2.out : F) • m τ) δ ι P} =>
          (1 / 2 * ∏ v ∈ D.Sg, ((D.S v).cG : ℂ)) * (ch τ.1 * ms τ.1) *
            D.nL (x.1.1.out : F) (d τ) ((x.1.2.out : F) • m τ)).Finite ∧
      ∑ᶠ x : {x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ.1) //
        ∃ δ ι P, Models (x.1.out : F) (d τ) ((x.2.out : F) • m τ) δ ι P},
          (1 / 2 * ∏ v ∈ D.Sg, ((D.S v).cG : ℂ)) * (ch τ.1 * ms τ.1) *
            D.nL (x.1.1.out : F) (d τ) ((x.1.2.out : F) • m τ) =
        (((∏ v ∈ D.Sg, (D.S v).cG) * (D.Sel 1).ncard / 4 : ℝ) : ℂ) *
          (ch τ.1 * ms τ.1 * (D.nS τ.1 + (e : ℂ) * D.nK τ.1)) := by
    intro τ
    have hsg := sg_inner D hD τ.2.1.1 (spl τ) (hdm τ).1 (hdm τ).2.2
    constructor
    · refine (hsg.1.preimage Subtype.val_injective.injOn).subset (fun x hx => ?_)
      simp only [Set.mem_preimage, Function.mem_support] at hx ⊢
      intro h0
      apply hx
      have hw := weight_eq D hD (hdm τ).1 (hdm τ).2.1 x.1.1 x.1.2.out
        ((1 / 2 * ∏ v ∈ D.Sg, ((D.S v).cG : ℂ)) * (ch τ.1 * ms τ.1))
      rw [indicator_eq_one_of_true x.2, one_mul] at hw
      rw [hw, h0, mul_zero]
    · rw [sum_sub (fun (x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ.1)) => ∃ δ ι P, Models (x.1.out : F) (d τ) ((x.2.out : F) • m τ) δ ι P)
        (fun (x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ.1)) => (1 / 2 * ∏ v ∈ D.Sg, ((D.S v).cG : ℂ)) * (ch τ.1 * ms τ.1) *
          D.nL (x.1.out : F) (d τ) ((x.2.out : F) • m τ))]
      rw [finsum_congr (fun (x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ.1)) => weight_eq D hD (hdm τ).1 (hdm τ).2.1 x.1 x.2.out
        ((1 / 2 * ∏ v ∈ D.Sg, ((D.S v).cG : ℂ)) * (ch τ.1 * ms τ.1))), const_sum, hsg.2]
      push_cast
      ring
  rw [finsum_congr hterm]
  rw [sg_sigma _ (fun τ => (hinner τ).1)]
  rw [finsum_congr (fun τ => (hinner τ).2), const_sum, sum_GI D hD t ht ch (e : ℂ)]

end UpperTheory.V.Z.Sym.Glob
