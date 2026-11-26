module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothHolomorphicInSigmaFamilyAdd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleXSqAddOne
open NumberField Polynomial

noncomputable section

namespace GlobalTheory.GaussExt

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

theorem irreducible_X_sq_add_one : Irreducible (X ^ 2 + 1 : F[X]) := by
  have hdeg : (X ^ 2 + 1 : F[X]).natDegree = 2 := by compute_degree!
  refine (Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [hdeg]) (by rw [hdeg]; norm_num)).2 ?_
  refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
  rw [mem_roots (Monic.ne_zero (by monicity!)), IsRoot, eval_add, eval_pow, eval_X, eval_one] at hr
  obtain ⟨τ⟩ : Nonempty (F →+* ℝ) := by
    obtain ⟨φ⟩ := (inferInstance : Nonempty (F →+* ℂ))
    exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding⟩
  have := congrArg τ hr
  simp at this
  nlinarith [sq_nonneg (τ r)]

instance : Fact (Irreducible (X ^ 2 + 1 : F[X])) := ⟨irreducible_X_sq_add_one F⟩

abbrev Ext : Type := AdjoinRoot (X ^ 2 + 1 : F[X])

instance : Module.Finite F (Ext F) :=
  (AdjoinRoot.powerBasis (Monic.ne_zero (by monicity!) : (X ^ 2 + 1 : F[X]) ≠ 0)).finite

instance : NumberField (Ext F) where
  to_charZero := charZero_of_injective_algebraMap (algebraMap F (Ext F)).injective
  to_finiteDimensional := Module.Finite.trans F (Ext F)

def ii : Ext F := AdjoinRoot.root _

theorem ii_sq : ii F ^ 2 = -1 := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 + 1 : F[X])
  simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_one] at h
  rw [ii]; linear_combination h

def gEmb (p : F × F) : Ext F := algebraMap F (Ext F) p.1 + algebraMap F (Ext F) p.2 * ii F

end GlobalTheory.GaussExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeSummandWeightTwoBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeSummandWeightTwoBound
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound

theorem normSq_lower (w : ℂ) (a b : ℝ) :
    (w.im) ^ 2 / (1 + ‖w‖ ^ 2) * (a ^ 2 + b ^ 2) ≤ ‖(a : ℂ) + b * w‖ ^ 2 := by
  have h1 : (0 : ℝ) < 1 + ‖w‖ ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ h1]
  have hw : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hn : ‖(a : ℂ) + b * w‖ ^ 2 = (a + b * w.re) ^ 2 + (b * w.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  rw [hw, hn]
  nlinarith [sq_nonneg (a + b * w.re), sq_nonneg ((a + b * w.re) * w.re + b * w.im * w.im)]

theorem bound : ∀ (F : Type) [Field F] [NumberField F] (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∃ C : ℝ, ∀ p : F × F, p ≠ 0 → ‖GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm 2 σ z p‖ ≤ C * (∏ τ : F →+* ℝ, ((τ p.1) ^ 2 + (τ p.2) ^ 2)) ^ (-(1 + σ.re)) := by
  intro F _ _ σ hσ z hz
  set s := σ.re with hs
  let c : (F →+* ℝ) → ℝ := fun τ => 4 * Real.pi ^ 2 * ((z τ).im ^ 2 / (1 + ‖z τ‖ ^ 2))
  have hc : ∀ τ, 0 < c τ := fun τ => by have := hz τ; positivity
  refine ⟨(∏ τ, c τ) ^ (-(1 + s)), fun p hp => ?_⟩
  set P := ∏ τ : F →+* ℝ, ((τ p.1) ^ 2 + (τ p.2) ^ 2) with hPdef
  have hP : 0 < P := Finset.prod_pos fun τ _ => by
    by_contra h
    push_neg at h
    have h1 : τ p.1 = 0 := by nlinarith [sq_nonneg (τ p.1), sq_nonneg (τ p.2)]
    have h2 : τ p.2 = 0 := by nlinarith [sq_nonneg (τ p.1), sq_nonneg (τ p.2)]
    exact hp (Prod.ext ((map_eq_zero τ).1 h1) ((map_eq_zero τ).1 h2))
  set N := ∏ τ, ‖latPt z p τ‖ with hN
  have hNpos : 0 < N := Finset.prod_pos fun τ _ => norm_pos_iff.2 (latPt_ne_zero hz hp τ)
  have hterm : ‖eisTerm 2 σ z p‖ = (N ^ 2) ^ (-(1 + s)) := by
    unfold eisTerm
    simp only [norm_mul, norm_pow, norm_inv, norm_prod]
    rw [← hN, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    rw [show (N ^ 2 : ℝ) = N ^ (2 : ℝ) from (Real.rpow_two N).symm, ← Real.rpow_mul hNpos.le]
    have : (2 : ℝ) * (-(1 + s)) = -(2 : ℝ) + (-2 * σ).re := by simp [hs]; ring
    rw [this, Real.rpow_add hNpos, Real.rpow_neg hNpos.le, Real.rpow_two, inv_pow]
  have hlow : (∏ τ, c τ) * P ≤ N ^ 2 := by
    rw [hPdef, hN, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
    refine Finset.prod_le_prod₀ (fun τ _ => mul_nonneg (hc τ).le (by positivity)) fun τ _ => ?_
    have hl : ‖latPt z p τ‖ ^ 2 = 4 * Real.pi ^ 2 * ‖((τ p.1 : ℝ) : ℂ) + (τ p.2 : ℝ) * z τ‖ ^ 2 := by
      simp only [latPt, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      ring
    rw [hl, mul_assoc (4 * Real.pi ^ 2)]
    exact mul_le_mul_of_nonneg_left (normSq_lower (z τ) _ _) (by positivity)
  rw [hterm, ← Real.mul_rpow (Finset.prod_nonneg fun τ _ => (hc τ).le) hP.le]
  exact Real.rpow_le_rpow_of_nonpos (mul_pos (Finset.prod_pos fun τ _ => hc τ) hP) hlow (by linarith)

end GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeSummandWeightTwoBoundStatement
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertEisensteinLatticeSummand_weightTwo_bound : ∀ (F : Type) [Field F] [NumberField F] (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∃ C : ℝ, ∀ p : F × F, p ≠ 0 → ‖GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm 2 σ z p‖ ≤ C * (∏ τ : F →+* ℝ, ((τ p.1) ^ 2 + (τ p.2) ^ 2)) ^ (-(1 + σ.re)) := by
  first | exact @GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound.bound | exact GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound.bound | (intros; apply GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound.bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGaussianExtensionUnitsQuotUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGaussianExtensionUnitsQuotUnits
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.GaussExt.UnitIdx

variable (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]

theorem aeval_neg_ii : aeval (-ii F) (X ^ 2 + 1 : F[X]) = 0 := by
  simp only [map_add (f := _), map_pow, aeval_X, map_one, neg_sq, ii_sq F]; ring

def conj : Ext F →ₐ[F] Ext F := AdjoinRoot.liftAlgHom (X ^ 2 + 1 : F[X]) (Algebra.ofId F (Ext F)) (-ii F)
  (by have := aeval_neg_ii F; rwa [aeval_def] at this)

theorem conj_ii : conj F (ii F) = -ii F := by
  simp [conj, ii]

theorem conj_algebraMap (a : F) : conj F (algebraMap F (Ext F) a) = algebraMap F (Ext F) a :=
  (conj F).commutes a

theorem exists_repr (x : Ext F) : ∃ a b : F, x = algebraMap F (Ext F) a + algebraMap F (Ext F) b * ii F := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  have hm : (X ^ 2 + 1 : F[X]).Monic := by monicity!
  have hdeg : (X ^ 2 + 1 : F[X]).natDegree = 2 := by compute_degree!
  set r := p %ₘ (X ^ 2 + 1 : F[X])
  have hr : AdjoinRoot.mk (X ^ 2 + 1 : F[X]) p = AdjoinRoot.mk _ r := by
    rw [AdjoinRoot.mk_eq_mk]
    exact ⟨p /ₘ (X ^ 2 + 1), by have := modByMonic_add_div p (X ^ 2 + 1 : F[X]); linear_combination -this⟩
  have hrd : r.natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt p hm (by intro h; have := congrArg natDegree h; rw [hdeg] at this; simp at this)
    change (p %ₘ (X ^ 2 + 1 : F[X])).natDegree ≤ 1
    omega
  refine ⟨r.coeff 0, r.coeff 1, ?_⟩
  rw [hr, eq_X_add_C_of_natDegree_le_one hrd]
  simp [ii, AdjoinRoot.algebraMap_eq, add_comm]

theorem ii_ne_zero : ii F ≠ 0 := by
  intro h
  have := ii_sq F
  rw [h] at this
  norm_num at this

theorem mem_range_of_conj_eq (x : Ext F) (hx : conj F x = x) : ∃ a : F, algebraMap F (Ext F) a = x := by
  obtain ⟨a, b, rfl⟩ := exists_repr F x
  refine ⟨a, ?_⟩
  simp only [map_add (f := _), map_mul, conj_algebraMap, conj_ii] at hx
  have h2 : (2 : Ext F) * algebraMap F (Ext F) b * ii F = 0 := by linear_combination -hx
  have hb : algebraMap F (Ext F) b = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h two_ne_zero
      · exact h
    · exact absurd h (ii_ne_zero F)
  rw [hb]; ring

theorem embedding_conj (φ : Ext F →+* ℂ) (x : Ext F) : φ (conj F x) = starRingEnd ℂ (φ x) := by
  have key : φ.comp (conj F).toRingHom = (starRingEnd ℂ).comp φ := by
    apply AdjoinRoot.ringHom_ext
    · ext a
      have hre := NumberField.IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap F (Ext F)))
      have h1 := hre.coe_embedding_apply a
      simp only [RingHom.comp_apply, AdjoinRoot.algebraMap_eq] at h1 ⊢
      have h3 : (conj F).toRingHom (AdjoinRoot.of _ a) = AdjoinRoot.of _ a := by
        rw [← AdjoinRoot.algebraMap_eq]; exact conj_algebraMap F a
      rw [h3, ← h1, Complex.conj_ofReal]
    · have h := congrArg φ (ii_sq F)
      simp only [map_pow, map_neg, map_one] at h
      have hc : (φ (ii F) - I) * (φ (ii F) + I) = 0 := by linear_combination h - I_sq
      simp only [RingHom.comp_apply]
      change φ (conj F (ii F)) = starRingEnd ℂ (φ (ii F))
      rw [conj_ii, map_neg]
      rcases mul_eq_zero.1 hc with h' | h'
      · rw [sub_eq_zero.1 h']; simp
      · rw [eq_neg_of_add_eq_zero_left h']; simp
  exact congrArg (fun f => f x) key

theorem isIntegral_conj {x : Ext F} (hx : IsIntegral ℤ x) : IsIntegral ℤ (conj F x) :=
  hx.map ((conj F).toRingHom.toIntAlgHom)

theorem pow_mem_range (u : (𝓞 (Ext F))ˣ) :
    ∃ m : ℕ, 0 < m ∧ u ^ m ∈ (Units.map (algebraMap (𝓞 F) (𝓞 (Ext F))).toMonoidHom).range := by
  set x : Ext F := ((u : 𝓞 (Ext F)) : Ext F)
  set y : Ext F := (((u⁻¹ : (𝓞 (Ext F))ˣ) : 𝓞 (Ext F)) : Ext F)
  have hxy : x * y = 1 := by
    have := congrArg (fun z : 𝓞 (Ext F) => (z : Ext F)) u.mul_inv
    simpa [x, y] using this
  have hx0 : x ≠ 0 := left_ne_zero_of_mul_eq_one hxy
  have hint : IsIntegral ℤ (x * conj F y) :=
    (RingOfIntegers.isIntegral_coe _).mul (isIntegral_conj F (RingOfIntegers.isIntegral_coe _))
  obtain ⟨m, hm, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one (Ext F) ℂ hint fun φ => by
    have h1 : φ x * φ y = 1 := by rw [← map_mul, hxy, map_one]
    rw [map_mul, embedding_conj, norm_mul, Complex.norm_conj, ← norm_mul, h1, norm_one]
  refine ⟨m, hm, ?_⟩

  have hcxy : conj F x * conj F y = 1 := by rw [← map_mul, hxy, map_one]
  have hfix : conj F (x ^ m) = x ^ m := by
    have : (x * conj F y) ^ m * (conj F x) ^ m = (conj F x) ^ m := by rw [hpow, one_mul]
    rw [map_pow, ← this, ← mul_pow, mul_assoc, mul_comm (conj F y), hcxy, mul_one]
  obtain ⟨a, ha⟩ := mem_range_of_conj_eq F _ hfix
  have hai : IsIntegral ℤ a := by
    refine (isIntegral_algebraMap_iff (B := Ext F)).1 ?_
    rw [ha]; exact (RingOfIntegers.isIntegral_coe _).pow m

  have hfix' : conj F (y ^ m) = y ^ m := by
    have e : y ^ m = (x ^ m)⁻¹ := by rw [← inv_pow, inv_eq_of_mul_eq_one_right hxy]
    rw [e, map_inv₀, hfix]
  obtain ⟨b, hb⟩ := mem_range_of_conj_eq F _ hfix'
  have hbi : IsIntegral ℤ b := by
    refine (isIntegral_algebraMap_iff (B := Ext F)).1 ?_
    rw [hb]; exact (RingOfIntegers.isIntegral_coe _).pow m
  have hab : a * b = 1 := by
    apply (algebraMap F (Ext F)).injective
    rw [map_mul, ha, hb, ← mul_pow, hxy, one_pow, map_one]
  let A : 𝓞 F := ⟨a, hai⟩
  let B : 𝓞 F := ⟨b, hbi⟩
  have hAB : A * B = 1 := RingOfIntegers.ext hab
  refine ⟨⟨A, B, hAB, by rw [mul_comm]; exact hAB⟩, ?_⟩
  apply Units.ext
  apply RingOfIntegers.ext
  simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
  rw [show (((u : 𝓞 (Ext F)) ^ m : 𝓞 (Ext F)) : Ext F) = x ^ m by simp [x], ← ha]
  rfl

theorem finite_quot : Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸
    (Units.map (algebraMap (NumberField.RingOfIntegers F)
      (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) := by
  haveI : Group.FG (𝓞 (Ext F))ˣ := Group.fg_iff_monoid_fg.2 inferInstance
  refine CommGroup.finite_of_fg_torsion _ fun q => ?_
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨m, hm, hu⟩ := pow_mem_range F u
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact hu

end GlobalTheory.GaussExt.UnitIdx

theorem GlobalTheory.GaussExt.finite_units_quot_units : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
    Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸
      (Units.map (algebraMap (NumberField.RingOfIntegers F)
        (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) :=
  fun F _ _ _ => GlobalTheory.GaussExt.UnitIdx.finite_quot F
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGaussianExtensionUnitsQuotUnitsStatement
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_gaussianExtension_units_quot_units : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F], Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸ (Units.map (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) := by
  first | exact @GlobalTheory.GaussExt.finite_units_quot_units | exact GlobalTheory.GaussExt.finite_units_quot_units | (intros; apply GlobalTheory.GaussExt.finite_units_quot_units <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraNormRatGaussianExtensionOfPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraNormRatGaussianExtensionOfPair
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.GaussExt

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

theorem X_sq_add_one_ne_zero : (X ^ 2 + 1 : F[X]) ≠ 0 := Monic.ne_zero (by monicity!)

theorem natDegree_X_sq_add_one : (X ^ 2 + 1 : F[X]).natDegree = 2 := by compute_degree!

def basisOneI : Module.Basis (Fin 2) F (Ext F) :=
  (AdjoinRoot.powerBasis (X_sq_add_one_ne_zero F)).basis.reindex
    (finCongr (by rw [AdjoinRoot.powerBasis_dim, natDegree_X_sq_add_one]))

theorem basisOneI_apply (j : Fin 2) : basisOneI F j = ii F ^ (j : ℕ) := by
  simp [basisOneI, Module.Basis.reindex_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen, ii]

theorem basisOneI_zero : basisOneI F 0 = 1 := by simp [basisOneI_apply]
theorem basisOneI_one : basisOneI F 1 = ii F := by simp [basisOneI_apply]

theorem gEmb_eq (a b : F) : gEmb F (a, b) = a • basisOneI F 0 + b • basisOneI F 1 := by
  simp [gEmb, basisOneI_zero, basisOneI_one, Algebra.smul_def]

theorem gEmb_mul_ii (a b : F) : gEmb F (a, b) * ii F = (-b) • basisOneI F 0 + a • basisOneI F 1 := by
  simp only [gEmb, basisOneI_zero, basisOneI_one, Algebra.smul_def, map_neg]
  linear_combination (algebraMap F (Ext F) b) * ii_sq F

theorem norm_gEmb_F (a b : F) : Algebra.norm F (gEmb F (a, b)) = a ^ 2 + b ^ 2 := by
  rw [Algebra.norm_eq_matrix_det (basisOneI F), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, Algebra.coe_lmul_eq_mul,
    LinearMap.mul_apply']
  rw [basisOneI_zero, mul_one, basisOneI_one, gEmb_mul_ii, gEmb_eq]
  simp [Module.Basis.repr_self, Finsupp.single_apply]
  ring

theorem norm_gEmb (a b : F) :
    ((Algebra.norm ℚ (gEmb F (a, b)) : ℚ) : ℝ) = ∏ τ : F →+* ℝ, ((τ a) ^ 2 + (τ b) ^ 2) := by
  rw [← Algebra.norm_norm (S := F), norm_gEmb_F]
  have h := prod_emb (F := F) (a ^ 2 + b ^ 2)
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, ← h, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp

end GlobalTheory.GaussExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraNormRatGaussianExtensionOfPairStatement
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraNorm_rat_gaussianExtensionOfPair : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (a b : F), ((Algebra.norm ℚ (GlobalTheory.GaussExt.gEmb F (a, b)) : ℚ) : ℝ) = ∏ τ : F →+* ℝ, ((τ a) ^ 2 + (τ b) ^ 2) := by
  first | exact @GlobalTheory.GaussExt.norm_gEmb | exact GlobalTheory.GaussExt.norm_gEmb | (intros; apply GlobalTheory.GaussExt.norm_gEmb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableGaussianExtensionNormRpow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableGaussianExtensionNormRpow
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.GaussSum

open GlobalTheory.GaussExt

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem eq_zero_of_add_mul_ii {x y : F}
    (h : algebraMap F (Ext F) x + algebraMap F (Ext F) y * ii F = 0) : x = 0 ∧ y = 0 := by
  have hy : y = 0 := by
    by_contra hy
    have hy' : algebraMap F (Ext F) y ≠ 0 := (_root_.map_ne_zero _).2 hy
    have hi : ii F = algebraMap F (Ext F) (-x / y) := by
      rw [map_div₀, map_neg, eq_div_iff hy']
      linear_combination h
    have h2 : algebraMap F (Ext F) ((-x / y) ^ 2 + 1) = 0 := by
      rw [map_add (f := _), map_pow, ← hi, ii_sq, map_one]; ring
    have h3 : (-x / y) ^ 2 + 1 = 0 := (map_eq_zero _).1 h2
    obtain ⟨τ⟩ : Nonempty (F →+* ℝ) := by
      obtain ⟨φ⟩ := (inferInstance : Nonempty (F →+* ℂ))
      exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding⟩
    have h4 := congrArg τ h3
    rw [map_add (f := _), map_pow, map_one, map_zero] at h4
    nlinarith [sq_nonneg (τ (-x / y))]
  refine ⟨?_, hy⟩
  rw [hy, map_zero, zero_mul, add_zero] at h
  exact (map_eq_zero _).1 h

theorem isIntegral_ii : IsIntegral ℤ (ii F) :=
  ⟨X ^ 2 + 1, by monicity!, by simp [ii_sq]⟩


set_option maxHeartbeats 1000000 in
theorem summable_norm_rpow (𝔞 𝔟 : Frac F) {t : ℝ} (ht : 1 < t)
    (hQ : Finite ((𝓞 (Ext F))ˣ ⧸ (Units.map (algebraMap (𝓞 F) (𝓞 (Ext F))).toMonoidHom).range)) :
    Summable (fun c : Quotient (latRel 𝔞 𝔟) => |((Algebra.norm ℚ (gEmb F c.out.1) : ℚ) : ℝ)| ^ (-t)) := by
  classical
  obtain ⟨d₁, hd₁, h₁⟩ := APart.exists_den (latM 𝔞)
  obtain ⟨d₂, hd₂, h₂⟩ := APart.exists_den (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
  have hd : ((d₁ : F) * (d₂ : F)) ≠ 0 := mul_ne_zero (by exact_mod_cast hd₁) (by exact_mod_cast hd₂)
  choose ga hga using fun c : Quotient (latRel 𝔞 𝔟) => h₁ c.out.1.1 c.out.2.1
  choose gb hgb using fun c : Quotient (latRel 𝔞 𝔟) => h₂ c.out.1.2 c.out.2.2.1
  let iO : 𝓞 (Ext F) := ⟨ii F, isIntegral_ii⟩
  let y : Quotient (latRel 𝔞 𝔟) → 𝓞 (Ext F) := fun c =>
    algebraMap (𝓞 F) (𝓞 (Ext F)) (d₂ * ga c) + algebraMap (𝓞 F) (𝓞 (Ext F)) (d₁ * gb c) * iO
  have hy : ∀ c, ((y c : 𝓞 (Ext F)) : Ext F) = algebraMap F (Ext F) ((d₁ : F) * (d₂ : F)) * gEmb F c.out.1 := by
    intro c
    have e : ((y c : 𝓞 (Ext F)) : Ext F) =
        algebraMap F (Ext F) ((d₂ * ga c : 𝓞 F) : F) + algebraMap F (Ext F) ((d₁ * gb c : 𝓞 F) : F) * ii F := rfl
    have ea : ((d₂ * ga c : 𝓞 F) : F) = (d₂ : F) * (ga c : F) := rfl
    have eb : ((d₁ * gb c : 𝓞 F) : F) = (d₁ : F) * (gb c : F) := rfl
    rw [e, ea, eb, hga, hgb, gEmb]
    simp only [map_mul]
    ring

  let rep : Ideal (𝓞 (Ext F)) → 𝓞 (Ext F) := fun J =>
    if h : ∃ x, J = Ideal.span {x} then h.choose else 0
  have hrep : ∀ c, Associated (rep (Ideal.span {y c})) (y c) := by
    intro c
    have hex : ∃ x, Ideal.span {y c} = Ideal.span {x} := ⟨y c, rfl⟩
    refine Ideal.span_singleton_eq_span_singleton.1 ?_
    simp only [rep, dif_pos hex]
    exact hex.choose_spec.symm
  choose u hu using hrep
  let Q := (𝓞 (Ext F))ˣ ⧸ (Units.map (algebraMap (𝓞 F) (𝓞 (Ext F))).toMonoidHom).range
  let φ : Quotient (latRel 𝔞 𝔟) → Ideal (𝓞 (Ext F)) × Q := fun c =>
    (Ideal.span {y c}, (QuotientGroup.mk (u c) : Q))
  have hinj : Function.Injective φ := by
    intro c c' h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨hJ, hq⟩ := h
    obtain ⟨η, hη⟩ := QuotientGroup.eq.1 hq
    have hu' : ((u c' : (𝓞 (Ext F))ˣ) : 𝓞 (Ext F)) = (u c : 𝓞 (Ext F)) * algebraMap (𝓞 F) (𝓞 (Ext F)) (η : 𝓞 F) := by
      have : u c' = u c * Units.map (algebraMap (𝓞 F) (𝓞 (Ext F))).toMonoidHom η := by
        rw [hη]; group
      rw [this]; simp
    have key : y c' = y c * algebraMap (𝓞 F) (𝓞 (Ext F)) (η : 𝓞 F) := by
      rw [← hu c', ← hu c, ← hJ, hu']; ring
    have h3 : ((y c' : 𝓞 (Ext F)) : Ext F) = (y c : Ext F) * algebraMap F (Ext F) ((η : 𝓞 F) : F) := by
      rw [key]; rfl
    rw [hy, hy] at h3
    have h4 : gEmb F c'.out.1 = gEmb F c.out.1 * algebraMap F (Ext F) ((η : 𝓞 F) : F) :=
      mul_left_cancel₀ ((_root_.map_ne_zero _).2 hd) (by rw [h3]; ring)
    unfold gEmb at h4
    have h5 : algebraMap F (Ext F) (c'.out.1.1 - ((η : 𝓞 F) : F) * c.out.1.1) +
        algebraMap F (Ext F) (c'.out.1.2 - ((η : 𝓞 F) : F) * c.out.1.2) * ii F = 0 := by
      simp only [map_sub, map_mul]
      linear_combination h4
    obtain ⟨e1, e2⟩ := eq_zero_of_add_mul_ii h5
    exact (Quotient.out_equiv_out.1 ⟨η, by linear_combination e1, by linear_combination e2⟩)
  haveI := hQ
  have hS : Summable (fun p : Ideal (𝓞 (Ext F)) × Q => ((Ideal.absNorm p.1 : ℕ) : ℝ) ^ (-t) * (fun _ : Q => (1 : ℝ)) p.2) :=
    (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal (Ext F) ht).mul_of_nonneg (Summable.of_finite)
      (fun J => Real.rpow_nonneg (Nat.cast_nonneg _) _) (fun _ => zero_le_one)
  have hS' := hS.comp_injective hinj
  set K : ℝ := |((Algebra.norm ℚ (algebraMap F (Ext F) ((d₁ : F) * (d₂ : F))) : ℚ) : ℝ)| with hK
  have hK0 : 0 < K := by
    rw [hK]
    have h0 : algebraMap F (Ext F) ((d₁ : F) * (d₂ : F)) ≠ 0 := (_root_.map_ne_zero _).2 hd
    have h1 : Algebra.norm ℚ (algebraMap F (Ext F) ((d₁ : F) * (d₂ : F))) ≠ 0 := Algebra.norm_ne_zero_iff.2 h0
    exact abs_pos.2 (by exact_mod_cast h1)
  refine (hS'.mul_left (K ^ t)).congr fun c => ?_
  have e1 : ((Algebra.norm ℤ (y c) : ℤ) : ℚ) =
      Algebra.norm ℚ (algebraMap F (Ext F) ((d₁ : F) * (d₂ : F))) * Algebra.norm ℚ (gEmb F c.out.1) := by
    rw [Algebra.coe_norm_int, hy, map_mul]
  have e2 : ((Algebra.norm ℤ (y c) : ℤ) : ℝ) =
      ((Algebra.norm ℚ (algebraMap F (Ext F) ((d₁ : F) * (d₂ : F))) : ℚ) : ℝ) * ((Algebra.norm ℚ (gEmb F c.out.1) : ℚ) : ℝ) := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) e1
  have hN : ((Ideal.absNorm (Ideal.span ({y c} : Set (𝓞 (Ext F)))) : ℕ) : ℝ) =
      K * |((Algebra.norm ℚ (gEmb F c.out.1) : ℚ) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, e2, abs_mul]
  simp only [Function.comp_apply, φ, mul_one]
  rw [hN, Real.mul_rpow hK0.le (abs_nonneg _), ← mul_assoc, ← Real.rpow_add hK0, add_neg_cancel,
    Real.rpow_zero, one_mul]

end GlobalTheory.GaussSum

theorem GlobalTheory.GaussSum.summable_gauss_norm : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (t : ℝ), 1 < t → Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸ (Units.map (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) → Summable (fun c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) => |((Algebra.norm ℚ (GlobalTheory.GaussExt.gEmb F c.out.1) : ℚ) : ℝ)| ^ (-t)) := by
  intro F _ _ _ 𝔞 𝔟 t ht hQ
  exact GlobalTheory.GaussSum.summable_norm_rpow 𝔞 𝔟 ht hQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableGaussianExtensionNormRpowStatement
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_gaussianExtension_norm_rpow : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (t : ℝ), 1 < t → Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸ (Units.map (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) → Summable (fun c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) => |((Algebra.norm ℚ (GlobalTheory.GaussExt.gEmb F c.out.1) : ℚ) : ℝ)| ^ (-t)) := by
  first | exact @GlobalTheory.GaussSum.summable_gauss_norm | exact GlobalTheory.GaussSum.summable_gauss_norm | (intros; apply GlobalTheory.GaussSum.summable_gauss_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHilbertEisensteinLatticeClassWeightTwo
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem GlobalTheory.HeckeTwo.summable_eisClass_two : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
    Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 2 σ z) := by
  intro F _ _ _ 𝔞 𝔟 σ hσ z hz
  obtain ⟨C, hC⟩ := GlobalTheory.T.hilbertEisensteinLatticeSummand_weightTwo_bound F σ hσ z hz
  have hS := (GlobalTheory.T.summable_gaussianExtension_norm_rpow F 𝔞 𝔟 (1 + σ.re) (by linarith) (GlobalTheory.T.finite_gaussianExtension_units_quot_units F)).mul_left C
  refine Summable.of_norm_bounded hS fun c => ?_
  have hp : c.out.1 ≠ 0 := c.out.2.2.2
  have e : |((Algebra.norm ℚ (GlobalTheory.GaussExt.gEmb F c.out.1) : ℚ) : ℝ)| =
      ∏ τ : F →+* ℝ, ((τ c.out.1.1) ^ 2 + (τ c.out.1.2) ^ 2) := by
    rw [GlobalTheory.T.algebraNorm_rat_gaussianExtensionOfPair F c.out.1.1 c.out.1.2]
    exact abs_of_nonneg (Finset.prod_nonneg fun τ _ => by positivity)
  rw [e]
  exact hC _ hp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHilbertEisensteinLatticeClassWeightTwoStatement
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_hilbertEisensteinLatticeClass_weight_two : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 2 σ z) := by
  first | exact @GlobalTheory.HeckeTwo.summable_eisClass_two | exact GlobalTheory.HeckeTwo.summable_eisClass_two | (intros; apply GlobalTheory.HeckeTwo.summable_eisClass_two <;> assumption)
end
