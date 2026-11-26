module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NormDetDenomLeRankOne
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW

variable {N : ℕ}

theorem im_quad_eq_re_imH (M : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) :
    (star x ⬝ᵥ M *ᵥ x).im = (star x ⬝ᵥ imH M *ᵥ x).re := by
  have hq : star x ⬝ᵥ Mᴴ *ᵥ x = star (star x ⬝ᵥ M *ᵥ x) := by
    rw [← star_dotProduct_star, star_mulVec, star_star, dotProduct_mulVec]
  unfold imH
  rw [smul_mulVec, dotProduct_smul, sub_mulVec, dotProduct_sub, hq, smul_eq_mul]
  generalize star x ⬝ᵥ M *ᵥ x = q
  rw [Complex.star_def, Complex.sub_conj,
    show ((2 * q.im : ℝ) : ℂ) * I = (2 * I) * (q.im : ℂ) by push_cast; ring,
    inv_mul_cancel_left₀ (mul_ne_zero two_ne_zero I_ne_zero), Complex.ofReal_re]

theorem imH_add_I_smul (Z P : Matrix (Fin N) (Fin N) ℂ) (hP : P.IsHermitian) :
    imH (Z + I • P) = imH Z + P := by
  unfold imH
  rw [conjTranspose_add, conjTranspose_smul, hP.eq]
  have e : Z + I • P - (Zᴴ + star I • P) = (Z - Zᴴ) + (2 * I) • P := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.star_def,
      Complex.conj_I]
    ring
  rw [e, smul_add, smul_smul, inv_mul_cancel₀ (mul_ne_zero two_ne_zero I_ne_zero), one_smul]

theorem imH_mul_denom (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian) :
    imH (C * (C * Z + D)ᴴ) = -(C * imH Z * Cᴴ) := by
  have hDC : D * Cᴴ = C * Dᴴ := by
    have e := h.eq
    rwa [conjTranspose_mul, conjTranspose_conjTranspose] at e
  have e : C * (C * Z + D)ᴴ - (C * (C * Z + D)ᴴ)ᴴ = -(C * (Z - Zᴴ) * Cᴴ) := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_add, conjTranspose_mul,
      Matrix.add_mul (C * Z) D Cᴴ, hDC]
    noncomm_ring
  unfold imH
  rw [e, Matrix.mul_smul, Matrix.smul_mul, smul_neg]

theorem im_quad_denom (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian)
    (x : Fin N → ℂ) :
    (star x ⬝ᵥ C *ᵥ ((C * Z + D)ᴴ *ᵥ x)).im =
      -(star (Cᴴ *ᵥ x) ⬝ᵥ imH Z *ᵥ (Cᴴ *ᵥ x)).re := by
  have e : star (Cᴴ *ᵥ x) ⬝ᵥ imH Z *ᵥ (Cᴴ *ᵥ x) = star x ⬝ᵥ (C * imH Z * Cᴴ) *ᵥ x := by
    rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  rw [e, mulVec_mulVec, im_quad_eq_re_imH, imH_mul_denom C D Z h, neg_mulVec, dotProduct_neg,
    Complex.neg_re]

theorem det_denom_ne_zero (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian)
    (hp : (C * Cᴴ + D * Dᴴ).PosDef) (hZ : (imH Z).PosDef) : (C * Z + D).det ≠ 0 := by
  intro hdet
  have h0 : ((C * Z + D)ᴴ).det = 0 := by rw [det_conjTranspose, hdet, star_zero]
  obtain ⟨x, hx0, hx⟩ := exists_mulVec_eq_zero_iff.mpr h0
  have h1 := im_quad_denom C D Z h x
  rw [hx, mulVec_zero, dotProduct_zero, Complex.zero_im] at h1
  have hCx : Cᴴ *ᵥ x = 0 := by
    by_contra hne
    have h2 := (Complex.pos_iff.mp (hZ.dotProduct_mulVec_pos hne)).1
    linarith
  have hDx : Dᴴ *ᵥ x = 0 := by
    rw [conjTranspose_add, conjTranspose_mul, add_mulVec, ← mulVec_mulVec, hCx, mulVec_zero,
      zero_add] at hx
    exact hx
  have h3 := hp.dotProduct_mulVec_pos hx0
  rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hCx, hDx, mulVec_zero, mulVec_zero, add_zero,
    dotProduct_zero] at h3
  exact lt_irrefl _ h3

theorem norm_det_denom_le_rank_one (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian)
    (hp : (C * Cᴴ + D * Dᴴ).PosDef) (hZ : (imH Z).PosDef) (v : Fin N → ℂ) :
    ‖(C * Z + D).det‖ ≤ ‖(C * (Z + I • vecMulVec v (star v)) + D).det‖ := by
  have hW := det_denom_ne_zero C D Z h hp hZ
  have hWh : IsUnit ((C * Z + D)ᴴ).det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hW)
  obtain ⟨y, rfl⟩ : ∃ y, (C * Z + D)ᴴ *ᵥ y = v :=
    ⟨((C * Z + D)ᴴ)⁻¹ *ᵥ v, by rw [mulVec_mulVec, mul_nonsing_inv (A := (C * Z + D)ᴴ) hWh, one_mulVec]⟩
  have hstar : star ((C * Z + D)ᴴ *ᵥ y) = star y ᵥ* (C * Z + D) := by
    rw [star_mulVec, conjTranspose_conjTranspose]
  have e1 : I • vecMulVec (C *ᵥ ((C * Z + D)ᴴ *ᵥ y)) (star y ᵥ* (C * Z + D)) =
      vecMulVec (I • (C *ᵥ ((C * Z + D)ᴴ *ᵥ y))) (star y) * (C * Z + D) := by
    rw [vecMulVec_mul]
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have key : C * (Z + I • vecMulVec ((C * Z + D)ᴴ *ᵥ y) (star ((C * Z + D)ᴴ *ᵥ y))) + D =
      (1 + vecMulVec (I • (C *ᵥ ((C * Z + D)ᴴ *ᵥ y))) (star y)) * (C * Z + D) := by
    rw [hstar, Matrix.mul_add C, Matrix.mul_smul C, mul_vecMulVec C, e1,
      Matrix.add_mul (1 : Matrix (Fin N) (Fin N) ℂ), Matrix.one_mul]
    abel
  have hs : (star y ⬝ᵥ C *ᵥ ((C * Z + D)ᴴ *ᵥ y)).im ≤ 0 := by
    rw [im_quad_denom C D Z h y]
    have h0 := (Complex.nonneg_iff.mp (hZ.posSemidef.dotProduct_mulVec_nonneg (Cᴴ *ᵥ y))).1
    linarith
  have hone : 1 ≤ ‖1 + I * (star y ⬝ᵥ C *ᵥ ((C * Z + D)ᴴ *ᵥ y))‖ := by
    refine le_trans ?_ ((le_abs_self _).trans (Complex.abs_re_le_norm _))
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_sub]
    linarith
  rw [key, det_mul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
    smul_eq_mul, norm_mul]
  exact le_mul_of_one_le_left (norm_nonneg _) hone

private theorem exists_eq_sum_vecMulVec_star {N : ℕ} (P : Matrix (Fin N) (Fin N) ℂ) (hP : P.PosSemidef) :
    ∃ w : Fin N → Fin N → ℂ, P = ∑ k, vecMulVec (w k) (star (w k)) := by
  refine ⟨fun k i => (Real.sqrt (hP.1.eigenvalues k) : ℂ) *
    (hP.1.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) i k, ?_⟩
  have hspec := hP.1.spectral_theorem
  ext i j
  conv_lhs => rw [hspec]
  rw [Unitary.conjStarAlgAut_apply, Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, vecMulVec_apply, Pi.star_apply, star_mul', Function.comp_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsq : ((Real.sqrt (hP.1.eigenvalues k) : ℝ) : ℂ) * (Real.sqrt (hP.1.eigenvalues k) : ℂ) =
      (RCLike.ofReal (hP.1.eigenvalues k) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hP.eigenvalues_nonneg k)]
    rfl
  have hs : star ((Real.sqrt (hP.1.eigenvalues k) : ℝ) : ℂ) = (Real.sqrt (hP.1.eigenvalues k) : ℂ) :=
    Complex.conj_ofReal _
  rw [Matrix.star_apply, hs, ← hsq]
  ring

theorem norm_det_denom_mono :
    ∀ (N : ℕ) (C D Z P : Matrix (Fin N) (Fin N) ℂ), (C * Dᴴ).IsHermitian → (C * Cᴴ + D * Dᴴ).PosDef → (imH Z).PosDef → P.PosSemidef → (C * Z + D).det ≠ 0 ∧ ‖(C * Z + D).det‖ ≤ ‖(C * (Z + I • P) + D).det‖ := by
  intro N C D Z P h hp hZ hP
  refine ⟨det_denom_ne_zero C D Z h hp hZ, ?_⟩
  obtain ⟨w, rfl⟩ := exists_eq_sum_vecMulVec_star P hP
  have gen : ∀ s : Finset (Fin N),
      (imH (Z + I • ∑ k ∈ s, vecMulVec (w k) (star (w k)))).PosDef ∧
        ‖(C * Z + D).det‖ ≤ ‖(C * (Z + I • ∑ k ∈ s, vecMulVec (w k) (star (w k))) + D).det‖ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, smul_zero, add_zero]
      exact ⟨hZ, le_rfl⟩
    | insert k s hk ih =>
      obtain ⟨ih1, ih2⟩ := ih
      rw [Finset.sum_insert hk, add_comm (vecMulVec _ _) _, smul_add, ← add_assoc]
      refine ⟨?_, ?_⟩
      · rw [imH_add_I_smul _ _ (posSemidef_vecMulVec_self_star (w k)).isHermitian]
        exact ih1.add_posSemidef (posSemidef_vecMulVec_self_star (w k))
      · exact ih2.trans (norm_det_denom_le_rank_one C D _ h hp ih1 (w k))
  exact (gen Finset.univ).2

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CycOfPrime
open scoped TensorProduct LinearAlgebra.Projectivization

namespace GlobalTheory.SW.Hyper

variable {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]

theorem exists_fun (P : Ideal O) [hP : P.IsMaximal] (N : Submodule O M) (v : M) (hv : v ∉ N)
    (hPv : ∀ c ∈ P, c • v ∈ N) (hc : ∀ x, ∃ r : O, x - r • v ∈ N) :
    ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N := by
  classical
  let g : O →ₗ[O] M ⧸ N := LinearMap.toSpanSingleton O (M ⧸ N) (N.mkQ v)
  have hker : LinearMap.ker g = P := by
    ext r
    simp only [LinearMap.mem_ker, g, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro h
      by_contra hr
      obtain ⟨y, i, hi, hyi⟩ := hP.exists_inv hr
      apply hv
      have hv' : v = y • (r • v) + i • v := by rw [smul_smul, ← add_smul, hyi, one_smul]
      rw [hv']
      exact N.add_mem (N.smul_mem y h) (hPv i hi)
    · exact hPv r
  have hs : Function.Surjective g := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N z
    obtain ⟨r, hr⟩ := hc x
    refine ⟨r, ?_⟩
    simp only [g, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← neg_sub]
    exact N.neg_mem hr
  let e : (O ⧸ P) ≃ₗ[O] M ⧸ N :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (g.quotKerEquivOfSurjective hs)
  refine ⟨e.symm.toLinearMap ∘ₗ N.mkQ, ?_, ?_⟩
  · intro h0
    apply hv
    have h1 : (e.symm.toLinearMap ∘ₗ N.mkQ) v = 0 := by rw [h0]; rfl
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using h1
  · rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]

theorem surj_of_ne (P : Ideal O) [hP : P.IsMaximal] (f : M →ₗ[O] O ⧸ P) (hf : f ≠ 0) :
    ∃ v, f v = 1 := by
  obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (LinearMap.ext fun x => by simpa using h x)
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv hw
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨c • w, ?_⟩
  rw [map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_comm, hb]

theorem index_ker (P : Ideal O) [hP : P.IsMaximal] (f : M →ₗ[O] O ⧸ P) (hf : f ≠ 0) :
    (LinearMap.ker f).toAddSubgroup.index = Nat.card (O ⧸ P) := by
  obtain ⟨v, hv⟩ := surj_of_ne P f hf
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨r • v, ?_⟩
    rw [map_smul, hv, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
  have h := AddSubgroup.index_ker f.toAddMonoidHom
  rw [AddMonoidHom.range_eq_top.mpr hs, AddSubgroup.card_top] at h
  exact h

theorem cyc_of_prime (N : Submodule O M) {q : ℕ} (hq : q.Prime)
    (h : N.toAddSubgroup.index = q) : ∃ v, v ∉ N ∧ ∀ x, ∃ r : O, x - r • v ∈ N := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hcard : Nat.card (M ⧸ N.toAddSubgroup) = q := by
    rw [← AddSubgroup.index_eq_card]; exact h
  have hne : N.toAddSubgroup ≠ ⊤ := by
    intro ht
    rw [ht, AddSubgroup.index_top] at h
    exact hq.one_lt.ne h
  obtain ⟨v, hv⟩ : ∃ v, v ∉ N := by
    by_contra hn
    push Not at hn
    exact hne (eq_top_iff.mpr fun x _ => hn x)
  refine ⟨v, hv, fun x => ?_⟩
  have hv0 : (QuotientAddGroup.mk v : M ⧸ N.toAddSubgroup) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]; exact hv
  have hx : (QuotientAddGroup.mk x : M ⧸ N.toAddSubgroup) ∈
      AddSubgroup.zmultiples (QuotientAddGroup.mk v) := mem_zmultiples_of_prime_card hcard hv0
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  refine ⟨(n : O), ?_⟩
  rw [Int.cast_smul_eq_zsmul]
  have h2 : (QuotientAddGroup.mk (n • v) : M ⧸ N.toAddSubgroup) = QuotientAddGroup.mk x := by
    rw [QuotientAddGroup.mk_zsmul]; exact hn
  rw [QuotientAddGroup.eq] at h2
  rw [sub_eq_neg_add]
  exact h2

theorem finrank_fibre (O M k : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [Algebra O k] :
    Module.finrank k (k ⊗[O] M) = Module.finrank O M := by
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  have hlc := Module.isLocallyConstant_rankAtStalk (R := O) (M := M)
  let q0 : PrimeSpectrum k := ⟨⊥, Ideal.isPrime_bot⟩
  let p0 : PrimeSpectrum O := ⟨⊥, Ideal.isPrime_bot⟩
  have h1 : Module.finrank k (k ⊗[O] M) = Module.rankAtStalk (R := k) (k ⊗[O] M) q0 := by
    rw [Module.rankAtStalk_eq_finrank_of_free]; rfl
  have hp : p0.asIdeal.primeCompl ≤ nonZeroDivisors O := by
    intro x hx
    have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ Ideal.zero_mem _)
    exact mem_nonZeroDivisors_of_ne_zero hx0
  have h2 : Module.rankAtStalk (R := O) M p0 = Module.finrank O M := by
    rw [Module.rankAtStalk,
      IsLocalization.finrank_eq (Localization.AtPrime p0.asIdeal) p0.asIdeal.primeCompl hp,
      IsLocalizedModule.finrank_eq p0.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap p0.asIdeal.primeCompl M) hp]
  rw [h1, Module.rankAtStalk_baseChange, hlc.apply_eq_of_preconnectedSpace _ p0, h2]


attribute [local instance] Ideal.Quotient.field in
theorem count [IsDomain O] [Module.Finite O M] [Module.Projective O M] (P : Ideal O)
    [hP : P.IsMaximal] [Finite (O ⧸ P)] :
    {N : Submodule O M | ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N}.Finite ∧
    {N : Submodule O M | ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N}.ncard *
      (Nat.card (O ⧸ P) - 1) = Nat.card (O ⧸ P) ^ Module.finrank O M - 1 := by
  classical
  have hcard : Nat.card (M →ₗ[O] O ⧸ P) = Nat.card (O ⧸ P) ^ Module.finrank O M := by
    rw [Nat.card_congr (LinearMap.liftBaseChangeEquiv (M := M) (N := O ⧸ P) (O ⧸ P)).toEquiv,
      Module.natCard_eq_pow_finrank (K := O ⧸ P)]
    congr 1
    rw [← finrank_fibre O M (O ⧸ P)]
    exact Subspace.dual_finrank_eq
  have : Finite (M →ₗ[O] O ⧸ P) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ Nat.card_pos.ne')
  let φ : ℙ (O ⧸ P) (M →ₗ[O] O ⧸ P) → Submodule O M :=
    Projectivization.lift (K := O ⧸ P) (V := M →ₗ[O] O ⧸ P)
      (fun f => LinearMap.ker f.1) (by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ t (hab : a = t • b)
      have ht : t ≠ 0 := by
        rintro rfl
        apply ha
        rw [hab, zero_smul]
      ext x
      simp only [LinearMap.mem_ker, hab, LinearMap.smul_apply, smul_eq_zero, ht, false_or])
  have key : ∀ (f g : M →ₗ[O] O ⧸ P) (hf : f ≠ 0) (hg : g ≠ 0),
      LinearMap.ker f = LinearMap.ker g →
      Projectivization.mk (O ⧸ P) g hg = Projectivization.mk (O ⧸ P) f hf := by
    intro f g hf hg hfg
    obtain ⟨w, hw⟩ := surj_of_ne P f hf
    rw [Projectivization.mk_eq_mk_iff']
    refine ⟨g w, ?_⟩
    ext x
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (f x)
    have hmem : x - r • w ∈ LinearMap.ker g := by
      rw [← hfg, LinearMap.mem_ker, map_sub, map_smul, hw, ← hr, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, mul_one, sub_self]
    rw [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at hmem
    rw [LinearMap.smul_apply, hmem, smul_eq_mul, ← hr, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, mul_comm]
  have hφ : Function.Injective φ := by
    intro x y hxy
    rw [← Projectivization.mk_rep x, ← Projectivization.mk_rep y] at hxy ⊢
    exact (key _ _ _ _ hxy).symm
  have hS : {N : Submodule O M | ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N}
      = Set.range φ := by
    ext N
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨Projectivization.mk _ f hf, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨x.rep, x.rep_nonzero, ?_⟩
      have h1 : φ (Projectivization.mk _ x.rep x.rep_nonzero) = LinearMap.ker x.rep := rfl
      rw [Projectivization.mk_rep] at h1
      exact h1.symm
  rw [hS]
  refine ⟨Set.finite_range φ, ?_⟩
  rw [Set.ncard_range_of_injective hφ]
  have h' := Projectivization.card' (O ⧸ P) (M →ₗ[O] O ⧸ P)
  rw [hcard] at h'
  rw [h', Nat.add_sub_cancel]

end GlobalTheory.SW.Hyper
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsUnitaryExt
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.RowExt

theorem exists_right_inv {E : Type} [Field E] [NumberField E] {κ ι : Type} [Fintype κ] [Fintype ι]
    [DecidableEq κ] (c : E) (W : Matrix κ ι E) (hW : IntM W)
    (hli : LinearIndependent E (fun i => W i))
    (hprim : ∀ t : κ → E, (∀ j, IsIntegral ℤ ((t ᵥ* W) j)) → ∀ i, IsIntegral ℤ (c * t i)) :
    ∃ X : Matrix ι κ E, IntM X ∧ W * X = c • (1 : Matrix κ κ E) := by
  classical
  have hinj : LinearMap.ker W.vecMulLinear = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Matrix.vecMul_injective_iff.mpr hli
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  have hg' : ∀ t, g (t ᵥ* W) = t := fun t => LinearMap.congr_fun hg t
  let j : (ι → 𝓞 E) →ₗ[𝓞 E] (ι → E) := (Algebra.linearMap (𝓞 E) E).compLeft ι
  let q : (ι → E) →ₗ[E] (ι → E) := LinearMap.id - W.vecMulLinear ∘ₗ g
  let φ : (ι → 𝓞 E) →ₗ[𝓞 E] (ι → E) := (q.restrictScalars (𝓞 E)) ∘ₗ j
  haveI : Module.Finite (𝓞 E) (LinearMap.range φ) := inferInstance
  haveI : Module.FinitePresentation (𝓞 E) (LinearMap.range φ) :=
    Module.finitePresentation_of_finite _ _
  haveI : Module.Flat (𝓞 E) (LinearMap.range φ) := inferInstance
  haveI : Module.Projective (𝓞 E) (LinearMap.range φ) :=
    Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property φ.rangeRestrict LinearMap.id
    φ.surjective_rangeRestrict
  let r : (ι → 𝓞 E) →ₗ[𝓞 E] (ι → 𝓞 E) := LinearMap.id - s ∘ₗ φ.rangeRestrict
  have hr : ∀ m, φ (r m) = 0 := by
    intro m
    have := congrArg Subtype.val (LinearMap.congr_fun hs (φ.rangeRestrict m))
    simp only [r, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub]
    rw [sub_eq_zero]
    exact this.symm
  have hr' : ∀ m, g (j (r m)) ᵥ* W = j (r m) := by
    intro m
    have : j (r m) - g (j (r m)) ᵥ* W = 0 := hr m
    exact (sub_eq_zero.mp this).symm
  let h : (ι → 𝓞 E) →ₗ[𝓞 E] (κ → E) := (g.restrictScalars (𝓞 E)) ∘ₗ j ∘ₗ r
  refine ⟨Matrix.of fun a k => c * h (Pi.single a 1) k, ?_, ?_⟩
  · intro a k
    refine hprim _ (fun b => ?_) k
    show IsIntegral ℤ ((g (j (r _)) ᵥ* W) b)
    rw [hr']
    exact RingOfIntegers.isIntegral_coe _
  · ext i k
    let w : ι → 𝓞 E := fun a => ⟨W i a, hW i a⟩
    have hjw : j w = Pi.single i 1 ᵥ* W := by
      rw [Matrix.single_one_vecMul]; rfl
    have hφw : φ.rangeRestrict w = 0 := by
      apply Subtype.ext
      show j w - g (j w) ᵥ* W = 0
      rw [hjw, hg', sub_self]
    have hw : h w = Pi.single i 1 := by
      show g (j (w - s (φ.rangeRestrict w))) = _
      rw [hφw, map_zero, sub_zero, hjw, hg']
    have hw2 : w = ∑ a, w a • Pi.single a 1 := pi_eq_sum_univ' w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hw2, map_sum] at hw
    have := congrFun hw k
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply] at this
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    have h1 : (1 : Matrix κ κ E) i k = (Pi.single i 1 : κ → E) k := by
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [h1, ← this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Algebra.smul_def, mul_left_comm]
    rfl

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {α β γ : Type}

theorem ccT_eq (A : Matrix α β E) : ccT A = Aᴴ := rfl

omit [NumberField E] [IsCMField E] in
theorem intM_mul [Fintype β] {A : Matrix α β E} {B : Matrix β γ E} (hA : IntM A) (hB : IntM B) :
    IntM (A * B) := fun a c => by
  rw [Matrix.mul_apply]
  exact IsIntegral.sum _ fun b _ => (hA a b).mul (hB b c)

theorem intM_conj {A : Matrix α β E} (hA : IntM A) : IntM Aᴴ := fun a b =>
  (hA b a).map ((IsCMField.complexConj E).toAlgHom.restrictScalars ℤ)

omit [NumberField E] [IsCMField E] in
theorem intM_nat {A : Matrix α β E} (n : ℕ) (hA : IntM A) : IntM ((n : E) • A) := fun a b =>
  (isIntegral_natCast n).mul (hA a b)

omit [NumberField E] [IsCMField E] in
theorem intM_J [DecidableEq α] : IntM (Matrix.J α E) := by
  rintro (a | a) (b | b) <;> by_cases h : a = b <;>
    simp [Matrix.J, Matrix.one_apply, h, isIntegral_zero, isIntegral_one, isIntegral_one.neg]

theorem J_conj [DecidableEq α] : (Matrix.J α E)ᴴ = -Matrix.J α E := by
  simp [Matrix.J, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg]

end

theorem exists_unitary_ext :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N c : ℕ), 0 < c → ∃ c' : ℕ, 0 < c' ∧
      ∀ W : Matrix (Fin N) (Fin N ⊕ Fin N) E, IntM W → LinearIndependent E (fun i => W i) →
        W * Matrix.J (Fin N) E * ccT W = 0 →
        (∀ t : Fin N → E, (∀ j, IsIntegral ℤ ((t ᵥ* W) j)) → ∀ i, IsIntegral ℤ ((c : E) * t i)) →
        ∃ γ ∈ UU E N, Den c' γ ∧ ∀ a, γ (Sum.inr a) = W a := by
  intro E _ _ _ N c hc
  refine ⟨2 * c * c, by positivity, fun W hW hli hiso hprim => ?_⟩
  obtain ⟨X, hX, hWX⟩ := exists_right_inv (c : E) W hW hli hprim
  rw [ccT_eq] at hiso
  have hc0 : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  set J := Matrix.J (Fin N) E with hJ
  have hJJ : J * J = -1 := Matrix.J_squared _ _
  have hJc : Jᴴ = -J := J_conj
  have hJi : IntM J := intM_J
  obtain ⟨V₀, hV₀⟩ : ∃ V₀ : Matrix (Fin N) (Fin N ⊕ Fin N) E, V₀ = (c : E)⁻¹ • (Xᴴ * J) := ⟨_, rfl⟩
  have hcV : (c : E) • V₀ = Xᴴ * J := by rw [hV₀, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  have hVi : IntM ((c : E) • V₀) := hcV ▸ intM_mul (intM_conj hX) hJi
  have h1 : V₀ * J * Wᴴ = -1 := by
    rw [hV₀, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc Xᴴ, hJJ, Matrix.mul_neg,
      Matrix.mul_one, Matrix.neg_mul, ← Matrix.conjTranspose_mul, hWX]
    simp [smul_smul, hc0]
  have skew : ∀ A B : Matrix (Fin N) (Fin N ⊕ Fin N) E, (A * J * Bᴴ)ᴴ = -(B * J * Aᴴ) := by
    intro A B
    simp [Matrix.conjTranspose_mul, hJc, Matrix.mul_assoc]
  have h2 : W * J * V₀ᴴ = 1 := by
    have := skew V₀ W
    rw [h1] at this
    simpa using this.symm
  obtain ⟨S, hS⟩ : ∃ S, S = V₀ * J * V₀ᴴ := ⟨_, rfl⟩
  have hSc : Sᴴ = -S := hS ▸ skew V₀ V₀
  obtain ⟨T, hT⟩ : ∃ T, T = (-(2 : E)⁻¹) • S := ⟨_, rfl⟩
  have hTc : Tᴴ = -T := by
    rw [hT, Matrix.conjTranspose_smul, hSc]; simp
  obtain ⟨V, hV⟩ : ∃ V, V = V₀ + T * W := ⟨_, rfl⟩
  have k2 : W * J * Vᴴ = 1 := by
    rw [hV, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.mul_add, h2,
      ← Matrix.mul_assoc, hiso, Matrix.zero_mul, add_zero]
  have k1 : V * J * Wᴴ = -1 := by
    have := skew W V
    rw [k2] at this
    rw [← neg_neg (V * J * Wᴴ), ← this]; simp
  have k0 : V * J * Vᴴ = 0 := by
    have e : V * J * V₀ᴴ = S + T := by
      rw [hV, Matrix.add_mul, Matrix.add_mul, ← hS, Matrix.mul_assoc T, Matrix.mul_assoc T, h2,
        Matrix.mul_one]
    conv_lhs => rw [show Vᴴ = V₀ᴴ + Wᴴ * Tᴴ by
      rw [hV, Matrix.conjTranspose_add, Matrix.conjTranspose_mul]]
    rw [Matrix.mul_add, e, ← Matrix.mul_assoc, k1, hTc, hT]
    simp only [Matrix.neg_mul, Matrix.one_mul, neg_neg]
    rw [add_assoc, ← add_smul, show (-(2 : E)⁻¹ + -(2 : E)⁻¹) = -1 by norm_num]
    simp
  have key : Matrix.fromRows V W * J * (Matrix.fromRows V W)ᴴ = J := by
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromRows_mul,
      Matrix.fromRows_mul_fromCols, k0, k1, k2, hiso]
    rfl
  refine ⟨Matrix.fromRows V W, ?_, ?_, fun a => rfl⟩
  · generalize Matrix.fromRows V W = g at key
    show gᴴ * J * g = J
    have e1 : g * (J * gᴴ * -J) = 1 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, key, Matrix.mul_neg, hJJ, neg_neg]
    have e2 := mul_eq_one_comm.mp e1
    have e3 : J * (J * gᴴ * -J * g) = J := by rw [e2, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ] at e3
    simpa using e3
  · have hVV : ((2 * c * c : ℕ) : E) • V = ((2 * c : ℕ) : E) • ((c : E) • V₀) -
        ((c : E) • V₀) * J * ((c : E) • V₀)ᴴ * W := by
      rw [hV, hT, hS]
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul,
        star_natCast, sub_eq_add_neg, ← neg_smul]
      congr 2
      · push_cast; ring
      · push_cast; field_simp
    have i1 := intM_nat (2 * c) hVi
    have i2 := intM_mul (intM_mul (intM_mul hVi hJi) (intM_conj hVi)) hW
    rintro (a | a) b
    · show IsIntegral ℤ ((((2 * c * c : ℕ) : E) • V) a b)
      rw [hVV]
      exact (i1 a b).sub (i2 a b)
    · exact intM_nat (2 * c * c) hW a b

end GlobalTheory.SW.RowExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLinearIndependentOfRatIndependent
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW

theorem exists_linearIndependent_of_rat_independent {E U : Type} [Field E] [NumberField E]
    [AddCommGroup U] [Module E U] [Module ℚ U] [IsScalarTower ℚ E U] (S : ℕ → Set U) (N : ℕ)
    (h : ∀ i < N, ∃ u : Fin (Module.finrank ℚ E * i + 1) → U,
      LinearIndependent ℚ u ∧ ∀ k, u k ∈ S i) :
    ∃ w : Fin N → U, LinearIndependent E w ∧ ∀ i : Fin N, w i ∈ S i := by
  induction N with
  | zero => exact ⟨Fin.elim0, linearIndependent_empty_type, fun i => i.elim0⟩
  | succ N ih =>
    obtain ⟨w, hw, hS⟩ := ih fun i hi => h i (by omega)
    obtain ⟨u, hu, huS⟩ := h N (by omega)
    obtain ⟨k, hk⟩ : ∃ k, u k ∉ Submodule.span E (Set.range w) := by
      by_contra! hc
      have : Module.Finite E (Submodule.span E (Set.range w)) :=
        Module.Finite.span_of_finite E (Set.finite_range w)
      have : Module.Finite ℚ (Submodule.span E (Set.range w)) := Module.Finite.trans E _
      have h1 : LinearIndependent ℚ (fun k => (⟨u k, hc k⟩ : Submodule.span E (Set.range w))) :=
        LinearIndependent.of_comp
          ((Submodule.span E (Set.range w)).subtype.restrictScalars ℚ) hu
      have h2 := h1.fintype_card_le_finrank
      rw [← Module.finrank_mul_finrank ℚ E (Submodule.span E (Set.range w)),
        finrank_span_eq_card hw] at h2
      simp at h2
    refine ⟨Fin.snoc w (u k), linearIndependent_finSnoc.2 ⟨hw, hk⟩, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using huS k
    · simpa using hS j

theorem prod_pow_le_prod_of_mono (l : ℕ → ℝ) (hl : ∀ i, 0 ≤ l i) (d N : ℕ)
    (hm : ∀ i j, i ≤ j → j ≤ d * N → l i ≤ l j) :
    ∏ i ∈ Finset.range N, l (d * i + 1) ^ d ≤ ∏ j ∈ Finset.range (d * N), l (j + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, mul_add, mul_one, Finset.prod_range_add]
    refine mul_le_mul (ih fun i j hij hj => hm i j hij (by nlinarith)) ?_ (pow_nonneg (hl _) _)
      (Finset.prod_nonneg fun _ _ => hl _)
    calc l (d * N + 1) ^ d = ∏ _j ∈ Finset.range d, l (d * N + 1) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hl _) fun j hj => hm _ _ (by omega) (by
          have := Finset.mem_range.1 hj
          rw [mul_add]; omega)

theorem IsType.prod_univ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) {M : Type} [CommMonoid M] (g : (E →+* ℂ) → M) :
    ∏ σ, g σ = ∏ τ : Ψ, (g τ * g (ComplexEmbedding.conjugate τ.1)) := by
  classical
  rw [Finset.prod_coe_sort Ψ (fun τ => g τ * g (ComplexEmbedding.conjugate τ)),
    Finset.prod_mul_distrib, ← Finset.prod_mul_prod_compl Ψ]
  congr 1
  symm
  refine Finset.prod_bij' (fun τ _ => ComplexEmbedding.conjugate τ)
    (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_ ?_ ?_
  · intro τ hτ; exact Finset.mem_compl.2 ((hΨ τ).1 hτ)
  · intro τ hτ
    by_contra hc
    exact Finset.mem_compl.1 hτ ((hΨ τ).2 hc)
  · intro τ _; exact star_star τ
  · intro τ _; exact star_star τ
  · intro τ _; rfl

theorem IsType.finrank_eq {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) : Module.finrank ℚ E = 2 * Ψ.card := by
  have h := hΨ.prod_univ (fun _ => Multiplicative.ofAdd (1 : ℕ))
  have h2 := congrArg Multiplicative.toAdd h
  simp only [Finset.prod_const, toAdd_pow, toAdd_mul, toAdd_ofAdd, smul_eq_mul, Finset.card_univ,
    Embeddings.card, Fintype.card_coe] at h2
  omega

theorem exists_linearIndependent_prod_norm_le {E U V ι : Type} [Field E] [NumberField E]
    [AddCommGroup U] [Module E U] [Module ℚ U] [IsScalarTower ℚ E U] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [Fintype ι] [DecidableEq ι] {N : ℕ}
    (hι : Fintype.card ι = Module.finrank ℚ E * N) (φ : U →ₗ[ℤ] V) (u : ι → U)
    (hu : LinearIndependent ℝ fun k => φ (u k)) :
    ∃ w : Fin N → U, LinearIndependent E w ∧ (∀ i, w i ∈ Submodule.span ℤ (Set.range u)) ∧
      ∏ i, ‖φ (w i)‖ ^ Module.finrank ℚ E ≤
        (Fintype.card ι : ℝ) ^ ((Fintype.card ι : ℝ) / 2) * √(gram ℝ fun k => φ (u k)).det := by
  set d := Module.finrank ℚ E with hd
  have hd0 : 0 < d := Module.finrank_pos
  set L := Submodule.span ℤ (Set.range fun k => φ (u k)) with hL
  have : DiscreteTopology L := discreteTopology_span_of_linearIndependent hu
  have huZ : LinearIndependent ℤ fun k => φ (u k) := hu.restrict_scalars' ℤ
  have hr : Module.finrank ℤ L = Fintype.card ι := finrank_span_eq_card huZ
  have hrR : Module.finrank ℝ (Submodule.span ℝ (L : Set V)) = d * N := by
    rw [finrank_span_eq_finrank_int, hr, hι]
  have hLm : L = (Submodule.span ℤ (Set.range u)).map φ := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  obtain ⟨w, hw, hS⟩ := exists_linearIndependent_of_rat_independent (E := E)
    (fun i => {t | t ∈ Submodule.span ℤ (Set.range u) ∧ ‖φ t‖ ≤ succMin L (d * i + 1)}) N (by
      intro i hi
      obtain ⟨v, hv, hvL⟩ := exists_linearIndependent_norm_le_succMin (L := L) (i := d * i + 1)
        (by rw [hrR]; nlinarith)
      have : ∀ k, ∃ t ∈ Submodule.span ℤ (Set.range u), φ t = v k := fun k => by
        have := (hvL k).1
        rwa [hLm] at this
      choose t ht htv using this
      refine ⟨t, (LinearIndependent.iff_fractionRing ℤ ℚ).1 (LinearIndependent.of_comp φ ?_),
        fun k => ⟨ht k, ?_⟩⟩
      · have : φ ∘ t = v := funext htv
        rw [this]; exact hv.restrict_scalars' ℤ
      · rw [htv]; exact (hvL k).2)
  refine ⟨w, hw, fun i => (hS i).1, ?_⟩
  have h1 := prod_succMin_le_rpow_mul_spanCovol L
  rw [spanCovol_span huZ, Fin.prod_univ_eq_prod_range (fun i => succMin L (i + 1)), hr] at h1
  refine le_trans ?_ h1
  rw [hι]
  refine le_trans ?_ (prod_pow_le_prod_of_mono (succMin L) (succMin_nonneg L) d N
    fun i j hij hj => succMin_mono hij (by rwa [hrR]))
  rw [← Fin.prod_univ_eq_prod_range (fun i => succMin L (d * i + 1) ^ d)]
  exact Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _) (hS i).2 _

theorem posDef_map_mul_conjTranspose {E m n : Type} [Field E] [Fintype m] [Fintype n]
    {W : Matrix n m E} (hW : LinearIndependent E fun i => W i) (σ : E →+* ℂ) :
    (W.map σ * (W.map σ)ᴴ).PosDef := by
  let _ := σ.toAlgebra
  exact PosDef.mul_conjTranspose_self _
    (vecMul_injective_iff.2 ((linearIndependent_algebraMap_comp_iff (S := ℂ)).2 hW))

noncomputable def rowEmb {E m n : Type} [Field E] [Fintype n] (W : Matrix n m E) :
    (n → E) →ₗ[ℤ] EuclideanSpace ℂ ((E →+* ℂ) × m) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun t => WithLp.toLp 2 fun p => p.1 ((t ᵥ* W) p.2)
      map_zero' := by ext p; simp
      map_add' := fun s t => by ext p; simp [add_vecMul] }

open scoped Classical in
open Classical in
theorem det_gram_rowEmb {E m : Type} [Field E] [NumberField E] [Fintype m] {N : ℕ}
    (W : Matrix (Fin N) m E) (ω : (E →+* ℂ) → E) :
    (((gram ℝ fun p : Fin N × (E →+* ℂ) => rowEmb W (Pi.single p.1 (ω p.2))).det : ℝ) : ℂ) =
      (normSq (Matrix.of fun k σ : E →+* ℂ => σ (ω k)).det : ℂ) ^ N *
        ∏ σ : E →+* ℂ, (W.map σ * (W.map σ)ᴴ).det := by
  set A : Matrix (E →+* ℂ) (E →+* ℂ) ℂ := Matrix.of fun k σ : E →+* ℂ => σ (ω k) with hA
  set P : Matrix (Fin N × (E →+* ℂ)) (Fin N × (E →+* ℂ)) ℂ :=
    kroneckerMap (· * ·) (1 : Matrix (Fin N) (Fin N) ℂ) A with hP
  have hdP : P.det = A.det ^ N := by simp [hP, det_kronecker]
  have key : (gram ℝ fun p : Fin N × (E →+* ℂ) => rowEmb W (Pi.single p.1 (ω p.2))).map ofRealHom
      = (P * blockDiagonal (fun σ : E →+* ℂ => W.map σ * (W.map σ)ᴴ) * Pᴴ)ᵀ := by
    ext ⟨i, k⟩ ⟨i', k'⟩
    have hR : (P * blockDiagonal (fun σ : E →+* ℂ => W.map σ * (W.map σ)ᴴ) * Pᴴ)ᵀ (i, k) (i', k')
        = ∑ σ : E →+* ℂ, ∑ j, σ (ω k' * W i' j) * conj (σ (ω k * W i j)) := by
      simp only [transpose_apply, Matrix.mul_apply, Fintype.sum_prod_type, hP, hA, kroneckerMap_apply,
        Matrix.one_apply, blockDiagonal_apply, conjTranspose_apply, of_apply, map_apply]
      simp [Finset.mul_sum, Finset.sum_mul, apply_ite]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [hR]
    have hreal : conj (∑ σ : E →+* ℂ, ∑ j, σ (ω k' * W i' j) * conj (σ (ω k * W i j))) =
        ∑ σ : E →+* ℂ, ∑ j, σ (ω k' * W i' j) * conj (σ (ω k * W i j)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Fintype.sum_equiv (Function.Involutive.toPerm _
        (ComplexEmbedding.involutive_conjugate E)) _ _ fun σ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum]
    rw [← conj_eq_iff_re.1 hreal]
    simp [gram_apply, PiLp.inner_apply, Fintype.sum_prod_type, Complex.inner, rowEmb]
  rw [← ofRealHom_eq_coe, RingHom.map_det, RingHom.mapMatrix_apply, key, det_transpose, det_mul,
    det_mul, det_conjTranspose, hdP, det_blockDiagonal, normSq_eq_conj_mul_self]
  simp only [star_pow, RCLike.star_def]
  ring

theorem IsType.prod_det_eq_sq {E m n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype m]
    [Fintype n] [DecidableEq n] {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (W : Matrix n m E) :
    ∏ σ : E →+* ℂ, (W.map σ * (W.map σ)ᴴ).det =
      (((∏ τ : Ψ, (W.map τ.1 * (W.map τ.1)ᴴ).det.re) ^ 2 : ℝ) : ℂ) := by
  rw [hΨ.prod_univ, ← Finset.prod_pow, ofReal_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 : W.map (ComplexEmbedding.conjugate τ.1) * (W.map (ComplexEmbedding.conjugate τ.1))ᴴ =
      (W.map τ.1 * (W.map τ.1)ᴴ)ᵀ := by
    ext i j
    simp [Matrix.mul_apply, mul_comm]
  have h2 : (((W.map τ.1 * (W.map τ.1)ᴴ).det.re : ℝ) : ℂ) = (W.map τ.1 * (W.map τ.1)ᴴ).det :=
    conj_eq_iff_re.1 (by
      rw [← RCLike.star_def, ← det_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose])
  rw [h1, det_transpose, ofReal_pow, h2, sq]

theorem exists_short_independent_rows :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ →
      ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (m : Type) [Fintype m] (W : Matrix (Fin N) m E),
        LinearIndependent E (fun i => W i) → ∃ a : Matrix (Fin N) (Fin N) E, IntM a ∧ a.det ≠ 0 ∧
          ∏ i, (∑ τ : Ψ, ∑ j, ‖τ.1 ((a * W) i j)‖ ^ 2) ^ Ψ.card ≤
            C * ∏ τ : Ψ, (W.map τ.1 * (W.map τ.1)ᴴ).det.re := by
  classical
  intro E _ _ _ Ψ hΨ N
  set ω : (E →+* ℂ) → E := fun k => integralBasis E (equivReindex E k) with hω
  have hωi : ∀ k, IsIntegral ℤ (ω k) := fun k => by
    rw [hω]; simp only [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _
  set A : Matrix (E →+* ℂ) (E →+* ℂ) ℂ := Matrix.of fun k σ : E →+* ℂ => σ (ω k) with hA
  have hA0 : A.det ≠ 0 := by
    have : A = basisMatrix E := by
      ext k σ
      simp only [hA, hω, basisMatrix, of_apply, canonicalEmbedding.latticeBasis_apply,
        canonicalEmbedding.apply_at]
    rw [this]; exact det_of_basisMatrix_non_zero E
  set n : ℕ := Fintype.card (Fin N × (E →+* ℂ)) with hn
  have hc : 0 < (n : ℝ) ^ ((n : ℝ) / 2) := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · positivity
  have hA1 : 0 < ‖A.det‖ := norm_pos_iff.2 hA0
  refine ⟨(n : ℝ) ^ ((n : ℝ) / 2) * ‖A.det‖ ^ N, by positivity, fun m _ W hW => ?_⟩
  have hpos : 0 < ∏ τ : Ψ, (W.map τ.1 * (W.map τ.1)ᴴ).det.re :=
    Finset.prod_pos fun τ _ => (Complex.pos_iff.1 (posDef_map_mul_conjTranspose hW τ.1).det_pos).1
  have hdet : (gram ℝ fun p : Fin N × (E →+* ℂ) => rowEmb W (Pi.single p.1 (ω p.2))).det =
      (‖A.det‖ ^ N * ∏ τ : Ψ, (W.map τ.1 * (W.map τ.1)ᴴ).det.re) ^ 2 := by
    have h := det_gram_rowEmb W ω
    rw [hΨ.prod_det_eq_sq, normSq_eq_norm_sq] at h
    rw [mul_pow, ← pow_mul, mul_comm N, pow_mul]
    exact_mod_cast h
  obtain ⟨a, ha, hai, hle⟩ := exists_linearIndependent_prod_norm_le (E := E) (N := N)
    (by rw [Fintype.card_prod, Fintype.card_fin, Embeddings.card, mul_comm]) (rowEmb W) (fun p : Fin N × (E →+* ℂ) => Pi.single p.1 (ω p.2))
    (det_gram_ne_zero_iff_linearIndependent.1 (by rw [hdet]; positivity))
  refine ⟨Matrix.of a, fun i => ?_, ?_, ?_⟩
  · show ∀ j, IsIntegral ℤ (a i j)
    refine Submodule.span_induction (p := fun t _ => ∀ j, IsIntegral ℤ (t j)) ?_ ?_ ?_ ?_ (hai i)
    · rintro _ ⟨p, rfl⟩ j
      simp only [Pi.single_apply]
      split_ifs
      · exact hωi _
      · exact isIntegral_zero
    · exact fun _ => isIntegral_zero
    · exact fun x y _ _ hx hy j => (hx j).add (hy j)
    · exact fun c x _ hx j => (hx j).smul c
  · exact ((Matrix.isUnit_iff_isUnit_det _).1
      (linearIndependent_row_iff_isUnit.1 (show LinearIndependent E (Matrix.of a).row from ha))).ne_zero
  · rw [hdet, Real.sqrt_sq (by positivity), ← mul_assoc, hΨ.finrank_eq] at hle
    refine le_trans (Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i _ => ?_) hle
    rw [pow_mul, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [Finset.sum_coe_sort Ψ (fun τ => ∑ j, ‖τ ((Matrix.of a * W) i j)‖ ^ 2)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Ψ)
      (f := fun τ => ∑ j, ‖τ ((Matrix.of a * W) i j)‖ ^ 2) fun _ _ _ => by positivity

end GlobalTheory.SW
end
