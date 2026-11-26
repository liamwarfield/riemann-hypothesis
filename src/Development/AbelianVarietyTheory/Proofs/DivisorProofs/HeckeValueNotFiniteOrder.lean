module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameFamilyCompactRepresentation
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Product
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPToLiftReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCentralizerComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeValueNotFiniteOrder
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeValueNotFiniteOrder
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.CMSplitValue

open WithZero GlobalTheory.CharVal GlobalTheory.Formalism.L2.Col.HostOk

theorem exists_aut_comp {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] (τ₀ τ₁ : E →+* ℂ) :
    ∃ g : E ≃ₐ[ℚ] E, ∀ x, τ₀ (g x) = τ₁ x := by
  letI : Algebra E ℂ := τ₀.toAlgebra
  haveI : IsScalarTower ℚ E ℂ := IsScalarTower.of_algebraMap_eq fun q => by
    show algebraMap ℚ ℂ q = τ₀ (algebraMap ℚ E q)
    rw [eq_ratCast (algebraMap ℚ ℂ), eq_ratCast (algebraMap ℚ E), map_ratCast]
  exact ⟨(τ₁.toRatAlgHom).restrictNormal' E, fun x => (τ₁.toRatAlgHom).restrictNormal_commutes E x⟩

theorem not_isOfFinOrder_val_of_tame (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (hgal : IsGalois ℚ E) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (χ : Formalism.L2.Host.HChar E) (n : InfinitePlace F → ℤ) (ht : ∀ v, χ.TameAt v) (hinf : χ.HasInf (fun w => (τ w).1) n)
    (hn : ∀ w, n w ≠ 0) (p : ℕ) (hp : p.Prime) (W : HeightOneSpectrum (𝓞 E)) (hN : Ideal.absNorm W.asIdeal = p)
    (hsq : (p : 𝓞 E) ∉ W.asIdeal ^ 2) : ¬ IsOfFinOrder (χ.val W) := by
  intro hfin
  classical
  obtain ⟨M, z, hM, h1, h2, h3⟩ := GlobalTheory.TamePow.exists_pow_locK_mul_inf E χ
    (GlobalTheory.Mem.UnrAe.unr_ae_and_level _ χ).1.toFinset (GlobalTheory.HeckeProduct.hchar_productRule _ χ)
    (fun v hv => by simpa using hv) ht W (Formalism.L2.Host.unif W)
  obtain ⟨a, ha, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  have h4 : χ.inf z ^ a = 1 := by
    have := congrArg (· ^ a) h3
    simp only [mul_pow, one_pow] at this
    rw [← pow_mul, mul_comm M a, pow_mul] at this
    change χ.val W ^ a = 1 at hpow
    unfold Formalism.L2.Host.HChar.val at hpow
    rwa [hpow, one_pow, one_mul] at this
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  set τ₀ : E →+* ℂ := (τ w₀).1 with hτ₀
  choose g hg using fun w => exists_aut_comp τ₀ (τ w).1
  have h5 : ((χ.inf z : ℂˣ) : ℂ) ^ 2 = τ₀ (∏ w, (g w z / g w (σ z)) ^ n w) := by
    rw [hinf z, map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [map_zpow₀, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    congr 1
    have e : τ₀ (g w (σ z)) = starRingEnd ℂ (τ₀ (g w z)) := by
      rw [hg, hg]
      exact hcm.2.2.2 _ _
    have e' : (τ w).1 z = τ₀ (g w z) := (hg w z).symm
    have h0 : τ₀ (g w z) ≠ 0 := by simp
    rw [map_div₀, e, e', div_pow, div_eq_div_iff (pow_ne_zero _ (by simpa using h0)) (by simpa using h0), sq, mul_assoc,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have h6 : (∏ w, (g w z / g w (σ z)) ^ n w) ^ a = 1 := by
    apply τ₀.injective
    rw [map_pow, ← h5, ← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, h4, map_one]
    simp
  have h7 := unit_of_pow (w := W) ha (by rw [h6, map_one])
  have hg0 : ∀ x, g w₀ x = x := fun x => τ₀.injective (hg w₀ x)
  have hres : ∀ w, (∀ f : F, τ₀ (algebraMap F E f) = w.embedding f) → w = w₀ := by
    intro w hw
    have e : w.embedding = w₀.embedding := by
      ext f
      rw [← hw f]
      exact (RingHom.congr_fun (τ w₀).2 f)
    rw [← InfinitePlace.mk_embedding w, e, InfinitePlace.mk_embedding]
  have hc : ∀ w, W.valuation E (g w (σ z)) = 1 := by
    intro w
    refine GlobalTheory.SplitValue.val_map_eq_one hp hN hsq h2 ((g w : E →+* E).comp (σ : E →+* E)) fun e => ?_
    have hw : w = w₀ := hres w fun f => by
      have := RingHom.congr_fun e (algebraMap F E f)
      change g w (σ (algebraMap F E f)) = algebraMap F E f at this
      rw [← this, hg, AlgHom.commutes]
      exact RingHom.congr_fun (τ w).2 f
    subst hw
    obtain ⟨x, hx⟩ := GlobalTheory.AdelicU.exists_cm_conj_ne hcm
    have := RingHom.congr_fun e x
    change g w (σ x) = x at this
    rw [hg0] at this
    exact hx this
  have hgw : ∀ w, w ≠ w₀ → W.valuation E (g w z) = 1 := by
    intro w hw
    refine GlobalTheory.SplitValue.val_map_eq_one hp hN hsq h2 (g w : E →+* E) fun e => hw (hres w fun f => ?_)
    have := RingHom.congr_fun e (algebraMap F E f)
    change g w (algebraMap F E f) = algebraMap F E f at this
    rw [← this, hg]
    exact RingHom.congr_fun (τ w).2 f
  rw [map_prod, Finset.prod_eq_single w₀ (fun w _ h => by rw [map_zpow₀, map_div₀, hgw w h, hc w, div_one, one_zpow])
    (by simp), map_zpow₀, map_div₀, hc, div_one, hg0, h1, val_unif, ← exp_nsmul, ← exp_zsmul,
    ← exp_zero, exp_inj] at h7
  simp only [nsmul_eq_mul, smul_eq_mul, mul_eq_zero] at h7
  rcases h7 with h | h | h
  · exact hn w₀ h
  · omega
  · omega

end GlobalTheory.CMSplitValue

namespace GlobalTheory.CMSplitValue

theorem not_isOfFinOrder_val : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → IsGalois ℚ E → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (H : Formalism.L2.Host.HChar E) (n : InfinitePlace F → ℤ), H.HasInf (fun w => (τ w).1) n → (∀ w, n w ≠ 0) → ∀ (p : ℕ), p.Prime → ∀ W : HeightOneSpectrum (𝓞 E), Ideal.absNorm W.asIdeal = p → (p : 𝓞 E) ∉ W.asIdeal ^ 2 → ¬ IsOfFinOrder (H.val W) := by
  intro F E _ _ _ _ _ σ hcm hgal τ H n hinf hn p hp W hN hsq hfin
  obtain ⟨N, hN0, hunr⟩ := GlobalTheory.Corev.UnrPow.exists_pow_unrAt E H
  have ht : ∀ v, (H ^ N).TameAt v := fun v x hx _ => hunr v x hx
  have hinf' : (H ^ N).HasInf (fun w => (τ w).1) (fun w => (N : ℤ) * n w) := by
    intro k
    rw [GlobalTheory.SplitValuePow.inf_pow, Units.val_pow_eq_pow_val, hinf k, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  refine not_isOfFinOrder_val_of_tame F E σ hcm hgal τ (H ^ N) _ ht hinf'
    (fun w => mul_ne_zero (by exact_mod_cast hN0.ne') (hn w)) p hp W hN hsq ?_
  rw [GlobalTheory.SplitValuePow.val_pow]
  exact hfin.pow

end GlobalTheory.CMSplitValue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeValueNotFiniteOrderStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_value_not_finite_order : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → IsGalois ℚ E → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (H : Formalism.L2.Host.HChar E) (n : InfinitePlace F → ℤ), H.HasInf (fun w => (τ w).1) n → (∀ w, n w ≠ 0) → ∀ (p : ℕ), p.Prime → ∀ W : HeightOneSpectrum (𝓞 E), Ideal.absNorm W.asIdeal = p → (p : 𝓞 E) ∉ W.asIdeal ^ 2 → ¬ IsOfFinOrder (H.val W) := by
  first | exact @GlobalTheory.CMSplitValue.not_isOfFinOrder_val | exact GlobalTheory.CMSplitValue.not_isOfFinOrder_val | (intros; apply GlobalTheory.CMSplitValue.not_isOfFinOrder_val <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SylvesterInertiaInvariance
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HopfOrderScalarExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeCardOfVanish
open NumberField Matrix

namespace GlobalTheory.SylvesterInertia

theorem re_quad_eq_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) (u : Fin n → ℂ) :
    (star u ⬝ᵥ M *ᵥ u).re = ∑ i, hM.eigenvalues i * Complex.normSq
      ((star (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ u) i) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hD : star U * M * U = diagonal (RCLike.ofReal ∘ hM.eigenvalues) := by
    have := hM.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, hU] using this
  set y := star U *ᵥ u with hy
  have hu : u = U *ᵥ y := by
    rw [hy, mulVec_mulVec, hU, Matrix.mem_unitaryGroup_iff.mp hM.eigenvectorUnitary.2, one_mulVec]
  have h1 : star u ⬝ᵥ M *ᵥ u = star y ⬝ᵥ (star U * M * U) *ᵥ y := by
    conv_lhs => rw [hu]
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, star_eq_conjTranspose, Matrix.mul_assoc]
  rw [h1, hD, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal]
  simp only [Pi.star_apply, Function.comp_apply, Complex.star_def, Complex.normSq_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
  have e1 : ((RCLike.ofReal (hM.eigenvalues i) : ℂ)).re = hM.eigenvalues i := by simp
  have e2 : ((RCLike.ofReal (hM.eigenvalues i) : ℂ)).im = 0 := by simp
  simp only [e1, e2]
  ring

theorem finrank_le_card_of_vanish {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (P : Submodule ℂ (Fin n → ℂ))
    (s : Fin n → Prop) [DecidablePred s]
    (h : ∀ u ∈ P, (∀ i, s i → (U *ᵥ u) i = 0) → u = 0) :
    Module.finrank ℂ P ≤ Fintype.card {i // s i} := by
  let f : P →ₗ[ℂ] ({i // s i} → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Subtype.val : {i // s i} → Fin n)) ∘ₗ (Matrix.mulVecLin U) ∘ₗ P.subtype
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have := h u u.2 (fun i hi => by
      have := congrFun hu ⟨i, hi⟩
      simpa [f, LinearMap.funLeft_apply] using this)
    exact Subtype.ext this
  have := LinearMap.finrank_le_finrank_of_injective hf
  simpa using this

end GlobalTheory.SylvesterInertia
end

open NumberField GlobalTheory.LKTrip
open scoped TensorProduct Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SimSign

open Matrix

variable {n : ℕ}

def extZero (s : Fin n → Prop) [DecidablePred s] : ({i // s i} → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun w i := if hi : s i then w ⟨i, hi⟩ else 0
  map_add' a b := by funext i; by_cases hi : s i <;> simp [hi]
  map_smul' r a := by funext i; by_cases hi : s i <;> simp [hi]

theorem extZero_apply_mem (s : Fin n → Prop) [DecidablePred s] (w : {i // s i} → ℂ) (i : {i // s i}) :
    extZero s w i = w i := by simp [extZero, i.2]

theorem extZero_apply_not (s : Fin n → Prop) [DecidablePred s] (w : {i // s i} → ℂ) {i : Fin n} (hi : ¬ s i) :
    extZero s w i = 0 := by simp [extZero, hi]

theorem quad_mulVec (h X : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    star (X *ᵥ u) ⬝ᵥ h *ᵥ (X *ᵥ u) = star u ⬝ᵥ (Xᴴ * h * X) *ᵥ u := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

theorem re_quad_ext (h : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (s : Fin n → Prop) [DecidablePred s]
    (w : {i // s i} → ℂ) :
    (star ((hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ extZero s w) ⬝ᵥ
        h *ᵥ ((hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ extZero s w)).re =
      ∑ i, hh.eigenvalues i * Complex.normSq (extZero s w i) := by
  rw [GlobalTheory.SylvesterInertia.re_quad_eq_sum h hh, Matrix.mulVec_mulVec,
    Matrix.mem_unitaryGroup_iff'.mp hh.eigenvectorUnitary.2, Matrix.one_mulVec]

theorem finrank_le_pos (h : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (S : Submodule ℂ (Fin n → ℂ))
    (hS : ∀ u ∈ S, u ≠ 0 → 0 < (star u ⬝ᵥ h *ᵥ u).re) :
    Module.finrank ℂ S ≤ Fintype.card {i : Fin n // 0 < hh.eigenvalues i} := by
  refine GlobalTheory.SylvesterInertia.finrank_le_card_of_vanish
    (star (hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) S _ fun u hu hv => ?_
  by_contra hne
  have hpos := hS u hu hne
  rw [GlobalTheory.SylvesterInertia.re_quad_eq_sum h hh u] at hpos
  refine absurd hpos (not_lt.mpr (Finset.sum_nonpos fun i _ => ?_))
  by_cases hi : 0 < hh.eigenvalues i
  · rw [hv i hi, map_zero, mul_zero]
  · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hi) (Complex.normSq_nonneg _)

end GlobalTheory.SimSign

namespace GlobalTheory.SimSign

open Matrix

variable {n : ℕ}

theorem sum_pos (h : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (w : {i // 0 < hh.eigenvalues i} → ℂ)
    (hw : w ≠ 0) : 0 < ∑ i, hh.eigenvalues i * Complex.normSq (extZero (fun i => 0 < hh.eigenvalues i) w i) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (0 : Fin n → ℝ) i ≤ hh.eigenvalues i * Complex.normSq (extZero (fun i => 0 < hh.eigenvalues i) w i) := by
    intro i _
    by_cases hi : 0 < hh.eigenvalues i
    · exact mul_nonneg hi.le (Complex.normSq_nonneg _)
    · rw [extZero_apply_not _ w hi]; simp
  have hlt : ∃ i ∈ (Finset.univ : Finset (Fin n)),
      (0 : Fin n → ℝ) i < hh.eigenvalues i * Complex.normSq (extZero (fun i => 0 < hh.eigenvalues i) w i) := by
    refine ⟨j.1, Finset.mem_univ _, ?_⟩
    rw [extZero_apply_mem]
    exact mul_pos j.2 (Complex.normSq_pos.mpr hj)
  simpa using Finset.sum_lt_sum hle hlt

end GlobalTheory.SimSign

namespace GlobalTheory.HTBetti

end GlobalTheory.HTBetti

end
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.SigCong

theorem card_pos_le_of_conj {n : ℕ} (A B X : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hX : Xᴴ * A * X = B) :
    Fintype.card {i : Fin n // 0 < hB.eigenvalues i} ≤ Fintype.card {i : Fin n // 0 < hA.eigenvalues i} := by
  set φ : ({i // 0 < hB.eigenvalues i} → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    Matrix.mulVecLin X ∘ₗ Matrix.mulVecLin (hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) ∘ₗ
      GlobalTheory.SimSign.extZero (fun i => 0 < hB.eigenvalues i) with hφ
  have hq : ∀ w, w ≠ 0 → 0 < (star (φ w) ⬝ᵥ A *ᵥ φ w).re := fun w hw => by
    simp only [hφ, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply]
    rw [GlobalTheory.SimSign.quad_mulVec, hX, GlobalTheory.SimSign.re_quad_ext]
    exact GlobalTheory.SimSign.sum_pos B hB w hw
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    have := hq w hne
    rw [hw] at this
    simp at this
  have hS : ∀ u ∈ LinearMap.range φ, u ≠ 0 → 0 < (star u ⬝ᵥ A *ᵥ u).re := by
    rintro u ⟨w, rfl⟩ hu
    exact hq w (fun h0 => hu (by rw [h0, map_zero]))
  have h1 := GlobalTheory.SimSign.finrank_le_pos A hA _ hS
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card] at h1
  exact h1

theorem sigPosH_congr : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian), A.det ≠ 0 →
    ∀ (Z : GL (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.IsHermitian),
      B = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (Z : Matrix (Fin n) (Fin n) ℂ) → sigPosH hB = sigPosH hA := by
  intro n A hA _ Z B hB hBZ
  unfold sigPosH
  refine le_antisymm (card_pos_le_of_conj A B _ hA hB hBZ.symm)
    (card_pos_le_of_conj B A ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) hB hA ?_)
  have h1 : (Z : Matrix (Fin n) (Fin n) ℂ) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Units.mul_inv Z
  rw [hBZ]
  calc (((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᴴ * ((Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * A *
        (Z : Matrix (Fin n) (Fin n) ℂ)) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      = ((Z : Matrix (Fin n) (Fin n) ℂ) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᴴ * A *
        ((Z : Matrix (Fin n) (Fin n) ℂ) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = A := by rw [h1]; simp

end GlobalTheory.SigCong
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeFactorFormGroupBoundedOfTestSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeFactorFormGroupBoundedOfTestSupport
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
namespace GlobalTheory.SimBound

theorem eq_one_of_forall_prime {r : ℚ} (hr : 0 < r)
    (h : ∀ q : ℕ, q.Prime → ¬ (q : ℤ) ∣ r.num ∧ ¬ (q : ℤ) ∣ (r.den : ℤ)) : r = 1 := by
  have hn : r.num.natAbs = 1 := by
    by_contra hne
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
    exact (h q hq).1 (Int.natCast_dvd.2 hqd)
  have hd : r.den = 1 := by
    by_contra hne
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
    exact (h q hq).2 (Int.natCast_dvd_natCast.2 hqd)
  have hpos : 0 < r.num := Rat.num_pos.2 hr
  have hn1 : r.num = 1 := by omega
  rw [← Rat.num_div_den r, hn1, hd]; simp

theorem not_dvd_of_iff {r : ℚ} {q : ℕ} (hq : q.Prime) (h : (q : ℤ) ∣ r.num ↔ (q : ℤ) ∣ (r.den : ℤ)) :
    ¬ (q : ℤ) ∣ r.num ∧ ¬ (q : ℤ) ∣ (r.den : ℤ) := by
  have key : ¬ ((q : ℤ) ∣ r.num ∧ (q : ℤ) ∣ (r.den : ℤ)) := by
    rintro ⟨h1, h2⟩
    have h1' : q ∣ r.num.natAbs := Int.natCast_dvd.1 h1
    have h2' : q ∣ r.den := Int.natCast_dvd_natCast.1 h2
    have h3 : q ∣ Nat.gcd r.num.natAbs r.den := Nat.dvd_gcd h1' h2'
    rw [r.reduced.gcd_eq_one] at h3
    exact hq.one_lt.ne' (Nat.dvd_one.1 h3)
  exact ⟨fun h1 => key ⟨h1, h.1 h1⟩, fun h2 => key ⟨h.2 h2, h2⟩⟩

theorem not_dvd_of_padicNorm (p : ℕ) [Fact p.Prime] {r : ℚ} (hr : padicNorm p r = 1) :
    ¬ (p : ℤ) ∣ r.num ∧ ¬ (p : ℤ) ∣ (r.den : ℤ) := by
  have e : padicNorm p (r.num : ℚ) = padicNorm p ((r.den : ℤ) : ℚ) := by
    rw [← Rat.mul_den_eq_num, padicNorm.mul, hr, one_mul, Int.cast_natCast]
  refine not_dvd_of_iff (Fact.out : p.Prime) ?_
  rw [← padicNorm.int_lt_one_iff, ← padicNorm.int_lt_one_iff, e]

theorem not_dvd_of_valuation {q : ℕ} (hq : q.Prime) (v : HeightOneSpectrum ℤ)
    (hv : v.asIdeal = Ideal.span {(q : ℤ)}) {r : ℚ} (hr : v.valuation ℚ r = 1) :
    ¬ (q : ℤ) ∣ r.num ∧ ¬ (q : ℤ) ∣ (r.den : ℤ) := by
  have e : v.valuation ℚ (algebraMap ℤ ℚ r.num) = v.valuation ℚ (algebraMap ℤ ℚ (r.den : ℤ)) := by
    rw [algebraMap_int_eq, eq_intCast, eq_intCast, ← Rat.mul_den_eq_num, map_mul, hr, one_mul,
      Int.cast_natCast]
  refine not_dvd_of_iff hq ?_
  rw [← Ideal.mem_span_singleton, ← Ideal.mem_span_singleton, ← hv, ← valuation_lt_one_iff_mem (K := ℚ),
    ← valuation_lt_one_iff_mem (K := ℚ), e]

def placeOf (p : ℕ) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) : AwayP p :=
  ⟨⟨Ideal.span {(q : ℤ)}, (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).2
      (Nat.prime_iff_prime_int.1 hq), by simpa using hq.ne_zero⟩, fun h => hqp (by
    have h1 := Ideal.span_singleton_eq_span_singleton.1 h
    have h2 := Int.natAbs_eq_natAbs_iff.2 (Int.associated_iff.1 h1)
    simpa using h2)⟩

theorem eq_one_of_units (p : ℕ) [Fact p.Prime] {r : ℚ} (hr : 0 < r)
    (hw : ∀ w : AwayP p, Valued.v (algebraMap ℚ (w.1.adicCompletion ℚ) r) = 1) (hp : padicNorm p r = 1) :
    r = 1 := by
  refine eq_one_of_forall_prime hr fun q hq => ?_
  by_cases hqp : q = p
  · subst hqp; exact not_dvd_of_padicNorm q hp
  · refine not_dvd_of_valuation hq (placeOf p hq hqp).1 rfl ?_
    rw [← valuedAdicCompletion_eq_valuation']
    exact hw (placeOf p hq hqp)

theorem valued_snd_eq_one {p : ℕ} [Fact p.Prime] (G : HTGroup p) (K : Subgroup G.GAf)
    (hK : IsCompact (K : Set G.GAf)) (w : AwayP p) {k : G.GAf} (hk : k ∈ K) :
    Valued.v (AfP.eval w (((k : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p)) = 1 := by
  letI : NontriviallyNormedField (w.1.adicCompletion ℚ) := Valued.toNontriviallyNormedField _ _
  let F : G.GAf → ℝ := fun g => ‖AfP.eval w (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p)‖
  have hev : Continuous (fun x : AfP p => AfP.eval w x) :=
    RestrictedProduct.continuous_eval (R := fun v : AwayP p => v.1.adicCompletion ℚ)
      (A := fun v : AwayP p => (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) w
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  have hF : Continuous F :=
    continuous_norm.comp (hev.comp (Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  have hmul : ∀ a b : G.GAf, F (a * b) = F a * F b := fun a b => by
    simp only [F, Subgroup.coe_mul, Prod.snd_mul, Units.val_mul, map_mul, norm_mul]
  have hone : F 1 = 1 := by simp [F]
  have hpow : ∀ (a : G.GAf) (n : ℕ), F (a ^ n) = F a ^ n := fun a n => by
    induction n with
    | zero => simpa using hone
    | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
  have hle : ∀ a ∈ K, F a ≤ 1 := by
    intro a ha
    by_contra hlt
    push_neg at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hlt
    have h1 := hC (a ^ n) (K.pow_mem ha n)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h1
    have : F (a ^ n) = F a ^ n := hpow a n
    linarith
  have h1 := hle k hk
  have h2 := hle k⁻¹ (K.inv_mem hk)
  have h3 : F k⁻¹ * F k = 1 := by rw [← hmul, inv_mul_cancel, hone]
  have h0 : 0 ≤ F k⁻¹ := norm_nonneg _
  have h0' : 0 ≤ F k := norm_nonneg _
  have hk1 : F k = 1 := by nlinarith
  have hle1 : Valued.v (AfP.eval w (((k : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p)) ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.1 hk1.le
  have hnlt : ¬ Valued.v (AfP.eval w (((k : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p)) < 1 :=
    fun h => by
      have := Valued.toNormedField.norm_lt_one_iff.2 h
      exact absurd hk1 (ne_of_lt this)
  exact le_antisymm hle1 (not_lt.1 hnlt)

noncomputable def nu1 (p : ℕ) [Fact p.Prime] (g : GL (Fin 1) (Qr p 1)) : ℝ :=
  ‖(((g : Matrix (Fin 1) (Fin 1) (Qr p 1)) 0 0 : Qr p 1) : PadicAlgCl p)‖

theorem glOneUnramifiedEntryNorm_mul (p : ℕ) [Fact p.Prime] (a b : GL (Fin 1) (Qr p 1)) : nu1 p (a * b) = nu1 p a * nu1 p b := by
  simp only [nu1, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_one, IntermediateField.coe_mul, norm_mul]

theorem glOneUnramifiedEntryNorm_one (p : ℕ) [Fact p.Prime] : nu1 p 1 = 1 := by simp [nu1]

theorem glOneUnramifiedEntryNorm_le_one_of_integral (p : ℕ) [Fact p.Prime] {k : GL (Fin 1) (Qr p 1)} (hk : k ∈ GlobalTheory.LKLoc.Kint p (Q0 p) 1 1) :
    nu1 p k ≤ 1 := by
  obtain ⟨u, rfl⟩ := hk
  have h := ((u : Matrix (Fin 1) (Fin 1) (GlobalTheory.LKLoc.intR p (Q0 p) 1)) 0 0).2
  exact ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff.1 h

theorem glOneUnramifiedEntryNorm_eq_one_of_integral (p : ℕ) [Fact p.Prime] {k : GL (Fin 1) (Qr p 1)}
    (hk : k ∈ GlobalTheory.LKLoc.Kint p (Q0 p) 1 1) : nu1 p k = 1 := by
  have h1 := glOneUnramifiedEntryNorm_le_one_of_integral p hk
  have h2 := glOneUnramifiedEntryNorm_le_one_of_integral p ((GlobalTheory.LKLoc.Kint p (Q0 p) 1 1).inv_mem hk)
  have h3 : nu1 p k⁻¹ * nu1 p k = 1 := by rw [← glOneUnramifiedEntryNorm_mul, inv_mul_cancel, glOneUnramifiedEntryNorm_one]
  have h0 : 0 ≤ nu1 p k⁻¹ := norm_nonneg _
  have h0' : 0 ≤ nu1 p k := norm_nonneg _
  nlinarith

theorem glOneUnramifiedEntryNorm_rat_scalar_eq_padicNorm (p : ℕ) [Fact p.Prime] (s : ℚˣ) :
    nu1 p (GeneralLinearGroup.scalar (Fin 1) (Units.map (algebraMap ℚ_[p] (Qr p 1)).toMonoidHom
      (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom s))) = ((padicNorm p (s : ℚ) : ℚ) : ℝ) := by
  have e : nu1 p (GeneralLinearGroup.scalar (Fin 1) (Units.map (algebraMap ℚ_[p] (Qr p 1)).toMonoidHom
      (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom s))) = ‖(((s : ℚ) : ℚ_[p]) : PadicAlgCl p)‖ := by
    simp [nu1, GeneralLinearGroup.scalar]
  rw [e, PadicAlgCl.norm_extends, Padic.eq_padicNorm]

noncomputable def lam {p : ℕ} [Fact p.Prime] (G : HTGroup p) (w : AwayP p) (g : G.GAf) : WithZero (Multiplicative ℤ) :=
  Valued.v (AfP.eval w (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p))

theorem lam_mul {p : ℕ} [Fact p.Prime] (G : HTGroup p) (w : AwayP p) (a b : G.GAf) :
    lam G w (a * b) = lam G w a * lam G w b := by
  simp only [lam, Subgroup.coe_mul, Prod.snd_mul, Units.val_mul, map_mul]

theorem lam_one {p : ℕ} [Fact p.Prime] (G : HTGroup p) (w : AwayP p) : lam G w 1 = 1 := by
  simp [lam]

theorem away {p : ℕ} [Fact p.Prime] (G : HTGroup p) (L : G.Level) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ)
    (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y : grp G β) (h σ k₁ k₂ : G.GAf) (hk₁ : k₁ ∈ L.K.toSubgroup)
    (hk₂ : k₂ ∈ L.K.toSubgroup) (e : h⁻¹ * toAfF G β x t hx y * h = k₁ * σ * k₂) (w : AwayP p) :
    Valued.v (algebraMap ℚ (w.1.adicCompletion ℚ) (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)) = lam G w σ := by
  have hc : IsCompact (L.K.toSubgroup : Set G.GAf) := L.compact
  have e1 : lam G w k₁ = 1 := valued_snd_eq_one G _ hc w hk₁
  have e2 : lam G w k₂ = 1 := valued_snd_eq_one G _ hc w hk₂
  have e3 := congrArg (lam G w) e
  rw [lam_mul, lam_mul, lam_mul, lam_mul, e1, e2, one_mul, mul_one] at e3
  have e4 : lam G w (toAfF G β x t hx y) = lam G w σ := by
    rw [← e3, mul_right_comm, ← lam_mul, inv_mul_cancel, lam_one, one_mul]
  rw [← e4]
  show _ = Valued.v (AfP.eval w (algebraMap ℚ (AfP p) (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)))
  rw [AlgHom.commutes]

theorem atp {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (y : grp G β) (h σ k₁ k₂ : Gr G 1)
    (hk₁ : k₁ ∈ KHT p G.m G.n 1 G.Fw) (hk₂ : k₂ ∈ KHT p G.m G.n 1 G.Fw)
    (e : h⁻¹ * toP1 G β y * h = k₁ * σ * k₂) :
    ((padicNorm p (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℚ) : ℝ) = nu1 p σ.1 := by
  have e1 : nu1 p k₁.1 = 1 := glOneUnramifiedEntryNorm_eq_one_of_integral p hk₁.1
  have e2 : nu1 p k₂.1 = 1 := glOneUnramifiedEntryNorm_eq_one_of_integral p hk₂.1
  have e3 := congrArg (fun g : Gr G 1 => nu1 p g.1) e
  simp only [Prod.fst_mul, Prod.fst_inv, glOneUnramifiedEntryNorm_mul, e1, e2, one_mul, mul_one] at e3
  have e4 : nu1 p (toP1 G β y).1 = nu1 p σ.1 := by
    rw [← e3, mul_right_comm, ← glOneUnramifiedEntryNorm_mul, inv_mul_cancel, glOneUnramifiedEntryNorm_one, one_mul]
  rw [← e4]
  exact (glOneUnramifiedEntryNorm_rat_scalar_eq_padicNorm p _).symm

theorem eq_of_valuations {p : ℕ} [Fact p.Prime] {s s₀ : ℚ} (hs : 0 < s) (hs₀ : 0 < s₀)
    (hw : ∀ w : AwayP p, Valued.v (algebraMap ℚ (w.1.adicCompletion ℚ) s) =
      Valued.v (algebraMap ℚ (w.1.adicCompletion ℚ) s₀))
    (hp : padicNorm p s = padicNorm p s₀) : s = s₀ := by
  have h := eq_one_of_units p (r := s * s₀⁻¹) (mul_pos hs (inv_pos.2 hs₀)) (fun w => by
      have h0 : Valued.v (algebraMap ℚ (w.1.adicCompletion ℚ) s₀) ≠ 0 :=
        (Valuation.ne_zero_iff _).2 ((map_ne_zero _).2 hs₀.ne')
      rw [map_mul, map_mul, map_inv₀, map_inv₀, hw w, mul_inv_cancel₀ h0])
    (by
      have h0 : padicNorm p s₀ ≠ 0 := fun h => hs₀.ne' (padicNorm.zero_of_padicNorm_eq_zero h)
      rw [← div_eq_mul_inv, padicNorm.div, hp, div_self h0])
  exact (mul_inv_eq_one₀ hs₀.ne').1 h

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
    IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t), ∃ S : ℝ, ∀ (y : grp G β) (h₁ : G.GAf) (h₂ : Gr G 1),
      f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → f' (h₂⁻¹ * toP1 G β y * h₂) ≠ 0 →
      (((y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) ≤ S := by
  intro p _ G L f hf K' f' hf' β x t hx
  obtain ⟨T, hT⟩ := hf.2.2.2
  obtain ⟨T', hT'⟩ := hf'.2.2.2
  let M : G.GAf → Gr G 1 → ℚ → Prop := fun σ σ' s => 0 < s ∧
    (∀ w : AwayP p, Valued.v (algebraMap ℚ (w.1.adicCompletion ℚ) s) = lam G w σ) ∧
    ((padicNorm p s : ℚ) : ℝ) = nu1 p σ'.1
  let g : G.GAf → Gr G 1 → ℝ := fun σ σ' => if h : ∃ s, M σ σ' s then ((h.choose : ℚ) : ℝ) else 0
  have g_nonneg : ∀ σ σ', 0 ≤ g σ σ' := by
    intro σ σ'
    simp only [g]
    split_ifs with h
    · exact_mod_cast h.choose_spec.1.le
    · exact le_rfl
  refine ⟨∑ σ ∈ T, ∑ σ' ∈ T', g σ σ', ?_⟩
  intro y h₁ h₂ h1 h2
  obtain ⟨σ, hσ, k₁, hk₁, k₂, hk₂, e⟩ := hT _ h1
  obtain ⟨σ', hσ', k₁', hk₁', k₂', hk₂', e'⟩ := hT' _ h2
  have hM : M σ σ' (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) :=
    ⟨y.2.2, fun w => away G L β x t hx y h₁ σ k₁ k₂ hk₁ hk₂ e w, atp G β y h₂ σ' k₁' k₂' hk₁' hk₂' e'⟩
  have hex : ∃ s, M σ σ' s := ⟨_, hM⟩
  have heq : (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) = hex.choose :=
    eq_of_valuations hM.1 hex.choose_spec.1 (fun w => by rw [hM.2.1 w, hex.choose_spec.2.1 w])
      (by exact_mod_cast hM.2.2.trans hex.choose_spec.2.2.symm)
  have hg : ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) = g σ σ' := by
    simp only [g, dif_pos hex, heq]
  rw [hg]
  calc g σ σ' ≤ ∑ σ'' ∈ T', g σ σ'' :=
        Finset.single_le_sum (f := fun σ'' => g σ σ'') (fun i _ => g_nonneg σ i) hσ'
    _ ≤ ∑ σ₀ ∈ T, ∑ σ'' ∈ T', g σ₀ σ'' :=
        Finset.single_le_sum (f := fun σ₀ => ∑ σ'' ∈ T', g σ₀ σ'')
          (fun i _ => Finset.sum_nonneg fun j _ => g_nonneg i j) hσ

end GlobalTheory.SimBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeFactorFormGroupBoundedOfTestSupportStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitudeFactor_formGroup_bounded_of_test_support : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), ∃ S : ℝ, ∀ (y : grp G β) (h₁ : G.GAf) (h₂ : Gr G 1), f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → f' (h₂⁻¹ * toP1 G β y * h₂) ≠ 0 → (((y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) ≤ S := by
  first | (exact @GlobalTheory.SimBound.main) | (exact GlobalTheory.SimBound.main) | (intros; apply GlobalTheory.SimBound.main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryAdelicProdLocalCompacts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryAdelicProdLocalCompacts
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.CompactOrbitVectors

variable {p : ℕ} [Fact p.Prime]

theorem isCompact_box (K : ∀ v : AwayP p, Set (Qv v)) (hK : ∀ v, IsCompact (K v))
    (h : ∀ᶠ v in Filter.cofinite, K v ⊆ v.1.adicCompletionIntegers ℚ) :
    IsCompact {a : AfP p | ∀ v, AfP.eval v a ∈ K v} := by
  let S : Set (AwayP p) := {v | K v ⊆ v.1.adicCompletionIntegers ℚ}
  have hS : Filter.cofinite ≤ Filter.principal S := Filter.le_principal_iff.2 h
  let P := RestrictedProduct (fun v : AwayP p => v.1.adicCompletion ℚ)
      (fun v => (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) (Filter.principal S)
  have h1 : IsCompact {x : P | ∀ v, x v ∈ K v} := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    convert isCompact_univ_pi hK
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ v -
      exact hy v
    · intro hx
      exact ⟨⟨x, fun v hv => hv (hx v trivial)⟩, fun v => hx v trivial, rfl⟩
  have h2 := h1.image (RestrictedProduct.continuous_inclusion hS)
  have e : {a : AfP p | ∀ v, AfP.eval v a ∈ K v} = RestrictedProduct.inclusion _ _ hS '' {x : P | ∀ v, x v ∈ K v} := by
    ext a
    constructor
    · intro ha
      exact ⟨⟨(LevelExists.rp a).1, fun v hv => hv (ha v)⟩, ha, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  rw [e]
  exact h2

end GlobalTheory.OrbFinAf.CompactOrbitVectors

namespace GlobalTheory.OrbFinAf.CompactOrbitVectors

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

def basA : Module.Basis (Fin (Module.finrank ℚ G.C)) (AfP p) (AfP p ⊗[ℚ] G.C) :=
  Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)

def tv (v : AwayP p) : AfP p ⊗[ℚ] G.C →+* Qv v ⊗[ℚ] G.C :=
  (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)).toRingHom

theorem repr_tv (v : AwayP p) (y : AfP p ⊗[ℚ] G.C) (i : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (tv G v y) i = AfP.eval v ((basA G).repr y i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp [tv, basV, basA, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem continuous_eval (v : AwayP p) : Continuous (AfP.eval (p := p) v) :=
  RestrictedProduct.continuous_eval v

end GlobalTheory.OrbFinAf.CompactOrbitVectors

namespace GlobalTheory.OrbFinAf.CompactOrbitVectors

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

theorem tv_eq (v : AwayP p) (y : AfP p ⊗[ℚ] G.C) :
    tv G v y = (basV G v).equivFun.symm (fun i => AfP.eval v ((basA G).equivFun y i)) := by
  apply (basV G v).equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  funext i
  simp only [Module.Basis.equivFun_apply]
  exact repr_tv G v y i

theorem continuous_tv (v : AwayP p) :
    @Continuous _ _ (moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)) (moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)) (tv G v) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : ContinuousAdd (Qv v ⊗[ℚ] G.C) := IsModuleTopology.toContinuousAdd (Qv v) _
  have h1 : Continuous (basA G).equivFun := IsModuleTopology.continuous_of_linearMap (basA G).equivFun.toLinearMap
  have h2 : Continuous (basV G v).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (basV G v).equivFun.symm.toLinearMap
  have : tv G v = fun y => (basV G v).equivFun.symm (fun i => AfP.eval v ((basA G).equivFun y i)) :=
    funext (tv_eq G v)
  rw [this]
  exact h2.comp (continuous_pi fun i => (continuous_eval v).comp ((continuous_apply i).comp h1))

theorem continuous_piV (v : AwayP p) : Continuous (piV G v) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  have ht := continuous_tv G v
  have hval : Continuous fun x : G.GAf => ((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
  have hinv : Continuous fun x : G.GAf => ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) :=
    Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val)
  have hval2 : Continuous fun x : G.GAf => ((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p) :=
    Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
  have hinv2 : Continuous fun x : G.GAf => ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p) :=
    Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · rw [Units.continuous_iff]
    exact ⟨ht.comp hval, ht.comp hinv⟩
  · rw [Units.continuous_iff]
    exact ⟨(continuous_eval v).comp hval2, (continuous_eval v).comp hinv2⟩

end GlobalTheory.OrbFinAf.CompactOrbitVectors

open scoped RestrictedProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]


open CompactOrbitVectors in
theorem isCompact_prod_local : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (D : ∀ v : AwayP p, Set (Gv G v)),
    (∀ v, IsCompact (D v)) → (∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), D v ⊆ IntV G v) →
    IsCompact {g : G.GAf | ∀ v, piV G v g ∈ D v} := by
  intro p _ G D hDc hDi
  haveI : T2Space (AfP p) := inferInstanceAs
    (T2Space (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]))
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) _
  haveI : T2Space (AfP p ⊗[ℚ] G.C) := LevelExists.t2Space_tensor_rat_finite_algebra_moduleTopology (AfP p) G.C

  let c1 : ∀ v : AwayP p, Fin (Module.finrank ℚ G.C) → Gv G v → Qv v := fun v i h =>
    (basV G v).repr (((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) i
  let c2 : ∀ v : AwayP p, Fin (Module.finrank ℚ G.C) → Gv G v → Qv v := fun v i h =>
    (basV G v).repr ((((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) i
  let c3 : ∀ v : AwayP p, Gv G v → Qv v := fun v h => (((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v)
  let c4 : ∀ v : AwayP p, Gv G v → Qv v := fun v h =>
    ((((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2)⁻¹ : (Qv v)ˣ) : Qv v)
  have hc : ∀ v, (∀ i, Continuous (c1 v i)) ∧ (∀ i, Continuous (c2 v i)) ∧ Continuous (c3 v) ∧
      Continuous (c4 v) := by
    intro v
    letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
    haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
    have hr : Continuous (basV G v).equivFun :=
      IsModuleTopology.continuous_of_linearMap (basV G v).equivFun.toLinearMap
    refine ⟨fun i => ?_, fun i => ?_, ?_, ?_⟩
    · exact (continuous_apply i).comp (hr.comp
        (Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)))
    · exact (continuous_apply i).comp (hr.comp
        (Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val)))
    · exact Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
    · exact Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)
  let K : ∀ v : AwayP p, Set (Qv v) := fun v =>
    ((⋃ i, c1 v i '' D v) ∪ (⋃ i, c2 v i '' D v)) ∪ (c3 v '' D v ∪ c4 v '' D v)
  have hKc : ∀ v, IsCompact (K v) := fun v =>
    ((isCompact_iUnion fun i => (hDc v).image ((hc v).1 i)).union
      (isCompact_iUnion fun i => (hDc v).image ((hc v).2.1 i))).union
      (((hDc v).image (hc v).2.2.1).union ((hDc v).image (hc v).2.2.2))
  have hKi : ∀ᶠ v in Filter.cofinite, K v ⊆ v.1.adicCompletionIntegers ℚ := by
    filter_upwards [hDi] with v hv
    rintro y ((hy | hy) | (hy | hy))
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      obtain ⟨h, hh, rfl⟩ := hi
      exact (hv hh).1 i
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      obtain ⟨h, hh, rfl⟩ := hi
      exact (hv hh).2.1 i
    · obtain ⟨h, hh, rfl⟩ := hy
      exact (hv hh).2.2.1
    · obtain ⟨h, hh, rfl⟩ := hy
      exact (hv hh).2.2.2
  let E : Set (AfP p) := {a | ∀ v, AfP.eval v a ∈ K v}
  have hE : IsCompact E := isCompact_box K hKc hKi
  let Bm : Set (AfP p ⊗[ℚ] G.C) := (basA G).equivFun.symm '' Set.univ.pi fun _ => E
  have hBm : IsCompact Bm := (isCompact_univ_pi fun _ => hE).image
    (IsModuleTopology.continuous_of_linearMap (basA G).equivFun.symm.toLinearMap)
  let B : Set (((AfP p ⊗[ℚ] G.C) × (AfP p ⊗[ℚ] G.C)ᵐᵒᵖ) × (AfP p × (AfP p)ᵐᵒᵖ)) :=
    (Bm ×ˢ (MulOpposite.op '' Bm)) ×ˢ (E ×ˢ (MulOpposite.op '' E))
  have hB : IsCompact B := (hBm.prod (hBm.image MulOpposite.continuous_op)).prod
    (hE.prod (hE.image MulOpposite.continuous_op))

  have hσ : Continuous (fun y : AfP p ⊗[ℚ] G.C ↦ (starT G.star (AfP p) y).unop) := by
    let σl : (AfP p ⊗[ℚ] G.C) →ₗ[AfP p] (AfP p ⊗[ℚ] G.C) :=
      { toFun := fun y ↦ (starT G.star (AfP p) y).unop
        map_add' := fun x y ↦ by simp only [map_add (f := _), MulOpposite.unop_add]
        map_smul' := by
          intro r x
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul a y =>
            simp only [TensorProduct.smul_tmul', smul_eq_mul, starT_tmul, RingHom.id_apply]
          | add x y hx hy => simp only [smul_add, map_add (f := _), MulOpposite.unop_add, hx, hy, RingHom.id_apply] }
    exact IsModuleTopology.continuous_of_linearMap σl
  have hj : Continuous (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AfP p) (AfP p ⊗[ℚ] G.C))
  have hGcl : IsClosed (UPts G.star (AfP p) : Set ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)) := by
    apply isClosed_eq
    · exact (Units.continuous_val.comp continuous_fst).mul
        (hσ.comp (Units.continuous_val.comp continuous_fst))
    · exact hj.comp (Units.continuous_val.comp continuous_snd)
  let emb : G.GAf → ((AfP p ⊗[ℚ] G.C) × (AfP p ⊗[ℚ] G.C)ᵐᵒᵖ) × (AfP p × (AfP p)ᵐᵒᵖ) :=
    fun x ↦ (Units.embedProduct _ x.1.1, Units.embedProduct _ x.1.2)
  have hemb : Topology.IsClosedEmbedding emb :=
    (Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct).comp
      hGcl.isClosedEmbedding_subtypeVal

  have hS : IsClosed {g : G.GAf | ∀ v, piV G v g ∈ D v} := by
    have : {g : G.GAf | ∀ v, piV G v g ∈ D v} = ⋂ v, piV G v ⁻¹' D v := by
      ext g; simp
    rw [this]
    refine isClosed_iInter fun v => ?_
    letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
    haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
    haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _
    haveI : T2Space (Qv v ⊗[ℚ] G.C) := LevelExists.t2Space_tensor_rat_finite_algebra_moduleTopology (Qv v) G.C
    haveI : T2Space (Gv G v) := inferInstance
    exact (hDc v).isClosed.preimage (continuous_piV G v)

  have hsub : emb '' {g : G.GAf | ∀ v, piV G v g ∈ D v} ⊆ B := by
    rintro _ ⟨x, hx, rfl⟩
    have hco : ∀ y : AfP p ⊗[ℚ] G.C,
        (∀ v i, (basV G v).repr (tv G v y) i ∈ K v) → y ∈ Bm := by
      intro y hy
      refine ⟨(basA G).equivFun y, fun i _ v => ?_, by simp⟩
      rw [Module.Basis.equivFun_apply, ← repr_tv]
      exact hy v i
    refine ⟨⟨hco _ fun v i => ?_, ⟨_, hco _ fun v i => ?_, rfl⟩⟩, ⟨fun v => ?_, ⟨_, fun v => ?_, rfl⟩⟩⟩
    · exact Or.inl (Or.inl (Set.mem_iUnion.2 ⟨i, piV G v x, hx v, rfl⟩))
    · exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, piV G v x, hx v, rfl⟩))
    · exact Or.inr (Or.inl ⟨piV G v x, hx v, rfl⟩)
    · exact Or.inr (Or.inr ⟨piV G v x, hx v, rfl⟩)
  exact hemb.isInducing.isCompact_iff.2 (hB.of_isClosed_subset (hemb.isClosedMap _ hS) hsub)

end GlobalTheory.OrbFinAf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryAdelicProdLocalCompactsStatement
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_unitaryAdelic_prod_local_compacts : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (D : ∀ v : AwayP p, Set (Gv G v)), (∀ v, IsCompact (D v)) → (∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), D v ⊆ IntV G v) → IsCompact {g : G.GAf | ∀ v, piV G v g ∈ D v} := by
  first | (exact @GlobalTheory.OrbFinAf.isCompact_prod_local) | (exact GlobalTheory.OrbFinAf.isCompact_prod_local) | (intros; apply GlobalTheory.OrbFinAf.isCompact_prod_local  <;> assumption)
end
end
