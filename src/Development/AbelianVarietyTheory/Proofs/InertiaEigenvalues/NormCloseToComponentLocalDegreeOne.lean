module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuedMapEqOfContinuousCompletionIsoExtending
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuedMapEqOfContinuousCompletionIsoExtending
open NumberField IsDedekindDomain

namespace GlobalTheory.CompletionIsom


open WithZero in
theorem valuation_eq_of_lt_one_iff {K : Type} [Field K] (v v' : Valuation K (WithZero (Multiplicative ℤ)))
    (h : ∀ y, v y < 1 ↔ v' y < 1) (π : K) (hπ : v π = exp (-1)) (y₀ : K) (hy₀ : v' y₀ = exp (-1)) :
    ∀ y, v' y = v y := by
  have hπ0 : π ≠ 0 := by rintro rfl; rw [map_zero] at hπ; exact exp_ne_zero hπ.symm
  have hy0 : y₀ ≠ 0 := by rintro rfl; rw [map_zero] at hy₀; exact exp_ne_zero hy₀.symm
  have hexp : ∀ (w : Valuation K (WithZero (Multiplicative ℤ))) (x : K), x ≠ 0 → ∃ a : ℤ, w x = exp a :=
    fun w x hx => ⟨_, (exp_log ((Valuation.ne_zero_iff w).2 hx)).symm⟩
  have hker : ∀ z, v z = 1 → v' z = 1 := by
    intro z hz
    have hz0 : z ≠ 0 := by rintro rfl; rw [map_zero] at hz; exact zero_ne_one hz
    obtain ⟨a, ha⟩ := hexp v' z hz0
    rcases lt_trichotomy a 0 with h1 | h1 | h1
    · have := (h z).2 (by rw [ha, ← exp_zero, exp_lt_exp]; exact h1)
      rw [hz] at this; exact absurd this (lt_irrefl _)
    · rw [ha, h1, exp_zero]
    · have := (h z⁻¹).2 (by rw [map_inv₀, ha, ← exp_neg, ← exp_zero, exp_lt_exp]; omega)
      rw [map_inv₀, hz, inv_one] at this; exact absurd this (lt_irrefl _)
  obtain ⟨e, he⟩ := hexp v' π hπ0
  obtain ⟨b, hb⟩ := hexp v y₀ hy0
  have he1 : e < 0 := by
    have := (h π).1 (by rw [hπ, ← exp_zero, exp_lt_exp]; omega)
    rwa [he, ← exp_zero, exp_lt_exp] at this
  have hb1 : b < 0 := by
    have := (h y₀).2 (by rw [hy₀, ← exp_zero, exp_lt_exp]; omega)
    rwa [hb, ← exp_zero, exp_lt_exp] at this
  have he2 : -1 ≤ e := by
    by_contra hc
    have := (h (π * y₀⁻¹)).2 (by
      rw [map_mul, map_inv₀, he, hy₀, ← exp_neg, ← exp_add, ← exp_zero, exp_lt_exp]; omega)
    rw [map_mul, map_inv₀, hπ, hb, ← exp_neg, ← exp_add, ← exp_zero, exp_lt_exp] at this
    omega
  have hπ' : v' π = exp (-1) := by rw [he]; congr 1; omega
  intro y
  by_cases hy : y = 0
  · rw [hy, map_zero, map_zero]
  obtain ⟨a, ha⟩ := hexp v y hy
  have hz := hker (y * π ^ a) (by
    rw [map_mul, map_zpow₀, ha, hπ, ← exp_zsmul, ← exp_add, ← exp_zero]; congr 1; simp)
  rw [map_mul, map_zpow₀, hπ', ← exp_zsmul] at hz
  rw [ha, eq_inv_of_mul_eq_one_left hz, ← exp_neg]
  congr 1; simp

theorem valued_v_map : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'))
    (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i →
    (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) →
    ∀ y : w.adicCompletion E, Valued.v (i y) = Valued.v y := by
  intro E E' _ _ _ _ _ w w' i hi _ y
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion E w
  have ho : IsOpenMap i :=
    AddMonoidHom.isOpenMap_of_sigmaCompact i.toAddEquiv.toAddMonoidHom i.surjective hi
  have hi' : Continuous i.symm := i.toEquiv.continuous_symm_iff.2 ho
  obtain ⟨π, hπ⟩ := w.valuedAdicCompletion_surjective E (WithZero.exp (-1))
  obtain ⟨ϖ, hϖ⟩ := w'.valuedAdicCompletion_surjective E' (WithZero.exp (-1))
  refine valuation_eq_of_lt_one_iff (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
    ((Valued.v : Valuation (w'.adicCompletion E') (WithZero (Multiplicative ℤ))).comap i.toRingHom)
    (fun x => ⟨fun hx => GlobalTheory.ConjParahoric.val_lt_one_map i.toRingHom hi hx, fun hx => ?_⟩) π hπ (i.symm ϖ) ?_ y
  · have := GlobalTheory.ConjParahoric.val_lt_one_map i.symm.toRingHom hi' hx
    simpa using this
  · simpa using hϖ

end GlobalTheory.CompletionIsom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuedMapEqOfContinuousCompletionIsoExtendingStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valued_map_eq_of_continuous_completionIso_extending : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) → ∀ y : w.adicCompletion E, Valued.v (i y) = Valued.v y := by
  first | exact @GlobalTheory.CompletionIsom.valued_v_map | exact GlobalTheory.CompletionIsom.valued_v_map | (intros; apply GlobalTheory.CompletionIsom.valued_v_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDivLocalEmbeddingCloseToOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLeOneOfSqSubSelfIntegralBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLeOneOfSqSubSelfIntegralBasis
open NumberField IsDedekindDomain TensorProduct

namespace GlobalTheory

theorem integral_of_sq_sub_integral (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    {ι : Type} [Fintype ι] (b : Module.Basis ι E E') (hbi : ∀ i, IsIntegral ℤ (b i))
    (w : HeightOneSpectrum (𝓞 E)) (w'' : HeightOneSpectrum (𝓞 E'))
    (hw : w''.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = w.asIdeal) (ε : E')
    (hε : ∀ i, w.valuation E (b.repr (ε * ε - ε) i) ≤ 1) : w''.valuation E' ε ≤ 1 := by
  have hunder : w''.under (𝓞 E) = w := HeightOneSpectrum.ext hw
  have hc : ∀ c : E, w.valuation E c ≤ 1 → w''.valuation E' (algebraMap E E' c) ≤ 1 := by
    intro c hc
    subst hunder
    have : w''.asIdeal.LiesOver (w''.under (𝓞 E)).asIdeal := ⟨rfl⟩
    rw [← HeightOneSpectrum.valuation_liesOver E' (w''.under (𝓞 E)) w'' c]
    exact pow_le_one' hc _
  have hb : ∀ i, w''.valuation E' (b i) ≤ 1 := by
    intro i
    have : b i = algebraMap (𝓞 E') E' (⟨b i, (mem_integralClosure_iff ℤ E').2 (hbi i)⟩ : 𝓞 E') := rfl
    rw [this]
    exact w''.valuation_le_one _
  have hu : w''.valuation E' (ε * ε - ε) ≤ 1 := by
    rw [← b.sum_repr (ε * ε - ε)]
    refine (Valuation.map_sum_le _ fun i _ => ?_)
    rw [Algebra.smul_def, map_mul]
    exact mul_le_one' (hc _ (hε i)) (hb i)
  by_contra h
  push_neg at h
  have h2 : w''.valuation E' (ε * ε) ≤ w''.valuation E' ε := by
    have : ε * ε = ε + (ε * ε - ε) := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le le_rfl (hu.trans h.le))
  rw [map_mul] at h2
  have h0 : (0 : _) < w''.valuation E' ε := lt_trans zero_lt_one h
  have := mul_lt_mul_of_pos_left h h0
  rw [mul_one] at this
  exact absurd h2 (not_le.2 this)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLeOneOfSqSubSelfIntegralBasisStatement
open NumberField IsDedekindDomain TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_le_one_of_sq_sub_self_integral_basis : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] {ι : Type} [Fintype ι] (b : Module.Basis ι E E'), (∀ i, IsIntegral ℤ (b i)) → ∀ (w : HeightOneSpectrum (𝓞 E)) (w'' : HeightOneSpectrum (𝓞 E')), w''.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = w.asIdeal → ∀ ε : E', (∀ i, w.valuation E (b.repr (ε * ε - ε) i) ≤ 1) → w''.valuation E' ε ≤ 1 := by
  first | exact @GlobalTheory.integral_of_sq_sub_integral | exact GlobalTheory.integral_of_sq_sub_integral | (intros; apply GlobalTheory.integral_of_sq_sub_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqMulNormIdempotentCorner
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqMulNormIdempotentCorner
open NumberField IsDedekindDomain TensorProduct

namespace GlobalTheory

theorem norm_scale_idem_add_compl {K A : Type} [Field K] [CommRing A] [Algebra K A]
    [Module.Finite K A] (ψ : A →ₐ[K] K) (e : A) (he : ψ e = 1)
    (hea : ∀ a, e * a = algebraMap K A (ψ a) * e) (c : K) :
    Algebra.norm K (algebraMap K A c * e + (1 - e)) = c := by
  classical
  let b := Module.Free.chooseBasis K A
  rw [Algebra.norm_apply, ← LinearMap.det_toMatrix b]
  have hM : LinearMap.toMatrix b b (Algebra.lmul K A (algebraMap K A c * e + (1 - e))) =
      1 + Matrix.replicateCol Unit (fun i => (c - 1) * b.repr e i) *
        Matrix.replicateRow Unit (fun j => ψ (b j)) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change b.repr ((algebraMap K A c * e + (1 - e)) * b j) i = _
    have h1 : (algebraMap K A c * e + (1 - e)) * b j = b j + ((c - 1) * ψ (b j)) • e := by
      have := hea (b j)
      rw [Algebra.smul_def, map_mul, map_sub, map_one]
      linear_combination (algebraMap K A c - 1) * this
    simp only [h1, map_add (f := _), map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Module.Basis.repr_self, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, Finset.univ_unique, Finset.sum_singleton, smul_eq_mul]
    rw [Finsupp.single_apply]
    congr 1
    · split_ifs with h h' h' <;> first | rfl | (exfalso; exact h' h.symm) | (exfalso; exact h h'.symm)
    · ring
  rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hs : ∑ j, ψ (b j) * ((c - 1) * b.repr e j) = (c - 1) * ψ e := by
    conv_rhs => rw [← b.sum_repr e]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]; ring
  rw [dotProduct, hs, he]; ring

theorem norm_eq_mul_norm_idem_corner : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] (ψ : A →ₐ[K] K) (e : A), ψ e = 1 → (∀ a, e * a = algebraMap K A (ψ a) * e) → ∀ a : A, Algebra.norm K a = ψ a * Algebra.norm K (e + (1 - e) * a) := by
  intro K A _ _ _ _ ψ e he hea a
  have hee : e * e = e := by rw [hea e, he, map_one, one_mul]
  have hid : a = (e + (1 - e) * a) * (algebraMap K A (ψ a) * e + (1 - e)) := by
    have h1 := hea a
    linear_combination (-(algebraMap K A (ψ a) - algebraMap K A (ψ a) * a + a - 1)) * hee + h1
  conv_lhs => rw [hid]
  rw [map_mul, norm_scale_idem_add_compl ψ e he hea, mul_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqMulNormIdempotentCornerStatement
open NumberField IsDedekindDomain TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_eq_mul_norm_idempotent_corner : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] (ψ : A →ₐ[K] K) (e : A), ψ e = 1 → (∀ a, e * a = algebraMap K A (ψ a) * e) → ∀ a : A, Algebra.norm K a = ψ a * Algebra.norm K (e + (1 - e) * a) := by
  first | exact @GlobalTheory.norm_eq_mul_norm_idem_corner | exact GlobalTheory.norm_eq_mul_norm_idem_corner | (intros; apply GlobalTheory.norm_eq_mul_norm_idem_corner <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalElementNearIdempotentAdicCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalElementNearIdempotentAdicCompletion
noncomputable section

open NumberField IsDedekindDomain TensorProduct Topology

namespace GlobalTheory

theorem exists_global_near_idempotent (E E' : Type) [Field E] [NumberField E] [Field E']
    [Algebra E E'] [FiniteDimensional E E'] (w : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι]
    (b : Module.Basis ι E E') (ψ : w.adicCompletion E ⊗[E] E' →ₐ[w.adicCompletion E] w.adicCompletion E)
    (e : w.adicCompletion E ⊗[E] E') (he : e * e = e) (hψ : ψ e = 1)
    (p q : w.adicCompletion E ⊗[E] E') (n : ℕ) :
    ∃ ε : E', (∀ i, w.valuation E (b.repr (ε * ε - ε) i) ≤ 1) ∧
      Valued.v (ψ ((1 : w.adicCompletion E) ⊗ₜ ε) - 1) ≤ WithZero.exp (-(n : ℤ)) ∧
      Valued.v (Algebra.norm (w.adicCompletion E) (p + q * ((1 : w.adicCompletion E) ⊗ₜ ε - e)) -
        Algebra.norm (w.adicCompletion E) p) ≤ WithZero.exp (-(n : ℤ)) := by
  classical
  set K := w.adicCompletion E with hK
  set B := Algebra.TensorProduct.basis K b with hB
  set Φ : (ι → K) → K ⊗[E] E' := fun t => ∑ i, t i • B i with hΦ
  have hrepr : ∀ t, B.repr (Φ t) = Finsupp.equivFunOnFinite.symm t := by
    intro t
    ext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hΦ, map_sum, Finsupp.smul_apply, Finsupp.single_apply]
  have hM : Continuous fun t => Algebra.leftMulMatrix B (Φ t) := by
    have h : (fun t => Algebra.leftMulMatrix B (Φ t)) =
        fun t => ∑ i, t i • Algebra.leftMulMatrix B (B i) := by
      funext t
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hΦ, map_sum, map_smul]
    rw [h]
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

  set f1 : (ι → K) → ι → K := fun t => B.repr (Φ t * Φ t - Φ t) with hf1
  set f2 : (ι → K) → K := fun t => ψ (Φ t) - 1 with hf2
  set f3 : (ι → K) → K := fun t => Algebra.norm K (p + q * (Φ t - e)) - Algebra.norm K p with hf3
  have hf1c : Continuous f1 := by
    have h : f1 = fun t => Matrix.mulVec (Algebra.leftMulMatrix B (Φ t)) t - t := by
      funext t
      funext i
      simp only [hf1, map_sub, Finsupp.coe_sub, Pi.sub_apply]
      rw [← Algebra.leftMulMatrix_mulVec_repr, hrepr]
      simp
    rw [h]
    exact (hM.matrix_mulVec continuous_id).sub continuous_id
  have hf2c : Continuous f2 := by
    have hl : Continuous fun t => ψ (Φ t) := by
      have h := LinearMap.continuous_on_pi (ψ.toLinearMap ∘ₗ B.equivFun.symm.toLinearMap)
      convert h using 1
      funext t
      simp [hΦ, Module.Basis.equivFun_symm_apply]
    exact hl.sub continuous_const
  have hf3c : Continuous f3 := by
    have h : (fun t => Algebra.norm K (p + q * (Φ t - e))) = fun t =>
        (Algebra.leftMulMatrix B (p - q * e) + Algebra.leftMulMatrix B q *
          Algebra.leftMulMatrix B (Φ t)).det := by
      funext t
      rw [Algebra.norm_eq_matrix_det B, ← map_mul, ← map_add (f := _)]
      congr 2
      ring
    have : Continuous fun t => Algebra.norm K (p + q * (Φ t - e)) := by
      rw [h]
      exact (continuous_const.add (continuous_const.matrix_mul hM)).matrix_det
    exact this.sub continuous_const
  set t₀ : ι → K := fun i => B.repr e i with ht₀
  have hΦ₀ : Φ t₀ = e := by simp only [hΦ, ht₀]; exact B.sum_repr e
  have hball' : ∀ x₀ : K, Valued.v x₀ ≠ 0 → {z : K | Valued.v z ≤ Valued.v x₀} ∈ 𝓝 (0 : K) := by
    intro x₀ hx₀
    have hl : {y : K | Valued.v y = Valued.v x₀} ∈ 𝓝 x₀ := Valued.locally_const hx₀
    have hc : ContinuousAt (fun z : K => z + x₀) 0 := (continuous_id.add continuous_const).continuousAt
    have h' := hc.preimage_mem_nhds (by simpa using hl)
    filter_upwards [h'] with z hz
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hz ⊢
    calc Valued.v z = Valued.v ((z + x₀) - x₀) := by rw [add_sub_cancel_right]
      _ ≤ max (Valued.v (z + x₀)) (Valued.v x₀) := Valuation.map_sub _ _ _
      _ = Valued.v x₀ := by rw [hz, max_self]
  have hva : ∀ x : E, Valued.v (algebraMap E K x) = w.valuation E x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  have hx₀ : Valued.v ((algebraMap E K π) ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hva, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hball : ∀ γ, γ = WithZero.exp (-(n : ℤ)) ∨ γ = 1 → {z : K | Valued.v z ≤ γ} ∈ 𝓝 (0 : K) := by
    rintro γ (rfl | rfl)
    · rw [← hx₀]
      exact hball' _ (by rw [hx₀]; exact WithZero.exp_ne_zero)
    · have := hball' 1 (by simp)
      simpa using this
  have h1 : ∀ᶠ t in 𝓝 t₀, ∀ i, Valued.v (f1 t i) ≤ 1 := by
    rw [Filter.eventually_all]
    intro i
    have hc : ContinuousAt (fun t => f1 t i) t₀ := ((continuous_apply i).comp hf1c).continuousAt
    have h0 : f1 t₀ i = 0 := by simp [hf1, hΦ₀, he]
    exact hc.preimage_mem_nhds (by rw [h0]; exact hball 1 (Or.inr rfl))
  have h2 : ∀ᶠ t in 𝓝 t₀, Valued.v (f2 t) ≤ WithZero.exp (-(n : ℤ)) := by
    have h0 : f2 t₀ = 0 := by simp [hf2, hΦ₀, hψ]
    exact hf2c.continuousAt.preimage_mem_nhds (by rw [h0]; exact hball _ (Or.inl rfl))
  have h3 : ∀ᶠ t in 𝓝 t₀, Valued.v (f3 t) ≤ WithZero.exp (-(n : ℤ)) := by
    have h0 : f3 t₀ = 0 := by simp [hf3, hΦ₀]
    exact hf3c.continuousAt.preimage_mem_nhds (by rw [h0]; exact hball _ (Or.inl rfl))
  have hd : DenseRange (Pi.map fun _ : ι => (algebraMap E K : E → K)) :=
    DenseRange.piMap fun _ => w.denseRange_algebraMap E
  obtain ⟨c, hc1, hc2, hc3⟩ := hd.mem_nhds (h1.and (h2.and h3))
  set ε : E' := ∑ i, c i • b i with hε
  have hΦc : Φ (Pi.map (fun _ : ι => (algebraMap E K : E → K)) c) = (1 : K) ⊗ₜ ε := by
    simp only [hΦ, Pi.map_apply, hε]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hB, Algebra.TensorProduct.basis_apply, TensorProduct.tmul_smul, algebraMap_smul]
  refine ⟨ε, ?_, ?_, ?_⟩
  · intro i
    have h := hc1 i
    simp only [hf1, hΦc] at h
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_sub,
      hB, Algebra.TensorProduct.basis_repr_tmul] at h
    simp only [one_smul, Finsupp.mapRange_apply] at h
    rw [← hva]
    exact h
  · have h := hc2
    simpa only [hf2, hΦc] using h
  · have h := hc3
    simpa only [hf3, hΦc] using h

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalElementNearIdempotentAdicCompletionStatement
open NumberField IsDedekindDomain TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_element_near_idempotent_adicCompletion : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [Algebra E E'] [FiniteDimensional E E'] (w : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι] (b : Module.Basis ι E E') (ψ : w.adicCompletion E ⊗[E] E' →ₐ[w.adicCompletion E] w.adicCompletion E) (e : w.adicCompletion E ⊗[E] E'), e * e = e → ψ e = 1 → ∀ (p q : w.adicCompletion E ⊗[E] E') (n : ℕ), ∃ ε : E', (∀ i, w.valuation E (b.repr (ε * ε - ε) i) ≤ 1) ∧ Valued.v (ψ ((1 : w.adicCompletion E) ⊗ₜ ε) - 1) ≤ WithZero.exp (-(n : ℤ)) ∧ Valued.v (Algebra.norm (w.adicCompletion E) (p + q * ((1 : w.adicCompletion E) ⊗ₜ ε - e)) - Algebra.norm (w.adicCompletion E) p) ≤ WithZero.exp (-(n : ℤ)) := by
  first | exact @GlobalTheory.exists_global_near_idempotent | exact GlobalTheory.exists_global_near_idempotent | (intros; apply GlobalTheory.exists_global_near_idempotent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTensorIdempotentOfAlgHomToBase
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTensorIdempotentOfAlgHomToBase
open NumberField IsDedekindDomain TensorProduct Polynomial

namespace GlobalTheory

theorem exists_tensor_idem_of_algHom (E K E' : Type) [Field E] [CharZero E] [Field K] [Field E']
    [Algebra E K] [Algebra E E'] [FiniteDimensional E E'] (ψ : K ⊗[E] E' →ₐ[K] K) :
    ∃ e : K ⊗[E] E', ψ e = 1 ∧ ∀ a, e * a = algebraMap K (K ⊗[E] E') (ψ a) * e := by
  classical
  set A := K ⊗[E] E'
  let pb := Field.powerBasisOfFiniteOfSeparable E E'
  set θ := pb.gen
  let T : A := Algebra.TensorProduct.includeRight θ
  set α : K := ψ T
  let f : E[X] := minpoly E θ
  let fK : K[X] := f.map (algebraMap E K)
  have hfT : aeval T fK = 0 := by
    rw [aeval_map_algebraMap]
    have : aeval T f = Algebra.TensorProduct.includeRight (aeval θ f) := by
      rw [aeval_algHom_apply]
    rw [this, minpoly.aeval, map_zero]
  have hroot : IsRoot fK α := by
    have h1 : aeval α fK = ψ (aeval T fK) := by
      rw [aeval_algHom_apply]
    rw [hfT, map_zero] at h1
    simpa [IsRoot, aeval_def, eval₂_eq_eval_map] using h1
  have hsep : fK.Separable := Polynomial.Separable.map (p := f) (Algebra.IsSeparable.isSeparable E θ)
  set g : K[X] := fK /ₘ (X - C α)
  have hfac : (X - C α) * g = fK := (mul_divByMonic_eq_iff_isRoot).2 hroot
  have hgα : g.eval α ≠ 0 := by
    have hd := hsep.eval₂_derivative_ne_zero (RingHom.id K) (x := α) (by simpa [eval₂_id] using hroot)
    rw [eval₂_id, ← hfac] at hd
    simpa [derivative_mul] using hd
  let e : A := algebraMap K A (g.eval α)⁻¹ * aeval T g
  have hψg : ψ (aeval T g) = g.eval α := by
    rw [← aeval_algHom_apply]; rfl
  have hψe : ψ e = 1 := by
    have hc : ψ (algebraMap K A (g.eval α)⁻¹) = (g.eval α)⁻¹ := ψ.commutes _
    simp only [e, map_mul, hc, hψg]
    exact inv_mul_cancel₀ hgα
  have hTe : e * T = algebraMap K A (ψ T) * e := by
    have h0 : (T - algebraMap K A α) * aeval T g = 0 := by
      have : aeval T ((X - C α) * g) = (T - algebraMap K A α) * aeval T g := by
        simp [map_mul, map_sub]
      rw [← this, hfac, hfT]
    have h1 : T * aeval T g = algebraMap K A α * aeval T g := by
      rw [sub_mul] at h0; exact sub_eq_zero.1 h0
    simp only [e]
    calc algebraMap K A (g.eval α)⁻¹ * aeval T g * T
        = algebraMap K A (g.eval α)⁻¹ * (T * aeval T g) := by ring
      _ = algebraMap K A α * (algebraMap K A (g.eval α)⁻¹ * aeval T g) := by rw [h1]; ring

  let Q : A → Prop := fun a => e * a = algebraMap K A (ψ a) * e
  have Qmul : ∀ a b, Q a → Q b → Q (a * b) := by
    intro a b ha hb
    show e * (a * b) = algebraMap K A (ψ (a * b)) * e
    rw [map_mul, map_mul, ← mul_assoc, ha, mul_assoc, hb]; ring
  have Qadd : ∀ a b, Q a → Q b → Q (a + b) := by
    intro a b ha hb
    show e * (a + b) = algebraMap K A (ψ (a + b)) * e
    rw [map_add (f := _), map_add (f := _), mul_add, ha, hb, add_mul]
  have Qalg : ∀ k : K, Q (algebraMap K A k) := by
    intro k
    show e * algebraMap K A k = algebraMap K A (ψ (algebraMap K A k)) * e
    rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
  have Qright : ∀ x : E', Q (Algebra.TensorProduct.includeRight x) := by
    intro x
    have hx : x ∈ Algebra.adjoin E ({θ} : Set E') := by rw [pb.adjoin_gen_eq_top]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff.1 hy]; exact hTe
    | algebraMap r =>
      have : (Algebra.TensorProduct.includeRight (algebraMap E E' r) : A)
          = algebraMap K A (algebraMap E K r) := by
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply E K A]
      rw [this]; exact Qalg _
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Qadd _ _ hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact Qmul _ _ hy hz
  refine ⟨e, hψe, fun a => ?_⟩
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul k x =>
    have : (k ⊗ₜ[E] x : A) = algebraMap K A k * Algebra.TensorProduct.includeRight x := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.algebraMap_self, RingHom.id_apply, one_mul]
    rw [this]; exact Qmul _ _ (Qalg k) (Qright x)
  | add a b ha hb => exact Qadd _ _ ha hb

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTensorIdempotentOfAlgHomToBaseStatement
open NumberField IsDedekindDomain TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensor_idempotent_of_algHom_to_base : ∀ (E K E' : Type) [Field E] [CharZero E] [Field K] [Field E'] [Algebra E K] [Algebra E E'] [FiniteDimensional E E'] (ψ : K ⊗[E] E' →ₐ[K] K), ∃ e : K ⊗[E] E', ψ e = 1 ∧ ∀ a, e * a = algebraMap K (K ⊗[E] E') (ψ a) * e := by
  first | exact @GlobalTheory.exists_tensor_idem_of_algHom | exact GlobalTheory.exists_tensor_idem_of_algHom | (intros; apply GlobalTheory.exists_tensor_idem_of_algHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDivLocalEmbeddingCloseToOne
noncomputable section

open NumberField IsDedekindDomain TensorProduct

namespace GlobalTheory.NormCompat.RatioClose

theorem norm_one_tmul' {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    [Module.Finite F E] (y : E) :
    Algebra.norm K ((1 : K) ⊗ₜ[F] y) = algebraMap F K (Algebra.norm F y) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem norm_div_close_to_one : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (σ : E' →+* w.adicCompletion E), (∀ x : E, σ (algebraMap E E' x) = algebraMap E _ x) → (∀ x : E', Valued.v (σ x) = w'.valuation E' x) → ∀ M : ℕ, ∃ M' : ℕ, ∀ z : E', z ≠ 0 → (∀ w'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'), w''.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal → w'' ≠ w' → w''.valuation E' (z - 1) ≤ WithZero.exp (-(M' : ℤ))) → Valued.v (algebraMap E (w.adicCompletion E) (Algebra.norm E z) / σ z - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  intro E E' _ _ _ _ _ w w' σ hσ hv M
  classical
  obtain ⟨M₁, hM₁⟩ := GlobalTheory.NormCompat.NormCont.norm_close_to_one E E' w M
  refine ⟨M₁, fun z hz0 hz => ?_⟩
  set K := w.adicCompletion E
  let σA : E' →ₐ[E] K := { σ with commutes' := hσ }
  let ψ : K ⊗[E] E' →ₐ[K] K := Algebra.TensorProduct.lift (Algebra.ofId K K) σA (fun _ _ => Commute.all _ _)
  have hψ : ∀ x : E', ψ ((1 : K) ⊗ₜ x) = σ x := fun x => by
    simp [ψ, σA, Algebra.TensorProduct.lift_tmul]
  obtain ⟨e, he1, he⟩ := GlobalTheory.T.exists_tensor_idempotent_of_algHom_to_base E K E' ψ
  have hee : e * e = e := by rw [he, he1, map_one, one_mul]
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral (𝓞 E) E E'
  have hb' : ∀ i, IsIntegral ℤ (b i) := fun i => isIntegral_trans _ (hb i)
  have hvK : ∀ x : E, Valued.v (algebraMap E K x) = w.valuation E x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  have hβ : ∀ x : E', x ≠ 0 → algebraMap E K (Algebra.norm E x) / σ x =
      Algebra.norm K (e + (1 - e) * ((1 : K) ⊗ₜ x)) := by
    intro x hx
    have h2 := GlobalTheory.T.norm_eq_mul_norm_idempotent_corner K (K ⊗[E] E') ψ e he1 he ((1 : K) ⊗ₜ x)
    rw [norm_one_tmul', hψ] at h2
    rw [h2, mul_div_cancel_left₀ _ ((map_ne_zero σ).2 hx)]
  let Z : K ⊗[E] E' := (1 : K) ⊗ₜ z
  set p : K ⊗[E] E' := e + (1 - e) * Z with hp
  set q : K ⊗[E] E' := (1 - e) * (1 - Z) with hq
  obtain ⟨K₀, hK₂, hK₁, hK₃⟩ : ∃ K₀ : ℕ, M ≤ K₀ ∧ M₁ ≤ K₀ ∧ 1 ≤ K₀ := ⟨M + M₁ + 1, by omega, by omega, by omega⟩
  set m : ℤ := (w'.valuation E' (z - 1)).log with hm
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, M ≤ n ∧ (K₀ : ℤ) + m ≤ n := ⟨M + K₀ + m.toNat, by omega, by omega⟩
  obtain ⟨ε, hε1, hε2, hε3⟩ := GlobalTheory.T.exists_global_element_near_idempotent_adicCompletion E E' w b ψ e hee he1 p q n
  set y : E' := ε + (1 - ε) * z with hy
  have hy1 : y - 1 = (1 - ε) * (z - 1) := by rw [hy]; ring
  have hw'ε : w'.valuation E' (ε - 1) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [← hv, map_sub, map_one, ← hψ]; exact hε2
  have hw'y : w'.valuation E' (y - 1) ≤ WithZero.exp (-(K₀ : ℤ)) := by
    rw [hy1, map_mul, Valuation.map_sub_swap]
    by_cases hz1 : w'.valuation E' (z - 1) = 0
    · rw [hz1, mul_zero]; exact zero_le'
    calc w'.valuation E' (ε - 1) * w'.valuation E' (z - 1)
        ≤ WithZero.exp (-(n : ℤ)) * WithZero.exp m := by
          rw [hm, WithZero.exp_log hz1]; exact mul_le_mul' hw'ε le_rfl
      _ = WithZero.exp (-(n : ℤ) + m) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp (-(K₀ : ℤ)) := by
          rw [WithZero.exp_le_exp]; omega
  have hall : ∀ w'' : HeightOneSpectrum (𝓞 E'), w''.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = w.asIdeal →
      w''.valuation E' (y - 1) ≤ WithZero.exp (-(M₁ : ℤ)) := by
    intro w'' h1
    by_cases h2 : w'' = w'
    · subst h2
      exact hw'y.trans (WithZero.exp_le_exp.2 (by omega))
    rw [hy1, map_mul]
    have hi := GlobalTheory.T.valuation_le_one_of_sq_sub_self_integral_basis E E' b hb' w w'' h1 ε hε1
    have h1e : w''.valuation E' (1 - ε) ≤ 1 :=
      (Valuation.map_sub _ _ _).trans (max_le (by simp) hi)
    calc w''.valuation E' (1 - ε) * w''.valuation E' (z - 1) ≤ 1 * WithZero.exp (-(M₁ : ℤ)) :=
          mul_le_mul' h1e (hz w'' h1 h2)
      _ = _ := one_mul _
  have hN := hM₁ y hall
  have hσy : Valued.v (σ y - 1) ≤ WithZero.exp (-(K₀ : ℤ)) := by
    rw [← map_one σ, ← map_sub, hv]; exact hw'y
  have hσy1 : Valued.v (σ y) = 1 := by
    have hlt : Valued.v (σ y - 1) < Valued.v (1 : K) := by
      rw [map_one]
      refine hσy.trans_lt ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    rw [Valuation.map_eq_of_sub_lt _ hlt, map_one]
  have hσy0 : σ y ≠ 0 := fun h => by rw [h, map_zero] at hσy1; exact zero_ne_one hσy1
  have hy0 : y ≠ 0 := fun h => hσy0 (by rw [h, map_zero])
  have hry : Valued.v (algebraMap E K (Algebra.norm E y) / σ y - 1) ≤ WithZero.exp (-(M : ℤ)) := by
    rw [div_sub_one hσy0, map_div₀, hσy1, div_one]
    have : algebraMap E K (Algebra.norm E y) - σ y =
        (algebraMap E K (Algebra.norm E y) - 1) - (σ y - 1) := by ring
    rw [this]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ (hσy.trans (WithZero.exp_le_exp.2 (by omega))))
    rw [← map_one (algebraMap E K), ← map_sub, hvK]; exact hN
  have hid : e + (1 - e) * ((1 : K) ⊗ₜ y) = p + q * ((1 : K) ⊗ₜ ε - e) := by
    have h1 : (1 : K) ⊗ₜ[E] y = (1 : K) ⊗ₜ ε + (1 - (1 : K) ⊗ₜ ε) * Z := by
      have := map_add (Algebra.TensorProduct.includeRight (R := E) (A := K) (B := E')) ε ((1 - ε) * z)
      simp only [Algebra.TensorProduct.includeRight_apply, map_mul, map_sub, map_one] at this
      rw [hy, this]
    rw [h1, hp, hq]
    linear_combination (Z - 1) * hee
  have hbz := hβ z hz0
  have hby : algebraMap E K (Algebra.norm E y) / σ y = Algebra.norm K (p + q * ((1 : K) ⊗ₜ ε - e)) := by
    rw [hβ y hy0, hid]
  rw [hbz]
  have : Algebra.norm K p - 1 = (Algebra.norm K (p + q * ((1 : K) ⊗ₜ ε - e)) - 1) -
      (Algebra.norm K (p + q * ((1 : K) ⊗ₜ ε - e)) - Algebra.norm K p) := by ring
  rw [this]
  refine (Valuation.map_sub _ _ _).trans (max_le (hby ▸ hry) (hε3.trans (WithZero.exp_le_exp.2 ?_)))
  omega

end GlobalTheory.NormCompat.RatioClose
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDivLocalEmbeddingCloseToOneStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_div_localEmbedding_close_to_one : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (σ : E' →+* w.adicCompletion E), (∀ x : E, σ (algebraMap E E' x) = algebraMap E _ x) → (∀ x : E', Valued.v (σ x) = w'.valuation E' x) → ∀ M : ℕ, ∃ M' : ℕ, ∀ z : E', z ≠ 0 → (∀ w'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'), w''.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal → w'' ≠ w' → w''.valuation E' (z - 1) ≤ WithZero.exp (-(M' : ℤ))) → Valued.v (algebraMap E (w.adicCompletion E) (Algebra.norm E z) / σ z - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  first | exact @GlobalTheory.NormCompat.RatioClose.norm_div_close_to_one | exact GlobalTheory.NormCompat.RatioClose.norm_div_close_to_one | (intros; apply GlobalTheory.NormCompat.RatioClose.norm_div_close_to_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCloseToComponentLocalDegreeOne
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.NormCompat.LocalDegOne

theorem valued_algebraMap_eq {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
  IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

theorem mul_sub_one_le {R : Type} [CommRing R] (v : Valuation R (WithZero (Multiplicative ℤ))) (a b : R) (M : ℕ)
    (ha : v (a - 1) ≤ WithZero.exp (-(M : ℤ))) (hb : v (b - 1) ≤ WithZero.exp (-(M : ℤ))) :
    v (a * b - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  have e : a * b - 1 = (a - 1) * (b - 1) + ((a - 1) + (b - 1)) := by ring
  have h1 : WithZero.exp (-(M : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  rw [e]
  refine (v.map_add _ _).trans (max_le ?_ ((v.map_add _ _).trans (max_le ha hb)))
  rw [v.map_mul]
  calc v (a - 1) * v (b - 1) ≤ WithZero.exp (-(M : ℤ)) * 1 := mul_le_mul' ha (hb.trans h1)
    _ = _ := mul_one _

theorem norm_div_close_to_one : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) → ∀ M : ℕ, ∃ M' : ℕ, ∀ (c : E) (z : E'), c ≠ 0 → (∀ w'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'), w''.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal → w'' ≠ w' → w''.valuation E' (z - 1) ≤ WithZero.exp (-(M' : ℤ))) → w'.valuation E' (z / algebraMap E E' c - 1) ≤ WithZero.exp (-(M' : ℤ)) → w.valuation E (Algebra.norm E z / c - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  intro E E' _ _ _ _ _ w w' i hi hcomp M
  set σ : E' →+* w.adicCompletion E := (i.symm : w'.adicCompletion E' →+* w.adicCompletion E).comp (algebraMap E' (w'.adicCompletion E')) with hσ
  have hσE : ∀ x : E, σ (algebraMap E E' x) = algebraMap E _ x := fun x => by
    simp only [hσ, RingHom.comp_apply, RingEquiv.coe_toRingHom, ← hcomp x, RingEquiv.symm_apply_apply]
  have hσv : ∀ x : E', Valued.v (σ x) = w'.valuation E' x := fun x => by
    rw [← GlobalTheory.T.valued_map_eq_of_continuous_completionIso_extending E E' w w' i hi hcomp (σ x)]
    simp only [hσ, RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    exact valued_algebraMap_eq w' x
  obtain ⟨M₁, hM₁⟩ := GlobalTheory.T.norm_div_localEmbedding_close_to_one E E' w w' σ hσE hσv M
  refine ⟨max (max M M₁) 1, fun c z hc hz hzw => ?_⟩
  have hle : ∀ k, k ≤ max (max M M₁) 1 → WithZero.exp (-((max (max M M₁) 1 : ℕ) : ℤ)) ≤ WithZero.exp (-(k : ℤ)) := fun k hk => by
    rw [WithZero.exp_le_exp]; omega
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_div, zero_sub, Valuation.map_neg, Valuation.map_one] at hzw
    have := hzw.trans (hle 1 (le_max_right _ _))
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at this
    omega
  have hF := hM₁ z hz0 fun w'' h1 h2 => (hz w'' h1 h2).trans (hle M₁ (by omega))
  have hσz : σ z ≠ 0 := (map_ne_zero σ).2 hz0
  have hcE : algebraMap E (w.adicCompletion E) c ≠ 0 := (map_ne_zero _).2 hc
  have h2 : Valued.v (σ z / algebraMap E (w.adicCompletion E) c - 1) ≤ WithZero.exp (-(M : ℤ)) := by
    have e : σ z / algebraMap E (w.adicCompletion E) c - 1 = σ (z / algebraMap E E' c - 1) := by
      rw [map_sub, map_div₀, hσE, map_one]
    rw [e, hσv]
    exact hzw.trans (hle M (by omega))
  rw [← valued_algebraMap_eq, map_sub, map_div₀, map_one]
  have e2 : algebraMap E (w.adicCompletion E) (Algebra.norm E z) / algebraMap E (w.adicCompletion E) c =
      (algebraMap E (w.adicCompletion E) (Algebra.norm E z) / σ z) * (σ z / algebraMap E (w.adicCompletion E) c) := by
    field_simp
  rw [e2]
  exact mul_sub_one_le Valued.v _ _ M hF h2

end GlobalTheory.NormCompat.LocalDegOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCloseToComponentLocalDegreeOneStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_close_to_component_localDegreeOne : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) → ∀ M : ℕ, ∃ M' : ℕ, ∀ (c : E) (z : E'), c ≠ 0 → (∀ w'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'), w''.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal → w'' ≠ w' → w''.valuation E' (z - 1) ≤ WithZero.exp (-(M' : ℤ))) → w'.valuation E' (z / algebraMap E E' c - 1) ≤ WithZero.exp (-(M' : ℤ)) → w.valuation E (Algebra.norm E z / c - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  first | exact @GlobalTheory.NormCompat.LocalDegOne.norm_div_close_to_one | exact GlobalTheory.NormCompat.LocalDegOne.norm_div_close_to_one | (intros; apply GlobalTheory.NormCompat.LocalDegOne.norm_div_close_to_one <;> assumption)
end
