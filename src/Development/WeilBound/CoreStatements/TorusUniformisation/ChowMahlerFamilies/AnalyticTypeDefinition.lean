module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingOpenImmersion
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieMultIffExistsFrame

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KahlerFormsOverSubalgebraClosureProperties
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RootMulComplexConjEqOne
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ZarhinBundleKernelSecondCoordEquations
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem root_of_unity_eq_one_of_dvd_sub_one :
    ∀ (E : Type) [Field E] [NumberField E] (u : 𝓞 E) (n M : ℕ),
      0 < n → u ^ n = 1 → 3 ≤ M → (M : 𝓞 E) ∣ u - 1 → u = 1 := by
  intro E _ _ u n M hn hu hM ⟨x, hx⟩
  have hlt : ∀ φ : E →+* ℂ, ‖φ (x : E)‖ < 1 := by
    intro φ
    have h1 : (φ (u : E)) ^ n = 1 := by
      have := congrArg (fun y : 𝓞 E => φ (y : E)) hu
      simpa using this
    have h2 : ‖φ (u : E)‖ = 1 := by
      have := congrArg norm h1
      rw [norm_pow, norm_one] at this
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
    have h3 : φ (u : E) - 1 = (M : ℂ) * φ (x : E) := by
      have := congrArg (fun y : 𝓞 E => φ (y : E)) hx
      simpa using this
    have h4 : (M : ℝ) * ‖φ (x : E)‖ ≤ 2 := by
      have h5 := norm_sub_le (φ (u : E)) 1
      rw [h3, norm_mul, h2, norm_one, Complex.norm_natCast] at h5
      linarith
    have h6 : (3 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith [norm_nonneg (φ (x : E))]
  by_contra hne
  have hx0 : (x : E) ≠ 0 := by
    intro h0
    have : x = 0 := by exact_mod_cast h0
    rw [this, mul_zero, sub_eq_zero] at hx
    exact hne hx
  obtain ⟨k, hk, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one E ℂ hx0
    (RingOfIntegers.isIntegral_coe x) (fun φ => (hlt φ).le)
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h7 := congrArg (fun y : E => ‖φ y‖) hpow
  simp only [map_pow, norm_pow, map_one, norm_one] at h7
  have h8 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 h7
  exact (hlt φ).ne h8

end GlobalTheory.CompanionTheory.Ar.Flat
end

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem root_mul_complexConj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E]
    (x : E) (n : ℕ) (hn : 0 < n) (hx : x ^ n = 1) : x * IsCMField.complexConj E x = 1 := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  have h1 : ‖φ x‖ = 1 := by
    have h : ‖φ x‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, hx, map_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h
  rw [map_mul, IsCMField.complexEmbedding_complexConj, map_one, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, h1]
  simp

theorem root_eq_one_of_halfLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → ∀ (I : Ideal (𝓞 E)) (M : ℕ), 3 ≤ M → I * I.map (bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(M : 𝓞 E)} → I ⊔ I.map (bar : 𝓞 E →+* 𝓞 E) = ⊤ → ∀ (u : 𝓞 E) (n : ℕ), 0 < n → u ^ n = 1 → u - 1 ∈ I → u = 1 := by
  intro E _ _ _ bar hbar I M hM hI hco u n hn hu h1
  have hub : u * bar u = 1 := by
    apply RingOfIntegers.ext
    have hx : (u : E) ^ n = 1 := by
      have := congrArg (fun a : 𝓞 E => (a : E)) hu
      simpa using this
    have := root_mul_complexConj_eq_one (u : E) n hn hx
    rw [← hbar] at this
    simpa using this
  have h2 : bar u - 1 ∈ I.map (bar : 𝓞 E →+* 𝓞 E) := by
    have := Ideal.mem_map_of_mem (bar : 𝓞 E →+* 𝓞 E) h1
    simpa using this
  have h3 : u - 1 ∈ I.map (bar : 𝓞 E →+* 𝓞 E) := by
    have e : u - 1 = (-u) * (bar u - 1) := by linear_combination hub
    rw [e]
    exact Ideal.mul_mem_left _ _ h2
  have h4 : u - 1 ∈ Ideal.span {(M : 𝓞 E)} := by
    rw [← hI, Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.2 hco)]
    exact ⟨h1, h3⟩
  exact GlobalTheory.CompanionTheory.Ar.Flat.root_of_unity_eq_one_of_dvd_sub_one E u n M hn hu hM (Ideal.mem_span_singleton.1 h4)

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowEqOneOfIsIntegralOfMulComplexConjEqOne
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem pow_eq_one_of_isIntegral_of_mul_complexConj_eq_one :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (u : E), IsIntegral ℤ u →
      u * IsCMField.complexConj E u = 1 → ∃ n : ℕ, 0 < n ∧ u ^ n = 1 := by
  intro E _ _ _ u hu h
  have hn : ∀ s : E →+* ℂ, ‖s u‖ = 1 := by
    intro s
    have h1 : s u * (starRingEnd ℂ) (s u) = 1 := by
      rw [← IsCMField.complexEmbedding_complexConj, ← map_mul, h, map_one]
    have h2 : ‖s u‖ ^ 2 = 1 := by
      have := congrArg norm h1
      rw [norm_mul, Complex.norm_conj, norm_one] at this
      rw [sq, this]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  obtain ⟨n, hn0, hn1⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ hu hn
  exact ⟨n, hn0, hn1⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DetMulMapDetEqOneOfSesq
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem det_mul_map_det_eq_one_of_sesq {E : Type*} [Field E] {V : Type*} [AddCommGroup V]
    [Module E V] [FiniteDimensional E V] (σ : E →+* E) (H : V →ₗ[E] V →ₛₗ[σ] E)
    (hH : ∀ x, (∀ y, H x y = 0) → x = 0) (g : V →ₗ[E] V)
    (hg : ∀ x y, H (g x) (g y) = H x y) :
    LinearMap.det g * σ (LinearMap.det g) = 1 := by
  classical
  let b := Module.finBasis E V
  let S : Matrix _ _ E := Matrix.of fun i j => H (b i) (b j)
  let G := LinearMap.toMatrix b b g
  have hgb : ∀ j, g (b j) = ∑ i, G i j • b i := by
    intro j
    simp only [G, LinearMap.toMatrix_apply]
    exact (b.sum_repr (g (b j))).symm
  have hS : G.transpose * S * σ.mapMatrix G = S := by
    ext i j
    have h1 : S i j = H (g (b i)) (g (b j)) := (hg _ _).symm
    rw [h1, hgb, hgb]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      LinearMap.map_smulₛₗ, smul_eq_mul, S, Matrix.of_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
  have hdet : S.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hvS⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hv
    have hx : ∑ i, v i • b i = 0 := by
      apply hH
      have : H (∑ i, v i • b i) = 0 := by
        apply b.ext
        intro j
        have := congrFun hvS j
        set_option synthInstance.maxHeartbeats 100000 in
          simpa [Matrix.vecMul, dotProduct, S, map_sum, LinearMap.sum_apply] using this
      intro y
      rw [this]; rfl
    funext i
    exact Fintype.linearIndependent_iff.mp b.linearIndependent v hx i
  have hd := congrArg Matrix.det hS
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det] at hd
  have hG : G.det = LinearMap.det g := LinearMap.det_toMatrix b g
  rw [hG] at hd
  apply mul_left_cancel₀ hdet
  linear_combination hd

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DetOneAddCompCommField
open NumberField TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem det_one_add_comp_comm_field {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K V] [Module.Finite K W]
    (A : V →ₗ[K] W) (B : W →ₗ[K] V) :
    LinearMap.det (1 + A ∘ₗ B) = LinearMap.det (1 + B ∘ₗ A) := by
  classical
  let bV := Module.finBasis K V
  let bW := Module.finBasis K W
  rw [← LinearMap.det_toMatrix bW, ← LinearMap.det_toMatrix bV, map_add (f := _), map_add (f := _),
    LinearMap.toMatrix_comp bW bV bW, LinearMap.toMatrix_comp bV bW bV,
    LinearMap.toMatrix_one, LinearMap.toMatrix_one, Matrix.det_one_add_mul_comm]

theorem exists_det_congr_one : ∀ (E : Type) [Field E] [NumberField E] (La : Type) [AddCommGroup La] [Module (𝓞 E) La] [Module.Finite (𝓞 E) La] [Module.Projective (𝓞 E) La] (I : Ideal (𝓞 E)) (g : La →ₗ[𝓞 E] La), (∀ a, g a - a ∈ I • (⊤ : Submodule (𝓞 E) La)) → ∃ u : 𝓞 E, u - 1 ∈ I ∧ (u : E) = LinearMap.det (g.baseChange E) := by
  intro E _ _ La _ _ _ _ I g hg
  classical
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) La
  set N : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → 𝓞 E) := i ∘ₗ ((g - 1) ∘ₗ p) with hN
  have key : ∀ (x : La), x ∈ I • (⊤ : Submodule (𝓞 E) La) → ∀ k, i x k ∈ I := by
    intro x hx k
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y _
      rw [map_smul, Pi.smul_apply, smul_eq_mul]
      exact I.mul_mem_right _ hr
    · intro x y hx hy
      rw [map_add (f := _), Pi.add_apply]
      exact I.add_mem hx hy
  refine ⟨LinearMap.det (1 + N), ?_, ?_⟩
  · rw [← Ideal.Quotient.eq, ← LinearMap.det_toMatrix', RingHom.map_det, map_one]
    have : (Ideal.Quotient.mk I).mapMatrix (LinearMap.toMatrix' (1 + N)) = 1 := by
      rw [map_add (f := _), map_add (f := _), LinearMap.toMatrix'_one, map_one, add_eq_left]
      ext a b
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
        LinearMap.toMatrix'_apply]
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact key _ (hg _) _
    rw [this, Matrix.det_one]
  · have h1 : ((LinearMap.det (1 + N) : 𝓞 E) : E) = LinearMap.det ((1 + N).baseChange E) :=
      (LinearMap.det_baseChange (A := E) (1 + N)).symm
    rw [h1, LinearMap.baseChange_add, LinearMap.baseChange_one, hN, LinearMap.baseChange_comp,
      det_one_add_comp_comm_field, ← LinearMap.baseChange_comp, LinearMap.comp_assoc, hpi,
      LinearMap.comp_id, LinearMap.baseChange_sub, LinearMap.baseChange_one, add_sub_cancel]

end GlobalTheory.CompanionTheory.Ar.Flat
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem perDet_trace_mul_ext {E : Type} [Field E] [NumberField E] (u v : E)
    (h : ∀ a : 𝓞 E, Algebra.trace ℚ E (u * a) = Algebra.trace ℚ E (v * a)) : u = v := by
  have hnd := traceForm_nondegenerate ℚ E
  apply ((Algebra.traceForm ℚ E).toDual hnd).injective
  apply (integralBasis E).ext
  intro i
  simpa [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply, integralBasis_apply] using
    h (RingOfIntegers.basis E i)

theorem perDet_exists_herm {E : Type} [Field E] [NumberField E] {La : Type} [AddCommGroup La]
    [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La) (x y : La) :
    ∃ u : E, ∀ a : 𝓞 E, Algebra.trace ℚ E (u * a) = ((EF (a • x) y : ℤ) : ℚ) := by
  have hnd := traceForm_nondegenerate ℚ E
  let f : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ
    (fun i => ((EF (RingOfIntegers.basis E i • x) y : ℤ) : ℚ))
  obtain ⟨u, hu⟩ := ((Algebra.traceForm ℚ E).toDual hnd).surjective f
  refine ⟨u, fun a => ?_⟩
  have h1 : Algebra.trace ℚ E (u * a) = f a := by
    have := LinearMap.congr_fun hu (a : E)
    simpa [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] using this
  rw [h1]
  let L1 : 𝓞 E →ₗ[ℤ] ℚ := AddMonoidHom.toIntLinearMap
    (f.toAddMonoidHom.comp (algebraMap (𝓞 E) E).toAddMonoidHom)
  let L2 : 𝓞 E →ₗ[ℤ] ℚ := AddMonoidHom.toIntLinearMap
    { toFun := fun a => ((EF (a • x) y : ℤ) : ℚ)
      map_zero' := by simp
      map_add' := fun a b => by simp [add_smul] }
  have hL : L1 = L2 := by
    apply (RingOfIntegers.basis E).ext
    intro i
    have hb : (algebraMap (𝓞 E) E) (RingOfIntegers.basis E i) = integralBasis E i :=
      (integralBasis_apply E i).symm
    change f (algebraMap (𝓞 E) E (RingOfIntegers.basis E i)) = _
    rw [hb]
    exact (integralBasis E).constr_basis ℚ _ i
  exact LinearMap.congr_fun hL a

theorem perDet_exists_clear {E : Type} [Field E] [NumberField E] {La : Type} [AddCommGroup La]
    [Module (𝓞 E) La] (v : E ⊗[𝓞 E] La) :
    ∃ (c : 𝓞 E) (x : La), c ≠ 0 ∧ ((c : E)) • v = (1 : E) ⊗ₜ[𝓞 E] x := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul e x =>
    obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
    have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
    have hcE : (algebraMap (𝓞 E) E c) ≠ 0 := by simpa using hc0
    refine ⟨c, b • x, hc0, ?_⟩
    rw [TensorProduct.smul_tmul', TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      smul_eq_mul, Algebra.smul_def (A := E) b (1 : E)]
    congr 1
    change algebraMap (𝓞 E) E c * _ = _
    field_simp
  | add v w hv hw =>
    obtain ⟨c, x, hc, hx⟩ := hv
    obtain ⟨d, y, hd, hy⟩ := hw
    refine ⟨c * d, d • x + c • y, mul_ne_zero hc hd, ?_⟩
    have hsm : ∀ (r : 𝓞 E) (t : La), (1 : E) ⊗ₜ[𝓞 E] (r • t) = ((r : E)) • ((1 : E) ⊗ₜ[𝓞 E] t) := by
      intro r t
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
        smul_eq_mul, _root_.mul_one, Algebra.smul_def, _root_.mul_one]
    rw [TensorProduct.tmul_add, hsm, hsm, ← hx, ← hy, smul_add, smul_smul, smul_smul]
    push_cast
    congr 2 <;> ring_nf

theorem perDet_det_mul_conj {E : Type} [Field E] [NumberField E] [IsCMField E]
    (bar : 𝓞 E ≃+* 𝓞 E)
    (hbar : ∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E))
    {La : Type} [AddCommGroup La] [Module (𝓞 E) La] [Module.Finite (𝓞 E) La]
    (EF : LinearMap.BilinForm ℤ La) (hinj : Function.Injective EF)
    (adj : ∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (bar a • y))
    (g : La →ₗ[𝓞 E] La) (hg : ∀ a b, EF (g a) (g b) = EF a b) :
    LinearMap.det (g.baseChange E) * IsCMField.complexConj E (LinearMap.det (g.baseChange E)) = 1 := by
  classical
  choose h hh using perDet_exists_herm (E := E) EF
  let σ : E →+* E := (IsCMField.complexConj E : E →+* E)
  have hσ : ∀ c : 𝓞 E, σ (c : E) = ((bar c : 𝓞 E) : E) := fun c => (hbar c).symm
  have hbb : ∀ c : 𝓞 E, bar (bar c) = c := by
    intro c
    apply RingOfIntegers.ext
    rw [hbar, hbar]
    exact IsCMField.complexConj_apply_apply E _
  have h_add_l : ∀ x x' y, h (x + x') y = h x y + h x' y := fun x x' y =>
    perDet_trace_mul_ext _ _ fun a => by
      rw [add_mul, map_add (f := _), hh, hh, hh, smul_add, map_add (f := _), LinearMap.add_apply]
      push_cast
      rfl
  have h_add_r : ∀ x y y', h x (y + y') = h x y + h x y' := fun x y y' =>
    perDet_trace_mul_ext _ _ fun a => by
      rw [add_mul, map_add (f := _), hh, hh, hh, map_add (f := _)]
      push_cast
      rfl
  have h_smul_l : ∀ (c : 𝓞 E) x y, h (c • x) y = (c : E) * h x y := fun c x y =>
    perDet_trace_mul_ext _ _ fun a => by
      have e1 : (c : E) * h x y * (a : E) = h x y * ((a * c : 𝓞 E) : E) := by
        push_cast; ring
      rw [e1, hh, hh, smul_smul]
  have h_smul_r : ∀ (c : 𝓞 E) x y, h x (c • y) = σ (c : E) * h x y := fun c x y =>
    perDet_trace_mul_ext _ _ fun a => by
      have e1 : σ (c : E) * h x y * (a : E) = h x y * ((bar c * a : 𝓞 E) : E) := by
        rw [hσ]; push_cast; ring
      rw [e1, hh, hh, ← smul_smul, adj (bar c), hbb]
  have h_iso : ∀ x y, h (g x) (g y) = h x y := fun x y =>
    perDet_trace_mul_ext _ _ fun a => by
      rw [hh, hh, ← map_smul, hg]
  let f : La → (La →ₗ[𝓞 E] E) := fun y =>
    { toFun := fun x => h x y
      map_add' := fun x x' => h_add_l x x' y
      map_smul' := fun c x => by
        rw [h_smul_l, RingHom.id_apply, Algebra.smul_def] }
  let F : La → ((E ⊗[𝓞 E] La) →ₗ[E] E) := fun y => LinearMap.liftBaseChange E (f y)
  have F_tmul : ∀ y (e : E) x, F y (e ⊗ₜ[𝓞 E] x) = e * h x y := by
    intro y e x
    simp only [F, LinearMap.liftBaseChange_tmul, smul_eq_mul]
    rfl
  have F_add : ∀ y y', F (y + y') = F y + F y' := by
    intro y y'
    apply LinearMap.ext
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul e x => rw [LinearMap.add_apply, F_tmul, F_tmul, F_tmul, h_add_r, mul_add]
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _), ha, hb]
  have F_smul : ∀ (c : 𝓞 E) y, F (c • y) = σ (c : E) • F y := by
    intro c y
    apply LinearMap.ext
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul e x =>
      rw [LinearMap.smul_apply, F_tmul, F_tmul, h_smul_r, smul_eq_mul]
      ring
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _), ha, hb]
  let f0 : E →+ La →+ ((E ⊗[𝓞 E] La) →ₗ[E] E) := AddMonoidHom.mk'
    (fun e => AddMonoidHom.mk' (fun y => σ e • F y) (fun y y' => by rw [F_add, smul_add]))
    (fun e e' => by
      ext y : 1
      simp [add_smul])
  let G : (E ⊗[𝓞 E] La) →+ ((E ⊗[𝓞 E] La) →ₗ[E] E) := TensorProduct.liftAddHom f0
    (fun r e y => by
      change σ (r • e) • F y = σ e • F (r • y)
      rw [F_smul, smul_smul, Algebra.smul_def, map_mul, _root_.mul_comm])
  have G_tmul : ∀ (e : E) y, G (e ⊗ₜ[𝓞 E] y) = σ e • F y := fun e y => rfl
  have G_smul : ∀ (c : E) w, G (c • w) = σ c • G w := by
    intro c w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul e y =>
      rw [TensorProduct.smul_tmul', G_tmul, G_tmul, smul_eq_mul, map_mul, smul_smul]
    | add a b ha hb => rw [smul_add, map_add (f := _), map_add (f := _), ha, hb, smul_add]
  let Hf : (E ⊗[𝓞 E] La) →ₗ[E] (E ⊗[𝓞 E] La) →ₛₗ[σ] E :=
    LinearMap.mk₂'ₛₗ (RingHom.id E) σ (fun v w => G w v)
      (fun v v' w => map_add _ _ _)
      (fun c v w => by rw [map_smul]; rfl)
      (fun v w w' => by rw [map_add (f := _), LinearMap.add_apply])
      (fun c v w => by rw [G_smul, LinearMap.smul_apply])
  have hHf : ∀ v w, Hf v w = G w v := fun _ _ => rfl
  have hnd : ∀ v, (∀ w, Hf v w = 0) → v = 0 := by
    intro v hv
    obtain ⟨c, x, hc, hx⟩ := perDet_exists_clear v
    have hcE : (c : E) ≠ 0 := by simpa using hc
    have h0 : ∀ y, h x y = 0 := by
      intro y
      have h1 := hv ((1 : E) ⊗ₜ[𝓞 E] y)
      rw [hHf, G_tmul, map_one, one_smul] at h1
      have h2 : F y ((c : E) • v) = 0 := by rw [map_smul, h1, smul_zero]
      rw [hx, F_tmul, _root_.one_mul] at h2
      exact h2
    have hx0 : x = 0 := by
      apply hinj
      rw [map_zero]
      ext y
      have h3 := hh x y 1
      rw [h0 y] at h3
      simpa using h3.symm
    rw [hx0, TensorProduct.tmul_zero] at hx
    exact (smul_eq_zero.1 hx).resolve_left hcE
  have hiso : ∀ v w, Hf (g.baseChange E v) (g.baseChange E w) = Hf v w := by
    intro v w
    rw [hHf, hHf]
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, ha, hb]
    | tmul e y =>
      rw [LinearMap.baseChange_tmul, G_tmul, G_tmul, LinearMap.smul_apply, LinearMap.smul_apply]
      congr 1
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
      | tmul e' x => rw [LinearMap.baseChange_tmul, F_tmul, F_tmul, h_iso]
  exact det_mul_map_det_eq_one_of_sesq σ Hf hnd (g.baseChange E) hiso

theorem per_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (gam : D.La ≃ₗ[𝓞 E] D.La), (∀ a b, D.EF (gam a) (gam b) = D.EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gam a = a + l.M • e) → LinearMap.det ((gam : D.La →ₗ[𝓞 E] D.La).baseChange E) = 1 := by
  intro E _ _ _ H D l gam hiso hlev
  haveI := D.fin
  haveI := D.proj
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.mem_span_singleton_self _
    rw [← l.prod] at h1
    have h2 : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb := Ideal.mul_le_left
    exact h2 h1
  have h1mem : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.coprime]; exact Submodule.mem_top
  obtain ⟨m', hm', m, hm, hmm⟩ := Submodule.mem_sup.1 h1mem
  have hcong : ∀ a, (gam : D.La →ₗ[𝓞 E] D.La) a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
    intro a
    obtain ⟨e, he⟩ := hlev (m • a) (Submodule.smul_mem_smul hm Submodule.mem_top)
    have h1 : m • gam a = m • a + ((l.M : ℕ) : 𝓞 E) • e := by
      rw [← map_smul, he, Nat.cast_smul_eq_nsmul]
    have h3 : gam a - a = m' • (gam a - a) + m • (gam a - a) := by
      rw [← add_smul, hmm, one_smul]
    have h4 : m • (gam a - a) = ((l.M : ℕ) : 𝓞 E) • e := by
      rw [smul_sub, h1, add_sub_cancel_left]
    rw [h4] at h3
    change gam a - a ∈ _
    rw [h3]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul hm' Submodule.mem_top)
      (Submodule.smul_mem_smul hM Submodule.mem_top)
  obtain ⟨u, hu1, hu2⟩ := exists_det_congr_one E D.La l.Mb (gam : D.La →ₗ[𝓞 E] D.La) hcong
  have hdet := perDet_det_mul_conj H.bar H.bar_eq D.EF D.unimod.1 D.adj
    (gam : D.La →ₗ[𝓞 E] D.La) hiso
  rw [← hu2] at hdet ⊢
  obtain ⟨n, hn, hun⟩ := pow_eq_one_of_isIntegral_of_mul_complexConj_eq_one E (u : E)
    (RingOfIntegers.isIntegral_coe u) hdet
  have hun' : u ^ n = 1 := RingOfIntegers.ext (by simpa using hun)
  have hu : u = 1 := root_eq_one_of_halfLevel E H.bar H.bar_eq l.Mb l.M l.three_le l.prod l.coprime
    u n hn hun' hu1
  rw [hu]
  simp

end GlobalTheory.CompanionTheory.Ar.Flat
end

section
open NumberField Matrix
open scoped TensorProduct

namespace PositivityTheory.Xgn.AnalyticTypeDefinition

theorem exists_matrix {E : Type} [Field E] [NumberField E] {La : Type} [AddCommGroup La] [Module (𝓞 E) La]
    [Module.Finite (𝓞 E) La] [Module.Projective (𝓞 E) La] {I : Type} [Fintype I] [DecidableEq I] (e : I → La)
    (he : LinearIndependent (𝓞 E) e) (hc : Fintype.card I = Module.finrank (𝓞 E) La) (gam : La →ₗ[𝓞 E] La) :
    ∃ A : Matrix I I E, A.det = LinearMap.det (gam.baseChange E) ∧
      ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (τ : E →+* ℂ) (φ : La →+ M),
        (∀ (a : 𝓞 E) x, φ (a • x) = τ (a : E) • φ x) → ∀ m, φ (gam (e m)) = ∑ n, τ (A m n) • φ (e n) := by
  let j : La →ₗ[𝓞 E] E ⊗[𝓞 E] La := TensorProduct.mk (𝓞 E) E La 1
  haveI : IsLocalizedModule (nonZeroDivisors (𝓞 E)) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (𝓞 E)) E j).2 (TensorProduct.isBaseChange _ _ _)
  have hli : LinearIndependent E (j ∘ e) := he.of_isLocalizedModule E (nonZeroDivisors (𝓞 E)) j
  have hr : Fintype.card I = Module.finrank E (E ⊗[𝓞 E] La) := by
    rw [hc]
    exact ((TensorProduct.isBaseChange (𝓞 E) La E).finrank_eq).symm
  haveI : FiniteDimensional E (E ⊗[𝓞 E] La) := inferInstance
  let b : Module.Basis I E (E ⊗[𝓞 E] La) := basisOfLinearIndependentOfCardEqFinrank' _ hli hr
  have hb : ∀ n, b n = j (e n) := fun n => by simp [b]
  refine ⟨(LinearMap.toMatrix b b (gam.baseChange E))ᵀ, by rw [det_transpose, LinearMap.det_toMatrix], ?_⟩
  intro M _ _ τ φ hφ m
  have h1 : j (gam (e m)) = ∑ n, (LinearMap.toMatrix b b (gam.baseChange E)) n m • j (e n) := by
    have := (b.sum_repr (gam.baseChange E (b m))).symm
    simp only [LinearMap.toMatrix_apply, ← hb]
    rw [← this, hb]
    rfl
  obtain ⟨N, hN⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E))
    (fun n => (LinearMap.toMatrix b b (gam.baseChange E)) n m)
  choose a ha using hN
  have h2 : j ((N : 𝓞 E) • gam (e m)) = j (∑ n, a n • e n) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, h1, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_smul, ← smul_assoc, ← ha n, algebraMap_smul]
  obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors (𝓞 E)) (f := j) h2
  have h3 := congrArg φ hs
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Submonoid.smul_def, hφ, map_sum] at h3
  have hs0 : τ ((s : 𝓞 E) : E) ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero s.2
  have hN0 : τ ((N : 𝓞 E) : E) ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero N.2
  have h4 := smul_right_injective M hs0 h3
  apply smul_right_injective M hN0
  simp only []
  rw [h4, Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smul_smul, ← map_mul, transpose_apply]
  congr 2
  exact (ha n).trans (Algebra.smul_def _ _)

theorem change_basis {p q g : ℕ} (T T' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (V : Fin p → Fin g → ℂ)
    (W : Fin q → Fin g → ℂ) (πe πf : Fin p ⊕ Fin q → Fin g → ℂ)
    (Se Sf A A' : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (hA : A.det = 1) (hA' : A'.det = 1)
    (h1 : ∀ m, T (πf m) = ∑ n, A m n • T (πe n)) (h2 : ∀ m, T' (πf m) = ∑ n, A' m n • T' (πe n))
    (hS : Sf = A * Se * A'ᵀ) (C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ) (Fm B : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ)
    (hC : ∀ a, T (∑ m, C a m • πf m) = V a) (hB : ∀ n, T' (πf n) = ∑ j, B j n • W j)
    (hF : ∀ j n, ∑ m, Fm j m * Sf m n = B j n) :
    ∃ (C' : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ) (Fm' B' : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ),
      (∀ a, T (∑ m, C' a m • πe m) = V a) ∧ (∀ n, T' (πe n) = ∑ j, B' j n • W j) ∧
      (∀ j n, ∑ m, Fm' j m * Se m n = B' j n) ∧ (Matrix.fromRows C' Fm').det = (Matrix.fromRows C Fm).det := by
  have hu : IsUnit A'.det := by rw [hA']; exact isUnit_one
  have hu' : IsUnit A'ᵀ.det := by rw [det_transpose]; exact hu
  refine ⟨C * A, Fm * A, B * A'ᵀ⁻¹, fun a => ?_, fun n => ?_, fun j n => ?_, ?_⟩
  · rw [← hC a]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, h1, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  · have e1 : (Matrix.of fun m k => T' (πf m) k) = A' * Matrix.of fun m k => T' (πe m) k := by
      ext m k; simp [h2, Matrix.mul_apply, Finset.sum_apply]
    have e2 : (Matrix.of fun m k => T' (πf m) k) = Bᵀ * Matrix.of W := by
      ext m k; simp [hB, Matrix.mul_apply, Finset.sum_apply]
    have e3 : (Matrix.of fun m k => T' (πe m) k) = (B * A'ᵀ⁻¹)ᵀ * Matrix.of W := by
      rw [transpose_mul, ← transpose_nonsing_inv, transpose_transpose, Matrix.mul_assoc, ← e2, e1,
        ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
    funext k
    have := congrFun (congrFun e3 n) k
    rw [Matrix.mul_apply] at this
    simpa [Finset.sum_apply] using this
  · have e1 : Fm * Sf = B := by ext j n; exact hF j n
    have e2 : Fm * A * Se = B * A'ᵀ⁻¹ := by
      rw [← e1, hS, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hu', Matrix.mul_one]
    exact congrFun (congrFun e2 j) n
  · rw [← fromRows_mul, det_mul, hA, mul_one]

theorem entry_zero {E : Type} [Field E] [NumberField E] {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hh : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k) (j k : Fin g)
    (hjk : ty j ≠ ty k) : h (Pi.single k 1) j = 0 := by
  by_contra h0
  apply hjk
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_)
  have e1 : (fun i => ty i (a : E) * (Pi.single k (1 : ℂ) : Fin g → ℂ) i) = ty k (a : E) • Pi.single k (1 : ℂ) := by
    funext i
    by_cases hi : i = k
    · subst hi; simp
    · simp [hi]
  have := congrFun (hh a (Pi.single k 1)) j
  rw [e1, map_smul] at this
  exact (mul_right_cancel₀ h0 this).symm

end PositivityTheory.Xgn.AnalyticTypeDefinition
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace PositivityTheory.Xgn.AnalyticTypeDefinition

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

noncomputable def tyLin {g : ℕ} (ty : Fin g → (E →+* ℂ)) (τ : E →+* ℂ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun := tyPart ty τ
  map_add' a b := by funext k; simp only [tyPart, Pi.add_apply]; split_ifs <;> simp
  map_smul' a b := by funext k; simp only [tyPart, Pi.smul_apply]; split_ifs <;> simp

theorem tyPart_comm {g : ℕ} (ty : Fin g → (E →+* ℂ)) (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hh : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k) (τ : E →+* ℂ)
    (z : Fin g → ℂ) : tyPart ty τ (h z) = h (tyPart ty τ z) := by
  have : tyLin ty τ ∘ₗ h = h ∘ₗ tyLin ty τ := by
    refine LinearMap.pi_ext' fun k => LinearMap.ext_ring ?_
    show tyPart ty τ (h (Pi.single k 1)) = h (tyPart ty τ (Pi.single k 1))
    by_cases hk : ty k = τ
    · have e1 : tyPart ty τ (Pi.single k (1 : ℂ)) = Pi.single k 1 := by
        funext i
        simp only [tyPart]
        split_ifs with hi
        · rfl
        · rw [Pi.single_eq_of_ne]; rintro rfl; exact hi hk
      rw [e1]
      funext j
      simp only [tyPart]
      split_ifs with hj
      · rfl
      · exact (entry_zero ty h hh j k (by rw [hk]; exact hj)).symm
    · have e1 : tyPart ty τ (Pi.single k (1 : ℂ)) = 0 := by
        funext i
        simp only [tyPart]
        split_ifs with hi
        · rw [Pi.single_eq_of_ne]; · rfl
          rintro rfl; exact hk hi
        · rfl
      rw [e1, map_zero]
      funext j
      simp only [tyPart]
      split_ifs with hj
      · exact entry_zero ty h hh j k (by rw [hj]; exact fun h' => hk h'.symm)
      · rfl
  exact LinearMap.congr_fun this z

theorem comm_of_period (D₁ D₂ : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (P : D₁.La →+ (Fin g → ℂ))
    (P' : D₂.La →+ (Fin g → ℂ)) (hP : IsPeriod D₁ ty P) (hP' : IsPeriod D₂ ty P')
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (gam : D₁.La →ₗ[𝓞 E] D₂.La) (hgam : ∀ a, P' (gam a) = h (P a))
    (a : 𝓞 E) (z : Fin g → ℂ) : h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k := by
  let d : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := LinearMap.pi fun k => ty k (a : E) • LinearMap.proj k
  have : (h ∘ₗ d).restrictScalars ℝ = (d ∘ₗ h).restrictScalars ℝ := by
    refine LinearMap.ext_on_range hP.2.2.2.1 fun x => ?_
    show h (d (P x)) = d (h (P x))
    have e1 : d (P x) = P (a • x) := funext fun i => (hP.1 a x i).symm
    have e2 : d (P' (gam x)) = P' (a • gam x) := funext fun i => (hP'.1 a _ i).symm
    rw [e1, ← hgam, ← hgam, e2, map_smul]
  exact LinearMap.congr_fun this z

theorem deriv_transport {g : ℕ} {X : Scheme.{0}} (e e' : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (he : ∀ z, e' (h z) = e z) (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ X)
    (hv : IsDerivAt0 e w v) : IsDerivAt0 e' (h w) v := by
  refine ⟨by rw [hv.1, ← he, map_zero], fun U hU f => ?_⟩
  rw [hv.2 U hU f]
  have e1 : (fun z => valAt' (e z) U f) = (fun z => valAt' (e' z) U f) ∘ h.toContinuousLinearEquiv := by
    funext z; simp [he]
  rw [e1, ContinuousLinearEquiv.comp_right_fderiv]
  simp

theorem tyPart_smul (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P)
    (τ : E →+* ℂ) (a : 𝓞 E) (x : D.La) : tyPart ty τ (P (a • x)) = τ (a : E) • tyPart ty τ (P x) := by
  funext k
  simp only [tyPart, Pi.smul_apply, hP.1]
  split_ifs with hk
  · rw [hk]; rfl
  · simp

noncomputable def sesqL (D : Datum H) (τ : E →+* ℂ) (y : D.La) : D.La →+ ℂ :=
  AddMonoidHom.mk' (fun x => τ (sesq D x y)) fun x x' => by
    simp [sesq, Finset.sum_add_distrib, add_mul]

noncomputable def sesqR (D : Datum H) (τ : E →+* ℂ) (x : D.La) : D.La →+ ℂ :=
  AddMonoidHom.mk' (fun y => τ (sesq D x y)) fun y y' => by
    simp [sesq, Finset.sum_add_distrib, add_mul]

def Cond (D : Datum H) {g p q : ℕ} (ty : Fin g → (E →+* ℂ)) (τ' : E →+* ℂ) (e : Fin p ⊕ Fin q → D.La)
    (P : D.La →+ (Fin g → ℂ)) (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ)
    (C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ) (Fm B : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ) : Prop :=
  (∀ a, tyPart ty τ' (∑ m, C a m • P (e m)) = V a) ∧
    (∀ n, tyPart ty (ComplexEmbedding.conjugate τ') (P (e n)) = ∑ j, B j n • W j) ∧
    (∀ j n, ∑ m, Fm j m * τ' (sesq D (e m) (e n)) = B j n)

theorem cond_transport (D : Datum H) {g p q : ℕ} (ty : Fin g → (E →+* ℂ)) (τ' : E →+* ℂ) (e : Fin p ⊕ Fin q → D.La)
    (he : LinearIndependent (𝓞 E) e) (hc : p + q = D.p + D.q)
    (P P' : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (hP' : IsPeriod D ty P')
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (gam : D.La →ₗ[𝓞 E] D.La) (hgam : ∀ a, P' (gam a) = h (P a))
    (hiso : ∀ a b, D.EF (gam a) (gam b) = D.EF a b) (hdet : LinearMap.det (gam.baseChange E) = 1)
    (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ)
    (C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ) (Fm B : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ)
    (hC : Cond D ty τ' e P V W C Fm B) :
    ∃ C' Fm' B', Cond D ty τ' e P' (fun a => h (V a)) (fun j => h (W j)) C' Fm' B' ∧
      (Matrix.fromRows C' Fm').det = (Matrix.fromRows C Fm).det := by
  haveI := D.fin
  haveI := D.proj
  obtain ⟨A, hA, hφ⟩ := exists_matrix e he (by rw [D.rank, ← hc]; simp) gam
  rw [hdet] at hA
  have hcomm := tyPart_comm ty h (comm_of_period D D ty P P' hP hP' h gam hgam)
  have hT : ∀ (τ : E →+* ℂ) m, tyLin ty τ (P' (gam (e m))) = ∑ n, (A.map τ) m n • tyLin ty τ (P' (e n)) := fun τ m =>
    hφ _ τ ((tyLin ty τ).toAddMonoidHom.comp P') (tyPart_smul D ty P' hP' τ) m
  have hd : ∀ τ : E →+* ℂ, (A.map τ).det = 1 := fun τ => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hA, map_one]
  have hs : ∀ x y, sesq D (gam x) (gam y) = sesq D x y := fun x y => by
    simp only [sesq, ← map_smul, hiso]
  have hL : ∀ y m, τ' (sesq D (gam (e m)) y) = ∑ n, τ' (A m n) • τ' (sesq D (e n) y) := fun y m =>
    hφ _ τ' (sesqL D τ' y) (fun a x => by
      show τ' (sesq D (a • x) y) = τ' a * τ' (sesq D x y)
      rw [GlobalTheory.CompanionTheory.Ar.Fl.Test.sesq_smul_left, map_mul]) m
  have hR : ∀ x m, τ' (sesq D x (gam (e m))) =
      ∑ n, ComplexEmbedding.conjugate τ' (A m n) • τ' (sesq D x (e n)) := fun x m =>
    hφ _ (ComplexEmbedding.conjugate τ') (sesqR D τ' x) (fun a y => by
      show τ' (sesq D x (a • y)) = ComplexEmbedding.conjugate τ' a * τ' (sesq D x y)
      obtain ⟨b, rfl⟩ := H.bar.surjective a
      rw [GlobalTheory.CompanionTheory.Ar.Fl.Test.sesq_smul_right, map_mul, H.bar_eq]
      congr 1
      show _ = starRingEnd ℂ (τ' _)
      rw [IsCMField.complexEmbedding_complexConj, Complex.conj_conj]) m
  obtain ⟨C', Fm', B', k1, k2, k3, k4⟩ := change_basis (tyLin ty τ') (tyLin ty (ComplexEmbedding.conjugate τ'))
    (fun a => h (V a)) (fun j => h (W j)) (fun m => P' (e m)) (fun m => P' (gam (e m)))
    (Matrix.of fun m n => τ' (sesq D (e m) (e n))) (Matrix.of fun m n => τ' (sesq D (e m) (e n)))
    (A.map τ') (A.map (ComplexEmbedding.conjugate τ')) (hd _) (hd _) (hT _) (hT _)
    (by
      ext m n
      rw [Matrix.of_apply, ← hs, hR, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hL, Matrix.mul_apply, smul_eq_mul, mul_comm]
      rfl) C Fm B
    (fun a => by
      show tyPart ty τ' _ = _
      rw [← hC.1 a, ← hcomm]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hgam, map_sum, map_smul])
    (fun n => by
      show tyPart ty _ _ = _
      rw [hgam, hcomm, hC.2.1]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul])
    hC.2.2
  exact ⟨C', Fm', B', ⟨k1, k2, k3⟩, k4⟩

theorem solve (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
    (hty : IsTypeFn H D.p D.q ty) (hrt : τ' (H.rt : E) = H.rt0) (hτ : ∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E))
    (i : Fin FU.n) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (P : (FU.Di i).La →+ (Fin g → ℂ))
    (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (he : LinearIndependent (𝓞 E) e)
    (hP : IsPeriod (FU.Di i) ty P) (hy : under y = FU.u i P) (hfr : IsFramed Set.univ τ σ y v w) :
    ∃ d : ℂ, d ≠ 0 ∧ ∀ V W C Fm B, (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (V a) (v a).left) →
      (∀ j, IsDerivAt0 (fun z => (FU.ex i P z).left) (W j) (w j).left) →
      Cond (FU.Di i) ty τ' e P V W C Fm B → (Matrix.fromRows C Fm).det = d := by
  obtain ⟨⟨V₀, W₀, F₀, B₀, d⟩, ⟨k1, k2, k3, k4, k5, -, k7⟩, -⟩ :=
    anSolve E H D l Xo c τ τ' σ g ty FU hty hrt hτ i e P y v w he hP hy hfr
  obtain ⟨-, -, hv, hw⟩ := hfr
  have hc : ∀ a : 𝓞 E, (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) a = ComplexEmbedding.conjugate τ' (a : E) := by
    intro a
    have h1 : tauIn c (ComplexEmbedding.conjugate τ) a = tauIn c τ (H.bar a) := by
      apply Subtype.ext
      show ComplexEmbedding.conjugate τ (a : E) = τ ((H.bar a : 𝓞 E) : E)
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
      rfl
    show σ (tauIn c (ComplexEmbedding.conjugate τ) a) = _
    rw [h1, hτ, H.bar_eq, IsCMField.complexEmbedding_complexConj]
    rfl
  obtain ⟨V₁, hVd, -, -⟩ := GlobalTheory.T.period_eigen_frame E H D l Xo _ g ty FU i P (under y) (σ.comp (tauIn c τ)) τ' D.p v hP hy hτ hv
  obtain ⟨W₁, hWd, hWl, -⟩ :=
    GlobalTheory.T.period_eigen_frame E H D l Xo _ g ty FU i P (under y) _ (ComplexEmbedding.conjugate τ') D.q w hP hy hc hw
  obtain ⟨Hm, hHh, -, hHi⟩ := id hP.2.2.2.2
  obtain ⟨-, -, hd⟩ := GlobalTheory.T.period_hermitian_type_compatibility E H (FU.Di i) g ty P Hm hP hHh hHi
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    rw [(FU.sig i).1, (FU.sig i).2]; simp
  have hS : (Matrix.of fun m n => τ' (sesq (FU.Di i) (e m) (e n))).det ≠ 0 := by
    have := hd 0 _ e hcard he
    have h2 : (Matrix.of fun m n => τ' (sesq (FU.Di i) (e m) (e n))) =
      (Matrix.of fun m n => sesq (FU.Di i) (e m) (e n)).map τ' := rfl
    rw [h2, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ').2 this
  refine ⟨d, k5, fun V W C Fm B a1 a2 a3 => ?_⟩
  have eV : V = V₀ := funext fun a => ((hVd a _).1 (a1 a)).trans ((hVd a _).1 (k1 a)).symm
  have eW : W = W₁ := funext fun a => (hWd a _).1 (a2 a)
  have eW₀ : W₀ = W₁ := funext fun a => (hWd a _).1 (k2 a)
  subst eV eW eW₀
  have eB : B = B₀ := by
    ext j n
    exact (Fintype.linearIndependent_iffₛ.1 hWl) (fun j => B j n) (fun j => B₀ j n) ((a3.2.1 n).symm.trans (k3 n)) j
  have eF : Fm = F₀ := by
    have e1 : Fm * (Matrix.of fun m n => τ' (sesq (FU.Di i) (e m) (e n))) =
        F₀ * (Matrix.of fun m n => τ' (sesq (FU.Di i) (e m) (e n))) := by
      ext j n
      exact ((a3.2.2 j n).trans (congrFun (congrFun eB j) n)).trans (k4 j n).symm
    have := congrArg (· * (Matrix.of fun m n => τ' (sesq (FU.Di i) (e m) (e n)))⁻¹) e1
    simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hS), Matrix.mul_one] using this
  rw [eF]
  exact k7 C a3.1

theorem level_of_marking {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) (i : Fin U.n) (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di i).La)
    (hgam : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gam (U.t i a) = U.t i a + l.M • e) :
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (U.Di i).La), ∃ e, gam a = a + l.M • e := by
  intro a ha
  refine Submodule.smul_induction_on ha (fun r hr b _ => ?_) ?_
  · obtain ⟨a', e', rfl⟩ := U.t_surj i b
    obtain ⟨e, he⟩ := hgam (r • a') (Submodule.smul_mem_smul hr Submodule.mem_top)
    obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
    refine ⟨e + k • r • (gam e' - e'), ?_⟩
    rw [smul_add, ← map_smul, map_add (f := _), he, hk, smul_comm r, map_nsmul, map_smul gam, mul_smul, mul_smul, smul_add,
      smul_sub, smul_sub, smul_sub]
    abel
  · rintro x y ⟨e, he⟩ ⟨e', he'⟩
    exact ⟨e + e', by rw [map_add (f := _), he, he', smul_add]; abel⟩

end PositivityTheory.Xgn.AnalyticTypeDefinition

theorem PositivityTheory.Xgn.analytic_type_definition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∀ (e : ∀ i : Fin FU.n, Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : Fin FU.n → ℂ), (∀ i, LinearIndependent (𝓞 E) (e i)) → ∃ Φ : CFn Xo c, ∀ i, IsFlatAn Set.univ τ τ' σ Φ FU i (e i) (ρ i) := by
  intro E _ _ _ H D l Xo c τ τ' σ g ty FU hty hrt hτ e ρ he
  have key : ∀ (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q), ∃ φ : ℂ, ∀ i P V W C Fm B,
      IsPeriod (FU.Di i) ty P → under y = FU.u i P → IsFramed Set.univ τ σ y v w →
      (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (V a) (v a).left) →
      (∀ j, IsDerivAt0 (fun z => (FU.ex i P z).left) (W j) (w j).left) →
      PositivityTheory.Xgn.AnalyticTypeDefinition.Cond (FU.Di i) ty τ' (e i) P V W C Fm B → φ * (Matrix.fromRows C Fm).det = ρ i := by
    intro y v w
    by_cases hex : ∃ i P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P ∧ IsFramed Set.univ τ σ y v w
    · obtain ⟨i₀, P₀, hP₀, hy₀, hfr⟩ := hex
      obtain ⟨d, hd0, hd⟩ := PositivityTheory.Xgn.AnalyticTypeDefinition.solve D l Xo c τ τ' σ g ty FU hty hrt hτ i₀ (e i₀) P₀ y v w
        (he i₀) hP₀ hy₀ hfr
      refine ⟨ρ i₀ / d, fun i P V W C Fm B hP hy _ a1 a2 a3 => ?_⟩
      obtain rfl : i = i₀ := FU.disj i i₀ P P₀ hP hP₀ (hy.symm.trans hy₀)
      obtain ⟨h, gam, b1, b2, b3, b4, -⟩ :=
        GlobalTheory.familyUnif_exp_unique E H D l Xo _ g ty FU i i P P₀ hP hP₀ (hy.symm.trans hy₀)
      have hdet := per_det_one E H (FU.Di i) l gam b3 (PositivityTheory.Xgn.AnalyticTypeDefinition.level_of_marking FU i gam b4)
      obtain ⟨C', Fm', B', k1, k2⟩ := PositivityTheory.Xgn.AnalyticTypeDefinition.cond_transport (FU.Di i) ty τ' (e i) (he i)
        (by rw [(FU.sig i).1, (FU.sig i).2]) P P₀ hP hP₀ h.toLinearMap gam.toLinearMap b2 b3 hdet V W C Fm B a3
      rw [← k2, hd _ _ C' Fm' B'
        (fun a => PositivityTheory.Xgn.AnalyticTypeDefinition.deriv_transport _ _ h b1 _ _ (a1 a))
        (fun j => PositivityTheory.Xgn.AnalyticTypeDefinition.deriv_transport _ _ h b1 _ _ (a2 j)) k1]
      exact div_mul_cancel₀ _ hd0
    · exact ⟨0, fun i P V W C Fm B hP hy hfr _ _ _ => absurd ⟨i, P, hP, hy, hfr⟩ hex⟩
  choose Φ hΦ using key
  exact ⟨Φ, fun i P y v w V W C Fm B h1 h2 h3 h4 h5 h6 h7 h8 => hΦ y v w i P V W C Fm B h1 h2 h3 h4 h5 ⟨h6, h7, h8⟩⟩
