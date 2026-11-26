module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBounded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSumFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivRemCompLe
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralSuperposition
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivTruncExpICompLe
open Filter Topology
open scoped Nat

noncomputable section

namespace GlobalTheory.GaussExpSeries

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_iteratedFDeriv_cexp (i : ℕ) (z : ℂ) : ‖iteratedFDeriv ℝ i Complex.exp z‖ = Real.exp z.re := by
  have hc : ContDiffAt ℂ (i : ℕ) Complex.exp z := Complex.contDiff_exp.contDiffAt
  rw [← hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp]
  rw [ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrFun (iteratedDeriv_cexp_const_mul i 1) z
  simp only [one_mul, one_pow] at h
  rw [h, Complex.norm_exp]

theorem norm_iteratedFDeriv_id_le (j : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ j (id : V → V) x‖ ≤ 1 + ‖x‖ := by
  rcases j with _ | n
  · rw [norm_iteratedFDeriv_zero]; simp
  · rw [← norm_iteratedFDeriv_fderiv,
      show fderiv ℝ (id : V → V) = fun _ => ContinuousLinearMap.id ℝ V from funext fun _ => fderiv_id]
    rcases n with _ | n
    · rw [norm_iteratedFDeriv_zero]
      exact (ContinuousLinearMap.norm_id_le).trans (by linarith [norm_nonneg x])
    · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
      simp only [Pi.zero_apply, norm_zero]
      positivity

theorem norm_iteratedFDeriv_diag_le (B : V →L[ℝ] V →L[ℝ] ℂ) (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y => B y y) x‖ ≤ ‖B‖ * (2 ^ n * (1 + ‖x‖) ^ 2) := by
  have h := B.norm_iteratedFDeriv_le_of_bilinear (f := id) (g := id) (N := (n : WithTop ℕ∞))
    contDiff_id contDiff_id x le_rfl
  simp only [id] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : V => y) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun y : V => y) x‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + ‖x‖) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [mul_assoc, sq]
        gcongr
        · exact norm_iteratedFDeriv_id_le i x
        · exact norm_iteratedFDeriv_id_le (n - i) x
    _ = 2 ^ n * (1 + ‖x‖) ^ 2 := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n

theorem norm_iteratedFDeriv_gauss_le (B : V →L[ℝ] V →L[ℝ] ℂ) (ε : ℝ)
    (hB : ∀ x, (B x x).re ≤ -(ε * ‖x‖ ^ 2)) (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y => Complex.exp (B y y)) x‖ ≤
      n ! * Real.exp (-(ε * ‖x‖ ^ 2)) * (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ n := by
  have hf : ContDiff ℝ ⊤ (fun y => B y y) := B.contDiff.clm_apply contDiff_id
  have hg : ContDiff ℝ ⊤ Complex.exp := Complex.contDiff_exp
  refine norm_iteratedFDeriv_comp_le (g := Complex.exp) (f := fun y => B y y) hg hf
    (by exact_mod_cast le_top) x (fun i _ => ?_) (fun i hi _ => ?_)
  · rw [norm_iteratedFDeriv_cexp]; exact Real.exp_le_exp.2 (hB x)
  · refine (norm_iteratedFDeriv_diag_le B i x).trans ?_
    have h1 : 1 ≤ (1 + ‖x‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg x])
    have ha : 1 ≤ (‖B‖ + 1) * (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg B]
    have h2 := le_self_pow₀ ha (show i ≠ 0 by omega)
    rw [mul_assoc, mul_pow]
    calc ‖B‖ * (2 ^ i * (1 + ‖x‖) ^ 2) = 2 ^ i * (‖B‖ * (1 + ‖x‖) ^ 2) := by ring
      _ ≤ 2 ^ i * ((‖B‖ + 1) * (1 + ‖x‖) ^ 2) := by gcongr; linarith
      _ ≤ 2 ^ i * ((‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ i := by gcongr

theorem exists_bound_poly_mul_exp (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ C, ∀ r : ℝ, 0 ≤ r → (1 + r) ^ N * Real.exp (-(c * r ^ 2)) ≤ C := by
  first
  | exact @_root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded
  | exact _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded
  | (apply _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded ..)

end GlobalTheory.GaussExpSeries

namespace GlobalTheory

open GlobalTheory.GaussExpSeries

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulatedSchwartzSeminormPolynomial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulatedSchwartzSeminormPolynomial
open Complex

namespace GlobalTheory.CharModGrowth

theorem norm_iteratedFDeriv_char_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (t : ℝ) (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun x : V => Complex.exp ((I * t) * (L x : ℂ))) x‖ ≤ (|t| * ‖L‖) ^ n := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (1 : ℂ) * Complex.exp ((I * t) * (y : ℂ))) := by
    fun_prop
  have e : (fun x : V => Complex.exp ((I * t) * (L x : ℂ)))
      = (fun y : ℝ => (1 : ℂ) * Complex.exp ((I * t) * (y : ℂ))) ∘ ⇑L := by
    funext x; simp
  rw [e, L.iteratedFDeriv_comp_right hc x (i := n) (by exact_mod_cast le_top)]
  calc _ ≤ ‖iteratedFDeriv ℝ n (fun y : ℝ => (1 : ℂ) * Complex.exp ((I * t) * (y : ℂ))) (L x)‖
          * ∏ _j : Fin n, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = (|t| * ‖L‖) ^ n := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
          GlobalTheory.CharFormDeriv.iteratedDeriv_const_mul_cexp]
        have hexp : (I * t) * ((L x : ℝ) : ℂ) = ((t * L x : ℝ) : ℂ) * I := by push_cast; ring
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [norm_mul, hexp, Complex.norm_exp_ofReal_mul_I, norm_mul, norm_pow, norm_mul,
          Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
        simp [mul_pow]

theorem seminorm_char_mul_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (t : ℝ) (f u : SchwartzMap V ℂ)
    (hu : ∀ x, u x = Complex.exp ((I * t) * (L x : ℂ)) * f x) {R : ℝ} (hR1 : 1 ≤ R)
    (hR : |t| * ‖L‖ ≤ R) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n u ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ k (n - i) f)
        * R ^ n := by
  have hS0 : 0 ≤ ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * SchwartzMap.seminorm ℂ k (n - i) f :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)
  have hR0 : 0 ≤ R := by linarith
  refine SchwartzMap.seminorm_le_bound ℂ k n u (by positivity) fun x => ?_
  have hu' : (⇑u) = fun x => Complex.exp ((I * t) * (L x : ℂ)) * f x := funext hu
  rw [hu']
  have hmul := norm_iteratedFDeriv_mul_le (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (GlobalTheory.CharFormDeriv.hasTemperateGrowth_char L t).1 (f.smooth ⊤) x (n := n)
    (by exact_mod_cast le_top)
  calc _ ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x : V => Complex.exp ((I * t) * (L x : ℂ))) x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖ :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
    _ ≤ _ := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 : ‖iteratedFDeriv ℝ i (fun x : V => Complex.exp ((I * t) * (L x : ℂ))) x‖
            ≤ R ^ n :=
          (norm_iteratedFDeriv_char_le L t i x).trans
            ((pow_le_pow_left₀ (by positivity) hR i).trans (pow_le_pow_right₀ hR1 hi'))
        have h2 : ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤ SchwartzMap.seminorm ℂ k (n - i) f :=
          SchwartzMap.le_seminorm ℂ k (n - i) f x
        calc _ = (n.choose i : ℝ) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) *
              ‖iteratedFDeriv ℝ i (fun x : V => Complex.exp ((I * t) * (L x : ℂ))) x‖ := by ring
          _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)) h1
              (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))

theorem seminorm_char_mul_polynomial_growth :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V) (h : SchwartzMap V ℂ) (v : V → SchwartzMap V ℂ),
    (∀ μ x, v μ x = Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ)) * h x) →
    ∀ k n : ℕ, ∃ C : ℝ, ∀ μ, SchwartzMap.seminorm ℂ k n (v μ) ≤ C * (1 + ‖μ‖) ^ n := by
  intro V _ _ _ P h v hv k n
  let Q : V →L[ℝ] (V →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).toLinearMap ∘ₗ
      LinearMap.flip P)
  have hQ : ∀ μ x, Q μ x = P x μ := fun μ x => rfl
  set A : ℝ := |2 * Real.pi| * ‖Q‖ with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨(∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ k (n - i) h)
    * (1 + A) ^ n, fun μ => ?_⟩
  have hμ : 0 ≤ ‖μ‖ := norm_nonneg μ
  rw [mul_assoc, ← mul_pow]
  refine seminorm_char_mul_le (Q μ) (2 * Real.pi) h (v μ) (fun x => ?_) ?_ ?_ k n
  · rw [hv, hQ]; congr 2; push_cast; ring
  · nlinarith [mul_nonneg hA0 hμ]
  · calc |2 * Real.pi| * ‖Q μ‖ ≤ |2 * Real.pi| * (‖Q‖ * ‖μ‖) :=
          mul_le_mul_of_nonneg_left (Q.le_opNorm μ) (abs_nonneg _)
      _ = A * ‖μ‖ := by rw [hA]; ring
      _ ≤ _ := by nlinarith

end GlobalTheory.CharModGrowth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulatedSchwartzSeminormPolynomialStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulated_schwartz_seminorm_polynomial : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V) (h : SchwartzMap V ℂ) (v : V → SchwartzMap V ℂ),
    (∀ μ x, v μ x = Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ)) * h x) →
    ∀ k n : ℕ, ∃ C : ℝ, ∀ μ, SchwartzMap.seminorm ℂ k n (v μ) ≤ C * (1 + ‖μ‖) ^ n := by
  first | exact @GlobalTheory.CharModGrowth.seminorm_char_mul_polynomial_growth | exact GlobalTheory.CharModGrowth.seminorm_char_mul_polynomial_growth | (intros; apply GlobalTheory.CharModGrowth.seminorm_char_mul_polynomial_growth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositumIntermediateFieldExistsPlaceValuationE
open NumberField IsDedekindDomain

namespace GlobalTheory.UnramCompositum

theorem card_inertia (k N : Type) [Field k] [NumberField k] [Field N] [NumberField N]
    [Algebra k N] [IsGalois k N] (Q : Ideal (𝓞 N)) [Q.IsPrime] :
    Nat.card (Q.inertia (N ≃ₐ[k] N)) = Q.ramificationIdx (𝓞 k) := by
  have : IsGaloisGroup (N ≃ₐ[k] N) (𝓞 k) (𝓞 N) := IsGaloisGroup.of_isFractionRing _ _ _ k N
  have hpr : (Q.under (𝓞 k)).IsPrime := Ideal.IsPrime.under _ Q
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := N ≃ₐ[k] N) (Q.under (𝓞 k)) Q
  rwa [Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 k)) Q (N ≃ₐ[k] N)] at hcard

theorem ramificationIdx_eq_one_iff_fix (k E N : Type) [Field k] [NumberField k] [Field E] [NumberField E]
    [Field N] [NumberField N] [Algebra k E] [Algebra k N] [Algebra E N] [IsScalarTower k E N] [IsGalois k N]
    (Q : Ideal (𝓞 N)) [Q.IsPrime] :
    (Q.under (𝓞 E)).ramificationIdx (𝓞 k) = 1 ↔
      ∀ τ : N ≃ₐ[k] N, (∀ x : 𝓞 N, τ • x - x ∈ Q) → ∀ y : E, τ (algebraMap E N y) = algebraMap E N y := by
  haveI : IsGalois E N := IsGalois.tower_top_of_isGalois k E N
  have h1 := card_inertia k N Q
  have h2 := card_inertia E N Q
  have h3 : Q.ramificationIdx (𝓞 k) = (Q.under (𝓞 E)).ramificationIdx (𝓞 k) * Q.ramificationIdx (𝓞 E) :=
    Ideal.ramificationIdx_tower (Q.under (𝓞 E)) Q
  have h4 : 0 < Q.ramificationIdx (𝓞 E) := Ideal.ramificationIdx_pos (R := 𝓞 E) Q
  let f : Q.inertia (N ≃ₐ[E] N) → Q.inertia (N ≃ₐ[k] N) := fun σ =>
    ⟨σ.1.restrictScalars k, AddSubgroup.mem_inertia.mpr fun x => AddSubgroup.mem_inertia.mp σ.2 x⟩
  have hf : Function.Injective f := fun σ σ' h =>
    Subtype.ext (AlgEquiv.restrictScalars_injective k (congrArg Subtype.val h))
  constructor
  · intro h τ hτ y
    have hb : Function.Bijective f := hf.bijective_of_nat_card_le (by rw [h1, h2, h3, h, one_mul])
    obtain ⟨σ, hσ⟩ := hb.2 ⟨τ, AddSubgroup.mem_inertia.mpr hτ⟩
    have : σ.1.restrictScalars k = τ := congrArg Subtype.val hσ
    rw [← this]
    exact σ.1.commutes y
  · intro h
    have hs : Function.Surjective f := fun τ =>
      ⟨⟨{ τ.1.toRingEquiv with commutes' := h τ.1 (AddSubgroup.mem_inertia.mp τ.2) },
        AddSubgroup.mem_inertia.mpr fun x => AddSubgroup.mem_inertia.mp τ.2 x⟩, rfl⟩
    have hc := Nat.card_eq_of_bijective f ⟨hf, hs⟩
    rw [h1, h2, h3] at hc
    exact Nat.eq_of_mul_eq_mul_right h4 (by rw [one_mul]; exact hc.symm)

theorem exists_galois_above (K : Type) [Field K] [NumberField K] :
    ∃ (N : Type) (_ : Field N) (_ : NumberField N) (_ : Algebra K N), IsGalois ℚ N := by
  have : IsAlgClosure ℚ (AlgebraicClosure K) := IsAlgClosure.ofAlgebraic ℚ K (AlgebraicClosure K)
  have : IsGalois ℚ (AlgebraicClosure K) := ⟨⟩
  have : NumberField (IntermediateField.normalClosure ℚ K (AlgebraicClosure K)) := ⟨⟩
  exact ⟨IntermediateField.normalClosure ℚ K (AlgebraicClosure K), inferInstance, inferInstance, inferInstance,
    IsGalois.normalClosure ℚ K (AlgebraicClosure K)⟩

theorem exists_valuation_eq (F F' K : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] [Field K]
    [NumberField K] [Algebra F K] [Algebra F' K]
    (hgen : ∀ (N : Type) [Field N] (f g : K →+* N), (∀ x : F, f (algebraMap F K x) = g (algebraMap F K x)) →
      (∀ x : F', f (algebraMap F' K x) = g (algebraMap F' K x)) → f = g)
    (q : ℕ) (hq : q.Prime) (hd : ¬ (q : ℤ) ∣ discr F') (w : HeightOneSpectrum (𝓞 F))
    (hw : ((q : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ∀ a : F, 𝔭.valuation K (algebraMap F K a) = w.valuation F a := by
  obtain ⟨N, _, _, _, hN⟩ := exists_galois_above K
  letI : Algebra F N := ((algebraMap K N).comp (algebraMap F K)).toAlgebra
  letI : Algebra F' N := ((algebraMap K N).comp (algebraMap F' K)).toAlgebra
  have : IsScalarTower F K N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsGalois F N := IsGalois.tower_top_of_isGalois ℚ F N
  have := w.isMaximal
  obtain ⟨Q, hQ, hQw⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 N) w.asIdeal
  have hqQ : ((q : ℕ) : 𝓞 N) ∈ Q := by
    have := (Ideal.mem_of_liesOver Q w.asIdeal _).1 hw
    rwa [map_natCast] at this
  have hu : Algebra.IsUnramifiedAt ℤ (Q.under (𝓞 F')) :=
    (not_dvd_discr_iff_forall_mem F' (𝓞 F') (Nat.prime_iff_prime_int.1 hq)).1 hd _ inferInstance (by
      rw [Ideal.under, Ideal.mem_comap, map_intCast, Int.cast_natCast]; exact hqQ)
  have hu' : Algebra.IsUnramifiedAt (𝓞 ℚ) (Q.under (𝓞 F')) := Algebra.IsUnramifiedAt.of_restrictScalars ℤ _
  have hfix := (ramificationIdx_eq_one_iff_fix ℚ F' N Q).1 (Ideal.ramificationIdx_eq_one _ _)
  have he : (Q.under (𝓞 K)).ramificationIdx (𝓞 F) = 1 := by
    refine (ramificationIdx_eq_one_iff_fix F K N Q).2 fun τ hτ y => ?_
    exact RingHom.congr_fun (hgen N ((τ : N →+* N).comp (algebraMap K N)) (algebraMap K N)
      (fun x => τ.commutes x) (fun x => hfix (τ.restrictScalars ℚ) hτ x)) y
  have hlo : (Q.under (𝓞 K)).LiesOver w.asIdeal := Ideal.LiesOver.tower_bot Q _ _
  let 𝔭 : HeightOneSpectrum (𝓞 K) :=
    ⟨Q.under (𝓞 K), inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot w.ne_bot _⟩
  have hlo' : 𝔭.asIdeal.LiesOver w.asIdeal := hlo
  refine ⟨𝔭, fun a => ?_⟩
  rw [← HeightOneSpectrum.valuation_liesOver K w 𝔭 a]
  change _ ^ (Q.under (𝓞 K)).ramificationIdx (𝓞 F) = _
  rw [he, pow_one]


open Formalism.L2.Pj in
theorem exists_vLa_eq : ∀ (F F' K : IntermediateField ℚ ℂ) [NumberField F] [NumberField F'] [NumberField K]
    (hF : F ≤ K), K = F ⊔ F' → ∀ q : ℕ, q.Prime → ¬ (q : ℤ) ∣ discr F' → ∀ w : HeightOneSpectrum (𝓞 F),
    ((q : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ 𝔭 : HeightOneSpectrum (𝓞 K),
      ∀ a : F, vLa 𝔭 (IntermediateField.inclusion hF a) = vLa w a := by
  intro F F' K _ _ _ hF hK q hq hd w hw
  have hF' : F' ≤ K := hK ▸ le_sup_right
  letI : Algebra F K := (IntermediateField.inclusion hF).toRingHom.toAlgebra
  letI : Algebra F' K := (IntermediateField.inclusion hF').toRingHom.toAlgebra
  obtain ⟨𝔭, h⟩ := exists_valuation_eq F F' K (fun N _ f g h1 h2 => by
    let T : Subfield ℂ := (RingHom.eqLocusField f g).map (K.val : K →+* ℂ)
    let S : IntermediateField ℚ ℂ := T.toIntermediateField fun x => by
      rw [eq_ratCast]; exact SubfieldClass.ratCast_mem T x
    have hle : K ≤ S := by
      refine hK.le.trans (sup_le (fun x hx => ⟨⟨x, hF hx⟩, h1 ⟨x, hx⟩, rfl⟩)
        (fun x hx => ⟨⟨x, hF' hx⟩, h2 ⟨x, hx⟩, rfl⟩))
    ext z
    obtain ⟨y, hy, hyz⟩ := hle z.2
    have hyz' : y = z := Subtype.ext hyz
    subst hyz'
    exact hy) q hq hd w hw
  exact ⟨𝔭, fun a => congrArg (fun t => -WithZero.log t) (h a)⟩

end GlobalTheory.UnramCompositum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicEmbeddingLiesOverOrComplexConjLiesOver
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicEmbeddingLiesOverOrComplexConjLiesOver
open GlobalTheory.LKTrip NumberField

namespace GlobalTheory.HTGroupOver

theorem exists_gen {F : Type} [Field F] [NumberField F] [IsCMField F] (Kq : Subfield F)
    (hKq : Module.finrank ℚ Kq = 2 ∧ ∀ τ : F →+* ℂ, ∃ x ∈ Kq, (τ x).im ≠ 0) :
    ∃ y : Kq, ∃ r : ℚ, (y : F) * y = r ∧ IsCMField.complexConj F (y : F) = -(y : F) ∧
      ∀ z : Kq, ∃ a b : ℚ, (z : F) = a + b * y := by
  classical
  let σ : F →+* ℂ := (IsAlgClosed.lift : F →ₐ[ℚ] ℂ).toRingHom
  obtain ⟨x0, hx0K, hx0⟩ := hKq.2 σ
  let x : Kq := ⟨x0, hx0K⟩
  have hσq : ∀ q : ℚ, (σ (q : F)).im = 0 := by intro q; simp [map_ratCast]
  have hdep : ¬ LinearIndependent ℚ ![(1 : Kq), x, x * x] := by
    intro h
    have := h.fintype_card_le_finrank
    simp [hKq.1] at this
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hg, i, hi⟩ := hdep
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hg
  have hgF : (g 0 : F) + g 1 * x0 + g 2 * (x0 * x0) = 0 := by
    have := congrArg (fun w : Kq => (w : F)) hg
    simpa [Rat.smul_def, x] using this

  have hnr : ∀ a b : ℚ, b ≠ 0 → (a : F) + b * x0 ≠ 0 := by
    intro a b hb h
    have h2 := congrArg (fun w => (σ w).im) h
    simp only [map_add (f := _), map_mul, map_ratCast, Complex.add_im, Complex.ratCast_im, Complex.mul_im,
      Complex.ratCast_re, zero_mul, add_zero, zero_add, map_zero, Complex.zero_im] at h2
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact hb (by exact_mod_cast h3)
    · exact hx0 h3
  have hg2 : g 2 ≠ 0 := by
    intro h2
    rw [h2] at hgF
    simp only [Rat.cast_zero, zero_mul, add_zero] at hgF
    by_cases h1 : g 1 = 0
    · rw [h1] at hgF
      simp only [Rat.cast_zero, zero_mul, add_zero, Rat.cast_eq_zero] at hgF
      fin_cases i <;> simp_all
    · exact hnr _ _ h1 hgF
  let y0 : F := 2 * g 2 * x0 + g 1
  have hy0K : y0 ∈ Kq := by
    refine add_mem (mul_mem (mul_mem (ofNat_mem Kq 2) (SubfieldClass.ratCast_mem Kq _)) hx0K)
      (SubfieldClass.ratCast_mem Kq _)
  have hy0sq : y0 * y0 = ((g 1 ^ 2 - 4 * g 0 * g 2 : ℚ) : F) := by
    push_cast
    linear_combination (4 * (g 2 : F)) * hgF
  have hy0ne : ∀ a b : ℚ, b ≠ 0 → (a : F) + b * y0 ≠ 0 := by
    intro a b hb h
    apply hnr (a + b * g 1) (2 * b * g 2) (by simp [hb, hg2])
    push_cast
    linear_combination h

  let y : Kq := ⟨y0, hy0K⟩
  refine ⟨y, g 1 ^ 2 - 4 * g 0 * g 2, hy0sq, ?_, ?_⟩
  · have hc : (IsCMField.complexConj F y0 - y0) * (IsCMField.complexConj F y0 + y0) = 0 := by
      have h1 : IsCMField.complexConj F y0 * IsCMField.complexConj F y0 = y0 * y0 := by
        rw [← map_mul, hy0sq, map_ratCast]
      linear_combination h1
    rcases mul_eq_zero.1 hc with h | h
    · exfalso
      have h1 : IsCMField.complexConj F y0 = y0 := sub_eq_zero.1 h
      have h2 := IsCMField.complexEmbedding_complexConj F σ y0
      rw [h1] at h2
      have h3 := congrArg Complex.im h2
      simp only [Complex.conj_im] at h3
      have h4 : (σ y0).im = 0 := by linarith
      have h5 : (σ y0).im = 2 * g 2 * (σ x0).im := by
        have e : σ y0 = ((2 * g 2 : ℚ) : ℂ) * σ x0 + ((g 1 : ℚ) : ℂ) := by
          simp only [y0, map_add (f := _), map_mul, map_ratCast, map_ofNat]; push_cast; ring
        rw [e, Complex.add_im, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im, Complex.ratCast_im]
        push_cast; ring
      rw [h5] at h4
      rcases mul_eq_zero.1 h4 with h6 | h6
      · rcases mul_eq_zero.1 h6 with h7 | h7
        · norm_num at h7
        · exact hg2 (by exact_mod_cast h7)
      · exact hx0 h6
    · exact eq_neg_of_add_eq_zero_left h
  · have hli : LinearIndependent ℚ ![(1 : Kq), y] := by
      rw [LinearIndependent.pair_iff' one_ne_zero]
      intro a ha
      have ha' := congrArg (fun w : Kq => (w : F)) ha
      simp only [Rat.smul_def, mul_one] at ha'
      apply hy0ne (-a) 1 one_ne_zero
      push_cast at ha' ⊢
      simp only [y] at ha'
      rw [← ha']
      ring
    have hsp := hli.span_eq_top_of_card_eq_finrank (by simp [hKq.1])
    intro z
    have hz : z ∈ Submodule.span ℚ (Set.range ![(1 : Kq), y]) := by rw [hsp]; trivial
    rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hz
    obtain ⟨a, b, hab⟩ := hz
    refine ⟨a, b, ?_⟩
    rw [← hab]
    simp [Rat.smul_def, y]

theorem liesOver_or_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (τ : G.F →+* PadicAlgCl p),
    LiesOver G.Kq G.u τ ∨ LiesOver G.Kq G.u (τ.comp (conjQ G.F).toRingHom) := by
  intro p _ G τ
  obtain ⟨y, r, hyr, hcy, hspan⟩ := exists_gen G.Kq G.hKq
  have hyK : y * y = (r : G.Kq) := Subtype.ext (by push_cast; exact hyr)
  have hsq : τ (y : G.F) * τ (y : G.F) =
      algebraMap ℚ_[p] (PadicAlgCl p) (G.u y) * algebraMap ℚ_[p] (PadicAlgCl p) (G.u y) := by
    rw [← map_mul, ← map_mul, ← map_mul, hyK, hyr, map_ratCast, map_ratCast, map_ratCast]
  have hz : ∀ z : G.Kq, ∃ a b : ℚ, z = (a : G.Kq) + (b : G.Kq) * y := by
    intro z
    obtain ⟨a, b, h⟩ := hspan z
    exact ⟨a, b, Subtype.ext (by push_cast; exact h)⟩
  rcases mul_self_eq_mul_self_iff.1 hsq with h | h
  · left
    intro z
    obtain ⟨a, b, rfl⟩ := hz z
    simp only [Subfield.coe_add, Subfield.coe_mul, SubfieldClass.coe_ratCast, map_add (f := _), map_mul, map_ratCast, h]
  · right
    intro z
    obtain ⟨a, b, rfl⟩ := hz z
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, conjQ_apply,
      Subfield.coe_add, Subfield.coe_mul, SubfieldClass.coe_ratCast, map_add, map_mul, map_ratCast, hcy, map_neg, h]
    ring

end GlobalTheory.HTGroupOver
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicEmbeddingLiesOverOrComplexConjLiesOverStatement
open GlobalTheory.LKTrip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicEmbedding_liesOver_or_complexConj_liesOver : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (τ : G.F →+* PadicAlgCl p), LiesOver G.Kq G.u τ ∨ LiesOver G.Kq G.u (τ.comp (conjQ G.F).toRingHom) := by
  first | exact @GlobalTheory.HTGroupOver.liesOver_or_conj | exact GlobalTheory.HTGroupOver.liesOver_or_conj | (intros; apply GlobalTheory.HTGroupOver.liesOver_or_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalIntegralComm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalIntegralComm
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap BoundedContinuousFunction

noncomputable section

namespace GlobalTheory.SchwartzIntegral

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def weightedDeriv (k m : ℕ) (f : 𝓢(E, ℂ)) : E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ m f x)
    ((continuous_norm.pow k).smul ((f.smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)))
    (SchwartzMap.seminorm ℂ k m f) (fun x => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact f.le_seminorm ℂ k m x)

theorem weightedDeriv_apply (k m : ℕ) (f : 𝓢(E, ℂ)) (x : E) :
    weightedDeriv k m f x = (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ m f x := rfl

theorem norm_weightedDeriv_le (k m : ℕ) (f : 𝓢(E, ℂ)) :
    ‖weightedDeriv k m f‖ ≤ SchwartzMap.seminorm ℂ k m f :=
  (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).mpr fun x => by
    rw [weightedDeriv_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact f.le_seminorm ℂ k m x

theorem seminorm_le_norm_weightedDeriv (k m : ℕ) (f : 𝓢(E, ℂ)) :
    SchwartzMap.seminorm ℂ k m f ≤ ‖weightedDeriv k m f‖ :=
  SchwartzMap.seminorm_le_bound ℂ k m f (norm_nonneg _) fun x => by
    have h := (weightedDeriv k m f).norm_coe_le_norm x
    rwa [weightedDeriv_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h

def weightedDerivCLM (k m : ℕ) :
    𝓢(E, ℂ) →L[ℂ] (E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (weightedDeriv k m)
    (fun f g => by
      ext x : 1
      simp only [weightedDeriv_apply, add_apply, FunLike.coe_add]
      rw [iteratedFDeriv_add_apply ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt
        ((g.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt, smul_add])
    (fun a f => by
      ext x : 1
      simp only [weightedDeriv_apply, FunLike.coe_smul, Pi.smul_apply, RingHom.id_apply]
      rw [iteratedFDeriv_const_smul_apply ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt,
        smul_comm])
    ⟨{(k, m)}, 1, zero_le_one, fun f => by
      simpa [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply] using norm_weightedDeriv_le k m f⟩

theorem weightedDerivCLM_apply (k m : ℕ) (f : 𝓢(E, ℂ)) : weightedDerivCLM k m f = weightedDeriv k m f := rfl

section Param

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] {ν : Measure W}

theorem continuous_iteratedFDeriv_param {G : W → 𝓢(E, ℂ)} (hG : Continuous G) (m : ℕ) (y : E) :
    Continuous fun w => iteratedFDeriv ℝ m (G w) y := by
  have h := ((BoundedContinuousFunction.evalCLM ℂ y).comp (weightedDerivCLM (E := E) 0 m)).continuous.comp hG
  refine h.congr fun w => ?_
  simp [weightedDerivCLM_apply, weightedDeriv_apply]

theorem integrable_iteratedFDeriv_param {G : W → 𝓢(E, ℂ)} (hG : Continuous G)
    (hint : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (G w)) ν) (m : ℕ) (y : E) :
    Integrable (fun w => iteratedFDeriv ℝ m (G w) y) ν :=
  (hint 0 m).mono' (continuous_iteratedFDeriv_param hG m y).aestronglyMeasurable
    (.of_forall fun w => (G w).norm_iteratedFDeriv_le_seminorm ℂ m y)

theorem iteratedFDeriv_eq_integral {G : W → 𝓢(E, ℂ)} (hG : Continuous G)
    (hint : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (G w)) ν) {g : 𝓢(E, ℂ)}
    (hg : ∀ x, g x = ∫ w, G w x ∂ν) (m : ℕ) :
    iteratedFDeriv ℝ m g = fun x => ∫ w, iteratedFDeriv ℝ m (G w) x ∂ν := by
  induction m with
  | zero =>
    funext x
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, hg x]
    exact ((continuousMultilinearCurryFin0 ℝ E ℂ).symm.toLinearIsometry.integral_comp_comm _).symm
  | succ m ih =>
    funext x
    set Ψ := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) ℂ
    have key : ∀ (f : E → ℂ) (y : E), iteratedFDeriv ℝ (m + 1) f y = Ψ.symm (fderiv ℝ (iteratedFDeriv ℝ m f) y) := by
      intro f y
      rw [iteratedFDeriv_succ_eq_comp_left]
      rfl
    have hdiff : ∀ w, Differentiable ℝ (iteratedFDeriv ℝ m (G w)) := fun w =>
      ((G w).smooth ⊤).differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top m)
    have hF' : ∀ w y, fderiv ℝ (iteratedFDeriv ℝ m (G w)) y = Ψ (iteratedFDeriv ℝ (m + 1) (G w) y) := by
      intro w y
      rw [key, LinearIsometryEquiv.apply_symm_apply]
    have hd : HasFDerivAt (fun y => ∫ w, iteratedFDeriv ℝ m (G w) y ∂ν)
        (∫ w, fderiv ℝ (iteratedFDeriv ℝ m (G w)) x ∂ν) x := by
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun w => SchwartzMap.seminorm ℂ 0 (m + 1) (G w))
        Filter.univ_mem (.of_forall fun y => (continuous_iteratedFDeriv_param hG m y).aestronglyMeasurable)
        (integrable_iteratedFDeriv_param hG hint m x) ?_ (.of_forall fun w y _ => ?_) (hint 0 (m + 1))
        (.of_forall fun w y _ => (hdiff w y).hasFDerivAt)
      · simp_rw [hF']
        exact (Ψ.continuous.comp (continuous_iteratedFDeriv_param hG (m + 1) x)).aestronglyMeasurable
      · rw [norm_fderiv_iteratedFDeriv]
        exact (G w).norm_iteratedFDeriv_le_seminorm ℂ (m + 1) y
    rw [key, ih, hd.fderiv]
    have := Ψ.symm.toLinearIsometry.integral_comp_comm (μ := ν) (fun w => fderiv ℝ (iteratedFDeriv ℝ m (G w)) x)
    simp only [LinearIsometryEquiv.coe_toLinearIsometry] at this
    rw [← this]
    simp_rw [hF', LinearIsometryEquiv.symm_apply_apply]

abbrev Target (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Finset (ℕ × ℕ)) : Type :=
  (i : s) → (E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin i.1.2 => E) ℂ)

def embed (s : Finset (ℕ × ℕ)) : 𝓢(E, ℂ) →L[ℂ] Target E s :=
  ContinuousLinearMap.pi fun i => weightedDerivCLM i.1.1 i.1.2

theorem embed_apply (s : Finset (ℕ × ℕ)) (f : 𝓢(E, ℂ)) (i : s) : embed s f i = weightedDeriv i.1.1 i.1.2 f := rfl

theorem norm_embed_le (s : Finset (ℕ × ℕ)) (f : 𝓢(E, ℂ)) :
    ‖embed s f‖ ≤ ∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 f :=
  (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => apply_nonneg _ _)).mpr fun i =>
    (norm_weightedDeriv_le _ _ f).trans
      (Finset.single_le_sum (f := fun j : ℕ × ℕ => SchwartzMap.seminorm ℂ j.1 j.2 f)
        (fun j _ => apply_nonneg _ _) i.2)

theorem seminorm_le_norm_embed (s : Finset (ℕ × ℕ)) (f : 𝓢(E, ℂ)) {i : ℕ × ℕ} (hi : i ∈ s) :
    SchwartzMap.seminorm ℂ i.1 i.2 f ≤ ‖embed s f‖ :=
  (seminorm_le_norm_weightedDeriv _ _ f).trans (norm_le_pi_norm (embed s f) ⟨i, hi⟩)

theorem clm_apply_eq_integral (L : 𝓢(E, ℂ) →L[ℂ] ℂ) {G : W → 𝓢(E, ℂ)} (hG : Continuous G)
    (hint : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (G w)) ν) {g : 𝓢(E, ℂ)}
    (hg : ∀ x, g x = ∫ w, G w x ∂ν) : L g = ∫ w, L (G w) ∂ν := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ)
    ((normSeminorm ℂ ℂ).comp (L : 𝓢(E, ℂ) →ₗ[ℂ] ℂ)) (continuous_norm.comp L.continuous)
  have hL : ∀ f, ‖L f‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ E ℂ)) f := fun f => hC f
  set t := insert ((0 : ℕ), (0 : ℕ)) s
  have hLt : ∀ f, ‖L f‖ ≤ C * ‖embed t f‖ := fun f => (hL f).trans (mul_le_mul_of_nonneg_left
    (Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi =>
      seminorm_le_norm_embed t f (Finset.mem_insert_of_mem hi)) C.2)
  have hinj : Function.Injective (embed (E := E) t) := by
    refine (injective_iff_map_eq_zero (embed (E := E) t)).mpr fun f hf => ?_
    ext x
    have h1 := seminorm_le_norm_embed t f (Finset.mem_insert_self _ _)
    rw [hf, norm_zero] at h1
    have h2 := (f.norm_le_seminorm ℂ x).trans h1
    simpa using h2
  let Φ : 𝓢(E, ℂ) →ₗ[ℂ] Target E t := (embed (E := E) t : 𝓢(E, ℂ) →ₗ[ℂ] Target E t)
  let e := LinearEquiv.ofInjective Φ hinj
  have he : ∀ y : LinearMap.range Φ, embed t (e.symm y) = y := fun y => by
    have := congrArg Subtype.val (e.apply_symm_apply y)
    exact (LinearEquiv.ofInjective_apply Φ (e.symm y)).symm.trans this
  let f0 : LinearMap.range Φ →ₗ[ℂ] ℂ := (L : 𝓢(E, ℂ) →ₗ[ℂ] ℂ).comp e.symm.toLinearMap
  let f1 : StrongDual ℂ (LinearMap.range Φ) := f0.mkContinuous C fun y => by
    show ‖L (e.symm y)‖ ≤ C * ‖(y : Target E t)‖
    rw [← he]
    exact hLt _
  obtain ⟨ℓ, hℓ, -⟩ := exists_extension_norm_eq (LinearMap.range Φ) f1
  have hLℓ : ∀ f, L f = ℓ (embed t f) := by
    intro f
    have h1 := hℓ ⟨embed t f, LinearMap.mem_range_self Φ f⟩
    have h2 : e.symm ⟨embed t f, LinearMap.mem_range_self Φ f⟩ = f := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext rfl
    have h3 : ℓ (embed t f) = f1 ⟨embed t f, LinearMap.mem_range_self Φ f⟩ := h1
    rw [h3, LinearMap.mkContinuous_apply]
    show L f = L (e.symm _)
    rw [h2]
  have hcont : Continuous fun w => embed t (G w) := (embed t).continuous.comp hG
  haveI : SecondCountableTopology W := inferInstance
  haveI : SecondCountableTopologyEither W (Target E t) := secondCountableTopologyEither_of_left _ _
  have hInt : Integrable (fun w => embed t (G w)) ν :=
    (MeasureTheory.integrable_finsetSum t fun i _ => hint i.1 i.2).mono' hcont.aestronglyMeasurable
      (.of_forall fun w => norm_embed_le t (G w))
  have hemb : embed t g = ∫ w, embed t (G w) ∂ν := by
    funext i
    refine BoundedContinuousFunction.ext fun x => ?_
    have h1 := ((BoundedContinuousFunction.evalCLM ℂ x).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun i : t => E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin i.1.2 => E) ℂ) i)).integral_comp_comm hInt
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      BoundedContinuousFunction.evalCLM_apply] at h1
    rw [← h1]
    simp only [embed_apply, weightedDeriv_apply]
    rw [integral_smul, iteratedFDeriv_eq_integral hG hint hg]
  rw [hLℓ g, hemb, ← ℓ.integral_comp_comm hInt]
  simp_rw [← hLℓ]

end Param

theorem clm_integral_interchange : ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] (ν : Measure W) [SigmaFinite ν] (n : ℕ) (L : Sch (Fin n) →L[ℂ] ℂ)
    (G : W → Sch (Fin n)) (c : W → ℂ) (g : Sch (Fin n)), Continuous G → Continuous c →
    (∀ k m : ℕ, Integrable (fun w => ‖c w‖ * SchwartzMap.seminorm ℂ k m (G w)) ν) →
    (∀ x, g x = ∫ w, c w * G w x ∂ν) → L g = ∫ w, c w * L (G w) ∂ν := by
  intro W _ _ _ _ _ ν _ n L G c g hG hc hint hg
  have hG' : Continuous fun w => c w • G w := hc.smul hG
  have hint' : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (c w • G w)) ν := by
    intro k m
    simpa only [map_smul_eq_mul] using hint k m
  have hg' : ∀ x, g x = ∫ w, (c w • G w) x ∂ν := by
    intro x
    rw [hg x]
    rfl
  rw [clm_apply_eq_integral L hG' hint' hg']
  simp only [map_smul, smul_eq_mul]

end GlobalTheory.SchwartzIntegral
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalIntegralCommStatement
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_functional_integral_comm : ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
    [BorelSpace W] (ν : Measure W) [SigmaFinite ν] (n : ℕ) (L : Sch (Fin n) →L[ℂ] ℂ) (G : W → Sch (Fin n))
    (c : W → ℂ) (g : Sch (Fin n)), Continuous G → Continuous c →
    (∀ k m : ℕ, Integrable (fun w => ‖c w‖ * SchwartzMap.seminorm ℂ k m (G w)) ν) →
    (∀ x, g x = ∫ w, c w * G w x ∂ν) → L g = ∫ w, c w * L (G w) ∂ν := by
  first | exact @GlobalTheory.SchwartzIntegral.clm_integral_interchange | exact GlobalTheory.SchwartzIntegral.clm_integral_interchange | (intros; apply GlobalTheory.SchwartzIntegral.clm_integral_interchange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFirstCoords
noncomputable section

namespace GlobalTheory.SphereMeanDrop

open MeasureTheory Set

def gaussProb (n : ℕ) : Measure (EuclideanSpace ℂ (Fin n)) :=
  ProbabilityTheory.cond ((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity
    fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2))) univ

def radProb (n : ℕ) : Measure (Ioi (0 : ℝ)) :=
  ProbabilityTheory.cond ((Measure.volumeIoiPow (2 * n - 1)).withDensity
    fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2))) univ

def firstCoords {N n : ℕ} (h : N ≤ n) (x : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 fun j => WithLp.ofLp x (Fin.castLE h j)

end GlobalTheory.SphereMeanDrop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingOfRegularQuotient
open IsLocalRing TensorProduct

namespace GlobalTheory.RegularAscent

theorem height_add_ringKrullDim_quotient_le {R : Type} [CommRing R] (p : Ideal R) [hp : p.IsPrime] :
    ((p.height : ℕ∞) : WithBot ℕ∞) + ringKrullDim (R ⧸ p) ≤ ringKrullDim R := by
  let P : PrimeSpectrum R := ⟨p, hp⟩
  haveI : Nonempty (PrimeSpectrum R) := ⟨P⟩
  have h1 : PrimeSpectrum.zeroLocus (p : Set R) = Set.Ici P := by
    ext x
    simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici]
    rfl
  have h2 : ringKrullDim (R ⧸ p) = (Order.coheight P : ℕ∞) := by
    rw [ringKrullDim_quotient, h1, Order.coheight_eq_krullDim_Ici]
  have h3 : p.height = Order.height P := PrimeSpectrum.height_eq_orderHeight P
  rw [h2, h3, ← WithBot.coe_add]
  change _ ≤ Order.krullDim (PrimeSpectrum R)
  rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, WithBot.coe_le_coe]
  exact le_iSup (fun x : PrimeSpectrum R => Order.height x + Order.coheight x) P

end GlobalTheory.RegularAscent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelMulLevelSubstPow
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem hasQ_mul_spread : ∀ (N M : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < N → 0 < M → HasQ N f a →
    HasQ (N * M) f (spread M a) := by
  intro N M f a hN hM h τ
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hinj : Function.Injective (fun k : ℕ => M * k) := fun x y hxy =>
    Nat.eq_of_mul_eq_mul_left hM hxy
  refine (hinj.hasSum_iff ?_).mp ?_
  · intro n hn
    simp only [spread]
    rw [if_neg, zero_mul]
    rintro ⟨k, rfl⟩
    exact hn ⟨k, rfl⟩
  · convert h τ using 1
    funext k
    simp only [Function.comp, spread, dvd_mul_right, if_true, Nat.mul_div_cancel_left k hM]
    congr 2
    push_cast
    field_simp

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyIffValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyIffValues
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem isFam_iff_values (ι : Type) (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ) :
    IsFam act w f ↔ ∀ (i : ι) (γ : SL(2, ℤ)) (τ : ℍ),
      f i (γ • τ) = (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ w * f (act i γ) τ := by
  unfold IsFam
  refine forall_congr' fun i => forall_congr' fun γ => ?_
  rw [funext_iff]
  refine forall_congr' fun τ => ?_
  have hD : UpperHalfPlane.denom γ τ = ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
    simp [UpperHalfPlane.denom]
  have hne : UpperHalfPlane.denom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ τ
  rw [ModularForm.SL_slash_apply, zpow_neg, mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ hne), hD,
    mul_comm (f (act i γ) τ)]

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyIffValuesStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSLTwoPermutedModularFamily_iff_values : ∀ (ι : Type) (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ), IsFam act w f ↔ ∀ (i : ι) (γ : SL(2, ℤ)) (τ : ℍ), f i (γ • τ) = (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ w * f (act i γ) τ := by
  first | exact @GlobalTheory.QFam.isFam_iff_values | exact GlobalTheory.QFam.isFam_iff_values | (intros; apply GlobalTheory.QFam.isFam_iff_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapIntegralClosureTensorEq
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory

noncomputable def tensorIntegralClosureInclusion (S L D : Type) [CommRing S] [Field L] [Algebra S L]
    [CommRing D] [Algebra S D] :
    integralClosure S L →ₐ[S] integralClosure D (TensorProduct S D L) where
  toRingHom := GlobalTheory.AbhyankarLocal.toNorm S L D
  commutes' s := by
    ext
    change (1 : D) ⊗ₜ[S] (algebraMap S L s) = _
    exact (Algebra.TensorProduct.includeRight (R := S) (A := D) (B := L)).commutes s

noncomputable instance instAlgebraIntegralClosureTensor (S L D : Type) [CommRing S] [Field L]
    [Algebra S L] [CommRing D] [Algebra S D] :
    Algebra (integralClosure S L) (integralClosure D (TensorProduct S D L)) :=
  (GlobalTheory.AbhyankarLocal.toNorm S L D).toAlgebra

instance (S L D : Type) [CommRing S] [Field L] [Algebra S L] [CommRing D] [Algebra S D] :
    IsScalarTower S (integralClosure S L) (integralClosure D (TensorProduct S D L)) :=
  IsScalarTower.of_algebraMap_eq fun s =>
    ((tensorIntegralClosureInclusion S L D).commutes s).symm

theorem algebraMap_integralClosure_tensor_eq (S L D : Type) [CommRing S] [Field L]
    [Algebra S L] [CommRing D] [Algebra S D] :
    algebraMap (integralClosure S L) (integralClosure D (TensorProduct S D L)) =
      GlobalTheory.AbhyankarLocal.toNorm S L D := rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanImageInfOfLinearIndependent
open scoped TensorProduct

namespace GlobalTheory

theorem span_image_inf_of_linearIndependent {K V W ι : Type} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module ℂ W] [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W)
    (b : Module.Basis ι K V) (hb : LinearIndependent ℂ (fun k => j (b k)))
    (U U' : Submodule K V) :
    Submodule.span ℂ (j '' (U : Set V)) ⊓ Submodule.span ℂ (j '' (U' : Set V)) =
      Submodule.span ℂ (j '' ((U ⊓ U' : Submodule K V) : Set V)) := by
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  haveI := Fintype.ofFinite ι
  let B := Algebra.TensorProduct.basis ℂ b
  let J : ℂ ⊗[K] V →ₗ[ℂ] W := B.constr ℂ (fun k => j (b k))
  have hJb : ∀ k, J (1 ⊗ₜ b k) = j (b k) := fun k => by
    have := B.constr_basis ℂ (fun k => j (b k)) k
    rwa [Algebra.TensorProduct.basis_apply] at this
  have hJ : ∀ v, J (1 ⊗ₜ v) = j v := fun v => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr v, TensorProduct.tmul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.tmul_smul, map_smulₛₗ j, ← hJb, ← map_smul,
      ← algebraMap_smul ℂ (b.repr v k)]
    rfl
  have hinj : Function.Injective J := by
    apply Module.Basis.injective_constr_of_linearIndependent
    exact hb
  have key : ∀ A : Submodule K V,
      Submodule.span ℂ (j '' (A : Set V)) = (A.baseChange ℂ).map J := fun A => by
    rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]
    congr 1
    exact Set.image_congr fun v _ => (hJ v).symm
  rw [key, key, key, baseChange_inf, Submodule.map_inf _ hinj]

end GlobalTheory
end
