module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsNumberFieldFg
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

theorem _root_.GlobalTheory.countable_ideal_and_summable_absNorm_rpow :
    ∀ (K : Type) [Field K] [NumberField K], Countable (Ideal (𝓞 K)) ∧ ∀ σ : ℝ, 1 < σ → (Summable fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-σ)) ∧ Summable fun P : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm P.asIdeal : ℝ) ^ (-σ) := by
  intro K _ _
  refine ⟨?_, fun σ hσ => ?_⟩
  · have hU : (Set.univ : Set (Ideal (𝓞 K))) = ⋃ n : ℕ, {I | Ideal.absNorm I = n} := by
      ext I; simp
    have hc : (Set.univ : Set (Ideal (𝓞 K))).Countable := by
      rw [hU]
      exact Set.countable_iUnion fun n => (Ideal.finite_setOfPred_absNorm_eq n).countable
    exact Set.countable_univ_iff.mp hc
  · have hsum : Summable fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-σ) := by
      have h := _root_.GlobalTheory.Mem.summable_norm_absNorm_cpow K (s := (σ : ℂ)) (by simpa using hσ)
      refine h.congr fun I => ?_
      rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (by simp; linarith)]
      simp
    refine ⟨hsum, ?_⟩
    have hinj : Function.Injective fun P : HeightOneSpectrum (𝓞 K) => P.asIdeal :=
      fun P Q h => HeightOneSpectrum.ext h
    exact hsum.comp_injective hinj

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormaliseMeanSquareOfCocompact
open scoped ContDiff

namespace GlobalTheory

open MeasureTheory in
theorem exists_normalise_meanSquare_of_cocompact : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x : G, ∃ g ∈ Γ, g + x ∈ K) → ∀ f : G → ℂ, Continuous f → f ≠ 0 → (∀ g ∈ Γ, ∀ w, ‖f (g + w)‖ = ‖f w‖) → (∃ (μ : MeasureTheory.Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1) ∧ ∃ c : ℂ, ∀ (μ : MeasureTheory.Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → MeasureTheory.IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → ∫ w in 𝓕, ‖c * f w‖ ^ 2 ∂μ = 1 := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov f hf hf0 hinv
  have : Countable Γ := countable_of_discrete_addSubgroup Γ
  obtain ⟨hex, h⟩ := meanSquare_addFundamentalDomain_of_cocompact G Γ K hK hcov
  obtain ⟨N, hN⟩ := h f hf hinv
  refine ⟨hex, ?_⟩
  have hN0 : N ≠ 0 := by
    intro h0
    obtain ⟨μ, F, hμ, hF, h1⟩ := hex
    have h2 := (hN μ F hμ hF).2.2.1
    rw [h0, ENNReal.coe_zero, mul_zero] at h2
    have h3 : ∫⁻ w, ‖f w‖ₑ ^ 2 ∂μ = 0 := by
      rw [hF.lintegral_eq_tsum'']
      have e : ∀ (g : Γ) (x : G), ‖f (g +ᵥ x)‖ₑ = ‖f x‖ₑ := fun g x => by
        have := hinv g g.2 x
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← this]
        rfl
      simp only [e, h2, tsum_zero]
    rw [lintegral_eq_zero_iff (hf.enorm.measurable.pow_const 2)] at h3
    apply hf0
    rw [← hf.ae_eq_iff_eq μ continuous_zero]
    filter_upwards [h3] with w hw
    simpa using hw
  have hpos : (0 : ℝ) < N := by positivity
  refine ⟨((√(N : ℝ))⁻¹ : ℝ), fun μ F hμ hF h1 => ?_⟩
  have h2 := (hN μ F hμ hF).2.2.2
  rw [h1, ENNReal.toReal_one, one_mul] at h2
  simp only [norm_mul, mul_pow]
  rw [integral_const_mul, h2, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAdicCompleteAndCardQuotientAdicCompletionInteg
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem mem_span_singleton_adicCompletionIntegers {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {t : v.adicCompletionIntegers F}
    (ht : Valued.v (t : v.adicCompletion F) ≠ 0) (x : v.adicCompletionIntegers F) :
    x ∈ Ideal.span {t} ↔
      Valued.v (x : v.adicCompletion F) ≤ Valued.v (t : v.adicCompletion F) := by
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    have ha : Valued.v (a : v.adicCompletion F) ≤ 1 := a.2
    change Valued.v ((a : v.adicCompletion F) * t) ≤ _
    rw [map_mul]
    exact mul_le_of_le_one_left' ha
  · intro hx
    have ht1 : (t : v.adicCompletion F) ≠ 0 := by
      intro h; rw [h] at ht; simp at ht
    have hm : (x : v.adicCompletion F) / t ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, div_le_one₀ (zero_lt_iff.2 ht)]
      exact hx
    refine ⟨⟨_, hm⟩, Subtype.ext ?_⟩
    change (x : v.adicCompletion F) / t * t = x
    rw [div_mul_cancel₀ _ ht1]

theorem isAdicComplete_and_card_quotient_adicCompletionIntegers :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), (∀ t : v.adicCompletionIntegers F, Valued.v (t : v.adicCompletion F) < 1 → IsAdicComplete (Ideal.span {t}) (v.adicCompletionIntegers F)) ∧ ∀ (t : v.adicCompletionIntegers F) (e : ℕ), Valued.v (t : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) → Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {t}) = Ideal.absNorm v.asIdeal ^ e := by
  intro F _ _ v
  refine ⟨fun t ht => ?_, fun t e ht => ?_⟩
  · refine NormIntegers.isAdicComplete_of_fg (C := v.adicCompletion F) ⟨?_, ?_, ?_⟩
      (IsNoetherian.noetherian _) ?_
    · exact FaithfulSMul.algebraMap_injective _ _
    · intro x
      have : ‖(x : v.adicCompletion F)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 x.2
      exact_mod_cast this
    · intro x hx
      have : ‖x‖ ≤ 1 := by exact_mod_cast hx
      exact ⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩
    · rw [Ne, Ideal.span_singleton_eq_top,
        HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      exact ht.ne
  · have ht0 : Valued.v (t : v.adicCompletion F) ≠ 0 := by rw [ht]; exact WithZero.exp_ne_zero
    let f : 𝓞 F →+* v.adicCompletionIntegers F ⧸ Ideal.span {t} :=
      (Ideal.Quotient.mk _).comp (algebraMap (𝓞 F) (v.adicCompletionIntegers F))
    have hs : Function.Surjective f := by
      intro y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨s, hs⟩ := Idele.exists_valued_sub_le v (a := (y : v.adicCompletion F)) y.2 e
      refine ⟨s, ?_⟩
      change Ideal.Quotient.mk _ _ = _
      rw [eq_comm, Ideal.Quotient.eq, mem_span_singleton_adicCompletionIntegers v ht0, ht]
      exact hs
    have hk : RingHom.ker f = v.asIdeal ^ e := by
      ext s
      rw [RingHom.mem_ker]
      change Ideal.Quotient.mk _ _ = _ ↔ _
      rw [Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton_adicCompletionIntegers v ht0, ht,
        HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
        HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]
    rw [← Nat.card_congr (RingHom.quotientKerEquivOfSurjective hs).toEquiv, hk, ← map_pow,
      Ideal.absNorm_apply, Submodule.cardQuot_apply]

end GlobalTheory.CNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryQuasiReflectionLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryQuasiReflectionLaws
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.ReflLaws

variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ}
  (G : Matrix (Fin n) (Fin n) E)

theorem _root_.GlobalTheory.UnRep.ReflLaws.hermE_eq_dot (v x : Fin n → E) :
    _root_.GlobalTheory.UnRep.hermE c G v x = (G *ᵥ fun b => c (x b)) ⬝ᵥ v := by
  unfold _root_.GlobalTheory.UnRep.hermE
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem _root_.GlobalTheory.UnRep.ReflLaws.refl_mulVec (x : Fin n → E) (u : E) (v : Fin n → E) :
    _root_.GlobalTheory.UnRep.refl c G x u *ᵥ v =
      v + ((u - 1) * _root_.GlobalTheory.UnRep.hermE c G v x /
        _root_.GlobalTheory.UnRep.hermE c G x x) • x := by
  unfold _root_.GlobalTheory.UnRep.refl
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    _root_.GlobalTheory.UnRep.ReflLaws.hermE_eq_dot]
  congr 1
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
    _root_.GlobalTheory.UnRep.ReflLaws.hermE_eq_dot]
  ring

private theorem hermE_add_smul_left' (v x y : Fin n → E) (t : E) :
    _root_.GlobalTheory.UnRep.hermE c G (v + t • x) y =
      _root_.GlobalTheory.UnRep.hermE c G v y + t * _root_.GlobalTheory.UnRep.hermE c G x y := by
  simp only [_root_.GlobalTheory.UnRep.ReflLaws.hermE_eq_dot, dotProduct_add, dotProduct_smul,
    smul_eq_mul]

private theorem hermE_conj_eq_swap_of_involutive_of_conj_symm (hinv : ∀ z : E, c (c z) = z) (hG : ∀ a b, c (G a b) = G b a)
    (a b : Fin n → E) :
    c (_root_.GlobalTheory.UnRep.hermE c G a b) = _root_.GlobalTheory.UnRep.hermE c G b a := by
  unfold _root_.GlobalTheory.UnRep.hermE
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hinv, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem hermE_add_smul_right' (v x y : Fin n → E) (t : E) :
    _root_.GlobalTheory.UnRep.hermE c G v (y + t • x) =
      _root_.GlobalTheory.UnRep.hermE c G v y + c t * _root_.GlobalTheory.UnRep.hermE c G v x := by
  have hfun : (fun b => c ((y + t • x) b)) = (fun b => c (y b)) + c t • fun b => c (x b) := by
    funext b
    simp [map_add (f := _), map_mul]
  simp only [_root_.GlobalTheory.UnRep.ReflLaws.hermE_eq_dot, hfun, Matrix.mulVec_add,
    Matrix.mulVec_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]

theorem _root_.GlobalTheory.UnRep.ReflLaws.refl_laws : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E),
    _root_.GlobalTheory.UnRep.IsHermForm c G → ∀ x : Fin n → E,
    _root_.GlobalTheory.UnRep.hermE c G x x ≠ 0 →
    (∀ u v, _root_.GlobalTheory.UnRep.refl c G x u *ᵥ v =
      v + ((u - 1) * _root_.GlobalTheory.UnRep.hermE c G v x /
        _root_.GlobalTheory.UnRep.hermE c G x x) • x) ∧
    _root_.GlobalTheory.UnRep.refl c G x 1 = 1 ∧
    (∀ u u', _root_.GlobalTheory.UnRep.refl c G x u * _root_.GlobalTheory.UnRep.refl c G x u' =
      _root_.GlobalTheory.UnRep.refl c G x (u * u')) ∧
    ∀ u, u * c u = 1 → _root_.GlobalTheory.UnRep.IsUnE c G (_root_.GlobalTheory.UnRep.refl c G x u) := by
  intro F E _ _ _ _ _ c n G hG x hx
  obtain ⟨hinv, -, hsym, -⟩ := hG
  refine ⟨_root_.GlobalTheory.UnRep.ReflLaws.refl_mulVec c G x, ?_, ?_, ?_⟩
  · unfold _root_.GlobalTheory.UnRep.refl
    simp
  · intro u u'
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, _root_.GlobalTheory.UnRep.ReflLaws.refl_mulVec,
      hermE_add_smul_left']
    rw [add_assoc, ← add_smul]
    congr 2
    field_simp
    ring
  · intro u hu
    unfold _root_.GlobalTheory.UnRep.IsUnE
    intro v y
    have hxx : c (_root_.GlobalTheory.UnRep.hermE c G x x) = _root_.GlobalTheory.UnRep.hermE c G x x :=
      hermE_conj_eq_swap_of_involutive_of_conj_symm c G hinv hsym x x
    have hyx : c (_root_.GlobalTheory.UnRep.hermE c G y x) = _root_.GlobalTheory.UnRep.hermE c G x y :=
      hermE_conj_eq_swap_of_involutive_of_conj_symm c G hinv hsym y x
    simp only [_root_.GlobalTheory.UnRep.ReflLaws.refl_mulVec, hermE_add_smul_left', hermE_add_smul_right',
      map_div₀, map_mul, map_sub, map_one, hxx, hyx]
    field_simp
    linear_combination (_root_.GlobalTheory.UnRep.hermE c G v x * _root_.GlobalTheory.UnRep.hermE c G x y *
      1) * hu

end GlobalTheory.UnRep.ReflLaws
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryQuasiReflectionLawsStatement
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryQuasiReflection_laws : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ x : Fin n → E, hermE c G x x ≠ 0 → (∀ u v, refl c G x u *ᵥ v = v + ((u - 1) * hermE c G v x / hermE c G x x) • x) ∧ refl c G x 1 = 1 ∧ (∀ u u', refl c G x u * refl c G x u' = refl c G x (u * u')) ∧ ∀ u, u * c u = 1 → IsUnE c G (refl c G x u) := by
  first | exact @GlobalTheory.UnRep.ReflLaws.refl_laws | exact GlobalTheory.UnRep.ReflLaws.refl_laws | (intros; apply GlobalTheory.UnRep.ReflLaws.refl_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousSymmFinite
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors
open scoped Topology

namespace GlobalTheory.AdeleBaseChange

theorem continuous_symm_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ι : FiniteAdeleRing (𝓞 F) F ⊗[F] E ≃+* FiniteAdeleRing (𝓞 E) E), (∀ y, y ∈ AddSubgroup.closure {y : FiniteAdeleRing (𝓞 F) F ⊗[F] E | ∃ a ∈ {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} ↔ ∀ P, Valued.v (ι y P) ≤ 1) → letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E); Continuous ι.symm := by
  intro F E _ _ _ _ _ ι hι
  letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
    moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (FiniteAdeleRing (𝓞 F) F) _
  have h0 := (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat F E 0 ⊤ (Subsingleton.elim _ _)).2
  refine continuous_of_continuousAt_zero ι.symm.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  intro W hW
  obtain ⟨N, hN, hNW⟩ := h0 W hW
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds E N hN) ?_
  rintro _ ⟨a, ha, rfl⟩
  rw [Set.mem_preimage, map_nsmul]
  apply hNW
  have h1 := (hι (ι.symm a)).2 (fun P => by rw [ι.apply_symm_apply]; exact ha P)
  refine AddSubgroup.closure_mono ?_ h1
  rintro _ ⟨b, hb, x, rfl⟩
  exact ⟨b, hb, _, ⟨x, rfl⟩, rfl⟩

end GlobalTheory.AdeleBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TsumIdealMulAbsNormCpowEqExpTsum
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

theorem tsum_ideal_mul_absNorm_cpow_eq_exp_tsum :
    ∀ (K : Type) [Field K] [NumberField K] (X : Ideal (𝓞 K) → ℂ), X ⊥ = 0 → X ⊤ = 1 → (∀ I J, X (I * J) = X I * X J) → (∀ I, ‖X I‖ ≤ 1) → ∀ s : ℂ, 1 < s.re → ∑' I, X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  intro K _ _ X hbot htop hmul hle s hs
  have hnorm : ∀ P : HeightOneSpectrum (𝓞 K), 1 < Ideal.absNorm P.asIdeal := by
    intro P
    have h0 : Ideal.absNorm P.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
    have h1 : Ideal.absNorm P.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact P.isPrime.ne_top
    omega
  refine GlobalTheory.Mem.tsum_eq_exp_tsum_neg_log_of_primes (fun P : HeightOneSpectrum (𝓞 K) => P.asIdeal)
    (fun P => P.prime) ?_ (fun I => X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)) ?_ ?_ ?_ ?_ ?_
  ·
    intro P Q h
    rw [Ideal.dvd_iff_le] at h
    exact HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h).symm
  · intro I J
    rw [hmul, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  · simp [Ideal.one_eq_top, htop]
  · intro I hI hfI
    have hbot' : I ≠ ⊥ := by
      rintro rfl; exact hfI (by simp [hbot])
    have htop' : I ≠ ⊤ := by rwa [← Ideal.one_eq_top]
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I htop'
    have hMbot : M ≠ ⊥ := fun h => hbot' (le_bot_iff.mp (h ▸ hIM))
    exact ⟨⟨M, hM.isPrime, hMbot⟩, (Ideal.dvd_iff_le).mpr hIM⟩
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun I => ?_)
      (GlobalTheory.Mem.summable_norm_absNorm_cpow K hs)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hle I)
  · intro P hP
    have hlt : ‖X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)‖ < 1 := by
      have hn := hnorm P
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
      have hr : ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s).re < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn) (by simp; linarith)
      calc ‖X P.asIdeal‖ * ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s).re
          ≤ 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s).re :=
            mul_le_mul_of_nonneg_right (hle _) (by positivity)
        _ < 1 := by rw [one_mul]; exact hr
    rw [sub_eq_zero] at hP
    rw [← hP, norm_one] at hlt
    exact lt_irrefl _ hlt

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdeleCongruenceUnitCriterion
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors Topology

namespace GlobalTheory.IdeleCharLevel

variable (K : Type) [Field K] [NumberField K]

theorem exists_level (U : Set (FiniteAdeleRing (𝓞 K) K)) (hU : U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K)) :
    ∃ M : ℕ, M ≠ 0 ∧ ∀ a : FiniteAdeleRing (𝓞 K) K,
      (∀ P : HeightOneSpectrum (𝓞 K), Valued.v (a P) ≤ P.intValuation (M : 𝓞 K)) → a ∈ U := by
  obtain ⟨M, hM, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele K U hU
  refine ⟨M, hM.ne', fun a ha => ?_⟩
  have hM0 : (M : K) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hM1 : (M : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have := h (algebraMap K (FiniteAdeleRing (𝓞 K) K) (M : K)⁻¹ * a) fun P => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) (M : K)⁻¹) P * a P) ≤ 1
    rw [map_mul, FiniteAdeleRing.algebraMap_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀,
      ← map_natCast (algebraMap (𝓞 K) K), HeightOneSpectrum.valuation_of_algebraMap]
    have h0 : P.intValuation (M : 𝓞 K) ≠ 0 := P.intValuation_ne_zero _ hM1
    rw [inv_mul_le_iff₀ (zero_lt_iff.mpr h0), mul_one]
    exact ha P
  rwa [nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap K (FiniteAdeleRing (𝓞 K) K)) M,
    ← map_mul, mul_inv_cancel₀ hM0, map_one, one_mul] at this

end GlobalTheory.IdeleCharLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryTransvectionSubmonoidNormalDetOne
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryTransvectionSubmonoidNormalDetOne
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans

theorem IsU.transpose_mul_mul_map {R : Type} [CommRing R] {n : ℕ} {σ : R →+* R}
    {G γ : Matrix (Fin n) (Fin n) R} (h : IsU σ G γ) : γᵀ * G * γ.map σ = G := by
  ext a b
  have h1 := h (Pi.single a 1) (Pi.single b 1)
  have h2 : hf σ G (Pi.single a 1) (Pi.single b 1) = G a b := by
    simp [hf, Pi.single_apply, apply_ite σ]
  rw [h2] at h1
  rw [← h1]
  simp only [hf, Matrix.mulVec_single_one, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.col_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem IsU.det_mul_conj_det {E : Type} [Field E] {n : ℕ} {σ : E →+* E}
    {G γ : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0) (h : IsU σ G γ) : γ.det * σ γ.det = 1 := by
  have h1 := congrArg Matrix.det h.transpose_mul_mul_map
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
  have h2 : (γ.map σ).det = σ γ.det := by
    rw [RingHom.map_det]; rfl
  rw [h2] at h1
  apply mul_left_cancel₀ hG
  linear_combination h1

theorem IsU.nonsing_inv {E : Type} [Field E] {n : ℕ} {σ : E →+* E}
    {G γ : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0) (h : IsU σ G γ) : IsU σ G γ⁻¹ := by
  have hu : IsUnit γ.det := IsUnit.of_mul_eq_one _ (h.det_mul_conj_det hG)
  intro x y
  rw [← h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mulVec, Matrix.one_mulVec]

theorem tvGen_normal : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), IsHerm σ G → (∀ γ, IsU σ G γ → γ.det * σ γ.det = 1 ∧ IsU σ G γ⁻¹) ∧ (∀ m ∈ TvGen σ G, IsU σ G m ∧ m.det = 1 ∧ m⁻¹ ∈ TvGen σ G ∧ ∀ γ, IsU σ G γ → ∃ m' ∈ TvGen σ G, γ * m = m' * γ ∧ ∃ m'' ∈ TvGen σ G, m * γ = γ * m'') := by
  intro E _ _ n σ G hG
  obtain ⟨-, -, hmul, hdet, hU, hconj, -, hUmul⟩ := GlobalTheory.T.transvection_identities_unitary E n σ G hG.invol hG.herm
  refine ⟨fun γ h => ⟨h.det_mul_conj_det hG.det_ne, h.nonsing_inv hG.det_ne⟩, ?_⟩
  have key : ∀ m ∈ TvGen σ G, IsU σ G m ∧ m.det = 1 ∧ m⁻¹ ∈ TvGen σ G ∧
      ∀ γ, IsU σ G γ → ∃ m' ∈ TvGen σ G, γ * m = m' * γ := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem m hm =>
      obtain ⟨x, t, hx, ht, rfl⟩ := hm
      refine ⟨hU x t (by rw [ht, hx]; simp), by rw [hdet, hx]; simp, ?_, ?_⟩
      · have h1 : tv σ G x t * tv σ G x (-t) = 1 := by
          rw [hmul, hx]
          ext a b
          simp [tv]
        rw [Matrix.inv_eq_right_inv h1]
        exact Submonoid.subset_closure ⟨x, -t, hx, by rw [map_neg]; linear_combination -ht, rfl⟩
      · intro γ hγ
        exact ⟨tv σ G (γ *ᵥ x) t, Submonoid.subset_closure ⟨_, t, by rw [hγ, hx], ht, rfl⟩,
          hconj γ x t hγ⟩
    | one =>
      refine ⟨fun x y => by simp, by simp, by rw [inv_one]; exact one_mem _, fun γ _ => ⟨1, one_mem _, by simp⟩⟩
    | mul a b _ _ ha hb =>
      obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
      obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
      refine ⟨hUmul _ _ ha1 hb1, by rw [Matrix.det_mul, ha2, hb2, one_mul], ?_, ?_⟩
      · rw [Matrix.mul_inv_rev]; exact mul_mem hb3 ha3
      · intro γ hγ
        obtain ⟨a', ha', ea⟩ := ha4 γ hγ
        obtain ⟨b', hb', eb⟩ := hb4 γ hγ
        exact ⟨a' * b', mul_mem ha' hb', by rw [← mul_assoc, ea, mul_assoc, eb, mul_assoc]⟩
  intro m hm
  obtain ⟨h1, h2, h3, h4⟩ := key m hm
  refine ⟨h1, h2, h3, fun γ hγ => ?_⟩
  obtain ⟨m', hm', e⟩ := h4 γ hγ
  obtain ⟨m'', hm'', e'⟩ := h4 γ⁻¹ (hγ.nonsing_inv hG.det_ne)
  have hu : IsUnit γ.det := IsUnit.of_mul_eq_one _ (hγ.det_mul_conj_det hG.det_ne)
  refine ⟨m', hm', e, m'', hm'', ?_⟩
  calc m * γ = γ * (γ⁻¹ * m) * γ := by
        rw [← mul_assoc, Matrix.mul_nonsing_inv _ hu, one_mul]
    _ = γ * m'' := by
        rw [e', mul_assoc, mul_assoc, Matrix.nonsing_inv_mul _ hu, mul_one]

end GlobalTheory.UTrans
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryTransvectionSubmonoidNormalDetOneStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryTransvectionSubmonoid_normal_det_one : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), IsHerm σ G → (∀ γ, IsU σ G γ → γ.det * σ γ.det = 1 ∧ IsU σ G γ⁻¹) ∧ (∀ m ∈ TvGen σ G, IsU σ G m ∧ m.det = 1 ∧ m⁻¹ ∈ TvGen σ G ∧ ∀ γ, IsU σ G γ → ∃ m' ∈ TvGen σ G, γ * m = m' * γ ∧ ∃ m'' ∈ TvGen σ G, m * γ = γ * m'') := by
  first | exact @GlobalTheory.UTrans.tvGen_normal | exact GlobalTheory.UTrans.tvGen_normal | (intros; apply GlobalTheory.UTrans.tvGen_normal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTwoPlacesOverOfIsSquareLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTwoPlacesOverOfIsSquareLocal
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem val_integer_le_one {E Γ : Type} [Field E] [LinearOrderedCommGroupWithZero Γ]
    (u : Valuation E Γ) (x : 𝓞 E) : u (algebraMap (𝓞 E) E x) ≤ 1 := by
  have h : IsIntegral u.integer (algebraMap (𝓞 E) E x) :=
    (RingOfIntegers.isIntegral_coe x).tower_top
  exact (Valuation.integer.integers u).mem_of_integral h

theorem exists_centre_over {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (u : Valuation E ℤᵐ⁰)
    (hu : ∀ a : F, u (algebraMap F E a) = v.valuation F a) :
    ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v ∧
      ∀ x : 𝓞 E, x ∈ w.asIdeal ↔ u (algebraMap (𝓞 E) E x) < 1 := by
  let I : Ideal (𝓞 E) :=
    { carrier := {x | u (algebraMap (𝓞 E) E x) < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add (f := _)] at *
        exact u.map_add_lt ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_integer_le_one u c)) hx }
  have hI : ∀ x : 𝓞 E, x ∈ I ↔ u (algebraMap (𝓞 E) E x) < 1 := fun x => Iff.rfl
  have hp : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hI]; simp
    · intro a b hab
      rw [hI, map_mul, map_mul] at hab
      rw [hI, hI]
      by_contra hc
      push Not at hc
      exact absurd hab (not_lt.2 (one_le_mul hc.1 hc.2))
  have hc : ∀ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) a ∈ I ↔ a ∈ v.asIdeal := by
    intro a
    rw [hI, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E, hu]
    exact v.valuation_lt_one_iff_mem a
  have hne : I ≠ ⊥ := by
    intro h0
    apply v.ne_bot
    rw [eq_bot_iff]
    intro a ha
    have := (hc a).2 ha
    rw [h0, Ideal.mem_bot] at this
    rw [Ideal.mem_bot]
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))).1 this
  refine ⟨⟨I, hp, hne⟩, ?_, hI⟩
  ext a
  exact hc a

theorem IsQuad.exists_embedding_root {F E L : Type} [Field F] [Field E] [Algebra F E] [Field L]
    {δ : F} {θ : E} {σ : E ≃ₐ[F] E} (h : IsQuad δ θ σ) (φ : F →+* L) (r : L)
    (hr : φ δ = r * r) :
    ∃ ψ : E →+* L, (∀ a : F, ψ (algebraMap F E a) = φ a) ∧ ψ θ = r := by
  choose A B hAB using h.span
  have key : ∀ (x : E) (a b : F), x = algebraMap F E a + algebraMap F E b * θ →
      φ (A x) + φ (B x) * r = φ a + φ b * r := by
    intro x a b hx
    have := h.coord_indep (A x - a) (B x - b) (by
      rw [map_sub, map_sub]; linear_combination hx - hAB x)
    rw [sub_eq_zero.1 this.1, sub_eq_zero.1 this.2]
  refine ⟨{ toFun := fun x => φ (A x) + φ (B x) * r
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩
  · rw [key 1 1 0 (by simp)]; simp
  · intro x y
    rw [key (x * y) (A x * A y + δ * B x * B y) (A x * B y + B x * A y) (by
      simp only [map_add (f := _), map_mul, ← h.sq]
      linear_combination y * hAB x + (algebraMap F E (A x) + algebraMap F E (B x) * θ) * hAB y)]
    simp only [map_add (f := _), map_mul, hr]; ring
  · rw [key 0 0 0 (by simp)]; simp
  · intro x y
    rw [key (x + y) (A x + A y) (B x + B y) (by
      simp only [map_add (f := _)]
      linear_combination hAB x + hAB y)]
    simp only [map_add (f := _)]; ring
  · intro a
    change φ (A _) + φ (B _) * r = _
    rw [key _ a 0 (by simp)]; simp
  · change φ (A _) + φ (B _) * r = _
    rw [key _ 0 1 (by simp)]; simp

theorem exists_val_sub_mul_lt_one {F L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ]
    [Valued L Γ] (φ : F → L) (hφ : DenseRange φ) (r c : L) :
    ∃ ρ : F, Valued.v ((r - φ ρ) * c) < (1 : Γ) := by
  have hopen : IsOpen {x : L | Valued.v x < (1 : Γ)} := by
    simpa only [Valuation.restrict_lt_one_iff] using (Valued.isOpen_ball L 1)
  have hcont : Continuous fun x : L => (r - x) * c := by fun_prop
  exact hφ.exists_mem_open (hopen.preimage hcont) ⟨r, by simp⟩

theorem two_places_of_isSquare : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ v : HeightOneSpectrum (𝓞 F), IsSquare (algebraMap F (v.adicCompletion F) δ) → ∃ w w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ w.under (𝓞 F) = v ∧ w'.under (𝓞 F) = v := by
  intro F E _ _ _ _ _ δ θ σ h v ⟨r, hr⟩
  obtain ⟨ψ, hψ, hθ⟩ := h.exists_embedding_root (algebraMap F (v.adicCompletion F)) r hr
  let u : Valuation E ℤᵐ⁰ := (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).comap ψ
  let u' : Valuation E ℤᵐ⁰ := u.comap (σ : E →+* E)
  have hu : ∀ a : F, u (algebraMap F E a) = v.valuation F a := by
    intro a
    change Valued.v (ψ _) = _
    rw [hψ]
    exact v.valuedAdicCompletion_eq_valuation' a
  have hu' : ∀ a : F, u' (algebraMap F E a) = v.valuation F a := by
    intro a
    change u (σ _) = _
    rw [AlgEquiv.commutes, hu]
  obtain ⟨w, hw, hwm⟩ := exists_centre_over v u hu
  obtain ⟨w', hw', hwm'⟩ := exists_centre_over v u' hu'
  refine ⟨w, w', ?_, hw, hw'⟩
  rintro rfl
  have hr0 : r ≠ 0 := by
    rw [← hθ]; exact (map_ne_zero ψ).2 h.root_ne_zero
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by
    have : (2 : v.adicCompletion F) = algebraMap F _ 2 := by rw [map_ofNat]
    rw [this]; exact (map_ne_zero _).2 two_ne_zero
  obtain ⟨ρ, hρ⟩ := exists_val_sub_mul_lt_one _ (HeightOneSpectrum.denseRange_algebraMap F v)
    r (2 * r)⁻¹
  set t := (r - algebraMap F (v.adicCompletion F) ρ) * (2 * r)⁻¹ with ht
  have hn : θ - algebraMap F E ρ ≠ 0 := by
    intro h0
    exact one_ne_zero (h.coord_indep (-ρ) 1 (by simp; linear_combination h0)).2
  have hd : -θ - algebraMap F E ρ ≠ 0 := by
    intro h0
    exact one_ne_zero (h.coord_indep ρ 1 (by simp; linear_combination -h0)).2
  set y := (θ - algebraMap F E ρ) / (-θ - algebraMap F E ρ) with hy
  have hy1 : y * σ y = 1 := by
    rw [hy, map_div₀, map_sub, map_sub, map_neg, h.conj, AlgEquiv.commutes, neg_neg]
    field_simp
  have huy : u y < 1 := by
    change Valued.v (ψ y) < 1
    have e1 : r - algebraMap F (v.adicCompletion F) ρ = 2 * r * t := by
      rw [ht]; field_simp
    have e2 : -r - algebraMap F (v.adicCompletion F) ρ = -(2 * r * (1 - t)) := by
      linear_combination e1
    rw [hy, map_div₀, map_sub, map_sub, map_neg, hθ, hψ, e1, e2, map_div₀, Valuation.map_neg,
      map_mul _ _ t, map_mul _ _ (1 - t), Valuation.map_one_sub_of_lt _ hρ, mul_one,
      mul_div_cancel_left₀ _ ((Valuation.ne_zero_iff _).2 (mul_ne_zero h2 hr0))]
    exact hρ
  have huu : u y * u' y = 1 := by
    change u y * u (σ y) = 1
    rw [← map_mul, hy1, map_one]
  obtain ⟨n, ⟨d, hd'⟩, hnd | hnd⟩ := w.exists_primeCompl_mul_eq_or_mul_eq (K := E) y
  · have hd1 : 1 ≤ u' (algebraMap (𝓞 E) E d) := not_lt.1 fun a => hd' ((hwm' d).2 a)
    have h1 : u' y ≤ 1 := by
      have := val_integer_le_one u' n
      rw [← hnd, map_mul] at this
      exact le_trans (le_mul_of_one_le_right' hd1) this
    have : u y * u' y < 1 := lt_of_le_of_lt (mul_le_of_le_one_right' h1) huy
    exact this.ne huu
  · have hd1 : 1 ≤ u (algebraMap (𝓞 E) E d) := not_lt.1 fun a => hd' ((hwm d).2 a)
    rw [← hnd, map_mul] at hd1
    exact absurd (lt_of_le_of_lt (mul_le_of_le_one_right' (val_integer_le_one u n)) huy)
      (not_lt.2 hd1)

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTwoPlacesOverOfIsSquareLocalStatement
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_two_places_over_of_isSquare_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ v : HeightOneSpectrum (𝓞 F), IsSquare (algebraMap F (v.adicCompletion F) δ) → ∃ w w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ w.under (𝓞 F) = v ∧ w'.under (𝓞 F) = v := by
  first | exact @GlobalTheory.QNorm.two_places_of_isSquare | exact GlobalTheory.QNorm.two_places_of_isSquare | (intros; apply GlobalTheory.QNorm.two_places_of_isSquare <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsKum
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_isKum : ∀ (p : ℕ) (F : Type) [Field F] [CharZero F] (ζ δ : F), p.Prime → IsPrimitiveRoot ζ p → (∀ r : F, r ^ p ≠ δ) → ∃ (E : Type) (_ : Field E) (_ : Algebra F E) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ := by
  intro p F _ _ ζ δ hp hζ hδ
  have : Fact (Irreducible (X ^ p - C δ)) := ⟨X_pow_sub_C_irreducible_of_prime hp hδ⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨AdjoinRoot (X ^ p - C δ), inferInstance, inferInstance, AdjoinRoot.root _,
    autAdjoinRootXPowSubC p δ hζ.toRootsOfUnity, ?_⟩
  refine ⟨hp, hζ, hδ, ?_, ?_, AdjoinRoot.adjoinRoot_eq_top⟩
  · have h := AdjoinRoot.eval₂_root (X ^ p - C δ)
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h
    rw [h, AdjoinRoot.algebraMap_eq]
  · rw [autAdjoinRootXPowSubC_root, Algebra.smul_def, IsPrimitiveRoot.val_toRootsOfUnity_coe]

end GlobalTheory.CNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsDenominatorPrimesPrescribed
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep

theorem exists_pow_eq_span_singleton (E : Type) [Field E] [NumberField E] (a : Ideal (𝓞 E))
    (ha : a ≠ ⊥) : ∃ (h : ℕ) (s : 𝓞 E), h ≠ 0 ∧ a ^ h = Ideal.span {s} := by
  have ha0 : a ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero ha
  have hone : ClassGroup.mk0 ⟨a, ha0⟩ ^ Fintype.card (ClassGroup (𝓞 E)) = 1 := pow_card_eq_one
  rw [← map_pow, SubmonoidClass.mk_pow] at hone
  have hprin : (a ^ Fintype.card (ClassGroup (𝓞 E))).IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff _).mp hone
  exact ⟨Fintype.card (ClassGroup (𝓞 E)), Submodule.IsPrincipal.generator _, Fintype.card_ne_zero,
    (Ideal.span_singleton_generator _).symm⟩

theorem exists_denominator_primes_prescribed :
    ∀ (E : Type) [Field E] [NumberField E] (Q : Ideal (𝓞 E) → Prop) (ι : Type) [Finite ι]
      (x : ι → E),
      (∀ i, ∀ P : HeightOneSpectrum (𝓞 E), ¬ Q P.asIdeal → P.valuation E (x i) ≤ 1) →
      ∃ s : 𝓞 E, s ≠ 0 ∧ (∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → Q P) ∧
        ∀ i, ∃ b : 𝓞 E, (s : E) * x i = (b : E) := by
  intro E _ _ Q ι _ x hx
  classical
  have : Fintype ι := Fintype.ofFinite ι

  have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : E), v.valuation E y ≤ 1 →
      ∃ u : 𝓞 E, u ∉ v.asIdeal ∧ ∃ b : 𝓞 E, (u : E) * y = (b : E) := by
    intro v y hy
    obtain ⟨n, d, hnd | hnd⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := E) y
    · exact ⟨d, d.2, n, by rw [mul_comm]; exact hnd⟩
    · have hd : v.valuation E (algebraMap (𝓞 E) E d) = 1 := by
        rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
        exact d.2
      have hprod : v.valuation E y * v.valuation E (algebraMap (𝓞 E) E n) = 1 := by
        rw [← map_mul, hnd, hd]
      have hn1 : 1 ≤ v.valuation E (algebraMap (𝓞 E) E n) := by
        calc (1 : _) = v.valuation E y * v.valuation E (algebraMap (𝓞 E) E n) := hprod.symm
          _ ≤ v.valuation E (algebraMap (𝓞 E) E n) := mul_le_of_le_one_left' hy
      have hn : n ∉ v.asIdeal := by
        rw [← HeightOneSpectrum.intValuation_eq_one_iff, ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
        exact le_antisymm (HeightOneSpectrum.valuation_le_one _ _) hn1
      exact ⟨n, hn, d, by rw [mul_comm]; exact hnd⟩

  let A : ι → Ideal (𝓞 E) := fun i =>
    { carrier := {r | ∃ b : 𝓞 E, (r : E) * x i = (b : E)}
      add_mem' := by
        rintro r₁ r₂ ⟨b₁, h₁⟩ ⟨b₂, h₂⟩
        exact ⟨b₁ + b₂, by push_cast; rw [add_mul, h₁, h₂]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c r ⟨b, h⟩
        exact ⟨c * b, by simp only [smul_eq_mul]; push_cast; rw [mul_assoc, h]⟩ }
  have memA : ∀ i r, r ∈ A i ↔ ∃ b : 𝓞 E, (r : E) * x i = (b : E) := fun _ _ => Iff.rfl
  let A0 : Ideal (𝓞 E) := ⨅ i, A i
  have hA0 : A0 ≠ ⊥ := by
    obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E)) x
    have hc0 : (c : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero c
    intro hbot
    apply hc0
    have hcmem : (c : 𝓞 E) ∈ A0 := by
      refine (Submodule.mem_iInf _).mpr fun i => (memA i _).mpr ?_
      obtain ⟨b, hb⟩ := hc i
      exact ⟨b, by rw [Algebra.smul_def] at hb; exact hb.symm⟩
    rw [hbot] at hcmem
    exact (Submodule.mem_bot _).mp hcmem
  obtain ⟨h, s, hh, hs⟩ := exists_pow_eq_span_singleton E A0 hA0
  have hsA : s ∈ A0 := Ideal.pow_le_self hh (hs ▸ Ideal.mem_span_singleton_self s)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hs
    exact hA0 (pow_eq_zero_iff hh |>.mp hs)
  refine ⟨s, hs0, ?_, fun i => (memA i s).mp ((Submodule.mem_iInf _).mp hsA i)⟩
  intro P hP hsP
  by_contra hQ
  have hPne : P ≠ ⊥ := fun hb => hs0 ((Submodule.mem_bot _).mp (hb ▸ hsP))
  let v : HeightOneSpectrum (𝓞 E) := ⟨P, hP, hPne⟩
  have hle : A0 ≤ P := by
    refine hP.le_of_pow_le (n := h) ?_
    rw [hs, Ideal.span_le, Set.singleton_subset_iff]
    exact hsP
  choose u hu b hb using fun i => key v (x i) (hx i v hQ)
  have hU : (∏ i, u i) ∉ P := by
    intro hmem
    obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hu i hi
  apply hU
  refine hle ((Submodule.mem_iInf _).mpr fun i => ?_)
  exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem u (Finset.mem_univ i)) ((memA i _).mpr ⟨b i, hb i⟩)

end GlobalTheory.UnRep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAnisotropicOrthogonalBasisHermitian
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAnisotropicOrthogonalBasisHermitian
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep

theorem exists_anisotropic_orthogonal_basis :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G →
      ∃ x : Fin n → Fin n → E, (∀ i, hermE c G (x i) (x i) ≠ 0) ∧
        (∀ i j, i ≠ j → hermE c G (x i) (x j) = 0) ∧ Submodule.span E (Set.range x) = ⊤ := by
  intro F E _ _ _ _ _ c n G ⟨hc, _, hG, hdet⟩
  let σ : E →+* E := (c : E →+* E)
  have he : ∀ x y : Fin n → E, hermE c G x y = x ⬝ᵥ G *ᵥ (σ ∘ y) := fun x y =>
    (GlobalTheory.HermDiag.dotProduct_mulVec_comp_eq_sum σ G x y).symm
  obtain ⟨v, hv⟩ := GlobalTheory.HermDiag.exists_orthogonal_basis_dotProduct (c := σ) two_ne_zero hc hG
  have hd := GlobalTheory.HermDiag.congr_diagonal_of_orthogonal σ v hv
  refine ⟨v, fun i => ?_, fun i j hij => ?_, v.span_eq⟩
  · rw [he]
    exact GlobalTheory.HermDiag.ne_zero_of_congr_diagonal (GlobalTheory.HermDiag.det_of_basis_ne_zero v) hd hdet i
  · rw [he]
    exact hv i j hij

end GlobalTheory.UnRep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAnisotropicOrthogonalBasisHermitianStatement
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_anisotropic_orthogonal_basis_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∃ x : Fin n → Fin n → E, (∀ i, hermE c G (x i) (x i) ≠ 0) ∧ (∀ i j, i ≠ j → hermE c G (x i) (x j) = 0) ∧ Submodule.span E (Set.range x) = ⊤ := by
  first | exact @GlobalTheory.UnRep.exists_anisotropic_orthogonal_basis | exact GlobalTheory.UnRep.exists_anisotropic_orthogonal_basis | (intros; apply GlobalTheory.UnRep.exists_anisotropic_orthogonal_basis <;> assumption)
end
end
