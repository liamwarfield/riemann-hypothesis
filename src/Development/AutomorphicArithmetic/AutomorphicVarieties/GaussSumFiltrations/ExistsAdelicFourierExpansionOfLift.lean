module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HasQExpansionAffineTranslateCoeff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.FinSupp

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.CountSpanInt
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
open scoped nonZeroDivisors

namespace GlobalTheory.HilbertThetaSeries.DualIdele

variable {K : Type} [Field K] [NumberField K]

theorem count_span_int (v : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K} (hr : r ≠ 0) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r)) =
      -WithZero.log (v.valuation K (algebraMap (𝓞 K) K r)) := by
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v
    (by rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]),
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ hr, WithZero.log_exp,
    neg_neg]

theorem count_span (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) = -WithZero.log (v.valuation K x) := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (𝓞 K)⁰ x
  have hs : (s : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hr : r ≠ 0 := by
    rintro rfl
    exact hx (by simp)
  have hs' : algebraMap (𝓞 K) K s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hs
  have e : IsLocalization.mk' K r s * algebraMap (𝓞 K) K s = algebraMap (𝓞 K) K r :=
    IsLocalization.mk'_spec K r s
  have e2 := congrArg (FractionalIdeal.count K v) (congrArg (FractionalIdeal.spanSingleton (𝓞 K)⁰) e)
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K v
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr hx) ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr hs'),
    count_span_int v hs, count_span_int v hr] at e2
  have e3 := congrArg (v.valuation K) e
  rw [map_mul] at e3
  have hv1 : v.valuation K (algebraMap (𝓞 K) K s) ≠ 0 := (map_ne_zero _).mpr hs'
  have hv2 : v.valuation K (IsLocalization.mk' K r s) ≠ 0 := (map_ne_zero _).mpr hx
  rw [← e3, WithZero.log_mul hv2 hv1] at e2
  linarith

theorem exists_ideal (y : (Af K)ˣ) : ∃ I : FractionalIdeal (𝓞 K)⁰ K, I ≠ 0 ∧
    ∀ w, FractionalIdeal.count K w I = -WithZero.log (Valued.v (pLoc K w (y : Af K))) := by
  have hy := (FiniteAdeleRing.isUnit_iff.1 y.isUnit).2
  refine ⟨∏ᶠ w : HeightOneSpectrum (𝓞 K), (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
    (-WithZero.log (Valued.v (pLoc K w (y : Af K)))), ?_, fun w => ?_⟩
  · refine finprod_induction (fun I : FractionalIdeal (𝓞 K)⁰ K => I ≠ 0) one_ne_zero
      (fun _ _ => mul_ne_zero) fun w => zpow_ne_zero _ ?_
    exact FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot
  · refine FractionalIdeal.count_finprod K w (fun w => -WithZero.log (Valued.v (pLoc K w (y : Af K)))) ?_
    filter_upwards [hy] with v hv
    have : Valued.v (pLoc K v (y : Af K)) = 1 := hv
    rw [this, WithZero.log_one, neg_zero]

theorem genD_of_trace : ∀ (F : Type) [Field F] [NumberField F] (y : (Af F)ˣ) (ξ : F), ξ ≠ 0 → (∀ b : F, (∀ w, w.valuation F b ≤ Valued.v (pLoc F w (y : Af F))) → ∃ n : ℤ, Algebra.trace ℚ F (ξ * b) = n) → ∃ 𝔪, GenD (algebraMap F (Af F) ξ * (y : Af F)) 𝔪 := by
  intro F _ _ y ξ hξ h
  obtain ⟨I, hI, hc⟩ := exists_ideal y
  have hy0 : ∀ w, Valued.v (pLoc F w (y : Af F)) ≠ 0 := fun w =>
    (map_ne_zero _).2 ((FiniteAdeleRing.isUnit_iff.1 y.isUnit).1 w)
  have hmem : ξ ∈ FractionalIdeal.dual ℤ ℚ I := by
    rw [FractionalIdeal.mem_dual hI]
    intro b hb
    obtain ⟨n, hn⟩ := h b fun w => by
      rcases eq_or_ne b 0 with rfl | hb0
      · simp
      have h1 := FractionalIdeal.count_mono F w ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr hb0)
        (FractionalIdeal.spanSingleton_le_iff_mem.2 hb)
      rw [hc, count_span w hb0, neg_le_neg_iff] at h1
      exact (WithZero.log_le_log ((map_ne_zero _).2 hb0) (hy0 w)).1 h1
    exact ⟨n, by rw [Algebra.traceForm_apply]; simpa using hn.symm⟩
  have hD := FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))
  have hd := coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have hd0 : (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := hd ▸ inv_ne_zero hD
  have hs0 : FractionalIdeal.spanSingleton (𝓞 F)⁰ ξ ≠ 0 := (FractionalIdeal.spanSingleton_ne_zero_iff).mpr hξ
  have hle : FractionalIdeal.spanSingleton (𝓞 F)⁰ ξ * (I * (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)) ≤ 1 := by
    have h1 := FractionalIdeal.spanSingleton_le_iff_mem.2 hmem
    rw [FractionalIdeal.dual_eq_mul_inv] at h1
    refine (mul_le_mul_left h1 _).trans (le_of_eq ?_)
    rw [hd]
    field_simp
  obtain ⟨𝔪, h𝔪⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hm0 : 𝔪 ≠ ⊥ := FractionalIdeal.coeIdeal_ne_zero.1 (h𝔪 ▸ mul_ne_zero hs0 (mul_ne_zero hI hd0))
  refine ⟨𝔪, hm0, fun w => ?_⟩
  have h2 := congrArg (FractionalIdeal.count F w) h𝔪
  rw [FractionalIdeal.count_mul F w hs0 (mul_ne_zero hI hd0), FractionalIdeal.count_mul F w hI hd0,
    FractionalIdeal.count_coe F w hm0, FractionalIdeal.count_coe F w (FractionalIdeal.coeIdeal_ne_zero.1 hd0),
    hc, count_span w hξ] at h2
  have h3 : Valued.v (pLoc F w (algebraMap F (Af F) ξ)) = w.valuation F ξ :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w ξ
  have hx0 : w.valuation F ξ ≠ 0 := (map_ne_zero _).2 hξ
  rw [map_mul, map_mul, h3, ← WithZero.exp_log hx0, ← WithZero.exp_log (hy0 w), ← WithZero.exp_add]
  congr 1
  unfold ordI
  linarith

end GlobalTheory.HilbertThetaSeries.DualIdele
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ConstEqZero
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.QUniq

def chr {V : Type} [Fintype V] (μ x : V → ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ v, (μ v : ℂ) * (x v : ℂ))

theorem chr_add {V : Type} [Fintype V] (μ x y : V → ℝ) : chr μ (x + y) = chr μ x * chr μ y := by
  simp only [chr, Pi.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib, Complex.exp_add]

theorem chr_add' {V : Type} [Fintype V] (μ ν x : V → ℝ) : chr (μ + ν) x = chr μ x * chr ν x := by
  simp only [chr, Pi.add_apply, Complex.ofReal_add, mul_add, add_mul, Finset.sum_add_distrib, Complex.exp_add]

theorem chr_zero {V : Type} [Fintype V] (μ : V → ℝ) : chr μ 0 = 1 := by simp [chr]

theorem chr_zero' {V : Type} [Fintype V] (x : V → ℝ) : chr 0 x = 1 := by simp [chr]

theorem norm_chr {V : Type} [Fintype V] (μ x : V → ℝ) : ‖chr μ x‖ = 1 := by
  have : (2 * Real.pi * Complex.I * ∑ v, (μ v : ℂ) * (x v : ℂ)) = ((2 * Real.pi * ∑ v, μ v * x v : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [chr, this, Complex.norm_exp_ofReal_mul_I]

theorem exists_chr {V : Type} [Fintype V] (μ : V → ℝ) (h : μ ≠ 0) : ∃ g, chr μ g = -1 := by
  classical
  obtain ⟨v, hv⟩ := Function.ne_iff.1 h
  have hv' : (μ v : ℂ) ≠ 0 := by exact_mod_cast hv
  refine ⟨Pi.single v (1 / (2 * μ v)), ?_⟩
  have : ∑ w, (μ w : ℂ) * ((Pi.single v (1 / (2 * μ v)) : V → ℝ) w : ℂ) = 1 / 2 := by
    rw [Finset.sum_eq_single v]
    · simp only [Pi.single_eq_same]; push_cast; field_simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · simp
  rw [chr, this, ← Complex.exp_pi_mul_I]
  congr 1; ring

theorem hasSum_congr' {ι : Type} {f g : ι → ℂ} {d : ℂ} (h : HasSum f d) (e : ∀ i, g i = f i) : HasSum g d := by
  rwa [show g = f from funext e]

private theorem hasSum_average_chr_of_hasSum {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (C : ι → ℂ) (d : ℂ)
    (h : ∀ x, HasSum (fun i => C i * chr (μ i) x) d) (g : V → ℝ) (x : V → ℝ) :
    HasSum (fun i => C i * ((1 + chr (μ i) g) / 2) * chr (μ i) x) d := by
  have h2 := ((h x).add (h (x + g))).div_const 2
  have hd : (d + d) / 2 = d := by ring
  rw [hd] at h2
  refine hasSum_congr' h2 (fun i => ?_)
  rw [chr_add]
  ring

private theorem norm_one_add_chr_div_two_le_one {V : Type} [Fintype V] (μ x : V → ℝ) : ‖(1 + chr μ x) / 2‖ ≤ 1 := by
  rw [norm_div]
  have h1 := norm_add_le (1 : ℂ) (chr μ x)
  rw [norm_one, norm_chr] at h1
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  linarith

theorem kill_freq {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (B : ι → ℂ) (d : ℂ) (hμ : ∀ i, B i ≠ 0 → μ i ≠ 0)
    (h : ∀ x, HasSum (fun i => B i * chr (μ i) x) d) (S : Finset ι) :
    ∃ C : ι → ℂ, (∀ i, ‖C i‖ ≤ ‖B i‖) ∧ (∀ i ∈ S, C i = 0) ∧ ∀ x, HasSum (fun i => C i * chr (μ i) x) d := by
  classical
  refine Finset.induction_on S ?_ ?_
  · exact ⟨B, fun i => le_rfl, by simp, h⟩
  · intro j S _ ih
    obtain ⟨C, hCn, hCS, hC⟩ := ih
    by_cases hj : C j = 0
    · refine ⟨C, hCn, fun i hi => ?_, hC⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hj
      · exact hCS i hi
    · have hB : B j ≠ 0 := by
        intro hB0
        apply hj
        have h3 := hCn j
        rw [hB0, norm_zero] at h3
        exact norm_le_zero_iff.mp h3
      obtain ⟨g, hg⟩ := exists_chr (μ j) (hμ j hB)
      refine ⟨fun i => C i * ((1 + chr (μ i) g) / 2), fun i => ?_, fun i hi => ?_,
        fun x => hasSum_average_chr_of_hasSum μ C d hC g x⟩
      · rw [norm_mul]
        calc ‖C i‖ * ‖(1 + chr (μ i) g) / 2‖ ≤ ‖C i‖ * 1 :=
              mul_le_mul_of_nonneg_left (norm_one_add_chr_div_two_le_one _ _) (norm_nonneg _)
          _ ≤ ‖B i‖ := by
              rw [mul_one]
              exact hCn i
      · rcases Finset.mem_insert.mp hi with rfl | hi
        · simp [hg]
        · simp [hCS i hi]

theorem const_eq_zero {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (B : ι → ℂ) (d : ℂ) (hμ : ∀ i, B i ≠ 0 → μ i ≠ 0)
    (h : ∀ x, HasSum (fun i => B i * chr (μ i) x) d) : d = 0 := by
  classical
  have hB : Summable B := by
    have h0 := (h 0).summable
    simpa [chr_zero] using h0
  have hnB : Summable (fun i => ‖B i‖) := summable_norm_iff.mpr hB
  have key : ∀ ε > 0, ‖d‖ ≤ ε := by
    intro ε hε
    obtain ⟨S, hS⟩ := (summable_iff_vanishing_norm.mp hnB) ε hε
    obtain ⟨C, hCn, hCS, hC⟩ := kill_freq μ B d hμ h S
    have hC0 := Filter.Tendsto.norm (hC 0)
    refine le_of_tendsto' hC0 (fun t => ?_)
    simp only [chr_zero, mul_one]
    have e1 : ∑ i ∈ t \ S, C i = ∑ i ∈ t, C i :=
      Finset.sum_subset Finset.sdiff_subset (fun i hi hni => hCS i (by
        rw [Finset.mem_sdiff] at hni
        tauto))
    rw [← e1]
    calc ‖∑ i ∈ t \ S, C i‖ ≤ ∑ i ∈ t \ S, ‖C i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ t \ S, ‖B i‖ := Finset.sum_le_sum (fun i _ => hCn i)
      _ ≤ ‖∑ i ∈ t \ S, ‖B i‖‖ := Real.le_norm_self _
      _ ≤ ε := (hS _ Finset.sdiff_disjoint).le
  by_contra hd
  have hpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have h3 := key (‖d‖ / 2) (by linarith)
  linarith

theorem coef_eq_zero {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (B : ι → ℂ) (hμ : Function.Injective μ)
    (h : ∀ x, HasSum (fun i => B i * chr (μ i) x) 0) (j : ι) : B j = 0 := by
  classical
  apply neg_eq_zero.mp
  apply const_eq_zero (fun i => μ i + -μ j) (Function.update B j 0) (-B j)
  · intro i hi h0
    have hij : i ≠ j := by
      rintro rfl
      simp at hi
    exact hij (hμ (add_neg_eq_zero.mp h0))
  · intro x
    have h1 := ((h x).mul_left (chr (-μ j) x)).update j 0
    have hc : chr (-μ j) x * chr (μ j) x = 1 := by
      rw [← chr_add', neg_add_cancel, chr_zero']
    have hval : (0 - chr (-μ j) x * (B j * chr (μ j) x) + chr (-μ j) x * 0) = -B j := by
      linear_combination (-B j) * hc
    rw [hval] at h1
    refine hasSum_congr' h1 (fun i => ?_)
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Function.update_of_ne hij, Function.update_of_ne hij, chr_add']
      ring

end GlobalTheory.HilbertThetaSeries.QUniq

private theorem ez_at_imaginary_unit_shift_eq {F : Type} [Field F] [NumberField F] (ζ : F) (x : InfinitePlace F → ℝ) :
    ez ζ (fun v => UpperHalfPlane.mk ((x v : ℂ) + Complex.I) (by simp)) =
      GlobalTheory.HilbertThetaSeries.QUniq.chr (fun v => reAt v ζ) x *
        Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ζ : ℂ) * Complex.I) := by
  simp only [ez, GlobalTheory.HilbertThetaSeries.QUniq.chr, UpperHalfPlane.coe_mk]
  rw [← Complex.exp_add]
  congr 1
  simp only [mul_add, Finset.sum_add_distrib]


open GlobalTheory.HilbertThetaSeries.QUniq in
theorem GlobalTheory.HilbertThetaSeries.hasQ_unique : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f : Hn F → ℂ) (a b : F → ℂ),
    HasQ f a → HasQ f b → a = b := by
  intro F _ _ _ f a b ha hb
  funext ξ
  have hinj : Function.Injective (fun ζ : F => fun v : InfinitePlace F => reAt v ζ) := by
    intro ζ η hζη
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    have hv := IsTotallyReal.isReal v
    have h1 := congrFun hζη v
    simp only [reAt] at h1
    apply (InfinitePlace.embedding_of_isReal hv).injective
    rw [← InfinitePlace.embedding_of_isReal_apply hv ζ, ← InfinitePlace.embedding_of_isReal_apply hv η,
      Complex.ofReal_re, Complex.ofReal_re] at h1
    exact h1
  have hsum : ∀ x : InfinitePlace F → ℝ, HasSum (fun ζ => ((a ζ - b ζ) *
      Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ζ : ℂ) * Complex.I)) *
        chr (fun v => reAt v ζ) x) 0 := by
    intro x
    have h2 := (ha.2 (fun v => UpperHalfPlane.mk ((x v : ℂ) + Complex.I) (by simp))).sub
      (hb.2 (fun v => UpperHalfPlane.mk ((x v : ℂ) + Complex.I) (by simp)))
    rw [sub_self] at h2
    refine hasSum_congr' h2 (fun ζ => ?_)
    simp only [ez_at_imaginary_unit_shift_eq]
    ring
  have key := coef_eq_zero (fun ζ : F => fun v => reAt v ζ) _ hinj hsum ξ
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right (Complex.exp_ne_zero _))
end
end

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.LiftExp

variable {F : Type} [Field F] [NumberField F]

theorem genD_eq {y : Af F} {𝔪 𝔫 : Ideal (𝓞 F)} (h : GenD y 𝔪) (h' : GenD y 𝔫) : 𝔪 = 𝔫 := by
  have hc : ∀ w : HeightOneSpectrum (𝓞 F), ordI w 𝔪 = ordI w 𝔫 := fun w => by
    have := (h.2 w).symm.trans (h'.2 w)
    rw [WithZero.exp_inj] at this
    omega
  rw [← Ideal.finprod_heightOneSpectrum_factorization h.1, ← Ideal.finprod_heightOneSpectrum_factorization h'.1]
  refine finprod_congr fun w => ?_
  exact congrArg (fun n => w.asIdeal ^ n) (hc w)

theorem coefAt_of_genD {y : Af F} {𝔪 : Ideal (𝓞 F)} (h : GenD y 𝔪) (a : Ideal (𝓞 F) → ℂ) : coefAt a y = a 𝔪 := by
  have h' : ∃ 𝔪, GenD y 𝔪 := ⟨𝔪, h⟩
  rw [coefAt, dif_pos h', genD_eq h'.choose_spec h]

theorem ordI_eventually {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ordI w I = 0 := by
  have := Associates.finite_factors (R := 𝓞 F) hI
  filter_upwards [this] with w hw
  exact_mod_cast hw

theorem exists_unit_genD {𝔪 : Ideal (𝓞 F)} (h : 𝔪 ≠ ⊥) : ∃ y : (Af F)ˣ, GenD (y : Af F) 𝔪 := by
  choose t ht using fun w : HeightOneSpectrum (𝓞 F) => w.valuedAdicCompletion_surjective F
    (WithZero.exp ((ordI w (differentIdeal ℤ (𝓞 F)) : ℤ) - (ordI w 𝔪 : ℤ)))
  have hf : ∀ᶠ w in Filter.cofinite, Valued.v (t w) = 1 := by
    filter_upwards [ordI_eventually h, ordI_eventually (I := differentIdeal ℤ (𝓞 F)) differentIdeal_ne_bot] with w h1 h2
    rw [ht, h1, h2]; simp
  let a : FiniteAdeleRing (𝓞 F) F := ⟨t, by
    filter_upwards [hf] with w hw
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hw.le⟩
  have hu : IsUnit a := FiniteAdeleRing.isUnit_iff.2 ⟨fun w hw => by
    have := ht w
    rw [show t w = 0 from hw, map_zero] at this
    exact WithZero.exp_ne_zero this.symm, hf⟩
  exact ⟨hu.unit, h, fun w => ht w⟩

theorem aff_mul {R : Type} [CommRing R] (y z : Rˣ) (x : R) : aff (y * z) x = aff y 0 * aff z (((y⁻¹ : Rˣ) : R) * x) := by
  apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

theorem toFin_aff (ε : Fˣ) (b : F) :
    toFin (aff ε b) = aff (Units.map (algebraMap F (Af F)).toMonoidHom ε) (algebraMap F (Af F) b) := by
  apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [toFin, aff, Matrix.GeneralLinearGroup.map]

end GlobalTheory.HilbertThetaSeries.LiftExp

set_option linter.unusedSectionVars false

namespace GlobalTheory.HilbertThetaSeries.LiftExp

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem rhom_apply (x : F) (v : InfinitePlace F) : rhom x v = reAt v x := by
  have hv := IsTotallyReal.isReal v
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply hv, Complex.ofReal_re]; rfl

theorem det_toInf (γ : GL (Fin 2) F) (v : InfinitePlace F) :
    ((toInf γ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v = reAt v γ.val.det := by
  have : ((toInf γ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)) = (γ : Matrix (Fin 2) (Fin 2) F).map rhom := rfl
  rw [this]; change ((rhom (F := F)).mapMatrix (γ : Matrix (Fin 2) (Fin 2) F)).det v = _
  rw [← RingHom.map_det, rhom_apply]

theorem det_aff {R : Type} [CommRing R] (y : Rˣ) (x : R) : (aff y x).val.det = y := by
  simp [aff, Matrix.det_fin_two]

theorem slash_weight_smul (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) (c : ℂ) (f : Hn F → ℂ) : sl0 k h (c • f) = c • sl0 k h f := by
  funext z; simp only [sl0, Pi.smul_apply, smul_eq_mul]; ring

theorem tp_one : TP (1 : F) := fun v => by simp [reAt]

theorem et_zero : et (0 : F) = 1 := by simp [et]

theorem trace_int_of_et {x : F} (h : et x = 1) : ∃ n : ℤ, Algebra.trace ℚ F x = n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  refine ⟨n, ?_⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h3 : (((Algebra.trace ℚ F x : ℚ) : ℂ)) = ((n : ℚ) : ℂ) := by
    have := hn
    rw [mul_comm (2 * (Real.pi : ℂ) * Complex.I)] at this
    push_cast
    exact mul_right_cancel₀ h2 this
  exact_mod_cast h3

variable {k : ℕ} {Ψ : GL (Fin 2) (Af F) → Hn F → ℂ} {a : (Af F)ˣ → F → ℂ}

theorem coef_unit (hΨ : Sys k Ψ) (ha : ∀ y, HasQ ((((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0)) (a y))
    (y u : (Af F)ˣ) (hu : ∀ w, Valued.v (pLoc F w (u : Af F)) = 1) : a (y * u) = a y := by
  obtain ⟨-, hmul, hone, -⟩ := Hm.absf F
  have hK : aff u 0 ∈ KLev F 2 1 := ((GlobalTheory.HilbertThetaSeries.kMem F).2.1 u 0 hu (fun w => by simp)).1
  have e : Ψ (aff (y * u) 0) = Ψ (aff y 0) := by
    rw [aff_mul, mul_zero]; exact hΨ.right _ _ hK
  have h1 := ha (y * u)
  rw [e, hmul, hone u hu, mul_one] at h1
  exact hasQ_unique F _ _ _ h1 (ha y)

end GlobalTheory.HilbertThetaSeries.LiftExp

namespace GlobalTheory.HilbertThetaSeries.LiftExp

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem sl_toInf (k : ℕ) (γ : GL (Fin 2) F) (f : Hn F → ℂ) :
    sl k (toInf γ) f = ((((∏ v, |reAt v γ.val.det|) ^ ((k : ℝ) / 2) : ℝ) : ℂ)) • sl0 k (toInf γ) f := by
  funext z
  simp only [sl, det_toInf, Pi.smul_apply, smul_eq_mul]

variable {k : ℕ} {Ψ : GL (Fin 2) (Af F) → Hn F → ℂ} {a : (Af F)ˣ → F → ℂ}

theorem coef_rat (hΨ : Sys k Ψ) (ha : ∀ y, HasQ ((((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0)) (a y))
    (y : (Af F)ˣ) (ξ : Fˣ) (hξ : TP (ξ : F)) : a (Units.map (algebraMap F (Af F)).toMonoidHom ξ * y) 1 = a y ξ := by
  obtain ⟨-, hmul, -, hprod⟩ := Hm.absf F
  obtain ⟨hpos, -⟩ := Hm.absf F
  set ξ' := Units.map (algebraMap F (Af F)).toMonoidHom ξ with hξ'
  have e : toFin (aff ξ 0) * aff y 0 = aff (ξ' * y) 0 := by
    rw [toFin_aff, map_zero, aff_mul, mul_zero]
  have hl := hΨ.left (aff ξ 0) (by rw [det_aff]; exact hξ) (aff y 0)
  rw [e, sl_toInf, det_aff] at hl
  have hq := GlobalTheory.T.hasQExpansion_affineTranslate_coeff F k _ (a (ξ' * y)) ξ 0 hξ (ha (ξ' * y))
  have hP := hprod ξ
  have key : (((absF (ξ' * y) ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ =
      (((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ * (((∏ v, |reAt v (ξ : F)|) ^ ((k : ℝ) / 2) : ℝ) : ℂ) := by
    rw [hmul, Real.mul_rpow (hpos _).le (hpos _).le]
    have h0 : (0 : ℝ) ≤ ∏ v, |reAt v (ξ : F)| := Finset.prod_nonneg fun v _ => abs_nonneg _
    have h1 : (∏ v, |reAt v (ξ : F)|) ^ ((k : ℝ) / 2) * absF ξ' ^ ((k : ℝ) / 2) = 1 := by
      rw [← Real.mul_rpow h0 (hpos _).le, hP, Real.one_rpow]
    rw [eq_inv_of_mul_eq_one_left h1, Complex.ofReal_mul, mul_inv, Complex.ofReal_inv, mul_comm]
  have hf : sl0 k (toInf (aff ξ 0)) ((((absF (ξ' * y) ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff (ξ' * y) 0)) =
      (((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0) := by
    rw [slash_weight_smul, ← hl, smul_smul, key]
  rw [hf] at hq
  have := congrFun (hasQ_unique F _ _ _ hq (ha y)) (ξ : F)
  rw [div_self ξ.ne_zero, mul_zero, et_zero, mul_one] at this
  exact this

theorem coef_dual (hΨ : Sys k Ψ) (ha : ∀ y, HasQ ((((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0)) (a y))
    (y : (Af F)ˣ) (ξ : F) (hξ : ξ ≠ 0) (hne : a y ξ ≠ 0) : ∃ 𝔪, GenD (algebraMap F (Af F) ξ * (y : Af F)) 𝔪 := by
  obtain ⟨-, hK, -, hval, -⟩ := GlobalTheory.HilbertThetaSeries.kMem F
  refine GlobalTheory.HilbertThetaSeries.DualIdele.genD_of_trace F y ξ hξ fun b hb => ?_
  have hx : ∀ w, Valued.v (pLoc F w (((y⁻¹ : (Af F)ˣ) : Af F) * algebraMap F (Af F) b)) ≤ 1 := fun w => by
    rw [map_mul, map_mul, hval]
    have h1 : Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) * Valued.v (pLoc F w (y : Af F)) = 1 := by
      rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
    calc _ ≤ Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) * Valued.v (pLoc F w (y : Af F)) := mul_le_mul_right (hb w) _
      _ = 1 := h1
  have hu := (hK 1 _ (fun w => by simp) hx).1
  have e : toFin (aff 1 b) * aff y 0 = aff y 0 * aff 1 (((y⁻¹ : (Af F)ˣ) : Af F) * algebraMap F (Af F) b) := by
    rw [toFin_aff, map_one, ← aff_mul, mul_one]
    apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]
  have hl := hΨ.left (aff 1 b) (by rw [det_aff]; exact tp_one) (aff y 0)
  rw [e, hΨ.right _ _ hu, sl_toInf, det_aff] at hl
  simp only [Units.val_one, reAt, map_one, Complex.one_re, abs_one, Finset.prod_const_one, Real.one_rpow,
    Complex.ofReal_one, one_smul] at hl
  have hq := GlobalTheory.T.hasQExpansion_affineTranslate_coeff F k _ (a y) 1 b tp_one (ha y)
  rw [slash_weight_smul, hl] at hq
  have := congrFun (hasQ_unique F _ _ _ hq (ha y)) ξ
  simp only [Units.val_one, div_one] at this
  have h2 : et (ξ * b) = 1 := by
    have := mul_left_cancel₀ hne (this.trans (mul_one _).symm)
    exact this
  exact trace_int_of_et h2

end GlobalTheory.HilbertThetaSeries.LiftExp

namespace GlobalTheory.HilbertThetaSeries.LiftExp

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def pt (x : InfinitePlace F → ℝ) (y : (InfinitePlace F → ℝ)ˣ) (hy : ∀ v, 0 < y.val v) : Hn F :=
  fun v => UpperHalfPlane.mk ((x v : ℂ) + Complex.I * (y.val v : ℂ)) (by simpa using hy v)

theorem sl_aff_I (k : ℕ) (x : InfinitePlace F → ℝ) (y : (InfinitePlace F → ℝ)ˣ) (hy : ∀ v, 0 < y.val v) (f : Hn F → ℂ) :
    sl k (aff y x) f (fun _ => UpperHalfPlane.I) = (((∏ v, y.val v) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * f (pt x y hy) := by
  have hd : ∀ v (z : ℂ), UpperHalfPlane.denom (cmp v (aff y x)) z = 1 := fun v z => by
    simp [UpperHalfPlane.denom, cmp, aff]
  have hn : ∀ v (z : ℂ), UpperHalfPlane.num (cmp v (aff y x)) z = (y.val v : ℂ) * z + x v := fun v z => by
    simp [UpperHalfPlane.num, cmp, aff]
  have ha : act (aff y x) (fun _ => UpperHalfPlane.I) = pt x y hy := by
    funext v
    apply UpperHalfPlane.ext
    rw [act, UpperHalfPlane.coe_smul_of_det_pos (by simpa [cmp, aff, Matrix.det_fin_two] using hy v), hd, hn]
    simp [pt]; ring
  have hp : ∏ v, |(aff y x).val.det v| = ∏ v, y.val v :=
    Finset.prod_congr rfl fun v _ => by rw [det_aff, abs_of_pos (hy v)]
  simp only [sl, sl0, hd, ha, hp, Finset.prod_const_one, inv_one, one_pow, one_mul]

variable {k : ℕ} {Ψ : GL (Fin 2) (Af F) → Hn F → ℂ} {a : (Af F)ˣ → F → ℂ}

theorem ne_zero_of_tp {ξ : F} (h : TP ξ) : ξ ≠ 0 := by
  rintro rfl
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  simpa [reAt] using h v

theorem coefAt_eq_coef (hΨ : Sys k Ψ) (ha : ∀ y, HasQ ((((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0)) (a y))
    (c : Ideal (𝓞 F) → ℂ) (hc : ∀ 𝔪, 𝔪 ≠ ⊥ → ∃ Y : (Af F)ˣ, GenD (Y : Af F) 𝔪 ∧ c 𝔪 = a Y 1)
    (y : (Af F)ˣ) (ξ : F) (hξ : TP ξ) : coefAt c (algebraMap F (Af F) ξ * (y : Af F)) = a y ξ := by
  have h0 := ne_zero_of_tp hξ
  by_cases h : ∃ 𝔪, GenD (algebraMap F (Af F) ξ * (y : Af F)) 𝔪
  · obtain ⟨𝔪, hm⟩ := h
    obtain ⟨Y, hY, hcY⟩ := hc 𝔪 hm.1
    have hr := coef_rat hΨ ha y (Units.mk0 ξ h0) hξ
    set y' := Units.map (algebraMap F (Af F)).toMonoidHom (Units.mk0 ξ h0) * y with hy'
    have hv : (y' : Af F) = algebraMap F (Af F) ξ * (y : Af F) := rfl
    have hu := coef_unit hΨ ha Y (Y⁻¹ * y') fun w => by
      rw [Units.val_mul, map_mul, map_mul, hv, hm.2 w, ← hY.2 w, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
    rw [mul_inv_cancel_left] at hu
    rw [coefAt_of_genD hm, hcY, ← hu, hr, Units.val_mk0]
  · rw [coefAt, dite_eq_right h]
    by_contra hne
    exact h (coef_dual hΨ ha y ξ h0 (Ne.symm hne))

end GlobalTheory.HilbertThetaSeries.LiftExp


open GlobalTheory.HilbertThetaSeries.LiftExp in
theorem GlobalTheory.HilbertThetaSeries.lift_hasExp : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : GA F 2 → ℂ) (a : (Af F)ˣ → F → ℂ), Sys k Ψ → IsLift k Ψ φ → (∀ y, HasQ ((((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0)) (a y)) → ∃ c : Ideal (𝓞 F) → ℂ, HasExp φ k (fun y => a y 0) c ∧ ∀ 𝔪, 𝔪 ≠ ⊥ → ∃ y, c 𝔪 = a y 1 := by
  classical
  intro F _ _ _ k Ψ φ a hΨ hφ ha
  let c : Ideal (𝓞 F) → ℂ := fun 𝔪 => if h : 𝔪 ≠ ⊥ then a (exists_unit_genD h).choose 1 else 0
  have hc : ∀ 𝔪, 𝔪 ≠ ⊥ → ∃ Y : (Af F)ˣ, GenD (Y : Af F) 𝔪 ∧ c 𝔪 = a Y 1 := fun 𝔪 h =>
    ⟨_, (exists_unit_genD h).choose_spec, dif_pos h⟩
  refine ⟨c, fun x y hy yf => ?_, fun 𝔪 h => (hc 𝔪 h).imp fun _ h => h.2⟩
  have hP : 0 < ∏ v, y.val v := Finset.prod_pos fun v _ => hy v
  have hP' : (((∏ v, y.val v) ^ ((k : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hP _).ne'
  rw [hφ.2 (aff y x) (fun v => by rw [det_aff]; exact hy v), sl_aff_I k x y hy,
    Real.mul_rpow hP.le ((Hm.absf F).1 yf).le, Complex.ofReal_mul, mul_div_mul_left _ _ hP']
  obtain ⟨⟨D, -, hD⟩, hs⟩ := ha yf
  have h1 := (hs (pt x y hy)).update 0 0
  have h2 := (hasSum_subtype_iff_of_support_subset (s := {ξ : F | ∀ v, 0 < reAt v ξ}) (fun ξ hξ => by
    have hξ0 : ξ ≠ 0 := by rintro rfl; simp at hξ
    rw [Function.mem_support, Function.update_of_ne hξ0] at hξ
    exact (hD ξ (left_ne_zero_of_mul hξ)).1.resolve_left hξ0)).2 h1
  have e0 : ez (0 : F) (pt x y hy) = 1 := by simp [ez, reAt]
  rw [e0, mul_one, zero_sub, Pi.smul_apply, smul_eq_mul, neg_add_eq_sub, mul_comm, ← div_eq_mul_inv] at h2
  refine QUniq.hasSum_congr' h2 fun ξ => ?_
  rw [Function.comp_apply, Function.update_of_ne (ne_zero_of_tp ξ.2), coefAt_eq_coef hΨ ha c hc yf ξ.1 ξ.2]
  rfl

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_fourier_expansion_of_lift : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : GA F 2 → ℂ) (a : (Af F)ˣ → F → ℂ), Sys k Ψ → IsLift k Ψ φ → (∀ y, HasQ ((((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0)) (a y)) → ∃ c : Ideal (𝓞 F) → ℂ, HasExp φ k (fun y => a y 0) c ∧ ∀ 𝔪, 𝔪 ≠ ⊥ → ∃ y, c 𝔪 = a y 1 := by
  first | exact @GlobalTheory.HilbertThetaSeries.lift_hasExp | exact GlobalTheory.HilbertThetaSeries.lift_hasExp | (intros; apply GlobalTheory.HilbertThetaSeries.lift_hasExp <;> assumption)
