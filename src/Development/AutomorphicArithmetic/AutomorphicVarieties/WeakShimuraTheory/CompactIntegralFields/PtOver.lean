module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.UnivGr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.AmbPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PowOneInj

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.MonoMem
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.AmbScale
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.AmbAbs
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem dvd_pow_of {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {a b : A}
    (ha : ¬ IsUnit a) (hb : b ≠ 0) : ∃ n : ℕ, b ∣ a ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  by_cases ha0 : a = 0
  · exact ⟨1, by simp [ha0]⟩
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨m, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  have hk : k ≠ 0 := by
    rintro rfl
    exact ha (by simp)
  refine ⟨m, ?_⟩
  rw [Units.mul_left_dvd, mul_pow, ← pow_mul]
  exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero hk))) _

private theorem arch {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (f : A →+* 𝔞.V) (hf : 𝔞.IsDvr f) : MulArchimedean 𝔞.V.ValueGroup := by
  classical
  refine ⟨fun x y hy => ?_⟩
  obtain ⟨a, rfl⟩ := 𝔞.V.valuation_surjective x
  obtain ⟨b, rfl⟩ := 𝔞.V.valuation_surjective y
  by_cases ha : 𝔞.V.valuation a ≤ 1
  · exact ⟨0, by simpa using ha⟩
  push_neg at ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hy
  have hai : 𝔞.V.valuation a⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ ha
  have hbi : 𝔞.V.valuation b⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hy
  have haV : a⁻¹ ∈ 𝔞.V := (𝔞.V.valuation_le_one_iff _).1 hai.le
  have hbV : b⁻¹ ∈ 𝔞.V := (𝔞.V.valuation_le_one_iff _).1 hbi.le
  obtain ⟨A', _, _, _, f', g, hf', hcomp, hcl⟩ := smallExt 𝔞 A f hf {a⁻¹, b⁻¹}
  obtain ⟨c, hc⟩ := hcl ⟨a⁻¹, haV⟩ (Subfield.subset_closure (Or.inr (by simp)))
  obtain ⟨d, hd⟩ := hcl ⟨b⁻¹, hbV⟩ (Subfield.subset_closure (Or.inr (by simp)))
  have hdu : ¬ IsUnit d := by
    intro h
    have h2 := h.map f'
    rw [hd] at h2
    have h3 : (⟨b⁻¹, hbV⟩ : 𝔞.V) ∈ maximalIdeal 𝔞.V := (𝔞.V.valuation_lt_one_iff _).2 hbi
    exact ((mem_maximalIdeal _).1 h3) h2
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact inv_ne_zero ha0 (congrArg Subtype.val hc).symm
  obtain ⟨n, hn⟩ := dvd_pow_of hdu hc0
  obtain ⟨e, he⟩ := map_dvd f' hn
  rw [map_pow, hc, hd] at he
  have he' : (b⁻¹) ^ n = a⁻¹ * (e : 𝔞.K) := congrArg Subtype.val he
  have hae : a = (e : 𝔞.K) * b ^ n := by
    calc a = a * (b⁻¹ ^ n * b ^ n) := by rw [← mul_pow, inv_mul_cancel₀ hb0, one_pow, mul_one]
      _ = a * (a⁻¹ * (e * b ^ n)) := by rw [he', mul_assoc]
      _ = e * b ^ n := mul_inv_cancel_left₀ ha0 _
  refine ⟨n, ?_⟩
  rw [hae, map_mul, map_pow]
  calc 𝔞.V.valuation (e : 𝔞.K) * 𝔞.V.valuation b ^ n ≤ 1 * 𝔞.V.valuation b ^ n :=
        mul_le_mul_left (𝔞.V.valuation_le_one e) _
    _ = 𝔞.V.valuation b ^ n := one_mul _

theorem UpperTheory.V.Ws.Po.ambAbs :
    ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (f : A →+* 𝔞.V), 𝔞.IsDvr f →
      ∃ w : AbsoluteValue 𝔞.K ℝ, (∀ x, w x < 1 ↔ 𝔞.V.valuation x < 1) ∧ ∃ p, p ≠ 0 ∧ w p ≠ 1 := by
  intro l _ 𝔞 A _ _ _ f hf
  haveI := arch 𝔞 A f hf
  haveI : MulArchimedean (𝔞.V.ValueGroup)ˣ := ⟨fun x y hy => by
    obtain ⟨n, hn⟩ := MulArchimedean.arch (x : 𝔞.V.ValueGroup) (y := (y : 𝔞.V.ValueGroup)) hy
    refine ⟨n, ?_⟩
    show (x : 𝔞.V.ValueGroup) ≤ ((y ^ n : (𝔞.V.ValueGroup)ˣ) : 𝔞.V.ValueGroup)
    rw [Units.val_pow_eq_pow_val]
    exact hn⟩
  obtain ⟨φ, hφ⟩ := Archimedean.exists_orderAddMonoidHom_real_injective (Additive (𝔞.V.ValueGroup)ˣ)
  have hφm : StrictMono φ := φ.monotone'.strictMono_of_injective hφ
  let gg : 𝔞.V.ValueGroup → ℝ := fun γ =>
    if h : γ = 0 then 0 else Real.exp (φ (Additive.ofMul (Units.mk0 γ h)))
  have g0 : gg 0 = 0 := by simp [gg]
  have gpos : ∀ γ, γ ≠ 0 → 0 < gg γ := fun γ h => by
    simp only [gg, dif_neg h]
    exact Real.exp_pos _
  have gmono : StrictMono gg := by
    intro γ δ h
    have hδ : δ ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' h)
    by_cases hγ : γ = 0
    · rw [hγ, g0]
      exact gpos δ hδ
    · simp only [gg, dif_neg hγ, dif_neg hδ]
      apply Real.exp_lt_exp.2
      apply hφm
      exact (show Units.mk0 γ hγ < Units.mk0 δ hδ from h)
  have gnn : ∀ γ, 0 ≤ gg γ := fun γ => by
    rw [← g0]
    exact gmono.monotone zero_le'
  have gmul : ∀ γ δ, gg (γ * δ) = gg γ * gg δ := by
    intro γ δ
    by_cases hγ : γ = 0
    · simp [hγ, g0]
    by_cases hδ : δ = 0
    · simp [hδ, g0]
    have hγδ : γ * δ ≠ 0 := mul_ne_zero hγ hδ
    simp only [gg, dif_neg hγ, dif_neg hδ, dif_neg hγδ, ← Real.exp_add, ← map_add (f := _)]
    congr 2
    rw [← ofMul_mul, Units.mk0_mul]
  have g1 : gg 1 = 1 := by
    have h1 : (1 : 𝔞.V.ValueGroup) ≠ 0 := one_ne_zero
    simp only [gg, dif_neg h1, Units.mk0_one, ofMul_one, map_zero, Real.exp_zero]
  let w : AbsoluteValue 𝔞.K ℝ :=
    { toFun := fun x => gg (𝔞.V.valuation x)
      map_mul' := fun x y => by
        change gg (𝔞.V.valuation (x * y)) = gg (𝔞.V.valuation x) * gg (𝔞.V.valuation y)
        rw [Valuation.map_mul, gmul]
      nonneg' := fun x => gnn _
      eq_zero' := fun x => ⟨fun h => by
          by_contra hx
          exact (gpos _ ((Valuation.ne_zero_iff _).2 hx)).ne' h,
        fun h => by rw [h, Valuation.map_zero, g0]⟩
      add_le' := fun x y => by
        have hle := gmono.monotone (𝔞.V.valuation.map_add x y)
        have hx := gnn (𝔞.V.valuation x)
        have hy := gnn (𝔞.V.valuation y)
        rcases le_total (𝔞.V.valuation x) (𝔞.V.valuation y) with h | h
        · rw [max_eq_right h] at hle
          linarith
        · rw [max_eq_left h] at hle
          linarith }
  refine ⟨w, fun x => ?_, ?_⟩
  · change gg (𝔞.V.valuation x) < 1 ↔ 𝔞.V.valuation x < 1
    rw [← g1]
    exact gmono.lt_iff_lt
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
    refine ⟨𝔞.toK (f ϖ), ?_, ?_⟩
    · intro h
      apply hϖ.ne_zero
      apply hf.inj
      rw [map_zero]
      exact Subtype.val_injective h
    · have hlt : 𝔞.V.valuation (𝔞.toK (f ϖ)) < 1 := by
        have := Amb.IsDvr.loc hf
        have hnu : ¬ IsUnit (f ϖ) := fun h => hϖ.not_isUnit (isUnit_of_map_unit f ϖ h)
        exact (𝔞.V.valuation_lt_one_iff (f ϖ)).1 ((mem_maximalIdeal _).2 hnu)
      change gg _ ≠ 1
      rw [← g1]
      exact (gmono hlt).ne
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem carver_abs (K : Type) [Field K] [IsAlgClosed K] (w : AbsoluteValue K ℝ) (hp : ∃ p, p ≠ 0 ∧ w p ≠ 1)
    (σ : Type) [Finite σ] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (wt : σ → X) (z : σ → K)
    (hz : ∀ n : σ →₀ ℕ, n ≠ 0 → Finsupp.weight wt n = 0 → w (n.prod fun s k => z s ^ k) < 1) :
    ∃ t : Multiplicative X →* Kˣ, ∀ s, w ((t (Multiplicative.ofAdd (wt s)) : K) * z s) < 1 := by
  letI : NormedField K := w.toNormedField
  exact carver σ X wt K z hp hz

theorem UpperTheory.V.Ws.Po.ambScale :
    ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (f : A →+* 𝔞.V), 𝔞.IsDvr f →
      ∀ (σ : Type) [Finite σ] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (wt : σ → X) (z : σ → 𝔞.K),
      (∀ n : σ →₀ ℕ, n ≠ 0 → Finsupp.weight wt n = 0 → 𝔞.V.valuation (n.prod fun s k => z s ^ k) < 1) →
      ∃ t : Multiplicative X →* 𝔞.Kˣ, ∀ s, 𝔞.V.valuation ((t (Multiplicative.ofAdd (wt s)) : 𝔞.K) * z s) < 1 := by
  intro l _ 𝔞 A _ _ _ f hf σ _ X _ _ _ wt z hz
  obtain ⟨w, hw, hp⟩ := UpperTheory.V.Ws.Po.ambAbs 𝔞 A f hf
  obtain ⟨t, ht⟩ := carver_abs 𝔞.K w hp σ X wt z fun n hn h0 => (hw _).2 (hz n hn h0)
  exact ⟨t, fun s => (hw _).1 (ht s)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.ExtGraded
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

private theorem pt_of_ft {K C : Type} [Field K] [IsAlgClosed K] [CommRing C] [Algebra K C] [Nontrivial C]
    [Algebra.FiniteType K C] : Nonempty (C →ₐ[K] K) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  letI := Ideal.Quotient.field m
  haveI : Module.Finite K (C ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (C ⧸ m)
  exact ⟨(IsAlgClosed.lift : (C ⧸ m) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K m)⟩

private theorem pt_of_lin {A B K : Type} [CommRing A] [CommRing B] [Field K] [IsAlgClosed K] [Algebra A B]
    [Algebra A K] [Algebra.FiniteType A B] (ρ : B →ₗ[A] K) (h : ρ 1 = 1) : Nonempty (B →ₐ[A] K) := by
  haveI : Nontrivial (TensorProduct A K B) := by
    refine ⟨1, 0, fun e => ?_⟩
    have := congrArg (TensorProduct.lift ((LinearMap.mul A K).compl₂ ρ)) e
    rw [Algebra.TensorProduct.one_def, TensorProduct.lift.tmul, map_zero] at this
    simp [h] at this
  obtain ⟨y⟩ := pt_of_ft (K := K) (C := TensorProduct A K B)
  exact ⟨(y.restrictScalars A).comp Algebra.TensorProduct.includeRight⟩

private theorem ext_graded {O A X K : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup X]
    [DecidableEq X] (𝒜 : X → Submodule O A) [GradedAlgebra 𝒜] [Algebra.FiniteType (𝒜 0) A]
    [Field K] [IsAlgClosed K] [Algebra O K] (y : 𝒜 0 →ₐ[O] K) :
    ∃ ξ : A →ₐ[O] K, ∀ b : 𝒜 0, ξ b = y b := by
  letI : Algebra (𝒜 0) K := (y : 𝒜 0 →+* K).toAlgebra
  have key : ∀ (r : 𝒜 0) (a : A),
      DirectSum.decompose 𝒜 ((r : A) * a) 0 = r * DirectSum.decompose 𝒜 a 0 := by
    intro r a
    apply Subtype.ext
    have := DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 (i := 0) (j := 0) (b := a) r.2
    rw [add_zero] at this
    exact this
  let ρ : A →ₗ[𝒜 0] K :=
    { toFun := fun a => y (DirectSum.decompose 𝒜 a 0)
      map_add' := fun a b => by rw [DirectSum.decompose_add, DirectSum.add_apply, map_add (f := _)]
      map_smul' := fun r a => by
        show y (DirectSum.decompose 𝒜 ((r : A) * a) 0) = y r * y (DirectSum.decompose 𝒜 a 0)
        rw [key, map_mul] }
  have hρ : ρ 1 = 1 := by
    show y (DirectSum.decompose 𝒜 ((1 : 𝒜 0) : A) 0) = 1
    rw [DirectSum.decompose_coe, DirectSum.of_eq_same, map_one]
  obtain ⟨η⟩ := pt_of_lin ρ hρ
  have hη : ∀ b : 𝒜 0, η b = y b := fun b => η.commutes b
  refine ⟨{ (η : A →+* K) with commutes' := fun r => ?_ }, hη⟩
  exact (hη (algebraMap O (𝒜 0) r)).trans (y.commutes r)

theorem UpperTheory.V.Ws.Po.extA :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra O K] (y : W.gr 0 →ₐ[O] K),
      ∃ ξ : W.A →ₐ[O] K, ∀ b : W.gr 0, ξ b = y b := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W hz K _ _ _ y
  haveI := (gr_noeth O X R W hz).2.1
  exact ext_graded W.gr y
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.XrMonomial
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

section SlopeTestRemainingChoices

open MvPowerSeries

private theorem xr_ev {O S σ : Type} [CommRing O] [CommRing S] [Algebra O S] [Finite σ] (m : Ideal S)
    [IsAdicComplete m S] (a : σ → S) (ha : ∀ s, a s ∈ m) :
    ∃ F : MvPowerSeries σ O →ₐ[O] S, ∀ s, F (X s) = a s := by
  letI : UniformSpace O := ⊥
  haveI : DiscreteTopology O := ⟨rfl⟩
  letI : WithIdeal S := ⟨m⟩
  haveI : ContinuousSMul O S := continuousSMul_of_algebraMap O S continuous_of_discreteTopology
  have hadic : IsAdic m := rfl
  obtain ⟨_, _⟩ := (IsAdic.isAdicComplete_iff hadic).1 inferInstance
  have hE : MvPowerSeries.HasEval a := by
    refine ⟨fun s => ?_, ?_⟩
    · show Filter.Tendsto (fun n => a s ^ n) Filter.atTop (nhds 0)
      rw [hadic.hasBasis_nhds_zero.tendsto_right_iff]
      intro i _
      rw [Filter.eventually_atTop]
      exact ⟨i, fun n hn => Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow (ha s) n)⟩
    · simp
  refine ⟨MvPowerSeries.aeval hE, fun s => ?_⟩
  rw [← MvPolynomial.coe_X, MvPowerSeries.aeval_coe, MvPolynomial.aeval_X]

private theorem xr_monomial {O σ : Type} [CommRing O] [Fintype σ] (m : σ →₀ ℕ) :
    (monomial m (1 : O) : MvPowerSeries σ O) = ∏ i, (MvPowerSeries.X i) ^ (m i) := by
  classical
  rw [← MvPolynomial.coe_monomial, ← MvPolynomial.prod_X_pow_eq_monomial]
  have h := map_prod (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := O)) (fun x => MvPolynomial.X x ^ m x) m.support
  simp only [map_pow, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_X] at h
  rw [h]
  refine Finset.prod_subset (Finset.subset_univ _) ?_
  intro i _ hi
  rw [Finsupp.notMem_support_iff.1 hi, pow_zero]

private theorem mvPowerSeries_algHom_monomial_eq_prod_X_pow {O σ K : Type} [CommRing O] [Fintype σ] [CommRing K] [Algebra O K]
    (G : MvPowerSeries σ O →ₐ[O] K) (m : σ →₀ ℕ) :
    G (MvPowerSeries.monomial m 1) = ∏ s, G (MvPowerSeries.X s) ^ m s := by
  rw [xr_monomial, map_prod]
  simp only [map_pow]

private theorem prod_pow_mem_ideal_pow_of_mem_of_le_exponent {σ K : Type} [Fintype σ] [CommRing K] (I : Ideal K) (c : σ → K)
    (hc : ∀ s, c s ∈ I) (m : σ →₀ ℕ) (k : ℕ) (s0 : σ) (hs0 : k ≤ m s0) :
    ∏ s, c s ^ m s ∈ I ^ k := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ (fun s => c s ^ m s) (Finset.mem_univ s0)]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right hs0 (Ideal.pow_mem_pow (hc s0) _))

private theorem xr_agree {O R X K : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] [CommRing K] [Algebra O K] (I : Ideal K) [IsHausdorff I K]
    (W : WPres O X R) (F : MvPowerSeries W.σ O →ₐ[O] K) (η : W.A →ₐ[O] K)
    (hX : ∀ s, F (MvPowerSeries.X s) = η (W.zA s)) (hz : ∀ s, η (W.zA s) ∈ I) (j : X)
    (f : MvPowerSeries W.σ O) (hf : f ∈ wtPart O W.wt j) (x : W.A) (hx : (x : R) = W.π f) : F f = η x := by
  classical
  apply sub_eq_zero.1
  refine IsHausdorff.haus' (I := I) _ fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  let n' : W.σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => k)
  let T := Finset.Iic n'
  let p : MvPowerSeries W.σ O := ∑ m ∈ T, coeff m f • monomial m 1
  have hpc : ∀ m, coeff m p = if m ≤ n' then coeff m f else 0 := by
    intro m
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [p, map_sum, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_monomial, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [T, Finset.mem_Iic]
  have hf' : ∀ n, Finsupp.weight W.wt n ≠ j → coeff n f = 0 := hf
  obtain ⟨μ, hμ, hμf⟩ :=
    part_span O R X W {m | Finsupp.weight W.wt m = j ∧ ¬ m ≤ n'} j (fun n hn => hn.1)
  obtain ⟨b, hb, hg⟩ := hμf (f - p) (by
    intro n hn
    rw [map_sub, hpc]
    split_ifs with h
    · exact sub_self _
    · rw [sub_zero]
      apply hf'
      intro hw
      exact hn ⟨hw, h⟩)
  have hG : ∀ (K' : Type) [CommRing K'] [Algebra O K'] (G : MvPowerSeries W.σ O →ₐ[O] K'),
      G p = ∑ m ∈ T, coeff m f • ∏ s, G (MvPowerSeries.X s) ^ m s := by
    intro K' _ _ G
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [p, map_sum, map_smul, mvPowerSeries_algHom_monomial_eq_prod_X_pow]
  let y : W.A := ∑ m ∈ T, coeff m f • ∏ s, W.zA s ^ m s
  have hy : F p = η y := by
    rw [hG K F]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [y, map_sum, map_smul, map_prod, map_pow, hX]
  have hyR : (y : R) = W.π p := by
    rw [hG R W.π]
    show W.A.val y = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [y, map_sum, map_smul, map_prod, map_pow]
    rfl
  let e : W.A := ∑ m ∈ μ, (⟨W.π (b m), W.part_le_A (j := 0) (Submodule.mem_map_of_mem (hb m))⟩ : W.A) *
    ∏ s, W.zA s ^ m s
  have he : x - y = e := by
    apply Subtype.ext
    show W.A.val (x - y) = W.A.val e
    rw [map_sub]
    show (x : R) - (y : R) = _
    rw [hx, hyR, ← map_sub, hg]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [e, map_sum, map_mul, map_prod, map_pow, mvPowerSeries_algHom_monomial_eq_prod_X_pow]
    rfl
  have hdiff : F f - η x = F (f - p) - η e := by
    rw [← he, map_sub, map_sub, hy]
    ring
  rw [hdiff, hg]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e, map_sum, map_mul, mvPowerSeries_algHom_monomial_eq_prod_X_pow, hX, map_prod, map_pow]
  rw [← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun m hm => ?_
  rw [← sub_mul]
  refine Ideal.mul_mem_left _ _ ?_
  obtain ⟨-, hm2⟩ := hμ (Finset.mem_coe.2 hm)
  have hex : ∃ s0, k < m s0 := by
    by_contra hcon
    push_neg at hcon
    exact hm2 (Finsupp.le_def.2 fun s => by simpa [n'] using hcon s)
  obtain ⟨s0, hs0⟩ := hex
  exact prod_pow_mem_ideal_pow_of_mem_of_le_exponent I _ hz m k s0 hs0.le

private theorem xr_const {O S σ : Type} [CommRing O] [CommRing S] [Algebra O S] [Fintype σ] (I : Ideal S)
    (F : MvPowerSeries σ O →ₐ[O] S) (hF : ∀ s, F (X s) ∈ I) (f : MvPowerSeries σ O) :
    F f - algebraMap O S (constantCoeff f) ∈ I := by
  classical
  have key : ∀ T : Finset σ, ∀ g : MvPowerSeries σ O,
      (∀ n : σ →₀ ℕ, (∀ s ∈ T, n s = 0) → coeff n g = 0) → F g ∈ I := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · intro g hg
      have hg0 : g = 0 := by
        ext n
        exact hg n (by simp)
      rw [hg0, map_zero]
      exact I.zero_mem
    · intro s T _ ih g hg
      let r : MvPowerSeries σ O := fun n => if n s = 0 then coeff n g else 0
      have hr : ∀ n, coeff n r = if n s = 0 then coeff n g else 0 := fun n => rfl
      have hdvd : X s ∣ g - r := by
        rw [MvPowerSeries.X_dvd_iff]
        intro n hn
        rw [map_sub, hr, if_pos hn, sub_self]
      obtain ⟨q, hq⟩ := hdvd
      have hrI : F r ∈ I := by
        apply ih
        intro n hn
        rw [hr]
        split_ifs with h
        · apply hg
          intro t ht
          rcases Finset.mem_insert.1 ht with rfl | ht
          · exact h
          · exact hn t ht
        · rfl
      have hgq : g = X s * q + r := by rw [← hq, sub_add_cancel]
      rw [hgq, map_add (f := _), map_mul]
      exact I.add_mem (I.mul_mem_right _ (hF s)) hrI
  have h := key Finset.univ (f - algebraMap O (MvPowerSeries σ O) (constantCoeff f)) ?_
  · rwa [map_sub, F.commutes] at h
  · intro n hn
    have hn0 : n = 0 := Finsupp.ext fun s => hn s (Finset.mem_univ s)
    subst hn0
    rw [map_sub, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← MvPowerSeries.c_eq_algebraMap, MvPowerSeries.constantCoeff_C, sub_self]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.Po.extR :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (A' : Type) [CommRing A'] [IsLocalRing A'] [IsAdicComplete (maximalIdeal A') A'] [Algebra O A'] (η : W.A →ₐ[O] A'),
      (∀ s, η (W.zA s) ∈ maximalIdeal A') → (∀ b ∈ W.gr 0, (b : R) ∈ maximalIdeal R → η b ∈ maximalIdeal A') →
      ∃ Ξ : R →ₐ[O] A', Ξ.comp W.A.val = η ∧ ∀ x ∈ maximalIdeal R, Ξ x ∈ maximalIdeal A' := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W hzm A' _ _ _ _ η hηz hη0
  classical
  obtain ⟨F, hF⟩ := xr_ev (O := O) (σ := W.σ) (maximalIdeal A') (fun s => η (W.zA s)) hηz
  obtain ⟨n, f, c, hfc, hker⟩ := ker_gen O X W.σ W.wt (RingHom.ker W.π) W.homog
  have hkill : ∀ a ∈ RingHom.ker W.π, F a = 0 := by
    intro a ha
    rw [hker] at ha
    have hle : Ideal.span (Set.range f) ≤ RingHom.ker F := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have hfi : f i ∈ RingHom.ker W.π := by
        rw [hker]
        exact Ideal.subset_span ⟨i, rfl⟩
      rw [RingHom.mem_ker] at hfi
      show F (f i) = 0
      have h := xr_agree (I := maximalIdeal A') W F η hF hηz (c i) (f i) (hfc i) 0 (by rw [hfi]; rfl)
      rw [h, map_zero]
    exact hle ha
  let e := Ideal.quotientKerAlgEquivOfSurjective W.surj
  let Ξ : R →ₐ[O] A' := (Ideal.Quotient.liftₐ (RingHom.ker W.π) F hkill).comp e.symm.toAlgHom
  have hΞ : ∀ g, Ξ (W.π g) = F g := by
    intro g
    have h1 : e.symm (W.π g) = Ideal.Quotient.mk _ g := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    show Ideal.Quotient.liftₐ _ F hkill (e.symm (W.π g)) = F g
    rw [h1]
    rfl
  have hF' : ∀ s, F (MvPowerSeries.X s) ∈ maximalIdeal A' := fun s => by
    rw [hF]
    exact hηz s
  refine ⟨Ξ, ?_, ?_⟩
  · apply AlgHom.ext
    intro a
    have key : ∀ y : R, y ∈ (⨆ j, W.part j) → y ∈ W.A ∧ ∀ h : y ∈ W.A, Ξ y = η ⟨y, h⟩ := by
      intro y hy
      refine Submodule.iSup_induction (motive := fun y => y ∈ W.A ∧ ∀ h : y ∈ W.A, Ξ y = η ⟨y, h⟩) _ hy
        ?_ ?_ ?_
      · intro i y hy
        refine ⟨W.part_le_A hy, fun h => ?_⟩
        obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.1 hy
        exact (hΞ g).trans (xr_agree (I := maximalIdeal A') W F η hF hηz i g hg _ rfl)
      · refine ⟨W.A.zero_mem, fun h => ?_⟩
        rw [map_zero]
        exact (map_zero η).symm
      · rintro y z ⟨hy1, hy2⟩ ⟨hz1, hz2⟩
        refine ⟨W.A.add_mem hy1 hz1, fun h => ?_⟩
        rw [map_add (f := _), hy2 hy1, hz2 hz1, ← map_add (f := _)]
        rfl
    exact (key a a.2).2 a.2
  · intro x hx
    obtain ⟨g, rfl⟩ := W.surj x
    rw [hΞ]
    have h1 := xr_const (maximalIdeal R) W.π hzm g
    have h2 : algebraMap O R (MvPowerSeries.constantCoeff g) ∈ maximalIdeal R := by
      have h := Ideal.sub_mem _ hx h1
      rwa [sub_sub_cancel] at h
    have hb : (algebraMap O W.A (MvPowerSeries.constantCoeff g)) ∈ W.gr 0 := by
      show W.A.val (algebraMap O W.A (MvPowerSeries.constantCoeff g)) ∈ W.part 0
      rw [AlgHom.commutes]
      refine Submodule.mem_map.2 ⟨algebraMap O (MvPowerSeries W.σ O) (MvPowerSeries.constantCoeff g), ?_,
        W.π.commutes _⟩
      show ∀ k : W.σ →₀ ℕ, Finsupp.weight W.wt k ≠ 0 → MvPowerSeries.coeff k _ = 0
      intro k hk
      rw [← MvPowerSeries.c_eq_algebraMap, MvPowerSeries.coeff_C, if_neg]
      rintro rfl
      exact hk (map_zero _)
    have h3 := hη0 _ hb (by
      show W.A.val (algebraMap O W.A (MvPowerSeries.constantCoeff g)) ∈ maximalIdeal R
      rw [AlgHom.commutes]
      exact h2)
    rw [AlgHom.commutes] at h3
    have h4 := xr_const (maximalIdeal A') F hF' g
    have h5 := Ideal.add_mem _ h4 h3
    rwa [sub_add_cancel] at h5
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem mono_mem {O X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)
    (n : W.σ →₀ ℕ) : (n.prod fun s k => W.zA s ^ k) ∈ W.gr (Finsupp.weight W.wt n) := by
  rw [Finsupp.weight_apply]
  exact SetLike.prod_pow_mem_graded W.gr W.wt W.zA n fun s _ => W.z_mem s

private theorem mono_max {O X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)
    (I : Ideal R) (h : ∀ s, W.z s ∈ I) (n : W.σ →₀ ℕ) (hn : n ≠ 0) :
    ((n.prod fun s k => W.zA s ^ k : W.A) : R) ∈ I := by
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.2 hn
  show W.A.val _ ∈ I
  rw [Finsupp.prod, map_prod]
  refine Ideal.prod_mem _ hs ?_
  rw [map_pow]
  exact Ideal.pow_mem_of_mem _ (h s) _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hs))

private theorem factor {B C K : Type} [CommRing B] [CommRing C] [CommRing K] (F : C →+* K) (hF : Function.Injective F)
    (ξ : B →+* K) (h : ∀ x, ξ x ∈ F.range) : ∃ η : B →+* C, ∀ x, F (η x) = ξ x := by
  choose g hg using h
  exact ⟨{ toFun := g
           map_one' := hF (by rw [hg, map_one, map_one])
           map_mul' := fun a b => hF (by rw [map_mul, hg, hg, hg, map_mul])
           map_zero' := hF (by rw [hg, map_zero, map_zero])
           map_add' := fun a b => hF (by rw [map_add (f := _), hg, hg, hg, map_add (f := _)]) }, hg⟩

theorem UpperTheory.V.Ws.Po.ptA :
    ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (f : A →+* 𝔞.V), 𝔞.IsDvr f → ∀ (s : Finset 𝔞.K)
      (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) →
      ∀ y : W.gr 0 →+* 𝔞.V, (∀ b : W.gr 0, ((b : W.A) : R) ∈ maximalIdeal R → y b ∈ maximalIdeal 𝔞.V) →
      (∀ b, (y b : 𝔞.K) ∈ Subfield.closure (Set.range (𝔞.toK.comp f) ∪ s)) →
      ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A') (f' : A' →+* 𝔞.V) (Ξ : R →+* A'),
        𝔞.IsDvr f' ∧ (∀ x ∈ maximalIdeal R, Ξ x ∈ maximalIdeal A') ∧ ∀ b : W.gr 0, f' (Ξ ((b : W.A) : R)) = y b := by
  intro l _ 𝔞 A _ _ _ f hf s O _ _ _ _ X _ _ _ _ R _ _ _ W hz y hy hcl
  classical
  letI : Algebra O 𝔞.K := ((𝔞.toK.comp y).comp (algebraMap O (W.gr 0))).toAlgebra
  let y' : W.gr 0 →ₐ[O] 𝔞.K := { 𝔞.toK.comp y with commutes' := fun _ => rfl }
  obtain ⟨ξ, hξ⟩ := Po.extA O X R W hz 𝔞.K y'
  have hξ' : ∀ b : W.gr 0, ξ b = (y b : 𝔞.K) := hξ
  obtain ⟨t, ht⟩ := Po.ambScale 𝔞 A f hf W.σ X W.wt (fun i => ξ (W.zA i)) fun n hn hw => by
    have h0 : (n.prod fun s k => W.zA s ^ k) ∈ W.gr 0 := hw ▸ mono_mem W n
    have h1 := (𝔞.V.valuation_lt_one_iff _).1 (hy ⟨_, h0⟩ (mono_max W _ hz n hn))
    rw [← hξ'] at h1
    simpa only [Finsupp.prod, map_prod ξ, map_pow ξ] using h1
  let ζ : W.A →ₐ[O] 𝔞.K := act W.gr t ξ
  have hζ0 : ∀ b : W.gr 0, ζ b = (y b : 𝔞.K) := fun b => by
    rw [act_of_mem W.gr t ξ b.2, ofAdd_zero, map_one, Units.val_one, one_mul, hξ']
  have hζz : ∀ i, 𝔞.V.valuation (ζ (W.zA i)) < 1 := fun i => by
    rw [act_of_mem W.gr t ξ (j := W.wt i) (W.z_mem i)]
    exact ht i
  obtain ⟨A', _, _, _, f', g, hf', -, hr⟩ := smallExt 𝔞 A f hf (s ∪ Finset.univ.image fun i => ζ (W.zA i))
  have hmem : ∀ x : 𝔞.V, x ∈ f'.range → (x : 𝔞.K) ∈ (𝔞.toK.comp f').range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  have h0 : ∀ b : W.gr 0, ζ b ∈ (𝔞.toK.comp f').range := fun b => by
    rw [hζ0]
    refine hmem _ (hr _ (Subfield.closure_mono (Set.union_subset_union_right _ ?_) (hcl b)))
    exact Finset.coe_subset.2 Finset.subset_union_left
  have hall : ∀ x, (ζ : W.A →+* 𝔞.K) x ∈ (𝔞.toK.comp f').range := fun x => by
    have hx : x ∈ Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA) := by
      rw [gr_gen O R X W]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain hx | ⟨i, rfl⟩ := hx
      · exact h0 ⟨x, hx⟩
      · refine hmem ⟨_, 𝔞.V.mem_of_valuation_le_one _ (hζz i).le⟩ (hr _ (Subfield.subset_closure (.inr ?_)))
        exact Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))
    | algebraMap a => exact h0 (algebraMap O (W.gr 0) a)
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  obtain ⟨η, hη⟩ := factor (𝔞.toK.comp f') (Subtype.val_injective.comp hf'.inj) _ hall
  have hη' : ∀ x, (f' (η x) : 𝔞.K) = ζ x := hη
  have hmax : ∀ x, 𝔞.V.valuation (ζ x) < 1 → η x ∈ maximalIdeal A' := fun x hx hu => by
    rw [← hη', ← 𝔞.V.valuation_lt_one_iff] at hx
    exact hx (hu.map f')
  letI : Algebra O A' := (η.comp (algebraMap O W.A)).toAlgebra
  haveI := hf'.complete
  obtain ⟨Ξ, hΞ, hΞm⟩ := Po.extR O X R W hz A' { η with commutes' := fun _ => rfl } (fun i => hmax _ (hζz i))
    fun b hb hm => hmax b (by
      rw [hζ0 ⟨b, hb⟩]
      exact (𝔞.V.valuation_lt_one_iff _).1 (hy ⟨b, hb⟩ hm))
  refine ⟨A', inferInstance, inferInstance, inferInstance, f', Ξ, hf', hΞm, fun b => Subtype.ext ?_⟩
  have e : Ξ ((b : W.A) : R) = η b := AlgHom.congr_fun hΞ b
  show (f' (Ξ _) : 𝔞.K) = _
  rw [e, hη', hζ0]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.NonAlg
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

private theorem fix_mul {V : Type} [Monoid V] {l n : ℕ} {x : V} (h : x ^ l ^ n = x) (m : ℕ) : x ^ l ^ (n * m) = x := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

private theorem fix_both {V : Type} [Monoid V] {l : ℕ} {x z : V} (hx : ∃ n : ℕ, 0 < n ∧ x ^ l ^ n = x)
    (hz : ∃ n : ℕ, 0 < n ∧ z ^ l ^ n = z) : ∃ n : ℕ, 0 < n ∧ x ^ l ^ n = x ∧ z ^ l ^ n = z := by
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨b, hb, hzb⟩ := hz
  refine ⟨a * b, Nat.mul_pos ha hb, fix_mul hxa b, ?_⟩
  rw [Nat.mul_comm]
  exact fix_mul hzb a

theorem UpperTheory.V.Ws.Po.nonAlg :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] (Γ : Type) [Group Γ] (R : Type) [CommRing R] [Algebra O R]
      (ρ : Γ →* M4 R) (V : Type) [CommRing V] [IsLocalRing V] [CharP V l] (y : R →+* V), (∀ a ∈ maximalIdeal O, y (algebraMap O R a) = 0) →
      ∀ u ∈ Algebra.adjoin O (mono ρ 0), y u ∈ maximalIdeal V → y u ≠ 0 →
      ∃ x ∈ mono (mapRep y ρ) 0, ∀ n : ℕ, 0 < n → x ^ l ^ n ≠ x := by
  intro l _ O _ _ _ Γ _ R _ _ ρ V _ _ _ y hy u hu hum hu0
  by_contra hcon
  push_neg at hcon
  have key : ∀ v ∈ Algebra.adjoin O (mono ρ 0), ∃ n : ℕ, 0 < n ∧ (y v) ^ l ^ n = y v := by
    intro v hv
    induction hv using Algebra.adjoin_induction with
    | mem x hx =>
      apply hcon
      obtain ⟨L, hL, rfl⟩ := hx
      refine ⟨L, hL, ?_⟩
      rw [map_list_prod, List.map_map]
      rfl
    | algebraMap r =>
      let g : O →+* V := y.comp (algebraMap O R)
      have hg : ∀ a ∈ maximalIdeal O, g a = 0 := hy
      let f : ResidueField O →+* V := Ideal.Quotient.lift (maximalIdeal O) g hg
      have hf : Function.Injective f := f.injective
      haveI : CharP (ResidueField O) l := f.charP hf l
      letI : Fintype (ResidueField O) := Fintype.ofFinite _
      obtain ⟨m, -, hm⟩ := FiniteField.card (ResidueField O) l
      refine ⟨m, m.pos, ?_⟩
      have h1 : y (algebraMap O R r) = f (IsLocalRing.residue O r) :=
        (Ideal.Quotient.lift_mk (maximalIdeal O) g hg).symm
      rw [h1, ← map_pow, ← hm, FiniteField.pow_card]
    | add x z _ _ hx hz =>
      obtain ⟨n, hn, hxn, hzn⟩ := fix_both hx hz
      exact ⟨n, hn, by rw [map_add (f := _), add_pow_char_pow, hxn, hzn]⟩
    | mul x z _ _ hx hz =>
      obtain ⟨n, hn, hxn, hzn⟩ := fix_both hx hz
      exact ⟨n, hn, by rw [map_mul, mul_pow, hxn, hzn]⟩
  obtain ⟨n, hn, hun⟩ := key u hu
  obtain ⟨k, hk⟩ : ∃ k, l ^ n = k + 1 + 1 :=
    ⟨l ^ n - 2, by
      have := Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt
      omega⟩
  apply hu0
  have hmem : y u ^ (k + 1) ∈ maximalIdeal V := Ideal.pow_mem_of_mem _ hum _ (Nat.succ_pos k)
  have hunit : IsUnit (1 - y u ^ (k + 1)) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((mem_maximalIdeal _).mp hmem)
  have h0 : y u * (1 - y u ^ (k + 1)) = 0 := by
    rw [mul_sub, mul_one, ← pow_succ', ← hk, hun, sub_self]
  exact hunit.mul_left_eq_zero.mp h0
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.ZmPow
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

section

variable {O : Type} [CommRing O] {Γ : Type} [Group Γ] {R : Type} [CommRing R] [Algebra O R] (ρ : Γ →* M4 R)

private lemma zm_one : (1 : R) ∈ Submodule.span O (mono ρ 0) :=
  Submodule.subset_span ⟨[], by simp, by simp⟩

private lemma zm_mul {v w : ℤ × ℤ} {x y : R} (hx : x ∈ Submodule.span O (mono ρ v))
    (hy : y ∈ Submodule.span O (mono ρ w)) : x * y ∈ Submodule.span O (mono ρ (v + w)) := by
  open scoped Pointwise in
  have hsub : mono ρ v * mono ρ w ⊆ mono ρ (v + w) := by
    rintro _ ⟨a, ⟨L, hL, rfl⟩, b, ⟨M, hM, rfl⟩, rfl⟩
    exact ⟨L ++ M, by simp [hL, hM], by simp⟩
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  exact Submodule.span_mono hsub h

private lemma zm_pow {v : ℤ × ℤ} {x : R} (hx : x ∈ Submodule.span O (mono ρ v)) (k : ℕ) :
    x ^ k ∈ Submodule.span O (mono ρ (k • v)) := by
  induction k with
  | zero => simpa using zm_one (O := O) ρ
  | succ k ih => rw [pow_succ, succ_nsmul]; exact zm_mul ρ ih hx

end

theorem UpperTheory.V.Ws.Po.zMono :
    ∀ (O : Type) [CommRing O] (Γ : Type) [Group Γ] (R : Type) [CommRing R] [Algebra O R] (ρ : Γ →* M4 R) (W : WPres O (ℤ × ℤ) R)
      (c : Γ → Fin 4 → Fin 4 → O), (∀ g a b, a ≠ b → c g a b = 0) →
      (∀ i, ∃ g a b, W.z i = ρ g a b - algebraMap O R (c g a b) ∧ W.wt i = wt a b) →
      ∀ n : W.σ →₀ ℕ, Finsupp.weight W.wt n = 0 → (n.prod fun s k => W.z s ^ k) ∈ Algebra.adjoin O (mono ρ 0) := by
  intro O _ Γ _ R _ _ ρ W c hc hz n hn
  have hmem : ∀ i, W.z i ∈ Submodule.span O (mono ρ (W.wt i)) := by
    intro i
    obtain ⟨g, a, b, hzi, hwi⟩ := hz i
    rw [hzi, hwi]
    by_cases hab : a = b
    · subst hab
      have h0 : wt a a = 0 := (wt_eq_zero a a).mpr rfl
      rw [h0, Algebra.algebraMap_eq_smul_one]
      refine Submodule.sub_mem _ (Submodule.subset_span ⟨[(g, a, a)], by simp [h0], by simp⟩) ?_
      exact Submodule.smul_mem _ _ (zm_one ρ)
    · rw [hc g a b hab, map_zero, sub_zero]
      exact Submodule.subset_span ⟨[(g, a, b)], by simp, by simp⟩
  classical
  have hall : ∀ t : Finset W.σ,
      (∏ s ∈ t, W.z s ^ n s) ∈ Submodule.span O (mono ρ (∑ s ∈ t, n s • W.wt s)) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using zm_one (O := O) ρ
    | @insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact zm_mul ρ (zm_pow ρ (hmem a) _) ih
  have h := hall n.support
  rw [Finsupp.weight_apply, Finsupp.sum] at hn
  rw [hn] at h
  exact Algebra.span_le_adjoin O _ h
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem cont_map {Γ R R' : Type} [TopologicalSpace Γ] [CommRing R] [CommRing R'] (f : R →+* R') {I : Ideal R} {I' : Ideal R'}
    (h : ∀ x ∈ I, f x ∈ I') {F : Γ → R} (hF : AdicCont I F) : AdicCont I' fun g => f (F g) := fun N => by
  have hle : I ^ N ≤ (I' ^ N).comap f := le_trans (Ideal.pow_right_mono h N) (Ideal.le_comap_pow _ N)
  exact (hF N).comp (Ideal.quotientMap _ f hle)

theorem UpperTheory.V.Ws.ptOver :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ¬ D.Fin0 → ∃ (𝔞 : Amb l) (r : G ℚ Ω →* M4 𝔞.V), CharP 𝔞.K l ∧ VPt D 𝔞 r ∧ ∃ x ∈ mono r 0, ∀ n : ℕ, 0 < n → x ^ l ^ n ≠ x := by
  intro hC Ω _ _ _ l _ c D hD hF
  obtain ⟨U, _, _, _, ρ, W, hpt, hz, hform, hnf⟩ := Po.univGr hC D hD hF
  haveI : IsCO c.O (W.gr 0) := wPres_gr_zero_isCO_of_mem_maximalIdeal c.O _ U W hz
  obtain ⟨hmax, u, hu, hspan⟩ := wPres_maximalIdeal_gr_zero_eq_sup_span_monomials c.O _ U W hz
  obtain ⟨𝔞, A, _, _, _, f, s, y, hch, hf, hy, hloc, ⟨b, hb, hb0⟩, hO, hcl⟩ := Po.ambPt c (W.gr 0) hnf
  obtain ⟨A', _, _, _, f', Ξ, hf', hΞ, hext⟩ :=
    Po.ptA 𝔞 A f hf s c.O _ U W hz y (fun b hb => hloc b ((hmax b).2 hb)) hcl
  let Y : U →+* 𝔞.V := f'.comp Ξ
  have hya : ∀ a, y (algebraMap c.O (W.gr 0) a) = 𝔞.a c a := fun a => RingHom.congr_fun hy a
  have hYa : ∀ a, Y (algebraMap c.O U a) = 𝔞.a c a := fun a => by
    have e : ((algebraMap c.O (W.gr 0) a : W.A) : U) = algebraMap c.O U a := by
      simp
    rw [← hya, ← hext, e]
    rfl
  have hYm : ∀ x ∈ maximalIdeal U, Y x ∈ maximalIdeal 𝔞.V := fun x hx => by
    haveI := hf'.loc
    exact map_nonunit f' _ (hΞ x hx)
  refine ⟨𝔞, mapRep Y ρ.hom, hch, ⟨⟨A', inferInstance, inferInstance, inferInstance, f', ⟨mapRep Ξ ρ.hom, fun _ => 1⟩, hf',
    fun i j => cont_map Ξ hΞ (ρ.cont i j), PD.ext rfl (funext fun _ => Matrix.map_one _ (map_zero _) (map_one _))⟩,
    U, inferInstance, inferInstance, inferInstance, ρ, Y, hpt, RingHom.ext hYa, hYm, rfl⟩, ?_⟩
  have hex : ∃ v ∈ u, y v ≠ 0 := by
    by_contra hn
    push Not at hn
    refine hb0 (show b ∈ RingHom.ker y from (?_ : maximalIdeal (W.gr 0) ≤ RingHom.ker y) hb)
    rw [hspan]
    refine sup_le (Ideal.map_le_iff_le_comap.2 fun a ha => ?_) (Ideal.span_le.2 fun v hv => hn v hv)
    show y _ = 0
    rw [hya, hO a ha]
  obtain ⟨v, hv, hv0⟩ := hex
  obtain ⟨n, -, hn, hvn⟩ := hu v hv
  haveI := (Po.fin_res c).1
  haveI : CharP 𝔞.V l := haveI := hch; 𝔞.V.subtype.charP Subtype.val_injective l
  have hvm : v ∈ maximalIdeal (W.gr 0) := hspan ▸ Ideal.mem_sup_right (Ideal.subset_span hv)
  refine Po.nonAlg l c.O _ U ρ.hom 𝔞.V Y (fun a ha => by rw [hYa, hO a ha]) ((v : W.A) : U) ?_ (hYm _ ((hmax v).1 hvm)) ?_
  · rw [hvn]
    exact Po.zMono c.O _ U ρ.hom W (fun g a b => D.r0 g a b)
      (fun g a b h => Matrix.diagonal_apply_ne (fun i => (D.ps i g : c.O)) h) hform n hn
  · show f' (Ξ _) ≠ 0
    rwa [hext]
