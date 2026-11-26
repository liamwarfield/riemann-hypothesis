module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinGCls

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinGStab
noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc

section Local
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {Δ : K}

theorem stab_star_int {x : Lsq K Δ} (h : IsIntegral O x) : IsIntegral O (star x) := by
  let φ : Lsq K Δ →ₐ[O] Lsq K Δ :=
    { starRingEnd (Lsq K Δ) with
      commutes' := fun r => by
        show star (algebraMap O (Lsq K Δ) r) = algebraMap O (Lsq K Δ) r
        rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ)]
        ext <;> simp }
  exact h.map φ

theorem stab_re_int {x : Lsq K Δ} (h : IsIntegral O x) : IsIntegral O (2 * x.re) := by
  have h2 := h.add (stab_star_int h)
  have e : x + star x = algebraMap K (Lsq K Δ) (2 * x.re) := by
    ext <;> simp <;> ring
  rw [e] at h2
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom O K (Lsq K Δ)) (algebraMap K (Lsq K Δ)).injective).mp h2

theorem stab_im_int {x : Lsq K Δ} (h : IsIntegral O x) {c : K} (hc : IsIntegral O (c ^ 2 * Δ)) :
    IsIntegral O (2 * (c * Δ * x.im)) := by
  have hsq : (⟨0, c⟩ : Lsq K Δ) ^ 2 = algebraMap K (Lsq K Δ) (c ^ 2 * Δ) := by
    ext <;> simp [pow_two]
    ring
  have hω : IsIntegral O (⟨0, c⟩ : Lsq K Δ) := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hsq]
    exact hc.map (IsScalarTower.toAlgHom O K (Lsq K Δ))
  have hp := (h.sub (stab_star_int h)).mul hω
  have e : (x - star x) * (⟨0, c⟩ : Lsq K Δ) = algebraMap K (Lsq K Δ) (2 * (c * Δ * x.im)) := by
    ext <;> simp
    ring
  rw [e] at hp
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom O K (Lsq K Δ)) (algebraMap K (Lsq K Δ)).injective).mp hp

end Local

variable {F : Type} [Field F] [NumberField F] {Δ : F}

theorem stab_mem_of_int {v : Pl F} {a : Kv v} (h : IsIntegral (Ov v) a) : a ∈ v.adicCompletionIntegers F := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  rw [← hy]
  exact y.2

theorem stab_cv_mem (v : Pl F) (N : 𝓞 F) : cv v (N : F) ∈ v.adicCompletionIntegers F :=
  HeightOneSpectrum.coe_mem_adicCompletionIntegers v N

theorem stab_smul_int {v : Pl F} {d a : Kv v} (ha : a ∈ v.adicCompletionIntegers F) {x : Lsq (Kv v) d}
    (h : IsIntegral (Ov v) x) : IsIntegral (Ov v) (a • x) := by
  have e : a • x = algebraMap (Ov v) (Lsq (Kv v) d) ⟨a, ha⟩ * x := by
    rw [IsScalarTower.algebraMap_apply (Ov v) (Kv v) (Lsq (Kv v) d), Algebra.smul_def]
    rfl
  rw [e]
  exact isIntegral_algebraMap.mul h

theorem stab_glob_int {t : F} (h : ∀ v : Pl F, IsIntegral (Ov v) (cv v t)) : IsIntegral ℤ t := by
  obtain ⟨y, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F t (R := 𝓞 F) fun v => by
    have := stab_mem_of_int (h v)
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at this
    rwa [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact y.isIntegral_coe

private theorem exists_integer_mul_mem_adicCompletionIntegers (v : Pl F) (c : Kv v) :
    ∃ N : 𝓞 F, N ≠ 0 ∧ cv v (N : F) * c ∈ v.adicCompletionIntegers F := by
  have ho : IsOpen ((fun y => y - c) ⁻¹' (v.adicCompletionIntegers F : Set (Kv v))) :=
    (Valued.isOpen_valuationSubring (Kv v)).preimage (continuous_sub_right c)
  obtain ⟨f, hf⟩ := (HeightOneSpectrum.denseRange_algebraMap F v).exists_mem_open ho
    ⟨c, by
      show c - c ∈ v.adicCompletionIntegers F
      rw [sub_self]
      exact zero_mem _⟩
  obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (𝓞 F) f
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsF : (s : F) ≠ 0 := by exact_mod_cast hs0
  have hsf : (s : F) * f = r := by
    rw [← hrs]
    show (s : F) * ((r : F) / (s : F)) = r
    field_simp
  refine ⟨s, hs0, ?_⟩
  have hf' : cv v f - c ∈ v.adicCompletionIntegers F := hf
  have e : cv v (s : F) * c = cv v (r : F) - cv v (s : F) * (cv v f - c) := by
    rw [← hsf, map_mul]
    ring
  rw [e]
  exact sub_mem (stab_cv_mem v r) (mul_mem (stab_cv_mem v s) hf')

theorem stab_den_loc (v : Pl F) {d : Kv v} (x : Lsq (Kv v) d) :
    ∃ N : 𝓞 F, N ≠ 0 ∧ IsIntegral (Ov v) (cv v (N : F) • x) := by
  obtain ⟨N1, hN1, h1⟩ := exists_integer_mul_mem_adicCompletionIntegers v (2 * x.re)
  obtain ⟨N2, hN2, h2⟩ := exists_integer_mul_mem_adicCompletionIntegers v (x.re * x.re - d * x.im * x.im)
  refine ⟨N1 * N2, mul_ne_zero hN1 hN2, ?_⟩
  have ha : cv v ((N1 * N2 : 𝓞 F) : F) = cv v (N1 : F) * cv v (N2 : F) := by
    have e : ((N1 * N2 : 𝓞 F) : F) = (N1 : F) * (N2 : F) := map_mul (algebraMap (𝓞 F) F) N1 N2
    rw [e, map_mul]
  have ht : cv v ((N1 * N2 : 𝓞 F) : F) * (2 * x.re) ∈ v.adicCompletionIntegers F := by
    rw [ha, mul_comm (cv v (N1 : F)), mul_assoc]
    exact mul_mem (stab_cv_mem v N2) h1
  have hn : cv v ((N1 * N2 : 𝓞 F) : F) ^ 2 * (x.re * x.re - d * x.im * x.im) ∈ v.adicCompletionIntegers F := by
    have e : cv v ((N1 * N2 : 𝓞 F) : F) ^ 2 * (x.re * x.re - d * x.im * x.im) =
        (cv v (N1 : F) ^ 2 * cv v (N2 : F)) * (cv v (N2 : F) * (x.re * x.re - d * x.im * x.im)) := by
      rw [ha]
      ring
    rw [e]
    exact mul_mem (mul_mem (pow_mem (stab_cv_mem v N1) 2) (stab_cv_mem v N2)) h2
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (⟨_, ht⟩ : Ov v) * Polynomial.X + Polynomial.C (⟨_, hn⟩ : Ov v), ?_, ?_⟩
  · monicity!
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    have hre : ∀ r : Ov v, (algebraMap (Ov v) (Lsq (Kv v) d) r).re = r := fun r => rfl
    have him : ∀ r : Ov v, (algebraMap (Ov v) (Lsq (Kv v) d) r).im = 0 := fun r => rfl
    apply QuadraticAlgebra.ext
    · simp only [pow_two, QuadraticAlgebra.re_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, smul_eq_mul, hre, him,
        QuadraticAlgebra.re_zero]
      ring
    · simp only [pow_two, QuadraticAlgebra.im_add, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, smul_eq_mul, hre, him,
        QuadraticAlgebra.im_zero]
      ring

theorem stab_den {J : Type} [Finite J] (x : J → ∀ v : Pl F, Lsq (Kv v) (cv v Δ))
    (h : ∀ᶠ v in Filter.cofinite, ∀ j, IsIntegral (Ov v) (x j v)) :
    ∃ N : 𝓞 F, N ≠ 0 ∧ ∀ j v, IsIntegral (Ov v) (cv v (N : F) • x j v) := by
  classical
  have := Fintype.ofFinite J
  have hS := Filter.eventually_cofinite.mp h
  choose M hM0 hM using fun p : Pl F × J => stab_den_loc p.1 (x p.2 p.1)
  refine ⟨∏ p ∈ hS.toFinset ×ˢ Finset.univ, M p, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (fun p _ => hM0 p)
  · intro j v
    by_cases hv : v ∈ hS.toFinset
    · have hp : (v, j) ∈ hS.toFinset ×ˢ Finset.univ := Finset.mem_product.mpr ⟨hv, Finset.mem_univ _⟩
      rw [← Finset.mul_prod_erase _ _ hp]
      have e : cv v ((M (v, j) * ∏ q ∈ (hS.toFinset ×ˢ Finset.univ).erase (v, j), M q : 𝓞 F) : F) • x j v =
          cv v ((∏ q ∈ (hS.toFinset ×ˢ Finset.univ).erase (v, j), M q : 𝓞 F) : F) •
            (cv v (M (v, j) : F) • x j v) := by
        rw [smul_smul, ← map_mul]
        congr 2
        exact (map_mul (algebraMap (𝓞 F) F) _ _).trans (mul_comm _ _)
      rw [e]
      exact stab_smul_int (stab_cv_mem v _) (hM (v, j))
    · have hv' : ∀ j, IsIntegral (Ov v) (x j v) := by
        by_contra hc
        exact hv (hS.mem_toFinset.mpr hc)
      exact stab_smul_int (stab_cv_mem v _) (hv' j)

theorem stab_fin_bd [IsTotallyReal F] (B : ℝ) : {t : F | IsIntegral ℤ t ∧ ∀ σ : F →+* ℝ, |σ t| ≤ B}.Finite := by
  refine (Embeddings.finite_of_norm_le F ℂ B).subset fun t ht => ⟨ht.1, fun φ => ?_⟩
  have hr : ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
  rw [← hr.coe_embedding_apply t, Complex.norm_real, Real.norm_eq_abs]
  exact ht.2 _

theorem stab_fin_L [IsTotallyReal F] (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) (N : 𝓞 F) (hN : N ≠ 0) :
    {x : Lsq F Δ | (∀ v : Pl F, IsIntegral (Ov v) (cv v (N : F) • lmap (cv v) Δ x)) ∧
      ∀ σ : F →+* ℝ, σ (x.re ^ 2 - Δ * x.im ^ 2) ≤ 1}.Finite := by
  classical
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  let σ0 : F →+* ℝ := (InfinitePlace.isReal_iff.mp (IsTotallyReal.isReal w)).embedding
  have hΔ : Δ ≠ 0 := by
    intro h0
    have := hneg σ0
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 F) Δ
  have hb0 : algebraMap (𝓞 F) F b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr (nonZeroDivisors.ne_zero hb)
  set c : F := algebraMap (𝓞 F) F b with hc
  have hcΔ : IsIntegral ℤ (c ^ 2 * Δ) := by
    have e : c ^ 2 * Δ = algebraMap (𝓞 F) F (b * a) := by
      rw [← hab, map_mul]
      field_simp
      rw [hc]
      ring
    rw [e]
    exact (b * a).isIntegral_coe
  have hN' : (N : F) ≠ 0 := by
    intro h0
    apply hN
    exact_mod_cast h0
  have hloc : ∀ t : F, IsIntegral ℤ t → ∀ v : Pl F, IsIntegral (Ov v) (cv v t) := by
    intro t ht v
    have hm : cv v t ∈ v.adicCompletionIntegers F := stab_cv_mem v ⟨t, ht⟩
    exact isIntegral_algebraMap (x := (⟨cv v t, hm⟩ : Ov v))
  have hre : ∀ x : Lsq F Δ, (∀ v : Pl F, IsIntegral (Ov v) (cv v (N : F) • lmap (cv v) Δ x)) →
      IsIntegral ℤ (2 * ((N : F) * x.re)) := by
    intro x hx
    apply stab_glob_int
    intro v
    have h1 := stab_re_int (hx v)
    have e : 2 * (cv v (N : F) • lmap (cv v) Δ x).re = cv v (2 * ((N : F) * x.re)) := by
      rw [QuadraticAlgebra.re_smul, smul_eq_mul]
      simp [lmap, map_mul, map_ofNat]
    rwa [e] at h1
  have him : ∀ x : Lsq F Δ, (∀ v : Pl F, IsIntegral (Ov v) (cv v (N : F) • lmap (cv v) Δ x)) →
      IsIntegral ℤ (2 * (c * Δ * ((N : F) * x.im))) := by
    intro x hx
    apply stab_glob_int
    intro v
    have hc2 : IsIntegral (Ov v) (cv v c ^ 2 * cv v Δ) := by
      have := hloc _ hcΔ v
      simpa [map_mul, map_pow] using this
    have h1 := stab_im_int (hx v) hc2
    have e : 2 * (cv v c * cv v Δ * (cv v (N : F) • lmap (cv v) Δ x).im) =
        cv v (2 * (c * Δ * ((N : F) * x.im))) := by
      rw [QuadraticAlgebra.im_smul, smul_eq_mul]
      simp [lmap, map_mul, map_ofNat]
    rwa [e] at h1
  let B : ℝ := ∑ σ : F →+* ℝ, (2 * |σ (N : F)| + 2 * |σ c| * |σ (N : F)| * (1 - σ Δ))
  have hterm : ∀ σ : F →+* ℝ, 2 * |σ (N : F)| + 2 * |σ c| * |σ (N : F)| * (1 - σ Δ) ≤ B := by
    intro σ
    apply Finset.single_le_sum (f := fun σ : F →+* ℝ => 2 * |σ (N : F)| + 2 * |σ c| * |σ (N : F)| * (1 - σ Δ))
      _ (Finset.mem_univ σ)
    intro τ _
    have h1 : (0 : ℝ) ≤ 1 - τ Δ := by linarith [hneg τ]
    have h2 := abs_nonneg (τ (N : F))
    have h3 := abs_nonneg (τ c)
    have h4 : 0 ≤ 2 * |τ c| * |τ (N : F)| * (1 - τ Δ) := by positivity
    linarith
  have hbd : ∀ x : Lsq F Δ, (∀ σ : F →+* ℝ, σ (x.re ^ 2 - Δ * x.im ^ 2) ≤ 1) → ∀ σ : F →+* ℝ,
      |σ (2 * ((N : F) * x.re))| ≤ B ∧ |σ (2 * (c * Δ * ((N : F) * x.im)))| ≤ B := by
    intro x hx σ
    have h1 := hx σ
    simp only [map_sub, map_mul, map_pow] at h1
    have hd := hneg σ
    set r := σ x.re
    set i := σ x.im
    set d := σ Δ
    have hr : |r| ≤ 1 := abs_le.mpr ⟨by nlinarith [sq_nonneg i], by nlinarith [sq_nonneg i]⟩
    have hdi2 : (d * i) ^ 2 ≤ -d := by nlinarith [sq_nonneg i, sq_nonneg r]
    have hdi : |d * i| ≤ 1 - d := abs_le.mpr ⟨by nlinarith [sq_nonneg (d * i + 1)], by nlinarith [sq_nonneg (d * i - 1)]⟩
    have hA := abs_nonneg (σ (N : F))
    have hC := abs_nonneg (σ c)
    have hT := hterm σ
    have hP : 0 ≤ |σ c| * |σ (N : F)| * (1 - d) := mul_nonneg (mul_nonneg hC hA) (by linarith)
    constructor
    · simp only [map_mul, map_ofNat, abs_mul, abs_two]
      have : |σ (N : F)| * |r| ≤ |σ (N : F)| := by nlinarith
      nlinarith
    · simp only [map_mul, map_ofNat, abs_mul, abs_two]
      have e : |σ c| * |d| * (|σ (N : F)| * |i|) = |σ c| * |σ (N : F)| * |d * i| := by
        rw [abs_mul]; ring
      rw [e]
      have : |σ c| * |σ (N : F)| * |d * i| ≤ |σ c| * |σ (N : F)| * (1 - d) :=
        mul_le_mul_of_nonneg_left hdi (mul_nonneg hC hA)
      nlinarith
  let S1 := {t : F | IsIntegral ℤ t ∧ ∀ σ : F →+* ℝ, |σ t| ≤ B}
  have hS1 : S1.Finite := stab_fin_bd B
  let f : Lsq F Δ → F × F := fun x => (2 * ((N : F) * x.re), 2 * (c * Δ * ((N : F) * x.im)))
  apply Set.Finite.of_finite_image (f := f)
  · apply (hS1.prod hS1).subset
    rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
    exact ⟨⟨hre x hx1, fun σ => (hbd x hx2 σ).1⟩, ⟨him x hx1, fun σ => (hbd x hx2 σ).2⟩⟩
  · intro x _ y _ hxy
    have h1 := congrArg Prod.fst hxy
    have h2 := congrArg Prod.snd hxy
    simp only [f] at h1 h2
    have h2' : (2 * c * Δ * (N : F)) * x.im = (2 * c * Δ * (N : F)) * y.im := by linear_combination h2
    have h1' : (2 * (N : F)) * x.re = (2 * (N : F)) * y.re := by linear_combination h1
    have hne1 : (2 * (N : F)) ≠ 0 := mul_ne_zero two_ne_zero hN'
    have hne2 : (2 * c * Δ * (N : F)) ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hb0) hΔ) hN'
    exact QuadraticAlgebra.ext (mul_left_cancel₀ hne1 h1') (mul_left_cancel₀ hne2 h2')

theorem stab_norm_le (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) (γ : U3 Δ) (i j : Fin 3) (σ : F →+* ℝ) :
    σ (((γ : Matrix (Fin 3) (Fin 3) (Lsq F Δ)) i j).re ^ 2 - Δ * ((γ : Matrix (Fin 3) (Fin 3) (Lsq F Δ)) i j).im ^ 2) ≤ 1 := by
  set A : Matrix (Fin 3) (Fin 3) (Lsq F Δ) := (γ : Matrix (Fin 3) (Fin 3) (Lsq F Δ)) with hA
  have hu : star A * A = 1 := Matrix.mem_unitaryGroup_iff'.mp γ.2
  have hjj := congrArg QuadraticAlgebra.re (congrFun (congrFun hu j) j)
  have resum : ∀ (s : Finset (Fin 3)) (f : Fin 3 → Lsq F Δ), (∑ k ∈ s, f k).re = ∑ k ∈ s, (f k).re := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [Finset.sum_insert ha, ih]
  have key : ∀ z : Lsq F Δ, (star z * z).re = z.re ^ 2 - Δ * z.im ^ 2 := by
    intro z
    simp
    ring
  simp only [Matrix.mul_apply, Matrix.one_apply_eq, Matrix.star_apply, resum, key] at hjj
  have hnn : ∀ z : Lsq F Δ, 0 ≤ σ (z.re ^ 2 - Δ * z.im ^ 2) := by
    intro z
    have := hneg σ
    rw [map_sub, map_mul, map_pow, map_pow]
    nlinarith [sq_nonneg (σ z.re), sq_nonneg (σ z.im)]
  have hs := congrArg σ hjj
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at hs
  have hsum : ∑ k, σ ((A k j).re ^ 2 - Δ * (A k j).im ^ 2) = 1 := by
    rw [hs]
    exact (congrArg σ (QuadraticAlgebra.re_one)).trans (map_one σ)
  rw [← hsum]
  exact Finset.single_le_sum (f := fun k => σ ((A k j).re ^ 2 - Δ * (A k j).im ^ 2))
    (fun k _ => hnn (A k j)) (Finset.mem_univ i)

theorem stab_conj_int {v : Pl F} {d a : Kv v} (g x : U3 d)
    (h1 : ∀ i j, IsIntegral (Ov v) (a • (g : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) d)) i j))
    (h2 : ∀ i j, IsIntegral (Ov v) (a • ((g⁻¹ : U3 d) : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) d)) i j))
    (h : g⁻¹ * x * g ∈ KU (Ov v) d) (i j : Fin 3) :
    IsIntegral (Ov v) ((a * a) • (x : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) d)) i j) := by
  set G : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) d) := (g : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) d)) with hG
  set Gi : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) d) := ((g⁻¹ : U3 d) : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) d)) with hGi
  set Y : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) d) := ((g⁻¹ * x * g : U3 d) : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) d)) with hYd
  have hxe : (x : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) d)) = G * Y * Gi := by
    have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    conv_lhs => rw [e]
    rfl
  have hY : ∀ k l, IsIntegral (Ov v) (Y k l) := fun k l => (h k l).1
  have hm : (a * a) • (G * Y * Gi) = (a • G) * Y * (a • Gi) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hxe, ← Matrix.smul_apply, hm]
  let S := integralClosure (Ov v) (Lsq (Kv v) d)
  show ((a • G) * Y * (a • Gi)) i j ∈ S
  rw [Matrix.mul_apply]
  refine S.sum_mem (fun l _ => S.mul_mem ?_ ?_)
  · rw [Matrix.mul_apply]
    refine S.sum_mem (fun k _ => S.mul_mem ?_ (hY k l))
    rw [Matrix.smul_apply]
    exact h1 i k
  · rw [Matrix.smul_apply]
    exact h2 l j

theorem finG_stab [IsTotallyReal F] (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) (ι : U3 Δ →* GA Δ) (hι : IsIotaG ι) (g : GA Δ) :
    {γ : U3 Δ | ∀ v, (g⁻¹ * ι γ * g).1 v ∈ KU (Ov v) (cv v Δ)}.Finite := by
  classical
  have memKU : ∀ (w : Pl F) (y : U3 (cv w Δ)), y ∈ KU (Ov w) (cv w Δ) →
      ∀ i j, IsIntegral (Ov w) ((y : Matrix (Fin 3) (Fin 3) (Lsq (Kv w) (cv w Δ))) i j) := by
    intro w y hy i j
    exact ((show ∀ i j, IsInt (Ov w) ((y : Matrix (Fin 3) (Fin 3) (Lsq (Kv w) (cv w Δ))) i j) ∧
      IsInt (Ov w) (star ((y : Matrix (Fin 3) (Fin 3) (Lsq (Kv w) (cv w Δ))) i j)) from hy) i j).1
  let x : (Fin 3 × Fin 3 × Bool) → ∀ v : Pl F, Lsq (Kv v) (cv v Δ) := fun p v =>
    if p.2.2 then ((g.1 v : U3 (cv v Δ)) : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) (cv v Δ))) p.1 p.2.1
    else (((g.1 v)⁻¹ : U3 (cv v Δ)) : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) (cv v Δ))) p.1 p.2.1
  have hg : ∀ᶠ v in Filter.cofinite, g.1 v ∈ KU (Ov v) (cv v Δ) := g.2
  have hgi : ∀ᶠ v in Filter.cofinite, (g.1 v)⁻¹ ∈ KU (Ov v) (cv v Δ) := (g⁻¹).2
  have hx : ∀ᶠ v in Filter.cofinite, ∀ p, IsIntegral (Ov v) (x p v) := by
    filter_upwards [hg, hgi] with v h1 h2
    rintro ⟨i, j, b⟩
    cases b
    · exact memKU v _ h2 i j
    · exact memKU v _ h1 i j
  obtain ⟨N, hN0, hN⟩ := stab_den x hx
  have hNN : (N * N : 𝓞 F) ≠ 0 := mul_ne_zero hN0 hN0
  have hL := stab_fin_L hneg (N * N) hNN
  have key : ∀ γ ∈ {γ : U3 Δ | ∀ v, (g⁻¹ * ι γ * g).1 v ∈ KU (Ov v) (cv v Δ)}, ∀ i j,
      (γ : Matrix (Fin 3) (Fin 3) (Lsq F Δ)) i j ∈ {x : Lsq F Δ |
        (∀ v : Pl F, IsIntegral (Ov v) (cv v ((N * N : 𝓞 F) : F) • lmap (cv v) Δ x)) ∧
        ∀ σ : F →+* ℝ, σ (x.re ^ 2 - Δ * x.im ^ 2) ≤ 1} := by
    intro γ hγ i j
    refine ⟨fun v => ?_, fun σ => stab_norm_le hneg γ i j σ⟩
    have h1 : ∀ i j, IsIntegral (Ov v)
        (cv v (N : F) • ((g.1 v : U3 (cv v Δ)) : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) (cv v Δ))) i j) :=
      fun i j => hN (i, j, true) v
    have h2 : ∀ i j, IsIntegral (Ov v)
        (cv v (N : F) • (((g.1 v)⁻¹ : U3 (cv v Δ)) : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) (cv v Δ))) i j) :=
      fun i j => hN (i, j, false) v
    have h3 := stab_conj_int (g.1 v) ((ι γ).1 v) h1 h2 (hγ v) i j
    have e1 : (((ι γ).1 v : U3 (cv v Δ)) : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) (cv v Δ))) i j =
        lmap (cv v) Δ ((γ : Matrix (Fin 3) (Fin 3) (Lsq F Δ)) i j) := by
      rw [hι γ v]
      rfl
    have e2 : cv v ((N * N : 𝓞 F) : F) = cv v (N : F) * cv v (N : F) := by
      simp
    rw [e2, ← e1]
    exact h3
  apply Set.Finite.of_finite_image (f := fun γ : U3 Δ => (γ : Matrix (Fin 3) (Fin 3) (Lsq F Δ)))
  · refine (Set.Finite.pi (fun _ : Fin 3 => Set.Finite.pi (fun _ : Fin 3 => hL))).subset ?_
    rintro _ ⟨γ, hγ, rfl⟩
    simp only [Set.mem_pi]
    intro i _ j _
    exact key γ hγ i j
  · intro a _ b _ hab
    exact Subtype.ext hab

theorem finG_stab' {D : Dat Δ} {V : Type} [AddCommGroup V] [Module ℂ V] {ch : F → ℂ} {B : Base (U3 Δ) (GA Δ) V} {s : B.Tw}
    (hD : D.Ok) (hB : D.IsBG ch B s) (g : GA Δ) :
    B.Γ₀.relIndex ((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι) ≠ 0 := by
  haveI := hD.real
  have hfin := finG_stab hD.neg B.ι hB.ι g
  rw [hB.Γ₀, Subgroup.relIndex_bot_left]
  have hsub : (((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι : Subgroup (U3 Δ)) : Set (U3 Δ)) ⊆
      {γ : U3 Δ | ∀ v, (g⁻¹ * B.ι γ * g).1 v ∈ KU (Ov v) (cv v Δ)} := by
    intro γ hγ
    simp only [Subgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_map] at hγ
    obtain ⟨u, hu, hue⟩ := hγ
    have hu' : u ∈ D.UG := hB.U ▸ hu
    have e : g⁻¹ * B.ι γ * g = u := by
      rw [← hue]
      simp [MulAut.conj_apply, mul_assoc]
    show ∀ v, (g⁻¹ * B.ι γ * g).1 v ∈ KU (Ov v) (cv v Δ)
    rw [e]
    intro v
    simp only [Dat.UG, RPG.box, Subgroup.mem_iInf, Subgroup.mem_comap] at hu'
    have hv := hu' v
    by_cases hs : v ∈ D.Sg
    · have hJ : D.Jv v = (D.S v).J := by simp [Dat.Jv, hs]
      rw [hJ] at hv
      exact (hD.sig v hs).J_le hv
    · have hJ : D.Jv v = KU (Ov v) (cv v Δ) := by simp [Dat.Jv, hs]
      rw [hJ] at hv
      exact hv
  haveI : Finite ((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι) := (hfin.subset hsub).to_subtype
  exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩

end UpperTheory.V.Z.Sym.Glob
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinGTest
noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc

section Generic

variable {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)}

theorem finG_mem_box (P : RPG G Gv K) (U : ∀ v, Subgroup (Gv v)) (g : G) : g ∈ P.box U ↔ ∀ v, P.p v g ∈ U v := by
  simp [RPG.box, Subgroup.mem_iInf]

theorem finG_box_finite (P : RPG G Gv K) (U : ∀ v, Subgroup (Gv v)) (S : Finset I) (B : ∀ v, Set (Gv v ⧸ U v))
    (hB : ∀ v ∈ S, (B v).Finite) :
    {x : G ⧸ P.box U | (∀ v ∉ S, P.p v x.out ∈ U v) ∧ ∀ v ∈ S, (P.p v x.out : Gv v ⧸ U v) ∈ B v}.Finite := by
  classical
  let f : G ⧸ P.box U → ((v : S) → Gv v ⧸ U v) := fun x v => (P.p v x.out : Gv v ⧸ U v)
  apply Set.Finite.of_finite_image (f := f)
  · apply Set.Finite.subset (Set.Finite.pi (t := fun v : S => B v) (fun v => hB v v.2))
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, forall_const]
    intro v
    exact hx.2 v v.2
  · intro x hx y hy hxy
    have ex : ((x.out : G) : G ⧸ P.box U) = x := Quotient.out_eq x
    have ey : ((y.out : G) : G ⧸ P.box U) = y := Quotient.out_eq y
    rw [← ex, ← ey, QuotientGroup.eq, finG_mem_box]
    intro v
    rw [map_mul, map_inv]
    by_cases hv : v ∈ S
    · exact QuotientGroup.eq.mp (congrFun hxy ⟨v, hv⟩)
    · exact (U v).mul_mem ((U v).inv_mem (hx.1 v hv)) (hy.1 v hv)

theorem finG_finite_image_of_relIndex {H : Type} [Group H] {J L : Subgroup H} (h : J.relIndex L ≠ 0) :
    ((fun a : H => (a : H ⧸ J)) '' (L : Set H)).Finite := by
  have hf : Finite (L ⧸ J.subgroupOf L) := Subgroup.index_ne_zero_iff_finite.mp h
  let g : L ⧸ J.subgroupOf L → H ⧸ J :=
    Quotient.lift (fun a : L => ((a : H) : H ⧸ J)) (by
      intro a b hab
      apply QuotientGroup.eq.mpr
      have := (QuotientGroup.leftRel_apply).mp hab
      simpa [Subgroup.mem_subgroupOf] using this)
  apply Set.Finite.subset (Set.finite_range g)
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨(⟨a, ha⟩ : L), rfl⟩

theorem finG_cls_of_box {Γ : Type} (ι : Γ → G) (P : RPG G Gv K) (L U : ∀ v, Subgroup (Gv v)) (S : Finset I)
    (hle : ∀ v, U v ≤ L v) (hoff : ∀ v ∉ S, L v ≤ U v) (hfin : ∀ v ∈ S, (U v).relIndex (L v) ≠ 0)
    (h : ∃ T : Finset G, ∀ g, ∃ γ, ∃ s ∈ T, ∃ u : G, (∀ v, P.p v u ∈ L v) ∧ g = ι γ * s * u) :
    ∃ T : Finset G, ∀ g, ∃ γ, ∃ s ∈ T, ∃ u ∈ P.box U, g = ι γ * s * u := by
  classical
  obtain ⟨T, hT⟩ := h
  have hX := finG_box_finite P U S (fun v => (fun a : Gv v => (a : Gv v ⧸ U v)) '' (L v : Set (Gv v)))
    (fun v hv => finG_finite_image_of_relIndex (hfin v hv))
  refine ⟨(T ×ˢ hX.toFinset).image (fun q => q.1 * q.2.out), ?_⟩
  intro g
  obtain ⟨γ, s, hs, u, hu, rfl⟩ := hT g
  let x : G ⧸ P.box U := (u : G ⧸ P.box U)
  have e : ((x.out : G) : G ⧸ P.box U) = (u : G ⧸ P.box U) := Quotient.out_eq x
  have hw : x.out⁻¹ * u ∈ P.box U := QuotientGroup.eq.mp e
  have hwv := (finG_mem_box P U _).mp hw
  have hxX : x ∈ {x : G ⧸ P.box U | (∀ v ∉ S, P.p v x.out ∈ U v) ∧
      ∀ v ∈ S, (P.p v x.out : Gv v ⧸ U v) ∈ (fun a : Gv v => (a : Gv v ⧸ U v)) '' (L v : Set (Gv v))} := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have hxo : x.out = u * (x.out⁻¹ * u)⁻¹ := by simp
      rw [hxo, map_mul, map_inv]
      exact (U v).mul_mem (hoff v hv (hu v)) ((U v).inv_mem (hwv v))
    · refine ⟨P.p v u, hu v, ?_⟩
      refine (QuotientGroup.eq.mpr ?_).symm
      rw [← map_inv, ← map_mul]
      exact hwv v
  refine ⟨γ, s * x.out, ?_, x.out⁻¹ * u, hw, ?_⟩
  · exact Finset.mem_image.mpr ⟨(s, x), Finset.mem_product.mpr ⟨hs, hX.mem_toFinset.mpr hxX⟩, rfl⟩
  · simp [mul_assoc]

end Generic

section Local

variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {Δ : K}

theorem finG_theta_mem_KU (g : U3 Δ) : theta Δ g ∈ KU O Δ ↔ g ∈ KU O Δ := by
  show (∀ i j, IsInt O (((theta Δ g : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j) ∧
      IsInt O (star (((theta Δ g : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j))) ↔
    ∀ i j, IsInt O ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j) ∧
      IsInt O (star ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j))
  have hc : ∀ i j, ((theta Δ g : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j =
      star ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j) := fun i j => rfl
  simp only [hc, star_star]
  exact ⟨fun h i j => (h i j).symm, fun h i j => (h i j).symm⟩

end Local

variable {F : Type} [Field F] [NumberField F] {Δ : F} {D : Dat Δ}

theorem finG_Jv_of_mem {v : Pl F} (hv : v ∈ D.Sg) : D.Jv v = (D.S v).J := by simp [Dat.Jv, hv]

theorem finG_Jv_of_not_mem {v : Pl F} (hv : v ∉ D.Sg) : D.Jv v = KU (Ov v) _ := by simp [Dat.Jv, hv]

theorem finG_cls_of (hD : D.Ok) (ι : U3 Δ →* GA Δ)
    (h : ∃ S : Finset (GA Δ), ∀ g, ∃ γ, ∃ s ∈ S, ∃ u : GA Δ, (∀ v, u.1 v ∈ KU (Ov v) (cv v Δ)) ∧ g = ι γ * s * u) :
    ∃ S : Finset (GA Δ), ∀ g, ∃ γ, ∃ s ∈ S, ∃ u ∈ D.UG, g = ι γ * s * u := by
  refine finG_cls_of_box ι (rpg _ _) (fun v => KU (Ov v) (cv v Δ)) D.Jv D.Sg (fun v => ?_) (fun v hv => ?_) (fun v hv => ?_) h
  · by_cases hv : v ∈ D.Sg
    · rw [finG_Jv_of_mem hv]; exact (hD.sig v hv).J_le
    · rw [finG_Jv_of_not_mem hv]
  · rw [finG_Jv_of_not_mem hv]
  · rw [finG_Jv_of_mem hv]; exact (hD.sig v hv).J_fin

theorem finG_fGv_inv (hD : D.Ok) {t : Dat.Par F} (ht : D.Cone t) (v : Pl F) (u : U3 (cv v Δ)) (hu : u ∈ D.Jv v) (y : U3 (cv v Δ)) :
    D.fGv t v (u * y) = D.fGv t v y ∧ D.fGv t v (y * theta _ u) = D.fGv t v y := by
  by_cases hv : v ∈ D.Sg
  · rw [finG_Jv_of_mem hv] at hu
    simp only [Dat.fGv, hv, if_true]
    exact (hD.sig v hv).G_inv (t v) (ht v hv) u hu y
  · rw [finG_Jv_of_not_mem hv] at hu
    simp only [Dat.fGv, hv, if_false]
    have hθ : theta _ u ∈ KU (Ov v) (cv v Δ) := (finG_theta_mem_KU u).mpr hu
    constructor
    · rw [Subgroup.mul_mem_cancel_left _ hu]
    · rw [Subgroup.mul_mem_cancel_right _ hθ]

theorem finG_fGv_ne_zero {t : Dat.Par F} {g : GA Δ} (h : D.FG t g ≠ 0) (v : Pl F) : D.fGv t v (g.1 v) ≠ 0 := by
  intro h0
  apply h
  have hae := (rpg (fun v => U3 (cv v Δ)) (fun v => KU (Ov v) (cv v Δ))).ae g
  have hfin : {w | ¬ (g.1 w ∈ KU (Ov w) (cv w Δ))}.Finite := Filter.eventually_cofinite.mp hae
  show ∏ᶠ w, D.fGv t w (g.1 w) = 0
  apply finprod_eq_zero _ v h0
  apply ((D.Sg.finite_toSet).union hfin).subset
  intro w hw
  by_contra hc
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hc
  apply hw
  simp [Dat.fGv, hc.1, hc.2, one]

theorem finG_test (hD : D.Ok) {V : Type} [AddCommGroup V] [Module ℂ V] {ch : F → ℂ} {B : Base (U3 Δ) (GA Δ) V} {s : B.Tw}
    (hB : D.IsBG ch B s) (t : Dat.Par F) (ht : D.Cone t) : s.IsTest (D.FG t) := by
  have hU := hB.U
  have hω := hB.ω
  have hθ := hB.θ
  let P := rpg (fun v => U3 (cv v Δ)) (fun v => KU (Ov v) (cv v Δ))
  have hL : ∀ u ∈ D.UG, ∀ y : GA Δ, D.FG t (u * y) = D.FG t y := by
    intro u hu y
    have huv := (finG_mem_box P D.Jv u).mp hu
    show ∏ᶠ v, D.fGv t v ((u * y).1 v) = ∏ᶠ v, D.fGv t v (y.1 v)
    congr 1
    funext v
    exact (finG_fGv_inv hD ht v (u.1 v) (huv v) (y.1 v)).1
  have hR : ∀ u ∈ D.UG, ∀ y : GA Δ, D.FG t (y * s.θ u) = D.FG t y := by
    intro u hu y
    have huv := (finG_mem_box P D.Jv u).mp hu
    show ∏ᶠ v, D.fGv t v ((y * s.θ u).1 v) = ∏ᶠ v, D.fGv t v (y.1 v)
    congr 1
    funext v
    have e : (y * s.θ u).1 v = y.1 v * theta _ (u.1 v) := by
      show y.1 v * (s.θ u).1 v = _
      rw [hθ]
    rw [e]
    exact (finG_fGv_inv hD ht v (u.1 v) (huv v) (y.1 v)).2
  have hUm : ∀ u : B.U, (u : GA Δ) ∈ D.UG := fun u => hU ▸ u.2
  have hmemU : ∀ g : GA Δ, g ∈ D.UG → g ∈ B.U := fun g hg => hU ▸ hg
  refine ⟨fun u y => ?_, fun u y => ?_, ?_⟩
  · rw [hω]
    simp only [MonoidHom.one_apply, inv_one, Units.val_one, one_mul]
    exact hL u (hUm u) y
  · rw [hω]
    simp only [MonoidHom.one_apply, inv_one, Units.val_one, one_mul]
    exact hR u (hUm u) y
  · let Bs : ∀ v, Set (U3 (cv v Δ) ⧸ D.Jv v) := fun v => {c | D.fGv t v (theta _ c.out) ≠ 0}
    have hBs : ∀ v ∈ D.Sg, (Bs v).Finite := by
      intro v hv
      have hG := (hD.sig v hv).G_fin (t v) (ht v hv)
      show {c : U3 (cv v Δ) ⧸ D.Jv v | D.fGv t v (theta _ c.out) ≠ 0}.Finite
      rw [finG_Jv_of_mem hv]
      simpa [Dat.fGv, hv] using hG
    have hX := finG_box_finite P D.Jv D.Sg Bs hBs
    have hcls : ∀ v (a : U3 (cv v Δ)),
        D.fGv t v (theta _ ((a : U3 (cv v Δ) ⧸ D.Jv v).out)) = D.fGv t v (theta _ a) := by
      intro v a
      have e : (((a : U3 (cv v Δ) ⧸ D.Jv v).out : U3 (cv v Δ)) : U3 (cv v Δ) ⧸ D.Jv v) =
          (a : U3 (cv v Δ) ⧸ D.Jv v) := Quotient.out_eq _
      have hj := QuotientGroup.eq.mp e
      have ha : a = (a : U3 (cv v Δ) ⧸ D.Jv v).out * ((a : U3 (cv v Δ) ⧸ D.Jv v).out⁻¹ * a) := by simp
      conv_rhs => rw [ha, map_mul]
      exact ((finG_fGv_inv hD ht v _ hj _).2).symm
    have hmem : ∀ x : GA Δ ⧸ B.U, D.FG t (s.θ x.out) ≠ 0 →
        ((x.out : GA Δ) : GA Δ ⧸ P.box D.Jv) ∈ {z : GA Δ ⧸ P.box D.Jv | (∀ v ∉ D.Sg, P.p v z.out ∈ D.Jv v) ∧
          ∀ v ∈ D.Sg, (P.p v z.out : U3 (cv v Δ) ⧸ D.Jv v) ∈ Bs v} := by
      intro x hx
      have hne : ∀ v, D.fGv t v (theta _ (x.out.1 v)) ≠ 0 := by
        intro v
        have h1 := finG_fGv_ne_zero hx v
        rwa [hθ] at h1
      let z : GA Δ ⧸ P.box D.Jv := ((x.out : GA Δ) : GA Δ ⧸ P.box D.Jv)
      have e : ((z.out : GA Δ) : GA Δ ⧸ P.box D.Jv) = z := Quotient.out_eq z
      have hw : z.out⁻¹ * x.out ∈ P.box D.Jv := QuotientGroup.eq.mp e
      have hwv : ∀ v, (z.out⁻¹ * x.out).1 v ∈ D.Jv v := (finG_mem_box P D.Jv _).mp hw
      have hzv : ∀ v, z.out.1 v = x.out.1 v * ((z.out⁻¹ * x.out).1 v)⁻¹ := by
        intro v
        simp
      have hz' : ∀ v, D.fGv t v (theta _ (z.out.1 v)) ≠ 0 := by
        intro v
        rw [hzv v, map_mul, (finG_fGv_inv hD ht v ((z.out⁻¹ * x.out).1 v)⁻¹ ((D.Jv v).inv_mem (hwv v))
          (theta _ (x.out.1 v))).2]
        exact hne v
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · have h2 := hz' v
        simp [Dat.fGv, hv, one] at h2
        show z.out.1 v ∈ D.Jv v
        rw [finG_Jv_of_not_mem hv]
        exact (finG_theta_mem_KU _).mp h2
      · show D.fGv t v (theta _ ((z.out.1 v : U3 (cv v Δ) ⧸ D.Jv v).out)) ≠ 0
        rw [hcls]
        exact hz' v
    apply Set.Finite.of_finite_image (f := fun x : GA Δ ⧸ B.U => ((x.out : GA Δ) : GA Δ ⧸ P.box D.Jv))
    · exact hX.subset (by rintro _ ⟨x, hx, rfl⟩; exact hmem x hx)
    · intro x _ y _ hxy
      have hq := QuotientGroup.eq.mp hxy
      have ex : ((x.out : GA Δ) : GA Δ ⧸ B.U) = x := Quotient.out_eq x
      have ey : ((y.out : GA Δ) : GA Δ ⧸ B.U) = y := Quotient.out_eq y
      rw [← ex, ← ey]
      exact QuotientGroup.eq.mpr (hmemU _ hq)

end UpperTheory.V.Z.Sym.Glob
end
end

theorem UpperTheory.V.Z.Sym.Glob.finG :
    UpperTheory.V.Z.Sym.Glob.FinG := by
  intro F _ _ Δ D hD V _ _ ch B s hB
  haveI := hD.real
  refine ⟨⟨?_, finG_stab' hD hB⟩, finG_test hD hB⟩
  rw [hB.U]
  exact finG_cls_of hD B.ι (finG_cls hD.neg B.ι hB.ι)
