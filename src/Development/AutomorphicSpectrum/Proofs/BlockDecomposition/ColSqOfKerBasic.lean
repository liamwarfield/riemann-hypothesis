module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColSqOfKerBasic
open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KernelColumn

theorem colSq_of_kerBasic : KerBasic → ColSq := by
  intro hK X φ B Ω hT hB hΩ hS y
  letI : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  haveI : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  have hker := (hK X φ hT).2.2.2.2.2
  have hBe : ∀ z, ‖φ z‖ₑ ≤ ENNReal.ofReal B := fun z => by
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hB z)
  let A : X.G → ℝ≥0∞ := fun x => ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ
  have hterm : ∀ γ : X.Γ, Measurable fun x : X.G => ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ := fun γ =>
    (hT.1.comp (by fun_prop)).enorm.measurable
  have hAm : Measurable A := Measurable.tsum hterm
  have hAinv : ∀ (δ : X.Γ) (x : X.G), A ((δ : X.G) * x) = A x := by
    intro δ x
    simp only [A]
    rw [← (Equiv.mulLeft δ).tsum_eq (fun γ : X.Γ => ‖φ (((δ : X.G) * x)⁻¹ * (γ : X.G) * y)‖ₑ)]
    refine tsum_congr fun γ => ?_
    simp [mul_assoc]
  let g : X.G → ℝ≥0∞ := fun x => ‖φ (x⁻¹ * y)‖ₑ * A x
  have hgm : Measurable g :=
    ((hT.1.comp (by fun_prop : Continuous fun x : X.G => x⁻¹ * y)).enorm.measurable).mul hAm
  have hsq : ∀ x, A x ^ 2 = ∑' γ : X.Γ, g (γ⁻¹ • x) := by
    intro x
    rw [sq]
    calc A x * A x = (∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ) * A x := rfl
      _ = ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ * A x := ENNReal.tsum_mul_right.symm
      _ = ∑' γ : X.Γ, g (γ⁻¹ • x) := by
        refine tsum_congr fun γ => ?_
        have e : γ⁻¹ • x = ((γ⁻¹ : X.Γ) : X.G) * x := rfl
        simp only [g]
        rw [e, hAinv]
        simp [mul_assoc]
  let c : ℝ≥0∞ := ENNReal.ofReal B * (ENNReal.ofReal B * cnt X.Γ (Ω⁻¹ * Ω) y)
  have hg : ∀ x, g x ≤ (y • Ω⁻¹).indicator (fun _ => c) x := by
    intro x
    by_cases h0 : φ (x⁻¹ * y) = 0
    · simp [g, h0]
    · have hω : x⁻¹ * y ∈ Ω := hS h0
      have hx : x ∈ y • Ω⁻¹ := by
        rw [Set.mem_smul_set]
        exact ⟨y⁻¹ * x, by simpa [Set.mem_inv] using hω, by simp⟩
      rw [Set.indicator_of_mem hx]
      have h2 : A x ≤ ENNReal.ofReal B * cnt X.Γ (Ω⁻¹ * Ω) y := by
        simp only [A, cnt]
        rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun γ => ?_
        by_cases h3 : φ (x⁻¹ * (γ : X.G) * y) = 0
        · simp [h3]
        · have hm : y⁻¹ * (γ : X.G) * y ∈ Ω⁻¹ * Ω :=
            Set.mem_mul.2 ⟨(x⁻¹ * y)⁻¹, Set.inv_mem_inv.2 hω, x⁻¹ * (γ : X.G) * y, hS h3, by group⟩
          rw [Set.indicator_of_mem hm]
          simpa using hBe _
      exact mul_le_mul' (hBe _) h2
  calc ∫⁻ x, ‖ker X.Γ φ x y‖ₑ ^ 2 ∂X.ν ≤ ∫⁻ x, A x ^ 2 ∂X.ν :=
        lintegral_mono fun x => pow_le_pow_left' (hker x y) 2
    _ = ∫⁻ x in X.F, ∑' γ : X.Γ, g (γ⁻¹ • x) ∂X.μ := by
        simp only [hsq]; rfl
    _ = ∑' γ : X.Γ, ∫⁻ x in X.F, g (γ⁻¹ • x) ∂X.μ :=
        lintegral_tsum fun γ => (hgm.comp (measurable_const_mul ((γ⁻¹ : X.Γ) : X.G))).aemeasurable
    _ = ∫⁻ x, g x ∂X.μ := (X.fd.lintegral_eq_tsum' g).symm
    _ ≤ ∫⁻ x, (y • Ω⁻¹).indicator (fun _ => c) x ∂X.μ := lintegral_mono hg
    _ ≤ c * X.μ (y • Ω⁻¹) := lintegral_indicator_const_le _ _
    _ = ENNReal.ofReal B ^ 2 * X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y := by
        rw [measure_smul]
        simp only [c]
        ring

end GlobalTheory.CompanionTheory.KernelColumn
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqCOfToLaurentEqInvert
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.LaurSplit

variable {K : Type} [CommRing K]

theorem coeff_nat (p : Polynomial K) (k : ℕ) :
    (Polynomial.toLaurent p).coeff (k : ℤ) = p.coeff k := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective _ k

theorem coeff_neg (p : Polynomial K) (k : ℤ) (hk : k < 0) :
    (Polynomial.toLaurent p).coeff k = 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_notin_range
  rintro ⟨m, hm⟩
  have : (m : ℤ) = k := hm
  omega

theorem eq_C_of_toLaurent_eq_invert (a b : Polynomial K)
    (h : Polynomial.toLaurent a = LaurentPolynomial.invert (Polynomial.toLaurent b)) :
    a = Polynomial.C (a.coeff 0) ∧ b = Polynomial.C (a.coeff 0) := by
  have hc : ∀ n : ℤ, (Polynomial.toLaurent a).coeff n = (Polynomial.toLaurent b).coeff (-n) :=
    fun n => by rw [h, LaurentPolynomial.invert_apply]
  constructor
  · ext n
    rcases n with _ | n
    · simp
    · rw [Polynomial.coeff_C_succ, ← coeff_nat, hc]
      exact coeff_neg b _ (by omega)
  · ext n
    rcases n with _ | n
    · have h0 := hc ((0 : ℕ) : ℤ)
      rw [coeff_nat] at h0
      have h1 : (-(((0 : ℕ) : ℤ))) = ((0 : ℕ) : ℤ) := by simp
      rw [h1, coeff_nat] at h0
      simp [h0]
    · have h0 := hc (((n + 1 : ℕ) : ℤ) * (-1))
      have h1 : (-(((n + 1 : ℕ) : ℤ) * (-1))) = ((n + 1 : ℕ) : ℤ) := by ring
      rw [h1, coeff_nat, coeff_neg a _ (by omega)] at h0
      rw [Polynomial.coeff_C_succ, ← h0]

theorem exists_split (h : K[T;T⁻¹]) :
    ∃ h₁ h₂ : Polynomial K, h = Polynomial.toLaurent h₁ +
      LaurentPolynomial.T (-1) * LaurentPolynomial.invert (Polynomial.toLaurent h₂) := by
  induction h using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨p₁, p₂, rfl⟩ := hp
    obtain ⟨q₁, q₂, rfl⟩ := hq
    refine ⟨p₁ + q₁, p₂ + q₂, ?_⟩
    simp only [map_add (f := _)]
    ring
  | C_mul_T n a =>
    rcases lt_or_ge n 0 with hn | hn
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -1 + -(m : ℤ) := ⟨(-n - 1).toNat, by omega⟩
      refine ⟨0, Polynomial.C a * Polynomial.X ^ m, ?_⟩
      rw [Polynomial.toLaurent_C_mul_X_pow, map_mul, LaurentPolynomial.invert_C,
        LaurentPolynomial.invert_T, map_zero, zero_add, LaurentPolynomial.T_add]
      ring
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, by omega⟩
      refine ⟨Polynomial.C a * Polynomial.X ^ m, 0, ?_⟩
      rw [Polynomial.toLaurent_C_mul_X_pow]
      simp

theorem exists_const_of_mem_span : ∀ (K : Type) [CommRing K] (f g : K) (α β : Polynomial K),
    Polynomial.toLaurent α - LaurentPolynomial.invert (Polynomial.toLaurent β) ∈
      Ideal.span {(LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g : K[T;T⁻¹])} →
    ∃ c : K, α - Polynomial.C c ∈ Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g} ∧
      β - Polynomial.C c ∈ Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f} := by
  intro K _ f g α β hmem
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.1 hmem
  obtain ⟨h₁, h₂, rfl⟩ := exists_split h
  have hT : (LaurentPolynomial.T (-1) * LaurentPolynomial.T 1 : K[T;T⁻¹]) = 1 := by
    rw [← LaurentPolynomial.T_add]
    simp
  have key : Polynomial.toLaurent (α - (Polynomial.C f - Polynomial.X * Polynomial.C g) * h₁) =
      LaurentPolynomial.invert (Polynomial.toLaurent
        (β - (Polynomial.C g - Polynomial.X * Polynomial.C f) * h₂)) := by
    simp only [map_sub, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X,
      LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
    linear_combination (-1 : K[T;T⁻¹]) * hh -
      LaurentPolynomial.invert (Polynomial.toLaurent h₂) * LaurentPolynomial.C g * hT
  obtain ⟨ha, hb⟩ := eq_C_of_toLaurent_eq_invert _ _ key
  refine ⟨(α - (Polynomial.C f - Polynomial.X * Polynomial.C g) * h₁).coeff 0,
    Ideal.mem_span_singleton'.2 ⟨h₁, ?_⟩, Ideal.mem_span_singleton'.2 ⟨h₂, ?_⟩⟩
  · linear_combination (-1 : Polynomial K) * ha
  · linear_combination (-1 : Polynomial K) * hb

end GlobalTheory.CompanionTheory.LaurSplit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOfCompact
noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KernelBasic

theorem finite_of_compact (X : Ctx) {φ : X.G → ℂ} (hφ : HasCompactSupport φ) {U V : Set X.G}
    (hU : IsCompact U) (hV : IsCompact V) :
    {γ : X.Γ | ∃ x ∈ U, ∃ y ∈ V, φ (x⁻¹ * (γ : X.G) * y) ≠ 0}.Finite := by
  have hS : IsCompact (U * tsupport φ * V⁻¹) := (hU.mul hφ.isCompact).mul hV.inv
  refine (X.proper _ hS).subset ?_
  rintro γ ⟨x, hx, y, hy, h⟩
  refine Set.mem_setOf_eq ▸ ?_
  have e : (γ : X.G) = x * (x⁻¹ * (γ : X.G) * y) * y⁻¹ := by group
  rw [e]
  exact Set.mul_mem_mul (Set.mul_mem_mul hx (subset_tsupport _ (Function.mem_support.2 h)))
    (Set.inv_mem_inv.2 hy)

theorem support_finite (X : Ctx) {φ : X.G → ℂ} (hφ : HasCompactSupport φ) (x y : X.G) :
    (Function.support fun γ : X.Γ => φ (x⁻¹ * (γ : X.G) * y)).Finite := by
  refine (finite_of_compact X hφ (isCompact_singleton (x := x))
    (isCompact_singleton (x := y))).subset ?_
  intro γ h
  exact ⟨x, rfl, y, rfl, h⟩

theorem continuous_ker (X : Ctx) {φ : X.G → ℂ} (hφ : Tst φ) :
    Continuous (Function.uncurry (ker X.Γ φ)) := by
  have e : Function.uncurry (ker X.Γ φ) =
      fun p : X.G × X.G => ∑ᶠ γ : X.Γ, φ (p.1⁻¹ * (γ : X.G) * p.2) := by
    funext p
    rfl
  rw [e]
  refine continuous_finsum (fun γ => ?_) ?_
  · exact hφ.1.comp ((continuous_fst.inv.mul continuous_const).mul continuous_snd)
  · rintro ⟨x, y⟩
    obtain ⟨U, hU, hUx⟩ := exists_compact_mem_nhds x
    obtain ⟨V, hV, hVy⟩ := exists_compact_mem_nhds y
    refine ⟨U ×ˢ V, prod_mem_nhds hUx hVy, ?_⟩
    refine (finite_of_compact X hφ.2 hU hV).subset ?_
    rintro γ ⟨⟨a, b⟩, hs, hab⟩
    exact ⟨a, hab.1, b, hab.2, hs⟩

theorem ker_mul_left (X : Ctx) (φ : X.G → ℂ) {γ : X.G} (hγ : γ ∈ X.Γ) (x y : X.G) :
    ker X.Γ φ (γ * x) y = ker X.Γ φ x y := by
  unfold ker
  rw [← finsum_comp_equiv (Equiv.mulLeft (⟨γ, hγ⟩ : X.Γ))]
  refine finsum_congr fun δ => ?_
  congr 1
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul]
  group

theorem ker_mul_right (X : Ctx) (φ : X.G → ℂ) {γ : X.G} (hγ : γ ∈ X.Γ) (x y : X.G) :
    ker X.Γ φ x (γ * y) = ker X.Γ φ x y := by
  unfold ker
  rw [← finsum_comp_equiv (Equiv.mulRight (⟨γ, hγ⟩ : X.Γ)⁻¹)]
  refine finsum_congr fun δ => ?_
  congr 1
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem tst_adj (X : Ctx) {φ : X.G → ℂ} (hφ : Tst φ) : Tst (adj φ) := by
  refine ⟨Complex.continuous_conj.comp (hφ.1.comp continuous_inv), ?_⟩
  have h : HasCompactSupport (φ ∘ (Homeomorph.inv X.G)) :=
    hφ.2.comp_homeomorph (Homeomorph.inv X.G)
  exact h.comp_left (g := starRingEnd ℂ) (map_zero _)

theorem ker_adj (X : Ctx) {φ : X.G → ℂ} (hφ : HasCompactSupport φ) (x y : X.G) :
    ker X.Γ (adj φ) x y = starRingEnd ℂ (ker X.Γ φ y x) := by
  unfold ker
  rw [map_finsum _ (support_finite X hφ y x), ← finsum_comp_equiv (Equiv.inv X.Γ)]
  refine finsum_congr fun δ => ?_
  simp only [adj, Equiv.inv_apply, Subgroup.coe_inv]
  congr 2
  group

theorem enorm_ker_le (X : Ctx) {φ : X.G → ℂ} (hφ : HasCompactSupport φ) (x y : X.G) :
    ‖ker X.Γ φ x y‖ₑ ≤ ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ := by
  unfold ker
  rw [finsum_eq_sum _ (support_finite X hφ x y)]
  exact (enorm_sum_le _ _).trans (ENNReal.sum_le_tsum _)

theorem kerBasic : KerBasic := by
  intro X φ hφ
  exact ⟨support_finite X hφ.2, continuous_ker X hφ,
    fun γ hγ x y => ⟨ker_mul_left X φ hγ x y, ker_mul_right X φ hγ x y⟩,
    tst_adj X hφ, ker_adj X hφ.2, enorm_ker_le X hφ.2⟩

end GlobalTheory.CompanionTheory.KernelBasic

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardCompletionsToFullRank
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardCompletionsToFullRank
open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.CntCols

variable {k : Type} [Field k]

theorem rank_fromCols_eq_iff {n : ℕ} (C D : Matrix (Fin n) (Fin n) k) :
    (Matrix.fromCols C D).rank = n ↔ ∀ y : Fin n → k, y ᵥ* C = 0 → y ᵥ* D = 0 → y = 0 := by
  have h1 : (Matrix.fromCols C D).rank = Module.finrank k (LinearMap.range (Matrix.fromCols C D)ᵀ.mulVecLin) := by
    rw [← Matrix.rank_transpose]; rfl
  have h2 := LinearMap.finrank_range_add_finrank_ker (Matrix.fromCols C D)ᵀ.mulVecLin
  rw [← h1, Module.finrank_fin_fun] at h2
  constructor
  · intro h y hC hD
    have h3 : Module.finrank k (LinearMap.ker (Matrix.fromCols C D)ᵀ.mulVecLin) = 0 := by omega
    have h4 := Submodule.finrank_eq_zero.mp h3
    have h5 : y ∈ LinearMap.ker (Matrix.fromCols C D)ᵀ.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, Matrix.vecMul_fromCols, hC, hD]
      ext i; cases i <;> simp
    rw [h4] at h5
    simpa using h5
  · intro h
    have h3 : LinearMap.ker (Matrix.fromCols C D)ᵀ.mulVecLin = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro y hy
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, Matrix.vecMul_fromCols] at hy
      refine h y ?_ ?_
      · ext i; simpa using congrFun hy (Sum.inl i)
      · ext i; simpa using congrFun hy (Sum.inr i)
    rw [h3] at h2
    simpa using h2

theorem finrank_leftKer {n : ℕ} (D : Matrix (Fin n) (Fin n) k) :
    Module.finrank k (LinearMap.ker Dᵀ.mulVecLin) = n - D.rank := by
  have h1 : D.rank = Module.finrank k (LinearMap.range Dᵀ.mulVecLin) := by
    rw [← Matrix.rank_transpose]; rfl
  have h2 := LinearMap.finrank_range_add_finrank_ker Dᵀ.mulVecLin
  rw [← h1, Module.finrank_fin_fun] at h2
  omega

theorem li_iff {V Z ι : Type} [AddCommGroup V] [Module k V] [AddCommGroup Z] [Module k Z] [Fintype ι]
    (b : Module.Basis ι k Z) (g : Z →ₗ[k] V) :
    LinearIndependent k (fun i => g (b i)) ↔ ∀ y, g y = 0 → y = 0 := by
  constructor
  · intro h y hy
    have h1 := Fintype.linearIndependent_iff.mp h (fun i => b.repr y i) (by
      have := congrArg g (b.sum_repr y)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, hy] at this
      simpa using this)
    rw [← b.sum_repr y]
    simp [h1]
  · intro h
    have : LinearMap.ker g = ⊥ := by
      rw [Submodule.eq_bot_iff]; intro y hy; exact h y hy
    exact b.linearIndependent.map' g this

theorem card_completions : ∀ (k : Type) [Field k] [Fintype k] (n ρ : ℕ) (D : Matrix (Fin n) (Fin n) k), D.rank = ρ →
    Nat.card {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} =
      Fintype.card k ^ (n * ρ) * ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j) := by
  intro k _ _ n ρ D hD
  have hρ : ρ ≤ n := by simpa [hD] using D.rank_le_width
  have hZ : Module.finrank k (LinearMap.ker Dᵀ.mulVecLin) = n - ρ := by rw [finrank_leftKer, hD]
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.ker Dᵀ.mulVecLin)
  have hWf : Module.finrank k W = ρ := by
    have := Submodule.finrank_add_eq_of_isCompl hW
    rw [hZ, Module.finrank_fin_fun] at this
    omega
  let bZ := Module.finBasisOfFinrankEq k _ hZ
  let bW := Module.finBasisOfFinrankEq k _ hWf
  let bV := (bZ.prod bW).map (Submodule.prodEquivOfIsCompl _ W hW)
  let E : Matrix (Fin n) (Fin n) k ≃ (Fin (n - ρ) → Fin n → k) × (Fin ρ → Fin n → k) :=
    ((Matrix.transposeLinearEquiv (Fin n) (Fin n) k k).toEquiv.trans
      (Matrix.toLin' (R := k) (m := Fin n) (n := Fin n)).toEquiv).trans
      ((bV.constr k).symm.toEquiv.trans (Equiv.sumArrowEquivProdArrow _ _ _))
  have hE : ∀ C i, (E C).1 i = (bZ i : Fin n → k) ᵥ* C := by
    intro C i
    simp [E, bV, Equiv.sumArrowEquivProdArrow, Module.Basis.constr, Matrix.mulVec_transpose]
  have hp : ∀ C, (Matrix.fromCols C D).rank = n ↔ LinearIndependent k (E C).1 := by
    intro C
    have h1 : (E C).1 = fun i => (Cᵀ.mulVecLin ∘ₗ (LinearMap.ker Dᵀ.mulVecLin).subtype) (bZ i) := by
      funext i
      rw [hE]
      simp [Matrix.mulVec_transpose]
    rw [h1, li_iff, rank_fromCols_eq_iff]
    constructor
    · intro h y hy
      have h2 : (y : Fin n → k) ᵥ* D = 0 := by
        have := y.2
        rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose] at this
      have h3 : (y : Fin n → k) ᵥ* C = 0 := by simpa [Matrix.mulVec_transpose] using hy
      exact Subtype.ext (h _ h3 h2)
    · intro h y hC hD'
      have hy : y ∈ LinearMap.ker Dᵀ.mulVecLin := by
        rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose]
      have := h ⟨y, hy⟩ (by simpa [Matrix.mulVec_transpose] using hC)
      simpa using congrArg Subtype.val this
  rw [Nat.card_congr ((Equiv.subtypeEquiv (q := fun x => LinearIndependent k x.1) E hp).trans
      (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun s : Fin (n - ρ) → Fin n → k => LinearIndependent k s))), Nat.card_prod,
    card_linearIndependent (K := k) (V := Fin n → k) (by rw [Module.finrank_fin_fun]; omega), Module.finrank_fin_fun,
    Finset.prod_range (fun j => Fintype.card k ^ n - Fintype.card k ^ j), mul_comm]
  congr 1
  simp [Nat.card_fun, pow_mul]

end GlobalTheory.CompanionTheory.Jp.CntCols
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardCompletionsToFullRankStatement
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_completions_to_full_rank : ∀ (k : Type) [Field k] [Fintype k] (n ρ : ℕ) (D : Matrix (Fin n) (Fin n) k), D.rank = ρ →
    Nat.card {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} =
      Fintype.card k ^ (n * ρ) * ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.CntCols.card_completions | exact GlobalTheory.CompanionTheory.Jp.CntCols.card_completions | (intros; apply GlobalTheory.CompanionTheory.Jp.CntCols.card_completions <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionOrthogonalIdempotentSum
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionOrthogonalIdempotentSum
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
open CategoryTheory.Limits

namespace GlobalTheory.CompanionTheory.SecAdd

variable {S : Type} [CommRing S]

theorem away_self_eq_one {e : S} (he : IsIdempotentElem e) :
    algebraMap S (Localization.Away e) e = 1 := by
  have hu : IsUnit (algebraMap S (Localization.Away e) e) := IsLocalization.Away.algebraMap_isUnit e
  have h : algebraMap S (Localization.Away e) e * algebraMap S (Localization.Away e) e
      = algebraMap S (Localization.Away e) e * 1 := by
    rw [← map_mul, he.eq, mul_one]
  exact hu.mul_left_cancel h

theorem away_orth_eq_zero {e x : S} (he : IsIdempotentElem e) (h : e * x = 0) :
    algebraMap S (Localization.Away e) x = 0 := by
  have := congrArg (algebraMap S (Localization.Away e)) h
  rwa [map_mul, away_self_eq_one he, one_mul, map_zero] at this

theorem away_surj {e : S} (he : IsIdempotentElem e) :
    Function.Surjective (algebraMap S (Localization.Away e)) := by
  intro b
  obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj (Submonoid.powers e) b
  obtain ⟨n, hn⟩ := s.2
  refine ⟨x, ?_⟩
  have : algebraMap S (Localization.Away e) (s : S) = 1 := by
    rw [← hn, map_pow, away_self_eq_one he, one_pow]
  simp only [this, mul_one] at hx
  exact hx.symm

theorem away_ker {e x : S} (he : IsIdempotentElem e)
    (h : algebraMap S (Localization.Away e) x = 0) : e * x = 0 := by
  obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers e) _ x).1 h
  rcases n with _ | n
  · simp at hc
    simp [hc]
  · have : e ^ (n + 1) = e := he.pow_succ_eq n
    simpa [this] using hc

theorem isIdempotentElem_add {e e' : S} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (h : e * e' = 0) : IsIdempotentElem (e + e') := by
  have h' : e' * e = 0 := by rw [mul_comm, h]
  unfold IsIdempotentElem
  rw [add_mul, mul_add, mul_add, h, h', he.eq, he'.eq, add_zero, zero_add]

theorem isLocalization_prod {e e' : S} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (h : e * e' = 0) :
    IsLocalization.Away (e + e') (Localization.Away e × Localization.Away e') := by
  have h' : e' * e = 0 := by rw [mul_comm, h]
  have key : ∀ z : S, algebraMap S (Localization.Away e × Localization.Away e') z = 0 ↔
      (e + e') * z = 0 := by
    intro z
    constructor
    · intro hz
      have h1 : algebraMap S (Localization.Away e) z = 0 := congrArg Prod.fst hz
      have h2 : algebraMap S (Localization.Away e') z = 0 := congrArg Prod.snd hz
      rw [add_mul, away_ker he h1, away_ker he' h2, add_zero]
    · intro hz
      have h1 : e * z = 0 := by
        have := congrArg (e * ·) hz
        simp only [mul_zero] at this
        rw [← this, ← mul_assoc, mul_add, he.eq, h, add_zero]
      have h2 : e' * z = 0 := by
        have := congrArg (e' * ·) hz
        simp only [mul_zero] at this
        rw [← this, ← mul_assoc, mul_add, he'.eq, h', zero_add]
      exact Prod.ext (away_orth_eq_zero he h1) (away_orth_eq_zero he' h2)
  refine IsLocalization.away_of_isIdempotentElem_of_mul (isIdempotentElem_add he he' h) ?_ ?_
  · intro x y
    rw [← sub_eq_zero, ← map_sub, key, mul_sub, sub_eq_zero]
  · rintro ⟨b, c⟩
    obtain ⟨x, rfl⟩ := away_surj he b
    obtain ⟨y, rfl⟩ := away_surj he' c
    refine ⟨e * x + e' * y, Prod.ext ?_ ?_⟩
    · change algebraMap S (Localization.Away e) (e * x + e' * y) = _
      have : algebraMap S (Localization.Away e) e' = 0 := away_orth_eq_zero he h
      rw [map_add (f := _), map_mul, map_mul, away_self_eq_one he, this, one_mul, zero_mul, add_zero]
    · change algebraMap S (Localization.Away e') (e * x + e' * y) = _
      have : algebraMap S (Localization.Away e') e = 0 := away_orth_eq_zero he' h'
      rw [map_add (f := _), map_mul, map_mul, away_self_eq_one he', this, one_mul, zero_mul, zero_add]

theorem secOn_add : ∀ {S : Type} [CommRing S] (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of S)) (e e' : S), IsIdempotentElem e → IsIdempotentElem e' →
    e * e' = 0 → SecOn f e → SecOn f e' → SecOn f (e + e') := by
  intro S _ Y f e e' he he' h ⟨s, hs⟩ ⟨s', hs'⟩
  haveI := isLocalization_prod he he' h
  let B := Localization.Away e
  let C := Localization.Away e'
  let A := Localization.Away (e + e')
  let φ : (B × C) ≃ₐ[S] A :=
    IsLocalization.algEquiv (Submonoid.powers (e + e')) (B × C) A
  let t : Spec (CommRingCat.of (B × C)) ⟶ Y := inv (coprodSpec B C) ≫ coprod.desc s s'
  have ht : t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S (B × C))) := by
    rw [← cancel_epi (coprodSpec B C)]
    simp only [t, Category.assoc, IsIso.hom_inv_id_assoc]
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, hs, coprodSpec_inl_assoc, ← Spec.map_comp]
      rfl
    · rw [coprod.inr_desc_assoc, hs', coprodSpec_inr_assoc, ← Spec.map_comp]
      rfl
  refine ⟨Spec.map (CommRingCat.ofHom (φ : B × C →+* A)) ≫ t, ?_⟩
  rw [Category.assoc, ht, ← Spec.map_comp]
  congr 1
  ext x
  exact φ.commutes x

end GlobalTheory.CompanionTheory.SecAdd
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionOrthogonalIdempotentSumStatement
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_orthogonal_idempotent_sum : ∀ {S : Type} [CommRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)) (e e' : S), IsIdempotentElem e → IsIdempotentElem e' → e * e' = 0 → SecOn f e → SecOn f e' → SecOn f (e + e') := by
  first | exact @GlobalTheory.CompanionTheory.SecAdd.secOn_add | exact GlobalTheory.CompanionTheory.SecAdd.secOn_add | (intros; apply GlobalTheory.CompanionTheory.SecAdd.secOn_add <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StagedEstimateHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StagedEstimateHolds
namespace GlobalTheory.CompanionTheory.RgEis

open PositivityTheory.RgEis

variable {G : Type} [Group G] {P Δ Γ : Subgroup G}

def cls (y : Γ) : Cos P Γ := Quotient.mk _ y

theorem cls_eq {a b : Γ} : (cls a : Cos P Γ) = cls b ↔ (b : G) * (a : G)⁻¹ ∈ P := by
  unfold cls
  rw [Quotient.eq]
  show QuotientGroup.rightRel _ a b ↔ _
  rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
  simp

theorem rep_mem (q : Cos P Γ) : rep q ∈ Γ := (Quotient.out q).2

theorem cls_rep (q : Cos P Γ) : cls ⟨rep q, rep_mem q⟩ = q := Quotient.out_eq q

theorem rep_cls (y : Γ) : ∃ p ∈ P, p ∈ Γ ∧ rep (cls y : Cos P Γ) = p * y := by
  have h : (cls y : Cos P Γ) = cls ⟨rep (cls y : Cos P Γ), rep_mem _⟩ := (cls_rep _).symm
  refine ⟨rep (cls y : Cos P Γ) * (y : G)⁻¹, cls_eq.1 h, Γ.mul_mem (rep_mem _) (Γ.inv_mem y.2), by group⟩

noncomputable def glue (hΔ : Δ ≤ Γ) (s : (_ : Cos Δ Γ) × Cos P Δ) : Cos P Γ :=
  cls ⟨rep s.2 * rep s.1, Γ.mul_mem (hΔ (rep_mem _)) (rep_mem _)⟩

theorem glue_injective (hΔ : Δ ≤ Γ) (hP : ∀ γ ∈ Γ, γ ∈ P → γ ∈ Δ) :
    Function.Injective (glue (P := P) hΔ) := by
  rintro ⟨r, q⟩ ⟨r', q'⟩ h
  have h1 : rep q' * rep r' * (rep q * rep r)⁻¹ ∈ P := cls_eq.1 h
  have hΓ : rep q' * rep r' * (rep q * rep r)⁻¹ ∈ Γ :=
    Γ.mul_mem (Γ.mul_mem (hΔ (rep_mem _)) (rep_mem _))
      (Γ.inv_mem (Γ.mul_mem (hΔ (rep_mem _)) (rep_mem _)))
  have h2 := hP _ hΓ h1
  have h3 : rep r' * (rep r)⁻¹ ∈ Δ := by
    have : rep r' * (rep r)⁻¹ = (rep q')⁻¹ * (rep q' * rep r' * (rep q * rep r)⁻¹) * rep q := by
      group
    rw [this]
    exact Δ.mul_mem (Δ.mul_mem (Δ.inv_mem (rep_mem _)) h2) (rep_mem _)
  have hr : r = r' := by
    rw [← cls_rep r, ← cls_rep r']
    exact cls_eq.2 h3
  subst hr
  have h4 : rep q' * (rep q)⁻¹ ∈ P := by
    have : rep q' * (rep q)⁻¹ = rep q' * rep r * (rep q * rep r)⁻¹ := by group
    rw [this]
    exact h1
  have hq : q = q' := by
    rw [← cls_rep q, ← cls_rep q']
    exact cls_eq.2 h4
  subst hq
  rfl

theorem glue_surjective (hΔ : Δ ≤ Γ) (hP : ∀ γ ∈ Γ, γ ∈ P → γ ∈ Δ) :
    Function.Surjective (glue (P := P) hΔ) := by
  intro t
  obtain ⟨y, rfl⟩ : ∃ y : Γ, cls y = t := ⟨_, cls_rep t⟩
  obtain ⟨d, hdΔ, -, hd⟩ := rep_cls (P := Δ) y
  obtain ⟨p, hpP, hpΔ, hp⟩ := rep_cls (P := P) (⟨d⁻¹, Δ.inv_mem hdΔ⟩ : Δ)
  refine ⟨⟨cls y, cls ⟨d⁻¹, Δ.inv_mem hdΔ⟩⟩, ?_⟩
  apply cls_eq.2
  show (y : G) * (rep (cls ⟨d⁻¹, Δ.inv_mem hdΔ⟩ : Cos P Δ) * rep (cls y : Cos Δ Γ))⁻¹ ∈ P
  rw [hp, hd]
  have : (y : G) * (p * d⁻¹ * (d * y))⁻¹ = p⁻¹ := by group
  rw [this]
  exact P.inv_mem hpP

theorem f_rep {X : Type} {f : G → X} (hf : ∀ γ ∈ Γ, γ ∈ P → ∀ x, f (γ * x) = f x) (y : Γ) (g : G) :
    f (rep (cls y : Cos P Γ) * g) = f (y * g) := by
  obtain ⟨p, hpP, hpΓ, hp⟩ := rep_cls (P := P) y
  rw [hp, mul_assoc, hf p hpΓ hpP]

theorem stage : PiLocalization₂ := by
  intro G _ X _ _ P Δ Γ f hΔ hP hf g hs
  have hmem : ∀ (q : Cos P Δ) (x : G), x ∈ Γ → rep q * x ∈ Γ := fun q x hx =>
    Γ.mul_mem (hΔ (rep_mem q)) hx

  have h1 : ∀ x ∈ Γ, Summable fun q : Cos P Δ => ‖f (rep q * (x * g))‖ := by
    intro x hx
    have hinj : Function.Injective fun q : Cos P Δ => (cls ⟨rep q * x, hmem q x hx⟩ : Cos P Γ) := by
      intro q q' h
      have h1 : rep q' * x * (rep q * x)⁻¹ ∈ P := cls_eq.1 h
      have h2 : rep q' * (rep q)⁻¹ ∈ P := by
        have : rep q' * (rep q)⁻¹ = rep q' * x * (rep q * x)⁻¹ := by group
        rw [this]
        exact h1
      rw [← cls_rep q, ← cls_rep q']
      exact cls_eq.2 h2
    refine (hs.comp_injective hinj).congr fun q => ?_
    simp only [Function.comp_apply]
    rw [f_rep hf, mul_assoc]

  let e : ((_ : Cos Δ Γ) × Cos P Δ) ≃ Cos P Γ :=
    Equiv.ofBijective (glue hΔ) ⟨glue_injective hΔ hP, glue_surjective hΔ hP⟩
  let φ : ((_ : Cos Δ Γ) × Cos P Δ) → X := fun s => f (rep s.2 * (rep s.1 * g))
  have hφ : ∀ s, f (rep (e s) * g) = φ s := by
    intro s
    show f (rep (glue hΔ s) * g) = _
    unfold glue
    rw [f_rep hf, mul_assoc]
  have hn : Summable fun s => ‖φ s‖ := by
    refine ((e.summable_iff (f := fun q : Cos P Γ => ‖f (rep q * g)‖)).2 hs).congr fun s => ?_
    simp only [Function.comp_apply]
    rw [hφ]
  have hsig := (summable_sigma_of_nonneg (fun s => norm_nonneg (φ s))).1 hn
  have hφs : Summable φ := hn.of_norm
  refine ⟨h1, hsig.2, ?_⟩
  have hfib : ∀ r, Summable fun q : Cos P Δ => φ ⟨r, q⟩ := fun r => (hsig.1 r).of_norm
  calc ∑' q : Cos P Γ, f (rep q * g) = ∑' s, f (rep (e s) * g) := (e.tsum_eq _).symm
    _ = ∑' s, φ s := tsum_congr hφ
    _ = ∑' r : Cos Δ Γ, ∑' q : Cos P Δ, φ ⟨r, q⟩ := hφs.tsum_sigma' hfib

end GlobalTheory.CompanionTheory.RgEis
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StagedEstimateHoldsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.staged_estimate_holds : PositivityTheory.RgEis.PiLocalization₂ := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.stage | exact GlobalTheory.CompanionTheory.RgEis.stage | (intros; apply GlobalTheory.CompanionTheory.RgEis.stage <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureComplementImageEqZero
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr.SmallUnit

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]

theorem infinite_factor_points {f : A} (hf : NonDiscreteAt f) {W : Set A} (hW : W ∈ 𝓝 (0 : A)) :
    {x | x ∈ W ∧ f * x = x}.Infinite := by
  intro hfin
  have hfin' : ({x | x ∈ W ∧ f * x = x} \ {0}).Finite := hfin.subset Set.diff_subset
  have hV : ({x | x ∈ W ∧ f * x = x} \ {0})ᶜ ∈ 𝓝 (0 : A) :=
    hfin'.isClosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨x, hx, hx0, hfx⟩ := hf _ (inter_mem hW hV)
  exact hx.2 ⟨⟨hx.1, hfx⟩, hx0⟩

theorem measure_complement_image_eq_zero [MeasurableSpace A] [BorelSpace A]
    (h : Measure A) [h.IsAddHaarMeasure] {f : A} (hid : f * f = f) (hf : NonDiscreteAt f)
    {W : Set A} (hWc : IsCompact W) (hW : W ∈ 𝓝 (0 : A)) :
    h ((fun w => (1 - f) * w) '' W) = 0 := by
  set Q : Set A := (fun w => (1 - f) * w) '' W with hQ
  have hQc : IsCompact Q := hWc.image (by fun_prop)
  by_contra hne
  set K : Set A := (fun p : A × A => p.1 + p.2) '' (W ×ˢ Q) with hK
  have hKc : IsCompact K := (hWc.prod hQc).image (by fun_prop)
  have hKfin : h K ≠ ∞ := hKc.measure_lt_top.ne
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt hne hKfin
  obtain ⟨T, hTS, hTc⟩ := (infinite_factor_points hf hW).exists_subset_card_eq n
  have hdisj : (T : Set A).PairwiseDisjoint (fun p => (fun q => p + q) '' Q) := by
    intro p hp p' hp' hpp
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩ ⟨_, ⟨w', -, rfl⟩, hEq⟩
    apply hpp
    have hfp : f * p = p := (hTS hp).2
    have hfp' : f * p' = p' := (hTS hp').2
    have hz : f * (1 - f) = 0 := by rw [mul_sub, mul_one, hid, sub_self]
    have := congrArg (fun t => f * t) hEq
    simp only [mul_add, ← mul_assoc, hz, zero_mul, add_zero, hfp, hfp'] at this
    exact this.symm
  have hmeas : ∀ p ∈ T, MeasurableSet ((fun q => p + q) '' Q) := fun p _ =>
    (hQc.image (by fun_prop)).isClosed.measurableSet
  have hsum := measure_biUnion_finset (μ := h) hdisj hmeas
  have each : ∀ p, h ((fun q => p + q) '' Q) = h Q := fun p => by
    rw [Set.image_add_left]
    exact measure_preimage_add h (-p) Q
  have hle : h (⋃ p ∈ T, (fun q => p + q) '' Q) ≤ h K := by
    refine measure_mono (Set.iUnion₂_subset fun p hp => ?_)
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨(p, q), ⟨(hTS hp).1, hq⟩, rfl⟩
  rw [hsum, Finset.sum_congr rfl (fun p _ => each p), Finset.sum_const, hTc, nsmul_eq_mul] at hle
  exact absurd hle (not_le.2 hn)

theorem exists_nhds_add_mul_subset {Q W O : Set A} (hQ : IsCompact Q) (hW : IsCompact W)
    (hO : IsOpen O) (hQO : Q ⊆ O) :
    ∃ N ∈ 𝓝 (0 : A), ∀ x ∈ N, ∀ q ∈ Q, ∀ w ∈ W, q + x * w ∈ O := by
  have hn : IsOpen ((fun p : A × A × A => p.2.1 + p.1 * p.2.2) ⁻¹' O) :=
    hO.preimage (by fun_prop)
  obtain ⟨u, v, hu, -, h0u, hQWv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := (0 : A)))
    (hQ.prod hW) hn (by
      rintro ⟨x, q, w⟩ ⟨hx, hq, hw⟩
      have hx0 : x = 0 := hx
      simpa [hx0] using hQO hq)
  exact ⟨u, hu.mem_nhds (h0u rfl), fun x hx q hq w hw => huv (Set.mk_mem_prod hx (show (q, w) ∈ v from hQWv ⟨hq, hw⟩))⟩

end GlobalTheory.CompanionTheory.NullFr.SmallUnit

namespace GlobalTheory.CompanionTheory.NullFr


open SmallUnit in
theorem exists_unit_small_module {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A]
    [BorelSpace A] (md : Aˣ →* ℝ≥0) (hmd : IsHaarMod md) (f : A) (hfi : IsFieldIdem f)
    (hnd : NonDiscreteAt f) (ε : ℝ≥0) (hε : 0 < ε) (V : Set A) (hV : V ∈ 𝓝 (0 : A)) :
    ∃ u : Aˣ, (1 - f) * (u : A) = 1 - f ∧ f * (u : A) ∈ V ∧ md u < ε := by
  obtain ⟨W, hWc, hW⟩ := exists_compact_mem_nhds (0 : A)
  let h : Measure A := Measure.addHaar
  have hWpos : 0 < h W := Measure.measure_pos_of_mem_nhds h hW
  have hWfin : h W ≠ ∞ := hWc.measure_lt_top.ne
  set Q : Set A := (fun w => (1 - f) * w) '' W with hQdef
  have hQc : IsCompact Q := hWc.image (by fun_prop)
  have hQ0 : h Q = 0 := measure_complement_image_eq_zero h hfi.idem hnd hWc hW
  have hεW : h Q < (ε : ℝ≥0∞) * h W := by
    rw [hQ0]
    exact ENNReal.mul_pos (by exact_mod_cast hε.ne') hWpos.ne' |>.bot_lt
  obtain ⟨O, hQO, hOo, hOlt⟩ := Q.exists_isOpen_lt_of_lt _ hεW
  obtain ⟨N, hN, hNO⟩ := exists_nhds_add_mul_subset hQc hWc hOo hQO
  obtain ⟨x, ⟨hxN, hxV⟩, hx0, hfx⟩ := hnd _ (inter_mem hN hV)
  obtain ⟨y, hy⟩ := hfi.inv x (by rwa [hfx])
  rw [hfx] at hy
  have hz : f * (1 - f) = 0 := by rw [mul_sub, mul_one, hfi.idem, sub_self]
  have hzz : (1 - f) * (1 - f) = 1 - f := by
    rw [sub_mul, one_mul, hz, sub_zero]
  have hxz : (1 - f) * x = 0 := by rw [← hfx, ← mul_assoc, mul_comm (1 - f), hz, zero_mul]
  have huv : (1 - f + x) * (1 - f + f * y) = 1 := by
    have e : (1 - f + x) * (1 - f + f * y) =
        (1 - f) * (1 - f) + (f * (1 - f)) * y + (1 - f) * x + (f * x) * y := by ring
    rw [e, hzz, hz, hxz, hfx, hy]
    ring
  let u : Aˣ := ⟨1 - f + x, 1 - f + f * y, huv, by rw [mul_comm]; exact huv⟩
  have hu : (u : A) = 1 - f + x := rfl
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [hu, mul_add, hzz, hxz, add_zero]
  · rw [hu, mul_add, hz, zero_add, hfx]
    exact hxV
  · have hmap := hmd h inferInstance u⁻¹
    have hWm : MeasurableSet W := hWc.isClosed.measurableSet
    have hg : Measurable (fun z : A => ((u⁻¹ : Aˣ) : A) * z) := (by fun_prop : Continuous _).measurable
    have hpre : h ((fun z : A => ((u⁻¹ : Aˣ) : A) * z) ⁻¹' W) = (md u : ℝ≥0∞) * h W := by
      rw [← Measure.map_apply hg hWm, hmap, Measure.smul_apply, smul_eq_mul]
      congr 1
      have hm : md u⁻¹ * md u = 1 := by rw [← map_mul]; simp
      have : (md u⁻¹ : ℝ≥0∞) * (md u : ℝ≥0∞) = 1 := by exact_mod_cast hm
      exact (ENNReal.eq_inv_of_mul_eq_one_left (by rwa [mul_comm])).symm
    have hsub : (fun z : A => ((u⁻¹ : Aˣ) : A) * z) ⁻¹' W ⊆ O := by
      intro z hz'
      have hzw : ((u⁻¹ : Aˣ) : A) * z ∈ W := hz'
      have hzeq : z = (1 - f) * (((u⁻¹ : Aˣ) : A) * z) + x * (((u⁻¹ : Aˣ) : A) * z) := by
        rw [← add_mul, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
      rw [hzeq]
      exact hNO x hxN _ ⟨_, hzw, rfl⟩ _ hzw
    have hlt : (md u : ℝ≥0∞) * h W < (ε : ℝ≥0∞) * h W :=
      lt_of_le_of_lt (hpre ▸ measure_mono hsub) hOlt
    have : (md u : ℝ≥0∞) < ε := lt_of_mul_lt_mul_right' hlt
    exact_mod_cast this

end GlobalTheory.CompanionTheory.NullFr
end
