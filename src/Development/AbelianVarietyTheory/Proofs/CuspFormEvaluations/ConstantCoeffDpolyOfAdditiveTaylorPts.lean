module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasSubstEv
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Transference

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts
open Filter Topology MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory

section Comp

variable {σ τ W : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

omit [DecidableEq σ] in
theorem hasSubst_taylorDir (u : τ → W) {φ : W → σ → ℂ} (h0 : φ 0 = 0) :
    HasSubst fun i => taylorDir u fun z => φ z i := by
  refine hasSubst_of_constantCoeff_zero fun i => ?_
  simp [h0]

private theorem fderiv_comp_apply_eq_sum_pi_single {φ : W → σ → ℂ} {f : (σ → ℂ) → ℂ} {z : W}
    (hφ : DifferentiableAt ℂ φ z) (hf : DifferentiableAt ℂ f (φ z)) (v : W) :
    fderiv ℂ (f ∘ φ) z v =
      ∑ i, fderiv ℂ f (φ z) (Pi.single i 1) * fderiv ℂ (fun y => φ y i) z v := by
  have hi : ∀ i, fderiv ℂ (fun y => φ y i) z v = fderiv ℂ φ z v i := fun i => by
    rw [(hasFDerivAt_pi'.1 hφ.hasFDerivAt i).fderiv]
    rfl
  simp_rw [hi]
  rw [fderiv_comp z hf hφ, ContinuousLinearMap.comp_apply]
  conv_lhs => rw [← Finset.univ_sum_single (fderiv ℂ φ z v)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (Pi.single i (fderiv ℂ φ z v i) : σ → ℂ) = fderiv ℂ φ z v i • Pi.single i 1 by
    ext k; by_cases h : k = i <;> simp [h], map_smul, smul_eq_mul, mul_comm]

private theorem taylorDir_comp_eq_subst_taylor_of_analyticAt (u : τ → W) {φ : W → σ → ℂ} (hφ : AnalyticAt ℂ φ 0)
    (h0 : φ 0 = 0) :
    ∀ D ∈ {D : MvPowerSeries τ ℂ | ∃ f : (σ → ℂ) → ℂ, AnalyticAt ℂ f 0 ∧
      D = taylorDir u (f ∘ φ) - subst (fun i => taylorDir u fun z => φ z i) (taylor f)}, D = 0 := by
  have hs : HasSubst fun i => taylorDir u fun z => φ z i := hasSubst_taylorDir u h0
  have ha0 : ∀ i, constantCoeff (taylorDir u fun z => φ z i) = 0 := fun i => by simp [h0]
  have hT : Tendsto φ (𝓝 0) (𝓝 0) := by simpa [h0] using hφ.continuousAt.tendsto
  have hφi : ∀ i, AnalyticAt ℂ (fun z => φ z i) 0 := fun i =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt (φ 0)).comp hφ
  apply mvPowerSeries_eq_zero_of_pderiv_mem_span
  · rintro _ ⟨f, hf, rfl⟩
    rw [map_sub, FormalCalc.constantCoeff_subst_of_zero hs ha0]
    simp [h0]
  · rintro _ ⟨f, hf, rfl⟩ j
    have hfφ : AnalyticAt ℂ (f ∘ φ) 0 := hf.comp_of_eq hφ h0
    have hg : ∀ i, AnalyticAt ℂ (fun y => fderiv ℂ f y (Pi.single i 1)) 0 := fun i =>
      analyticAt_fderiv_apply hf _
    have hev : (fun z => fderiv ℂ (f ∘ φ) z (u j)) =ᶠ[𝓝 0] fun z => ∑ i,
        fderiv ℂ f (φ z) (Pi.single i 1) * fderiv ℂ (fun y => φ y i) z (u j) := by
      filter_upwards [hφ.eventually_analyticAt, hT.eventually hf.eventually_analyticAt] with z hz1 hz2
      exact fderiv_comp_apply_eq_sum_pi_single hz1.differentiableAt hz2.differentiableAt (u j)
    have hsum := taylorDir_sum u Finset.univ (F := fun i z =>
        fderiv ℂ f (φ z) (Pi.single i 1) * fderiv ℂ (fun y => φ y i) z (u j))
      (fun i _ => ((hg i).comp_of_eq hφ h0).mul (analyticAt_fderiv_apply (hφi i) _))
    beta_reduce at hsum
    have key : pderiv (R := ℂ) j (taylorDir u (f ∘ φ) -
        subst (fun i => taylorDir u fun z => φ z i) (taylor f)) =
        ∑ i, (taylorDir u ((fun y => fderiv ℂ f y (Pi.single i 1)) ∘ φ) -
          subst (fun i => taylorDir u fun z => φ z i) (taylor fun y => fderiv ℂ f y (Pi.single i 1))) *
            pderiv (R := ℂ) j (taylorDir u fun z => φ z i) := by
      rw [map_sub, FormalCalc.pderiv_subst hs, ← taylorDir_fderiv u hfφ j, taylorDir_congr u hev,
        hsum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sub_mul, ← taylorDir_fderiv u (hφi i) j, taylor_fderiv hf i]
      congr 1
      exact taylorDir_mul u ((hg i).comp_of_eq hφ h0) (analyticAt_fderiv_apply (hφi i) _)
    rw [key]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _
      (Ideal.subset_span ⟨_, hg i, rfl⟩)

theorem taylorDir_comp (u : τ → W) {φ : W → σ → ℂ} (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0)
    {f : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) :
    taylorDir u (f ∘ φ) = subst (fun i => taylorDir u fun z => φ z i) (taylor f) := by
  have hs : HasSubst fun i => taylorDir u fun z => φ z i := hasSubst_taylorDir u h0
  have hD := taylorDir_comp_eq_subst_taylor_of_analyticAt u hφ h0 (taylorDir u (f ∘ φ) -
    subst (fun i => taylorDir u fun z => φ z i) (taylor f)) ⟨f, hf, rfl⟩
  exact sub_eq_zero.1 hD

end Comp

section Points

variable {n d : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

variable (e : Fin 1 × Fin d → W) {f : W → ℂ}

variable {ι : Type} [Fintype ι]

end Points

section Curried

variable {m n d d' : ℕ}

section Algebra

variable {F G : (Fin n → Fin d → ℂ) → ℂ}

end Algebra

end Curried

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardExponentsAndChooseRatioBoundsPair
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardExponentsAndChooseRatioBoundsPair
namespace GlobalTheory

theorem card_exponents_sum_lt_sub (D T : ℕ) (hT : D < T) :
    Nat.card {α : Fin D → ℕ // ∑ i, α i < T - D} = (T - 1).choose D := by
  have e : {α : Fin D →₀ ℕ // α.degree ≤ T - D - 1} ≃ {α : Fin D → ℕ // ∑ i, α i < T - D} :=
    Finsupp.equivFunOnFinite.subtypeEquiv fun α => by
      rw [Finsupp.degree_eq_sum]
      simp only [Finsupp.equivFunOnFinite_apply]
      omega
  rw [← Nat.card_congr e, ReciprocityTheory.MultiplicativeHeights.card_degree_le, show T - D - 1 + D = T - 1 by omega]

theorem le_of_add_mul_choose_pred_le (D T δ d ρ : ℕ) (hD : 2 ≤ D) (hT : 11 * D ^ 2 ≤ T)
    (hd : d ≤ δ * (T + 2 * D + 6).choose D) (hρ : ρ + δ * (T - 1).choose D ≤ d) :
    (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T := by
  have hT' : D * (2 * D + 7) ≤ T := by nlinarith
  have hTpos : (0 : ℝ) < T := by
    have : 0 < T := by nlinarith
    exact_mod_cast this
  have key := ReciprocityTheory.ChartRestriction.G.T0.sub_mul_choose_le_mul_choose T D hT' D le_rfl
  have hd' : (d : ℝ) ≤ δ * (((T + 2 * D + 6).choose D : ℕ) : ℝ) := by exact_mod_cast hd
  have hρ' : (ρ : ℝ) + δ * (((T - 1).choose D : ℕ) : ℝ) ≤ d := by exact_mod_cast hρ
  have hTD : (0 : ℝ) ≤ (T : ℝ) - D * (2 * D + 7) := by
    have : ((D : ℝ) * (2 * D + 7)) ≤ T := by exact_mod_cast hT'
    linarith
  have hδ : (0 : ℝ) ≤ δ := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have s1 := mul_le_mul_of_nonneg_left key hδ
  have s2 := mul_le_mul_of_nonneg_left hd' hTD
  have s3 := mul_le_mul_of_nonneg_left hρ' hTpos.le
  have s4 : (D : ℝ) * (2 * D + 7) * d ≤ 22 * (D : ℝ) ^ 2 * d :=
    mul_le_mul_of_nonneg_right (by nlinarith) hd0
  rw [le_div_iff₀ hTpos]
  nlinarith

theorem card_exponents_and_choose_ratio_bounds : ∀ (D T : ℕ), (0 < D → D < T → Nat.card {α : Fin D → ℕ // ∑ i, α i < T - D} = (T - 1).choose D) ∧ ∀ (δ d ρ : ℕ), 2 ≤ D → 11 * D ^ 2 ≤ T → d ≤ δ * (T + 2 * D + 6).choose D → (ρ + δ * (T - 1).choose D ≤ d → (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T) ∧ (ρ + δ * (T + D).choose D ≤ d → (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T) := by
  intro D T
  refine ⟨fun _ h => card_exponents_sum_lt_sub D T h, fun δ d ρ hD hT hd =>
    ⟨le_of_add_mul_choose_pred_le D T δ d ρ hD hT hd, fun h => ?_⟩⟩
  refine le_of_add_mul_choose_pred_le D T δ d ρ hD hT hd (le_trans ?_ h)
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.choose_le_choose D (by omega))) _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardExponentsAndChooseRatioBoundsPairStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_exponents_and_choose_ratio_bounds_pair : ∀ (D T : ℕ), (0 < D → D < T → Nat.card {α : Fin D → ℕ // ∑ i, α i < T - D} = (T - 1).choose D) ∧ ∀ (δ d ρ : ℕ), 2 ≤ D → 11 * D ^ 2 ≤ T → d ≤ δ * (T + 2 * D + 6).choose D → (ρ + δ * (T - 1).choose D ≤ d → (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T) ∧ (ρ + δ * (T + D).choose D ≤ d → (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T) := by
  first | exact @GlobalTheory.card_exponents_and_choose_ratio_bounds | exact GlobalTheory.card_exponents_and_choose_ratio_bounds | (intros; apply GlobalTheory.card_exponents_and_choose_ratio_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortIndependentIntegers
open NumberField Module Submodule
open scoped nonZeroDivisors

namespace GlobalTheory

namespace ShortIntegers

section Pairing

variable {V : Type} [AddCommGroup V] [Module ℚ V]

end Pairing

variable {K : Type} [Field K] [NumberField K]

noncomputable def realCoords {M : ℕ} (e : Fin M ≃ (K →+* ℂ)) (ε : ℝ) :
    K →ₗ[ℚ] EuclideanSpace ℝ (Fin M) where
  toFun x := WithLp.toLp 2 fun i => (e i x).re + ε * (e i x).im
  map_add' x y := by
    ext i
    simp
    ring
  map_smul' c x := by
    ext i
    simp [Rat.smul_def]
    ring

end ShortIntegers

private lemma sum_embeddings_eq_zero_of_conjugate_neg {K : Type} [Field K] [NumberField K] (f : (K →+* ℂ) → ℝ)
    (hf : ∀ σ, f (NumberField.ComplexEmbedding.conjugate σ) = - f σ) : ∑ σ, f σ = 0 := by
  have h := Equiv.sum_comp (NumberField.ComplexEmbedding.involutive_conjugate K).toPerm f
  simp only [Function.Involutive.coe_toPerm, hf, Finset.sum_neg_distrib] at h
  linarith

private lemma inner_realCoords_one_neg_one_eq_trace {K : Type} [Field K] [NumberField K] {M : ℕ}
    (e : Fin M ≃ (K →+* ℂ)) (x y : K) :
    inner ℝ (_root_.GlobalTheory.ShortIntegers.realCoords e 1 x) (_root_.GlobalTheory.ShortIntegers.realCoords e (-1) y)
      = ((Algebra.trace ℚ K (x * y) : ℚ) : ℝ) := by
  have ht := congrArg Complex.re (_root_.GlobalTheory.trace_eq_sum_complexEmbeddings (x * y))
  simp [PiLp.inner_apply, _root_.GlobalTheory.ShortIntegers.realCoords]
  simp at ht
  rw [ht, Equiv.sum_comp e (fun σ => ((σ y).re + -(σ y).im) * ((σ x).re + (σ x).im)),
    ← Finset.sum_sub_distrib]
  have h0 := sum_embeddings_eq_zero_of_conjugate_neg (K := K) (fun σ => (σ x).im * (σ y).re - (σ x).re * (σ y).im)
    (by intro σ; simp [NumberField.ComplexEmbedding.conjugate_coe_eq]; ring)
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← h0]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

private lemma norm_sq_realCoords_eq_sum_norm_sq {K : Type} [Field K] [NumberField K] {M : ℕ}
    (e : Fin M ≃ (K →+* ℂ)) {ε : ℝ} (hε : ε ^ 2 = 1) (x : K) :
    ‖_root_.GlobalTheory.ShortIntegers.realCoords e ε x‖ ^ 2 = ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [_root_.GlobalTheory.ShortIntegers.realCoords, LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs,
    sq_abs]
  rw [Equiv.sum_comp e (fun σ => ((σ x).re + ε * (σ x).im) ^ 2)]
  have h0 := sum_embeddings_eq_zero_of_conjugate_neg (K := K) (fun σ => 2 * ε * (σ x).re * (σ x).im)
    (by intro σ; simp [NumberField.ComplexEmbedding.conjugate_coe_eq])
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← h0]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  linear_combination (σ x).im ^ 2 * hε

theorem _root_.GlobalTheory.exists_short_independent_integers (K : Type) [Field K] [NumberField K] :
    ∃ ω : Fin (Module.finrank ℚ K) → 𝓞 K, LinearIndependent ℚ (fun k => (ω k : K)) ∧
      ∀ (s : K →+* ℂ) k, ‖s (ω k : K)‖ ≤ (Module.finrank ℚ K : ℝ) ^ 3 *
        |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  set n := Module.finrank ℚ K with hn
  let e : Fin n ≃ (K →+* ℂ) := (Fintype.equivFinOfCardEq (NumberField.Embeddings.card K ℂ)).symm
  let φ := _root_.GlobalTheory.ShortIntegers.realCoords e 1
  let ψ := _root_.GlobalTheory.ShortIntegers.realCoords e (-1)
  have hpair : ∀ x y : K, inner ℝ (φ x) (ψ y) = ((Algebra.trace ℚ K (x * y) : ℚ) : ℝ) :=
    inner_realCoords_one_neg_one_eq_trace e
  let eι : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin n :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis (NumberField.integralBasis K)).symm
  let α : Module.Basis (Fin n) ℚ K := (NumberField.integralBasis K).reindex eι
  let β := (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) α
  have hαβ : ∀ i j, Algebra.trace ℚ K (α i * β j) = if i = j then 1 else 0 := by
    intro i j
    rw [mul_comm, ← Algebra.traceForm_apply, LinearMap.BilinForm.apply_dualBasis_left]
  have hli : LinearIndependent ℝ (fun j => ψ (β j)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h := congrArg (fun v => inner ℝ (φ (α i)) v) hc
    simp only [inner_sum, inner_smul_right, hpair, hαβ, inner_zero_right] at h
    simpa [apply_ite (Rat.cast : ℚ → ℝ), mul_ite] using h
  have hliφ : LinearIndependent ℝ (fun j => φ (α j)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h := congrArg (fun v => inner ℝ v (ψ (β i))) hc
    simp only [sum_inner, inner_smul_left, hpair, hαβ, inner_zero_left] at h
    simpa [apply_ite (Rat.cast : ℚ → ℝ), mul_ite] using h
  haveI : NeZero n := ⟨(Module.finrank_pos (R := ℚ) (M := K)).ne'⟩
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by simp
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  let bφ := basisOfLinearIndependentOfCardEqFinrank hliφ hcard
  have hα_int : ∀ j, α j = algebraMap (𝓞 K) K (RingOfIntegers.basis K (eι.symm j)) := by
    intro j
    simp [α, NumberField.integralBasis_apply]
  have hdual : ∀ c : Fin n → ℤ,
      (∑ i, (c i : ℚ) • β i) ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K) := by
    intro c
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨a', rfl⟩ := Submodule.mem_one.mp ha
    have hspan : algebraMap (𝓞 K) K a' ∈ Submodule.span ℤ (Set.range α) := by
      rw [show Set.range α = Set.range (NumberField.integralBasis K) from
        Module.Basis.range_reindex _ _]
      exact (NumberField.mem_span_integralBasis K).mpr ⟨a', rfl⟩
    refine Submodule.span_induction (p := fun x _ =>
      (Algebra.traceForm ℚ K) (∑ i, (c i : ℚ) • β i) x ∈ (algebraMap ℤ ℚ).range)
      ?_ ?_ ?_ ?_ hspan
    · rintro _ ⟨k, rfl⟩
      refine ⟨c k, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply]
      simp [Algebra.traceForm_apply, mul_comm (β _) (α k), hαβ]
    · simp
    · intro x y _ _ hx hy
      rw [map_add (f := _)]
      exact add_mem hx hy
    · intro m x _ hx
      rw [map_zsmul]
      exact zsmul_mem hx m
  set D : ℝ := |((NumberField.discr K : ℤ) : ℝ)| with hDdef
  have hD : 0 < D := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  set lam : ℝ := D ^ (-(1 / (n : ℝ))) with hlam
  have hlam0 : 0 < lam := Real.rpow_pos_of_pos hD _
  have hmin : ∀ x ∈ Submodule.span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    have hxz : ∑ i, c i • b i = ψ (∑ i, (c i : ℚ) • β i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smul, Int.cast_smul_eq_zsmul, coe_basisOfLinearIndependentOfCardEqFinrank]
    rw [hxz] at hx0 ⊢
    have hz0 : (∑ i, (c i : ℚ) • β i) ≠ 0 := by
      rintro h
      apply hx0
      rw [h, map_zero]
    have hle := _root_.GlobalTheory.finrank_mul_discr_rpow_le_sum_sq_of_mem_traceDual (hdual c) hz0
    rw [← norm_sq_realCoords_eq_sum_norm_sq e (ε := -1) (by norm_num)] at hle
    have hlam2 : lam ^ 2 ≤ (n : ℝ) * D ^ (-2 / (n : ℝ)) := by
      rw [hlam, ← Real.rpow_natCast, ← Real.rpow_mul hD.le]
      have : -(1 / (n : ℝ)) * ((2 : ℕ) : ℝ) = -2 / (n : ℝ) := by push_cast; ring
      rw [this]
      exact le_mul_of_one_le_left (Real.rpow_nonneg hD.le _) hn1
    exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) (hlam2.trans hle)
  obtain ⟨y, hyli, hyint, hynorm⟩ := _root_.ReciprocityTheory.ChartRestriction.G.T0.transference_dual b lam hlam0 hmin
  choose m hm using hyint
  let ω : Fin n → 𝓞 K := fun i => ∑ j, m i j • RingOfIntegers.basis K (eι.symm j)
  have hω : ∀ i, ((ω i : 𝓞 K) : K) = ∑ j, (m i j : ℚ) • α j := by
    intro i
    simp [ω, hα_int, Int.cast_smul_eq_zsmul]
  have hy : ∀ i, y i = φ (ω i) := by
    intro i
    refine InnerProductSpace.ext_inner_right_basis b fun j => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hm, coe_basisOfLinearIndependentOfCardEqFinrank, hpair, hω, Finset.sum_mul, map_sum]
    simp [smul_mul_assoc, hαβ]
  refine ⟨ω, ?_, ?_⟩
  · have h := hyli.restrict_scalars' ℚ
    rw [show y = fun k => φ (ω k) from funext hy] at h
    exact LinearIndependent.of_comp φ h
  · intro s k
    have hsq : ‖s (ω k : K)‖ ^ 2 ≤ ‖y k‖ ^ 2 := by
      rw [hy, norm_sq_realCoords_eq_sum_norm_sq e (ε := 1) (by norm_num)]
      exact Finset.single_le_sum (f := fun σ : K →+* ℂ => ‖σ (ω k : K)‖ ^ 2)
        (fun σ _ => sq_nonneg _) (Finset.mem_univ s)
    have h1 : ‖s (ω k : K)‖ ≤ ‖y k‖ :=
      le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hsq
    have h2 : (n : ℝ) ^ 2 / lam = (n : ℝ) ^ 2 * D ^ (1 / (n : ℝ)) := by
      rw [hlam, Real.rpow_neg hD.le, div_inv_eq_mul]
    calc ‖s (ω k : K)‖ ≤ (n : ℝ) ^ 2 / lam := h1.trans (hynorm k)
      _ = (n : ℝ) ^ 2 * D ^ (1 / (n : ℝ)) := h2
      _ ≤ (n : ℝ) ^ 3 * D ^ (1 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hn1 (by norm_num))
          (Real.rpow_nonneg hD.le _)

end GlobalTheory
end
