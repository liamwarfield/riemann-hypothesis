module

public import Mathlib

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
namespace ReciprocityTheory.ChartRestriction.G.I2.Ext

open scoped Matrix

def PackingCount : Prop :=
  ∀ (n : ℕ) (P : Finset (EuclideanSpace ℝ (Fin n))) (δ R : ℝ), 0 < δ → δ ≤ R →
    (∀ x ∈ P, ‖x‖ ≤ R) → (∀ x ∈ P, ∀ y ∈ P, x ≠ y → δ ≤ dist x y) →
    (P.card : ℝ) ≤ (3 * R / δ) ^ n

def GaussianTailBound : Prop :=
  ∀ (ι : Type) (h : ι → ℝ) (g : ℕ) (R0 : ℝ), 0 < R0 → 16 * (2 * (g : ℝ) + 1) ≤ R0 ^ 2 →
    (∀ i, R0 ≤ h i) →
    (∀ R : ℝ, R0 ≤ R → ∀ S : Finset ι, (∀ i ∈ S, h i ≤ R) → (S.card : ℝ) ≤ (3 * R / R0) ^ (2 * g)) →
      Summable (fun i => Real.exp (-(h i) ^ 2 / 16)) ∧
        ∑' i, Real.exp (-(h i) ^ 2 / 16) ≤ 2 * 9 ^ g * Real.exp (-R0 ^ 2 / 16)

def BallVolume : Prop :=
  ∀ (D : ℕ) (rr : ℝ), 0 < rr →
    MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * D))) rr) =
      ENNReal.ofReal (Real.pi ^ D * rr ^ (2 * D) / (D.factorial : ℝ))

def GHadamard : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ),
    |M.det| ≤ ∏ j, Real.sqrt (∑ i, M i j ^ 2)

def NearestPlane : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (n : ℕ) (v : Fin n → V),
    LinearIndependent ℝ v → ∀ x ∈ Submodule.span ℝ (Set.range v),
      ∃ c : Fin n → ℤ, ‖x - ∑ i, (c i : ℝ) • v i‖ ^ 2 ≤ (1 / 4) * ∑ i, ‖v i‖ ^ 2

def CauchyBinetMax : Prop :=
  ∀ (i N r : ℕ) (M : Matrix (Fin i) (Fin N) ℂ), M * Mᴴ = 1 → N ≤ r →
    ∃ s : Fin i → Fin N, StrictMono s ∧ (2 : ℝ) ^ (-(r : ℝ) / 2) ≤ ‖(M.submatrix id s).det‖

def DetPerturbation : Prop :=
  ∀ (𝕜 : Type) [NormedField 𝕜] (i : ℕ) (κ : Type) [Fintype κ] (w : κ → Fin i → 𝕜)
    (σ₀ : Fin i → κ) (ε : Fin i → κ → 𝕜) (Δmax : ℝ),
    (∀ σ : Fin i → κ, ‖(Matrix.of fun a j => w (σ j) a).det‖ ≤ Δmax) →
    ‖(Matrix.of fun a j => (w (σ₀ j) + ∑ k, ε j k • w k) a).det -
        (Matrix.of fun a j => w (σ₀ j) a).det‖ ≤
      ((∏ j, (1 + ∑ k, ‖ε j k‖)) - 1) * Δmax

def DetPerturbNumeric : Prop :=
  ∀ ρ : ℕ, 1 ≤ ρ → (1 + (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10) ^ ρ - 1 ≤ 1 / 2

def DetProductRest : Prop :=
  ∀ (i c : ℕ) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
    ((2 : ℝ) ^ c + ε) ^ i - (2 : ℝ) ^ (c * i) ≤ (i : ℝ) * ε * ((2 : ℝ) ^ c + 1) ^ i

def All : Prop :=
  PackingCount ∧ GaussianTailBound ∧ BallVolume ∧ GHadamard ∧ NearestPlane ∧ CauchyBinetMax ∧
    DetPerturbation ∧ DetPerturbNumeric ∧ DetProductRest

end ReciprocityTheory.ChartRestriction.G.I2.Ext
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.CubeIcoMeas
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory

noncomputable section

def cubeIco (κ : Type) : Set (κ → ℝ) := {x | ∀ i, x i ∈ Set.Ico (0 : ℝ) 1}

theorem cubeIco_eq (κ : Type) : cubeIco κ = Set.univ.pi fun _ => Set.Ico (0 : ℝ) 1 := by
  ext x
  simp [cubeIco, Set.mem_pi]

theorem cubeIco_meas (κ : Type) [Finite κ] : MeasurableSet (cubeIco κ) := by
  rw [cubeIco_eq]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem vol_cubeIco (κ : Type) [Fintype κ] : volume (cubeIco κ) = 1 := by
  rw [cubeIco_eq, Real.volume_pi_Ico]
  simp

theorem cube_ae_eq (κ : Type) [Fintype κ] :
    cubeIco κ =ᵐ[volume] {x : κ → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} := by
  have h2 : {x : κ → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} = Set.univ.pi fun _ => Set.Ioc (0 : ℝ) 1 := by
    ext x; simp [Set.mem_pi]
  rw [cubeIco_eq, h2]
  exact (Measure.univ_pi_Ico_ae_eq_Icc).trans (Measure.univ_pi_Ioc_ae_eq_Icc).symm

theorem avg_fd_cube {ι κ : Type} [Fintype ι] [Fintype κ]
    (B : Module.Basis κ ℝ (EuclideanSpace ℂ ι)) (f : EuclideanSpace ℂ ι → ℝ) :
    ⨍ v in ZSpan.fundamentalDomain B, f v = ∫ x in cubeIco κ, f (B.equivFun.symm x) := by
  classical
  let e : EuclideanSpace ℂ ι ≃L[ℝ] (κ → ℝ) := B.equivFun.toContinuousLinearEquiv
  have hfd : ZSpan.fundamentalDomain B = e ⁻¹' cubeIco κ := by
    ext v
    simp [ZSpan.mem_fundamentalDomain, cubeIco, e]
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  set μ : Measure (κ → ℝ) := (volume : Measure (EuclideanSpace ℂ ι)).map e with hμ
  haveI : μ.IsAddHaarMeasure := e.isAddHaarMeasure_map _
  have hsm : μ = μ.addHaarScalarFactor volume • volume := Measure.isAddLeftInvariant_eq_smul μ volume
  set c := μ.addHaarScalarFactor volume with hcdef
  have hvol : volume (ZSpan.fundamentalDomain B) = (c : ENNReal) := by
    rw [hfd, ← hme.map_apply, ← hμ, hsm]
    simp [vol_cubeIco]
  have hc : c ≠ 0 := by
    intro h0
    have h' : μ = 0 := by rw [hsm, h0, zero_smul]
    exact (NeZero.ne μ) h'
  have hint : ∫ v in ZSpan.fundamentalDomain B, f v = (c : ℝ) * ∫ x in cubeIco κ, f (e.symm x) := by
    have h3 : ∫ v in e ⁻¹' cubeIco κ, f v = ∫ v in e ⁻¹' cubeIco κ, (fun x => f (e.symm x)) (e v) := by
      simp
    have key := hme.setIntegral_map (μ := (volume : Measure (EuclideanSpace ℂ ι)))
      (fun x => f (e.symm x)) (cubeIco κ)
    rw [hfd, h3, ← key, ← hμ]
    conv_lhs => rw [hsm]
    rw [Measure.restrict_smul, integral_smul_nnreal_measure]
    all_goals rw [NNReal.smul_def, smul_eq_mul]
  rw [setAverage_eq, hint, Measure.real, hvol]
  have : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  simp only [ENNReal.coe_toReal, smul_eq_mul]
  field_simp
  rfl

theorem avg_fd_swap {ι κ₁ κ₂ : Type} [Fintype ι] [Fintype κ₁] [Fintype κ₂]
    (B₁ : Module.Basis κ₁ ℝ (EuclideanSpace ℂ ι)) (B₂ : Module.Basis κ₂ ℝ (EuclideanSpace ℂ ι))
    (h : Submodule.span ℤ (Set.range B₁) = Submodule.span ℤ (Set.range B₂))
    (f : EuclideanSpace ℂ ι → ℝ)
    (hf : ∀ γ ∈ Submodule.span ℤ (Set.range B₁), ∀ v, f (γ + v) = f v) :
    ⨍ v in ZSpan.fundamentalDomain B₁, f v = ⨍ v in ZSpan.fundamentalDomain B₂, f v := by
  haveI : VAddInvariantMeasure (Submodule.span ℤ (Set.range B₁)) (EuclideanSpace ℂ ι) volume :=
    ⟨fun c s _ => measure_preimage_add volume (c : EuclideanSpace ℂ ι) s⟩
  have h1 := ZSpan.isAddFundamentalDomain B₁ (volume : Measure (EuclideanSpace ℂ ι))
  have h2 := ZSpan.isAddFundamentalDomain B₂ (volume : Measure (EuclideanSpace ℂ ι))
  rw [← h] at h2
  have hinv : ∀ (g : Submodule.span ℤ (Set.range B₁)) (x : EuclideanSpace ℂ ι), f (g +ᵥ x) = f x :=
    fun g x => hf g g.2 x
  rw [setAverage_eq, setAverage_eq, h1.setIntegral_eq h2 hinv]
  simp only [Measure.real, h1.measure_eq h2]

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.IntegrableNormPowMulExpNegMulNormSq
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory

def monomialOfMultiindex {g : ℕ} (α : Fin g →₀ ℕ) (z : EuclideanSpace ℂ (Fin g)) : ℂ :=
  ∏ i ∈ α.support, z i ^ α i

theorem fa1Mono_eq {g : ℕ} (α : Fin g →₀ ℕ) (z : EuclideanSpace ℂ (Fin g)) :
    monomialOfMultiindex α z = ∏ i, z i ^ α i := by
  unfold monomialOfMultiindex
  exact Finset.prod_subset (Finset.subset_univ _) fun i _ hi => by
    rw [Finsupp.notMem_support_iff.mp hi, pow_zero]

theorem fa1Mono_continuous {g : ℕ} (α : Fin g →₀ ℕ) : Continuous (monomialOfMultiindex α) := by
  have h : monomialOfMultiindex α = fun z : EuclideanSpace ℂ (Fin g) => ∏ i, z i ^ α i := funext (fa1Mono_eq α)
  rw [h]
  exact continuous_finsetProd _ fun i _ => (PiLp.continuous_apply 2 _ i).pow _

theorem fa1Mono_norm_le {g : ℕ} (α : Fin g →₀ ℕ) (z : EuclideanSpace ℂ (Fin g)) :
    ‖monomialOfMultiindex α z‖ ≤ ‖z‖ ^ (∑ i, α i) := by
  rw [fa1Mono_eq, norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le z i) _

theorem fa1Mono_smul {g : ℕ} (α : Fin g →₀ ℕ) (r : ℝ) (z : EuclideanSpace ℂ (Fin g)) :
    monomialOfMultiindex α (r • z) = (r : ℂ) ^ (∑ i, α i) * monomialOfMultiindex α z := by
  rw [fa1Mono_eq, fa1Mono_eq, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [PiLp.smul_apply, Complex.real_smul, mul_pow]

theorem pow_mul_exp_neg_mul_sq_le (n : ℕ) {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    t ^ n * Real.exp (-b * t ^ 2) ≤
      (1 + n.factorial * (2 / b) ^ n) * Real.exp (-(b / 2) * t ^ 2) := by
  have hx : 0 ≤ b / 2 * t ^ 2 := by positivity
  have h1 : 1 ≤ Real.exp (b / 2 * t ^ 2) := Real.one_le_exp hx
  have h2 : (b / 2 * t ^ 2) ^ n / n.factorial ≤ Real.exp (b / 2 * t ^ 2) :=
    Real.pow_div_factorial_le_exp (x := b / 2 * t ^ 2) hx n
  have h3 : t ^ n ≤ 1 + t ^ (2 * n) := by
    rcases le_total t 1 with h | h
    · have : t ^ n ≤ 1 := pow_le_one₀ ht h
      linarith [pow_nonneg ht (2 * n)]
    · have : t ^ n ≤ t ^ (2 * n) := pow_le_pow_right₀ h (by omega)
      linarith
  have h4 : t ^ (2 * n) = (2 / b) ^ n * (b / 2 * t ^ 2) ^ n := by
    rw [pow_mul, ← mul_pow]
    congr 1
    field_simp
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h5 : t ^ (2 * n) ≤ n.factorial * (2 / b) ^ n * Real.exp (b / 2 * t ^ 2) := by
    rw [h4]
    have h2' := (div_le_iff₀ hfac).mp h2
    have hb2 : 0 ≤ (2 / b) ^ n := by positivity
    nlinarith
  have hexp : Real.exp (b / 2 * t ^ 2) * Real.exp (-b * t ^ 2) = Real.exp (-(b / 2) * t ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h6 : t ^ n ≤ (1 + n.factorial * (2 / b) ^ n) * Real.exp (b / 2 * t ^ 2) := by
    nlinarith
  calc t ^ n * Real.exp (-b * t ^ 2)
      ≤ (1 + n.factorial * (2 / b) ^ n) * Real.exp (b / 2 * t ^ 2) * Real.exp (-b * t ^ 2) :=
        mul_le_mul_of_nonneg_right h6 (Real.exp_pos _).le
    _ = (1 + n.factorial * (2 / b) ^ n) * Real.exp (-(b / 2) * t ^ 2) := by
        rw [mul_assoc, hexp]

theorem integrable_exp_neg_mul_norm_sq_euclidean {g : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) => Real.exp (-b * ‖z‖ ^ 2)) := by
  have hc := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := EuclideanSpace ℂ (Fin g))
    (b := (b : ℂ)) (by simpa using hb) 0 0
  refine hc.norm.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [zero_mul, add_zero]
  rw [Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

theorem integrable_norm_pow_mul_exp_neg_mul_norm_sq_euclidean {g : ℕ} (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) => ‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2)) := by
  have hb2 : 0 < b / 2 := by positivity
  refine ((integrable_exp_neg_mul_norm_sq_euclidean (g := g) hb2).const_mul (1 + n.factorial * (2 / b) ^ n)).mono' ?_ ?_
  · exact (by fun_prop : Continuous fun z : EuclideanSpace ℂ (Fin g) =>
      ‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_mul_exp_neg_mul_sq_le n hb (norm_nonneg z)

theorem integrable_of_norm_le_gaussian {g : ℕ} {E : Type*} [NormedAddCommGroup E]
    {f : EuclideanSpace ℂ (Fin g) → E} (hf : Continuous f) (n : ℕ) {b C : ℝ} (hb : 0 < b)
    (h : ∀ z, ‖f z‖ ≤ C * (‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2))) : Integrable f := by
  exact ((integrable_norm_pow_mul_exp_neg_mul_norm_sq_euclidean n hb).const_mul C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall h)

theorem integrable_monomial_mul_conj_gaussian {g : ℕ} (α β : Fin g →₀ ℕ) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) =>
      monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  have hcont : Continuous fun z : EuclideanSpace ℂ (Fin g) =>
      monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ) :=
    ((fa1Mono_continuous α).mul (Complex.continuous_conj.comp (fa1Mono_continuous β))).mul
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_norm.pow 2).neg))
  refine integrable_of_norm_le_gaussian hcont (∑ i, α i + ∑ i, β i) one_pos (C := 1) fun z => ?_
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), one_mul, neg_one_mul, pow_add]
  have h1 := fa1Mono_norm_le α z
  have h2 := fa1Mono_norm_le β z
  have he := (Real.exp_pos (-‖z‖ ^ 2)).le
  gcongr

theorem integrable_norm_monomial_sq_gaussian {g : ℕ} (α : Fin g →₀ ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) => ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-b * ‖z‖ ^ 2)) := by
  have hcont : Continuous fun z : EuclideanSpace ℂ (Fin g) =>
      ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-b * ‖z‖ ^ 2) :=
    ((fa1Mono_continuous α).norm.pow 2).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  refine integrable_of_norm_le_gaussian hcont (2 * ∑ i, α i) hb (C := 1) fun z => ?_
  rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_mul']
  have h1 := fa1Mono_norm_le α z
  gcongr

noncomputable def coordinateRotation {g : ℕ} (j : Fin g) (u : Circle) :
    EuclideanSpace ℂ (Fin g) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin g) :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun i => if i = j then rotation u else LinearIsometryEquiv.refl ℝ ℂ)

theorem fa1Rot_apply {g : ℕ} (j : Fin g) (u : Circle) (z : EuclideanSpace ℂ (Fin g)) (i : Fin g) :
    coordinateRotation j u z i = (if i = j then (u : ℂ) else 1) * z i := by
  simp only [coordinateRotation, LinearIsometryEquiv.piLpCongrRight_apply]
  split_ifs with h
  · simp [rotation_apply]
  · simp

theorem fa1Mono_rot {g : ℕ} (α : Fin g →₀ ℕ) (j : Fin g) (u : Circle)
    (z : EuclideanSpace ℂ (Fin g)) :
    monomialOfMultiindex α (coordinateRotation j u z) = (u : ℂ) ^ (α j) * monomialOfMultiindex α z := by
  rw [fa1Mono_eq, fa1Mono_eq]
  simp only [fa1Rot_apply, mul_pow, Finset.prod_mul_distrib, ite_pow, one_pow,
    Finset.prod_ite_eq', Finset.mem_univ, if_true]

theorem integral_monomial_mul_conj_gaussian_eq_zero {g : ℕ} {α β : Fin g →₀ ℕ} (h : α ≠ β) :
    ∫ z : EuclideanSpace ℂ (Fin g),
      monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ) = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, α j ≠ β j := by
    by_contra hcon
    exact h (Finsupp.ext fun j => not_not.mp fun hne => hcon ⟨j, hne⟩)
  have hm : ((α j : ℝ) - β j) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hj)
  set u : Circle := Circle.exp (Real.pi / ((α j : ℝ) - β j)) with hu
  set F : EuclideanSpace ℂ (Fin g) → ℂ := fun z =>
    monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ) with hF
  have hc : (u : ℂ) ^ (α j) * (starRingEnd ℂ) ((u : ℂ) ^ (β j)) = -1 := by
    rw [hu, Circle.coe_exp, map_pow, ← Complex.exp_conj, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul, ← Complex.exp_add]
    have hm' : ((α j : ℂ) - β j) ≠ 0 := by exact_mod_cast hm
    have : (α j : ℂ) * (↑(Real.pi / ((α j : ℝ) - β j)) * Complex.I) +
        (β j : ℂ) * (starRingEnd ℂ) (↑(Real.pi / ((α j : ℝ) - β j)) * Complex.I) =
        Real.pi * Complex.I := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      field_simp
      ring
    rw [this, Complex.exp_pi_mul_I]
  have hrot : ∀ z, F (coordinateRotation j u z) =
      ((u : ℂ) ^ (α j) * (starRingEnd ℂ) ((u : ℂ) ^ (β j))) * F z := by
    intro z
    simp only [hF, fa1Mono_rot, LinearIsometryEquiv.norm_map, map_mul]
    ring
  have hint : ∫ z, F (coordinateRotation j u z) = ∫ z, F z :=
    (coordinateRotation j u).measurePreserving.integral_comp (coordinateRotation j u).toHomeomorph.measurableEmbedding F
  simp_rw [hrot, hc] at hint
  rw [integral_const_mul] at hint
  linear_combination (-1 / 2 : ℂ) * hint

theorem integral_norm_monomial_sq_gaussian_pos {g : ℕ} (α : Fin g →₀ ℕ) :
    0 < ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by
  set f : EuclideanSpace ℂ (Fin g) → ℝ := fun z => ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) with hf
  have hcont : Continuous f :=
    ((fa1Mono_continuous α).norm.pow 2).mul (Real.continuous_exp.comp (continuous_norm.pow 2).neg)
  have hint : Integrable f := by
    have := integrable_norm_monomial_sq_gaussian α one_pos
    simpa [neg_one_mul] using this
  have hnn : 0 ≤ f := fun z => by
    simp only [Pi.zero_apply, hf]
    positivity
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  let z₀ : EuclideanSpace ℂ (Fin g) := WithLp.toLp 2 (fun _ => (1 : ℂ))
  have hz₁ : monomialOfMultiindex α z₀ = 1 := by
    rw [fa1Mono_eq]
    simp [z₀]
  have hz₀ : f z₀ ≠ 0 := by
    simp only [hf, hz₁, norm_one, one_pow, one_mul]
    exact (Real.exp_pos _).ne'
  exact hcont.isOpen_support.measure_pos _ ⟨z₀, hz₀⟩

theorem integral_norm_monomial_sq_gaussian_half {g : ℕ} (α : Fin g →₀ ℕ) :
    ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-(1 / 2) * ‖z‖ ^ 2) =
      2 ^ (g + ∑ i, α i) *
        ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpt : ∀ x : EuclideanSpace ℂ (Fin g),
      ‖monomialOfMultiindex α (Real.sqrt 2 • x)‖ ^ 2 * Real.exp (-(1 / 2) * ‖Real.sqrt 2 • x‖ ^ 2) =
        2 ^ (∑ i, α i) * (‖monomialOfMultiindex α x‖ ^ 2 * Real.exp (-‖x‖ ^ 2)) := by
    intro x
    rw [fa1Mono_smul, norm_mul, norm_pow, Complex.norm_real, norm_smul,
      Real.norm_of_nonneg (Real.sqrt_nonneg 2), mul_pow, mul_pow, ← pow_mul,
      mul_comm (∑ i, α i) 2, pow_mul, hs2, show -(1 / 2) * (2 * ‖x‖ ^ 2) = -‖x‖ ^ 2 by ring]
    ring
  have e1 : ∫ x : EuclideanSpace ℂ (Fin g),
      ‖monomialOfMultiindex α (Real.sqrt 2 • x)‖ ^ 2 * Real.exp (-(1 / 2) * ‖Real.sqrt 2 • x‖ ^ 2) =
        2 ^ (∑ i, α i) * ∫ x : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α x‖ ^ 2 * Real.exp (-‖x‖ ^ 2) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hdim : |(Real.sqrt 2 ^ Module.finrank ℝ (EuclideanSpace ℂ (Fin g)))⁻¹| = ((2 : ℝ) ^ g)⁻¹ := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin, pow_mul, hs2,
      abs_of_pos (by positivity)]
  have e2 := MeasureTheory.Measure.integral_comp_smul (volume : Measure (EuclideanSpace ℂ (Fin g)))
    (fun z => ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) (Real.sqrt 2)
  beta_reduce at e2
  rw [hdim, smul_eq_mul, e1] at e2
  have h2g : (2 : ℝ) ^ g ≠ 0 := by positivity
  rw [pow_add, mul_assoc, e2, ← mul_assoc, mul_inv_cancel₀ h2g, one_mul]

end ReciprocityTheory.ChartRestriction.G.I2
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.RCurveAlg
namespace ReciprocityTheory.ChartRestriction.G.I2

theorem one_sub_pow_mem {A : Type*} [CommRing A] (h : A) (K : Ideal A) (hK : h - 1 ∈ K) (m : ℕ) :
    1 - h ^ m ∈ K := by
  rw [← Ideal.Quotient.eq]
  have h1 : Ideal.Quotient.mk K h = 1 := by
    rw [← map_one (Ideal.Quotient.mk K)]; exact Ideal.Quotient.eq.mpr hK
  simp [map_pow, h1]

theorem quotientMap_bijective_of_loc {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (h : A) (K : Ideal A) (hK : h - 1 ∈ K)
    (hB : ∀ b : B, ∃ m : ℕ, ∃ a : A, algebraMap A B (h ^ m) * b = algebraMap A B a)
    (hinj : Function.Injective (algebraMap A B)) :
    Function.Bijective (Ideal.quotientMap (K.map (algebraMap A B)) (algebraMap A B)
      Ideal.le_comap_map) := by

  have key : ∀ x ∈ K.map (algebraMap A B), ∃ M : ℕ, ∃ k ∈ K, algebraMap A B (h ^ M) * x = algebraMap A B k := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact ⟨0, k, hk, by simp⟩
    | zero => exact ⟨0, 0, K.zero_mem, by simp⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨M₁, k₁, hk₁, e₁⟩ := ihx
      obtain ⟨M₂, k₂, hk₂, e₂⟩ := ihy
      refine ⟨M₁ + M₂, h ^ M₂ * k₁ + h ^ M₁ * k₂,
        K.add_mem (K.mul_mem_left _ hk₁) (K.mul_mem_left _ hk₂), ?_⟩
      rw [map_add (f := _), map_mul, map_mul, ← e₁, ← e₂, pow_add, map_mul]
      ring
    | smul b x _ ih =>
      obtain ⟨M, k, hk, e⟩ := ih
      obtain ⟨m, a, hb⟩ := hB b
      refine ⟨M + m, a * k, K.mul_mem_left _ hk, ?_⟩
      rw [smul_eq_mul, map_mul, ← hb, ← e, pow_add, map_mul]
      ring
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hz
    rw [Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨M, k, hk, e⟩ := key _ hz
    rw [← map_mul] at e
    have hM : h ^ M * a ∈ K := hinj e ▸ hk
    have h1 : (1 - h ^ M) * a ∈ K := K.mul_mem_right _ (one_sub_pow_mem h K hK M)
    have : a = h ^ M * a + (1 - h ^ M) * a := by ring
    rw [this]; exact K.add_mem hM h1
  · intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨m, a, hb⟩ := hB b
    refine ⟨Ideal.Quotient.mk K a, ?_⟩
    rw [Ideal.quotientMap_mk, ← hb, Ideal.Quotient.eq]
    have hmem : algebraMap A B (1 - h ^ m) ∈ K.map (algebraMap A B) :=
      Ideal.mem_map_of_mem _ (one_sub_pow_mem h K hK m)
    have : algebraMap A B (h ^ m) * b - b = -(algebraMap A B (1 - h ^ m) * b) := by
      rw [map_sub, map_one]; ring
    rw [this]
    exact Submodule.neg_mem _ (Ideal.mul_mem_right _ _ hmem)

end ReciprocityTheory.ChartRestriction.G.I2
end
