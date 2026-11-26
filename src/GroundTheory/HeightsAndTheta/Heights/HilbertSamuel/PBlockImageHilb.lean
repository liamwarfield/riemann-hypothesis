module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsDimZero
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalNef
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageHilb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BlockImageHilb

section Subst

variable {σ τ M M' : Type*} [AddCommMonoid M] [AddCommMonoid M']

theorem isWeightedHomogeneous_aeval {w : σ → M} {w' : τ → M'} (ψ : M →+ M') (φ : σ → MvPolynomial τ ℚ)
    (hφ : ∀ i, IsWeightedHomogeneous w' (φ i) (ψ (w i))) {f : MvPolynomial σ ℚ} {m : M}
    (hf : IsWeightedHomogeneous w f m) : IsWeightedHomogeneous w' (aeval φ f) (ψ m) := by
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simpa using isWeightedHomogeneous_zero ℚ w' (ψ m)
  | add p q hp hq ihp ihq => simpa using ihp.add ihq
  | monomial d r hr =>
    rw [aeval_monomial, algebraMap_eq, ← hr, Finsupp.weight_apply, map_finsuppSum]
    refine IsWeightedHomogeneous.C_mul ?_ r
    simp only [map_nsmul]
    exact IsWeightedHomogeneous.prod _ _ _ fun i _ => (hφ i).pow (d i)

end Subst

section Cone

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [CharZero Ω]

def mConeMapQ (y : (Σ k, ι k) → Ω) : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] MvPolynomial K Ω :=
  aeval fun p => MvPolynomial.C (y p) * MvPolynomial.X p.1

def valSpan {σ M : Type*} [AddCommMonoid M] (w : σ → M) (y : σ → Ω) (m : M) : Submodule ℚ Ω :=
  (weightedHomogeneousSubmodule ℚ w m).map (aeval y : MvPolynomial σ ℚ →ₐ[ℚ] Ω).toLinearMap


omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem map_mCoordIdeal (y : (Σ k, ι k) → Ω) :
    (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) = RingHom.ker (mConeMapQ y) := by
  have hring : ((mConeMapQ y : MvPolynomial (Σ k, ι k) ℚ →+* MvPolynomial K Ω).comp
      (MvPolynomial.map (Int.castRingHom ℚ))) = (mConeMap y : MvPolynomial (Σ k, ι k) ℤ →+* MvPolynomial K Ω) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [mConeMapQ, mConeMap]
    · intro i
      simp [mConeMapQ, mConeMap]
  have hker : mCoordIdeal y = (RingHom.ker (mConeMapQ y)).comap (MvPolynomial.map (Int.castRingHom ℚ)) := by
    ext f
    rw [Ideal.mem_comap]
    simp only [mCoordIdeal, RingHom.mem_ker]
    have h := RingHom.congr_fun hring f
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe] at h
    rw [h]
  let _ := MvPolynomial.algebraMvPolynomial (σ := Σ k, ι k) (R := ℤ) (S := ℚ)
  have e : algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) =
      MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]
  have h := IsLocalization.map_under ((nonZeroDivisors ℤ).map (C (σ := Σ k, ι k)))
    (MvPolynomial (Σ k, ι k) ℚ) (RingHom.ker (mConeMapQ y))
  rw [e] at h
  rw [hker]
  exact h

theorem weight_blockWeight_apply (μ : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (NumbersDVR.blockWeight ι) μ k = ∑ i : ι k, μ ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [NumbersDVR.blockWeight, Pi.single_apply]

theorem mConeMapQ_eq (y : (Σ k, ι k) → Ω) {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) :
    mConeMapQ y f = MvPolynomial.C (aeval y f) * ∏ k, MvPolynomial.X k ^ a k := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ μ p = ∏ k, MvPolynomial.X k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ μ ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, ← weight_blockWeight_apply, hf (mem_support_iff.mp hμ)]
  simp only [mConeMapQ, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow, MvPolynomial.algebraMap_apply]
  ring

theorem hilbFn_eq_finrank (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun k => (a k : ℤ)) =
      Module.finrank ℚ (valSpan (NumbersDVR.blockWeight ι) y a) := by
  rw [map_mCoordIdeal]
  set W := weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι) a
  set P := RingHom.ker (mConeMapQ y)
  let φ₁ : W →ₗ[ℚ] MvPolynomial (Σ k, ι k) ℚ ⧸ P := (Ideal.Quotient.mkₐ ℚ P).toLinearMap ∘ₗ W.subtype
  let φ₂ : W →ₗ[ℚ] Ω := (aeval y : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] Ω).toLinearMap ∘ₗ W.subtype
  have hk : LinearMap.ker φ₁ = LinearMap.ker φ₂ := by
    ext ⟨f, hf⟩
    simp only [LinearMap.mem_ker, φ₁, φ₂, LinearMap.comp_apply, Submodule.subtype_apply,
      AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, P, RingHom.mem_ker]
    rw [mConeMapQ_eq y hf, mul_eq_zero, C_eq_zero,
      or_iff_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k))]
  have h₁ : LinearMap.range φ₁ = NumbersDVR.gradedPiece P a := by
    simp only [φ₁, LinearMap.range_comp, Submodule.range_subtype, NumbersDVR.gradedPiece, W]
  have h₂ : LinearMap.range φ₂ = valSpan (NumbersDVR.blockWeight ι) y a := by
    simp only [φ₂, LinearMap.range_comp, Submodule.range_subtype, valSpan, W]
  have h := LinearEquiv.finrank_eq
    ((φ₁.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ hk)).trans φ₂.quotKerEquivRange)
  rw [h₁, h₂] at h
  unfold NumbersDVR.hilbFn
  rw [if_pos (fun k => Nat.cast_nonneg _)]
  show ((Module.finrank ℚ (NumbersDVR.gradedPiece P a) : ℕ) : ℤ) = _
  rw [h]

end Cone

section Block

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [CharZero Ω] {κ : Type} [Fintype κ]

def fwdSubst (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ) (j : Ix κ) : MvPolynomial (Σ k, ι k) ℚ :=
  ∑ i, MvPolynomial.C ((M j i : ℤ) : ℚ) * MvPolynomial.X ⟨k₀, i⟩

def backSubst (k₀ : K) (N : Matrix (ι k₀) (Ix κ) ℤ) : (Σ k, ι k) → MvPolynomial (Ix κ) ℚ
  | ⟨k, i⟩ => if h : k = k₀ then ∑ j, MvPolynomial.C ((N (h ▸ i) j : ℤ) : ℚ) * MvPolynomial.X j else 0

theorem valSpan_eq {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix κ) (ι k₀) ℤ} {N : Matrix (ι k₀) (Ix κ) ℤ}
    {x : Ix κ → Ω} (hxy : IsBlockImage y k₀ M N x) (n : ℕ) :
    valSpan (NumbersDVR.blockWeight (GlobalTheory κ)) x (fun _ => n) = valSpan (NumbersDVR.blockWeight ι) y (Pi.single k₀ n) := by
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    let ψ : (Unit → ℕ) →+ (K → ℕ) :=
      { toFun := fun a => Pi.single k₀ (a ()), map_zero' := by simp, map_add' := fun a b => by simp [Pi.single_add] }
    have hφ : ∀ j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (fwdSubst k₀ M j)
        (ψ (NumbersDVR.blockWeight (GlobalTheory κ) j)) := fun j => by
      have e : ψ (NumbersDVR.blockWeight (GlobalTheory κ) j) = Pi.single k₀ 1 := by
        simp [ψ, NumbersDVR.blockWeight]
      rw [e]
      exact IsWeightedHomogeneous.sum _ _ _ fun i _ =>
        (isWeightedHomogeneous_X ℚ (NumbersDVR.blockWeight ι) ⟨k₀, i⟩).C_mul _
    refine ⟨aeval (fwdSubst k₀ M) f, ?_, ?_⟩
    · simpa [ψ] using isWeightedHomogeneous_aeval ψ _ hφ hf
    · simp only [AlgHom.toLinearMap_apply]
      have e : (fun j => aeval y (fwdSubst k₀ M j)) = x := by
        funext j
        simp [fwdSubst, hxy.1 j]
      rw [← AlgHom.comp_apply, comp_aeval, e]
  · rintro _ ⟨g, hg, rfl⟩
    let ψ : (K → ℕ) →+ (Unit → ℕ) :=
      { toFun := fun a _ => ∑ k, a k, map_zero' := by ext; simp,
        map_add' := fun a b => by ext; simp [Finset.sum_add_distrib] }
    have hφ : ∀ p, IsWeightedHomogeneous (NumbersDVR.blockWeight (GlobalTheory κ)) (backSubst k₀ N p)
        (ψ (NumbersDVR.blockWeight ι p)) := by
      rintro ⟨k, i⟩
      have e : ψ (NumbersDVR.blockWeight ι ⟨k, i⟩) = fun _ => 1 := by
        funext u
        simp [ψ, NumbersDVR.blockWeight]
      rw [e]
      by_cases h : k = k₀
      · subst h
        simp only [backSubst, dite_true]
        refine IsWeightedHomogeneous.sum _ _ _ fun j _ => ?_
        convert (isWeightedHomogeneous_X ℚ (NumbersDVR.blockWeight (GlobalTheory κ)) j).C_mul _ using 1
        funext u
        simp [NumbersDVR.blockWeight]
      · simp only [backSubst, h, dite_false]
        exact isWeightedHomogeneous_zero ℚ _ _
    refine ⟨aeval (backSubst k₀ N) g, ?_, ?_⟩
    · simpa [ψ] using isWeightedHomogeneous_aeval ψ _ hφ hg
    · simp only [AlgHom.toLinearMap_apply]
      rw [← AlgHom.comp_apply, comp_aeval]
      refine hom_congr_vars (Subsingleton.elim _ _) (fun p hp _ => ?_) rfl
      obtain ⟨k, i⟩ := p
      obtain ⟨μ, hμ, hp⟩ := (mem_vars_iff_mem_support _).mp hp
      by_cases h : k = k₀
      · subst h
        simp [backSubst, hxy.2 i]
      · exfalso
        have hw := congrFun (hg (mem_support_iff.mp hμ)) k
        rw [weight_blockWeight_apply, Pi.single_eq_of_ne h] at hw
        have := Finset.single_le_sum (fun i' _ => Nat.zero_le (μ ⟨k, i'⟩)) (Finset.mem_univ i)
        rw [hw] at this
        exact (Finsupp.mem_support_iff.mp hp) (Nat.le_zero.mp this)

end Block

end BlockImageHilb


open BlockImageHilb in
theorem BlockImageHilb.proof : BlockImageHilb.Statement := by
  intro K _ _ ι _ Ω _ _ κ _ y k₀ M N x hxy n
  rw [coordIdeal_eq_mCoordIdeal]
  have e : (fun k => if k = k₀ then (n : ℤ) else 0) = fun k => ((Pi.single k₀ n : K → ℕ) k : ℤ) := by
    funext k
    by_cases h : k = k₀
    · subst h; simp
    · simp [h]
  rw [e, hilbFn_eq_finrank y (Pi.single k₀ n), ← valSpan_eq hxy n]
  exact hilbFn_eq_finrank (ι := GlobalTheory κ) x (fun _ => n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights
open scoped ContDiff

noncomputable section

namespace MetricChange

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}

theorem weight_continuousAt (W : Weight L) (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source) :
    ContinuousAt (W.φ j) x := by
  have hy : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source :=
    ⟨(A.chart j).map_source hx, by simpa [(A.chart j).left_inv hx] using hx⟩
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source) :=
    (A.chart j).isOpen_inter_preimage_symm (A.chart j).open_source
  have h1 : ContinuousAt (W.φ j ∘ (A.chart j).symm) (A.chart j x) :=
    ((W.smooth j j).continuousOn).continuousAt (hopen.mem_nhds hy)
  have h2 : ContinuousAt ((W.φ j ∘ (A.chart j).symm) ∘ A.chart j) x :=
    h1.comp ((A.chart j).continuousAt hx)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hx] with y hy
  simp [(A.chart j).left_inv hy]

theorem diff_continuous (W₁ W₀ : Weight L) : Continuous (Weight.diff W₁ W₀) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  have hx : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  have h := (weight_continuousAt W₁ _ hx).sub (weight_continuousAt W₀ _ hx)
  refine h.congr ?_
  filter_upwards [(A.chart (chartIdx A x)).open_source.mem_nhds hx] with y hy
  exact (Weight.diff_eq W₁ W₀ _ hy).symm

theorem levi_lerp {ι : Type*} [Fintype ι] {f₀ f₁ : (ι → ℂ) → ℝ} {y : ι → ℂ}
    (h₀ : ContDiffAt ℝ 2 f₀ y) (h₁ : ContDiffAt ℝ 2 f₁ y) (t : ℝ) (w : ι → ℂ) :
    levi (fun z ↦ f₀ z + t * (f₁ z - f₀ z)) y w = (1 - t) * levi f₀ y w + t * levi f₁ y w := by
  have e₀ := h₀.eventually (by simp)
  have e₁ := h₁.eventually (by simp)
  have hfun : (fun z ↦ f₀ z + t * (f₁ z - f₀ z)) = fun z ↦ (1 - t) * f₀ z + t * f₁ z := by
    funext z; ring
  have hfd : fderiv ℝ (fun z ↦ (1 - t) * f₀ z + t * f₁ z) =ᶠ[𝓝 y]
      fun z ↦ (1 - t) • fderiv ℝ f₀ z + t • fderiv ℝ f₁ z := by
    filter_upwards [e₀, e₁] with z hz₀ hz₁
    have d₀ := hz₀.differentiableAt (by norm_num)
    have d₁ := hz₁.differentiableAt (by norm_num)
    rw [fderiv_fun_add (d₀.const_mul _) (d₁.const_mul _), fderiv_const_mul d₀, fderiv_const_mul d₁]
  have D₀ : DifferentiableAt ℝ (fderiv ℝ f₀) y :=
    (h₀.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have D₁ : DifferentiableAt ℝ (fderiv ℝ f₁) y :=
    (h₁.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fun z ↦ (1 - t) • fderiv ℝ f₀ z + t • fderiv ℝ f₁ z) y =
      (1 - t) • fderiv ℝ (fderiv ℝ f₀) y + t • fderiv ℝ (fderiv ℝ f₁) y :=
    ((D₀.hasFDerivAt.const_smul (1 - t)).add (D₁.hasFDerivAt.const_smul t)).fderiv
  rw [hfun, levi, levi, levi, hfd.fderiv_eq, h2]
  simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem lerp_isSemipositive {W₀ W₁ : Weight L} (h₀ : W₀.IsSemipositive) (h₁ : W₁.IsSemipositive)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (W₀.lerp W₁ t).IsSemipositive := by
  intro j y hy w
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source) :=
    (A.chart j).isOpen_inter_preimage_symm (A.chart j).open_source
  have hy' : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source :=
    ⟨hy, (A.chart j).map_target hy⟩
  have c₀ : ContDiffAt ℝ 2 (W₀.φ j ∘ (A.chart j).symm) y :=
    ((W₀.smooth j j).contDiffAt (hopen.mem_nhds hy')).of_le (by norm_cast)
  have c₁ : ContDiffAt ℝ 2 (W₁.φ j ∘ (A.chart j).symm) y :=
    ((W₁.smooth j j).contDiffAt (hopen.mem_nhds hy')).of_le (by norm_cast)
  have key : levi ((W₀.lerp W₁ t).φ j ∘ (A.chart j).symm) y w =
      (1 - t) * levi (W₀.φ j ∘ (A.chart j).symm) y w +
        t * levi (W₁.φ j ∘ (A.chart j).symm) y w :=
    levi_lerp c₀ c₁ t w
  rw [key]
  have a₀ := h₀ j y hy w
  have a₁ := h₁ j y hy w
  have : 0 ≤ 1 - t := by linarith [ht.2]
  exact add_nonneg (mul_nonneg this a₀) (mul_nonneg ht.1 a₁)

theorem proof (hG : GramChiDerivative.Statement) (hBI : BergmanIntegrable.Statement)
    (hBD : BergmanDensIntegrable.Statement) (hU : UniformBergmanBound.Statement)
    (hL : BergmanL1Convergence.Statement) : MetricChange.Statement := by
  intro D X _ _ _ _ _ A L W₀ W₁ dV h₀ h₁ V _ hV hdim e ε hε
  have := dV.isProb
  set u := Weight.diff W₁ W₀ with hu_def
  have hu_cont : Continuous u := diff_continuous W₁ W₀
  obtain ⟨M₀, hM₀⟩ := isCompact_univ.exists_bound_of_continuousOn hu_cont.continuousOn
  set M := max M₀ 0 with hM_def
  have hM : ∀ x, ‖u x‖ ≤ M := fun x ↦ (hM₀ x (mem_univ x)).trans (le_max_left _ _)
  have hM0 : 0 ≤ M := le_max_right _ _
  have hu_meas : AEStronglyMeasurable u dV.μ := hu_cont.aestronglyMeasurable
  obtain ⟨C, hC⟩ := hU A L W₀ W₁ dV h₀ h₁
  let B : ℕ → ℝ → X → ℝ := fun n t x ↦ bergman (W₀.lerp W₁ t) dV (V n) n x
  let b : ℝ → X → ℝ := fun t x ↦ bergmanDens (W₀.lerp W₁ t) dV x
  let F : ℕ → ℝ → ℝ := fun n t ↦ ∫ x, u x * (((n : ℝ) ^ D)⁻¹ * B n t x) ∂dV.μ
  let f : ℝ → ℝ := fun t ↦ ∫ x, u x * b t x ∂dV.μ
  let χ : ℕ → ℝ → ℝ := fun n s ↦
    chiGram (W₀.lerp W₁ s) dV n (fun a ↦ (e n a : Fin A.n → X → ℂ))
  have hB0 : ∀ n t x, 0 ≤ B n t x := by
    intro n t x
    refine Real.iSup_nonneg fun s ↦ div_nonneg ?_ (integral_nonneg fun y ↦ ?_)
    · unfold ptNormSq; positivity
    · unfold ptNormSq; positivity
  have hderiv : ∀ n t, HasDerivAt (χ n) ((n : ℝ) / 2 * ∫ x, u x * B n t x ∂dV.μ) t :=
    fun n t ↦ hG A L W₀ W₁ dV n (V n) (hV n) (e n) t
  have hF : ∀ n t, F n t = ((n : ℝ) ^ D)⁻¹ * ∫ x, u x * B n t x ∂dV.μ := by
    intro n t
    show ∫ x, u x * (((n : ℝ) ^ D)⁻¹ * B n t x) ∂dV.μ = _
    rw [← integral_const_mul]
    congr 1; funext x; ring
  have hderiv' : ∀ n, 1 ≤ n → ∀ t, HasDerivAt (χ n) ((n : ℝ) ^ (D + 1) / 2 * F n t) t := by
    intro n hn t
    convert hderiv n t using 1
    have : (n : ℝ) ^ D ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : n ≠ 0))
    rw [hF]; field_simp; ring
  have hFmeas : ∀ n, 1 ≤ n → Measurable (F n) := by
    intro n hn
    have hpos : (0 : ℝ) < (n : ℝ) ^ (D + 1) / 2 := by
      have : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
      positivity
    have : F n = fun t ↦ ((n : ℝ) ^ (D + 1) / 2)⁻¹ * deriv (χ n) t := by
      funext t; rw [(hderiv' n hn t).deriv]; field_simp
    rw [this]; exact (measurable_deriv _).const_mul _
  have hFbound : ∀ n, 1 ≤ n → ∀ t ∈ Icc (0 : ℝ) 1, ‖F n t‖ ≤ M * C := by
    intro n hn t ht
    have hnD : (0 : ℝ) < (n : ℝ) ^ D := pow_pos (Nat.cast_pos.2 (by omega)) _
    have hg : ∀ x, ‖u x * (((n : ℝ) ^ D)⁻¹ * B n t x)‖ ≤ M * C := by
      intro x
      have h1 : B n t x ≤ C * (n : ℝ) ^ D := hC n hn t ht (V n) (hV n) x
      have h2 : 0 ≤ ((n : ℝ) ^ D)⁻¹ * B n t x := mul_nonneg (inv_nonneg.2 hnD.le) (hB0 n t x)
      have h3 : ((n : ℝ) ^ D)⁻¹ * B n t x ≤ C := by
        rw [inv_mul_le_iff₀ hnD]; linarith [mul_comm C ((n : ℝ) ^ D)]
      rw [norm_mul, Real.norm_of_nonneg h2]
      exact mul_le_mul (hM x) h3 h2 hM0
    calc ‖F n t‖ ≤ ∫ x, ‖u x * (((n : ℝ) ^ D)⁻¹ * B n t x)‖ ∂dV.μ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x, M * C ∂dV.μ :=
          integral_mono_of_nonneg (ae_of_all _ fun x ↦ norm_nonneg _) (integrable_const _)
            (ae_of_all _ hg)
      _ = M * C := by simp
  have hlim : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n ↦ F n t) atTop (𝓝 (f t)) := by
    intro t ht
    have hL1 := hL A L (W₀.lerp W₁ t) dV (lerp_isSemipositive h₀ h₁ ht) V hV (hdim t ht)
    have hbt : Integrable (b t) dV.μ := hBD A L (W₀.lerp W₁ t) dV
    have hub : Integrable (fun x ↦ u x * b t x) dV.μ := hbt.bdd_mul hu_meas (ae_of_all _ hM)
    have key : ∀ n, ‖F n t - f t‖ ≤ M * ∫ x, |((n : ℝ) ^ D)⁻¹ * B n t x - b t x| ∂dV.μ := by
      intro n
      have hg : Integrable (fun x ↦ ((n : ℝ) ^ D)⁻¹ * B n t x) dV.μ :=
        (hBI A L (W₀.lerp W₁ t) dV n (V n) (hV n)).const_mul _
      have hug : Integrable (fun x ↦ u x * (((n : ℝ) ^ D)⁻¹ * B n t x)) dV.μ :=
        hg.bdd_mul hu_meas (ae_of_all _ hM)
      have hd : Integrable (fun x ↦ |((n : ℝ) ^ D)⁻¹ * B n t x - b t x|) dV.μ := (hg.sub hbt).abs
      calc ‖F n t - f t‖ = ‖∫ x, u x * (((n : ℝ) ^ D)⁻¹ * B n t x - b t x) ∂dV.μ‖ := by
            rw [← integral_sub hug hub]; congr 2; funext x; ring
        _ ≤ ∫ x, ‖u x * (((n : ℝ) ^ D)⁻¹ * B n t x - b t x)‖ ∂dV.μ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x, M * |((n : ℝ) ^ D)⁻¹ * B n t x - b t x| ∂dV.μ := by
            refine integral_mono_of_nonneg (ae_of_all _ fun x ↦ norm_nonneg _) (hd.const_mul M)
              (ae_of_all _ fun x ↦ ?_)
            dsimp only
            rw [norm_mul, Real.norm_eq_abs (_ - _)]
            exact mul_le_mul_of_nonneg_right (hM x) (abs_nonneg _)
        _ = M * ∫ x, |((n : ℝ) ^ D)⁻¹ * B n t x - b t x| ∂dV.μ := integral_const_mul _ _
    have h0 : Tendsto (fun n : ℕ ↦ M * ∫ x, |((n : ℝ) ^ D)⁻¹ * B n t x - b t x| ∂dV.μ) atTop
        (𝓝 0) := by
      simpa using hL1.const_mul M
    exact tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n ↦ norm_nonneg _) key h0)
  have hI : Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, F n t) atTop (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ M * C) ?_ ?_
      intervalIntegrable_const ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact (hFmeas n hn).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop 1] with n hn
      refine ae_of_all _ fun t ht ↦ hFbound n hn t ?_
      rw [uIoc_of_le zero_le_one] at ht; exact Ioc_subset_Icc_self ht
    · refine ae_of_all _ fun t ht ↦ hlim t ?_
      rw [uIoc_of_le zero_le_one] at ht; exact Ioc_subset_Icc_self ht
  have hsmall : ∀ᶠ n in atTop,
      |(∫ t in (0 : ℝ)..1, F n t) - ∫ t in (0 : ℝ)..1, f t| ≤ 2 * ε := by
    have := (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1 hI)).2 (2 * ε) (by positivity)
    filter_upwards [this] with n hn
    rw [← Real.norm_eq_abs]; exact hn.le
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hn hn1
  have hint : IntervalIntegrable (F n) volume 0 1 := by
    refine (intervalIntegrable_const (c := M * C)).mono_fun (hFmeas n hn1).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun t ht ↦ ?_)
    rw [uIoc_of_le zero_le_one] at ht
    exact (hFbound n hn1 t (Ioc_subset_Icc_self ht)).trans (Real.le_norm_self _)
  have hftc : χ n 1 - χ n 0 = ∫ t in (0 : ℝ)..1, (n : ℝ) ^ (D + 1) / 2 * F n t :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv' n hn1 t)
      (hint.const_mul _)).symm
  rw [intervalIntegral.integral_const_mul] at hftc
  have hχ1 : χ n 1 = chiGram W₁ dV n (fun a ↦ (e n a : Fin A.n → X → ℂ)) := by
    simp [χ, chiGram, gram, Weight.lerp]
  have hχ0 : χ n 0 = chiGram W₀ dV n (fun a ↦ (e n a : Fin A.n → X → ℂ)) := by
    simp [χ, chiGram, gram, Weight.lerp]
  rw [hχ1, hχ0] at hftc
  change |chiGram W₁ dV n (fun a ↦ (e n a : Fin A.n → X → ℂ)) -
      chiGram W₀ dV n (fun a ↦ (e n a : Fin A.n → X → ℂ)) -
      (n : ℝ) ^ (D + 1) / 2 * ∫ t in (0 : ℝ)..1, f t| ≤ ε * (n : ℝ) ^ (D + 1)
  rw [hftc, ← mul_sub, abs_mul, abs_of_pos (by positivity)]
  calc (n : ℝ) ^ (D + 1) / 2 * |(∫ t in (0 : ℝ)..1, F n t) - ∫ t in (0 : ℝ)..1, f t|
      ≤ (n : ℝ) ^ (D + 1) / 2 * (2 * ε) := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = ε * (n : ℝ) ^ (D + 1) := by ring

end MetricChange

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUniformBergmanBound
section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.UnifBergmanLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}

theorem le_l2NormSq_of_chart [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (W : Weight L)
    (dV : SmoothVolume A) {n : ℕ} {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n) (j : Fin A.n)
    {B : Set (Fin D → ℂ)} (hB : MeasurableSet B) (hBt : B ⊆ (A.chart j).target) {c : ℝ}
    (hc : 0 ≤ c) (hdens : ∀ y ∈ B, c ≤ dV.dens j y) :
    c * ∫ y in B, ‖s j ((A.chart j).symm y)‖ ^ 2 *
        Real.exp (-(n : ℝ) * W.φ j ((A.chart j).symm y)) ≤ sectionL2NormSq W dV n s := by
  have := dV.isProb
  set P := ptNormSq W n s with hPdef
  have hPc : Continuous P := continuous_ptNormSq W hs
  have hP0 : ∀ x, 0 ≤ P x := ptNormSq_nonneg W n s
  have hPi : Integrable P dV.μ := integrable_ptNormSq W dV hs
  have hl0 : 0 ≤ sectionL2NormSq W dV n s := integral_nonneg hP0
  set h : (Fin D → ℂ) → ℝ := fun y => ‖s j ((A.chart j).symm y)‖ ^ 2 *
    Real.exp (-(n : ℝ) * W.φ j ((A.chart j).symm y)) with hh
  have hPh : ∀ y ∈ B, P ((A.chart j).symm y) = h y := fun y hy =>
    ptNormSq_eq_of_mem W hs j ((A.chart j).map_target (hBt hy))
  have hh0 : ∀ y, 0 ≤ h y := fun y => by rw [hh]; positivity
  rw [← integral_const_mul]
  by_cases hi : Integrable (fun y => c * h y) (volume.restrict B)
  swap
  · rw [integral_undef hi]; exact hl0
  rw [← ENNReal.ofReal_le_ofReal_iff hl0, ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun y => mul_nonneg hc (hh0 y)), sectionL2NormSq,
    ofReal_integral_eq_lintegral_ofReal hPi (ae_of_all _ hP0)]
  calc ∫⁻ y in B, ENNReal.ofReal (c * h y)
      ≤ ∫⁻ y in B, ENNReal.ofReal (P ((A.chart j).symm y)) * ENNReal.ofReal (dV.dens j y) := by
        refine setLIntegral_mono' hB fun y hy => ?_
        rw [hPh y hy, ← ENNReal.ofReal_mul (hh0 y), mul_comm c]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hdens y hy) (hh0 y))
    _ ≤ ∫⁻ y in (A.chart j).target, ENNReal.ofReal (P ((A.chart j).symm y)) *
          ENNReal.ofReal (dV.dens j y) := lintegral_mono_set hBt
    _ = ∫⁻ x in (A.chart j).source, ENNReal.ofReal (P x) ∂dV.μ :=
        (dV.chart_lintegral j _ hPc.measurable.ennreal_ofReal).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal (P x) ∂dV.μ := setLIntegral_le_lintegral _ _

lemma setIntegral_closedBall_add (y : Fin D → ℂ) (ρ : ℝ) (H : (Fin D → ℂ) → ℝ) :
    ∫ z in Metric.closedBall (0 : Fin D → ℂ) ρ, H (y + z) =
      ∫ w in Metric.closedBall y ρ, H w := by
  rw [← integral_indicator Metric.isClosed_closedBall.measurableSet,
    ← integral_indicator Metric.isClosed_closedBall.measurableSet]
  have e : (Metric.closedBall (0 : Fin D → ℂ) ρ).indicator (fun z => H (y + z)) =
      fun z => (Metric.closedBall y ρ).indicator H (y + z) := by
    funext z
    simp [Set.indicator, Metric.mem_closedBall, dist_eq_norm]
  rw [e, integral_add_left_eq_self]

theorem gauss_local (hP : PolydiscSubmean.Statement) {n : ℕ} (hn : 0 < n) {r M : ℝ} (hr : 0 < r)
    (hM : 0 ≤ M) {y : Fin D → ℂ} {F : (Fin D → ℂ) → ℂ} {ψ : (Fin D → ℂ) → ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall y r)) (hψ : ContinuousOn ψ (Metric.closedBall y r))
    (ℓ : (Fin D → ℂ) →L[ℝ] ℝ)
    (hT : ∀ z : Fin D → ℂ, ‖z‖ ≤ r → ψ (y + z) ≤ ψ y + ℓ z + M * ∑ i, ‖z i‖ ^ 2) :
    ‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ((n : ℝ) ^ D)⁻¹ * gaussDiscMass M r ^ D ≤
      ∫ w in Metric.closedBall y (r / Real.sqrt n), ‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w) := by
  set ρ := r / Real.sqrt n with hρ
  have hsq : 1 ≤ Real.sqrt n := Real.one_le_sqrt.2 (by exact_mod_cast hn)
  have hρr : ρ ≤ r := div_le_self hr.le hsq
  have hρ0 : 0 ≤ ρ := div_nonneg hr.le (Real.sqrt_nonneg _)
  set ℓc : StrongDual ℂ (Fin D → ℂ) := StrongDual.extendRCLike ℓ with hℓc
  have hre : ∀ z, (ℓc z).re = ℓ z := fun z => by
    rw [hℓc]; exact StrongDual.re_extendRCLike_apply (𝕜 := ℂ) ℓ z
  set f : (Fin D → ℂ) → ℂ := fun z => F (y + z) * Complex.exp (-(n : ℂ) * ℓc z / 2) with hf
  have hyz : ∀ z : Fin D → ℂ, ‖z‖ ≤ r → y + z ∈ Metric.closedBall y r := fun z hz => by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hfa : AnalyticOnNhd ℂ f (Metric.closedBall 0 (r / Real.sqrt n)) := by
    intro z hz
    have hz' : ‖z‖ ≤ r := (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz : ‖z‖ ≤ ρ).trans hρr
    have h1 : AnalyticAt ℂ (fun z : Fin D → ℂ => F (y + z)) z :=
      (hF (y + z) (hyz z hz')).comp (analyticAt_const.add analyticAt_id)
    have h2 : AnalyticAt ℂ (fun z : Fin D → ℂ => Complex.exp (-(n : ℂ) * ℓc z / 2)) z :=
      ((analyticAt_const.mul (ℓc.analyticAt z)).div_const).cexp
    exact h1.mul h2
  have hnorm : ∀ z, ‖f z‖ ^ 2 = ‖F (y + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ℓ z) := fun z => by
    have : (-(n : ℂ) * ℓc z / 2).re = -(n : ℝ) * ℓ z / 2 := by
      rw [← hre z]; simp [Complex.mul_re]
    rw [hf, norm_mul, Complex.norm_exp, this, mul_pow, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  have hf0 : f 0 = F y := by simp [hf]
  have key := hP D n (fun _ => M) r f hn hr (fun _ => hM) hfa
  rw [hf0, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at key

  set H : (Fin D → ℂ) → ℝ := fun w => ‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w) with hH
  have hHc : ContinuousOn H (Metric.closedBall y r) := by
    refine (hF.continuousOn.norm.pow 2).mul ?_
    exact (continuousOn_const.mul hψ).rexp
  have hHi : IntegrableOn (fun z => Real.exp ((n : ℝ) * ψ y) * H (y + z))
      (Metric.closedBall (0 : Fin D → ℂ) ρ) := by
    refine ContinuousOn.integrableOn_compact (isCompact_closedBall _ _) ?_
    refine continuousOn_const.mul (hHc.comp (continuousOn_const.add continuousOn_id) ?_)
    intro z hz
    exact hyz z ((by simpa [Metric.mem_closedBall, dist_eq_norm] using hz : ‖z‖ ≤ ρ).trans hρr)
  have hmono : ∫ z in Metric.closedBall (0 : Fin D → ℂ) ρ,
      ‖f z‖ ^ 2 * Real.exp (-(n : ℝ) * ∑ j, M * ‖z j‖ ^ 2) ≤
      ∫ z in Metric.closedBall (0 : Fin D → ℂ) ρ, Real.exp ((n : ℝ) * ψ y) * H (y + z) := by
    refine integral_mono_of_nonneg (ae_of_all _ fun z => by positivity) hHi ?_
    refine (ae_restrict_iff' Metric.isClosed_closedBall.measurableSet).2 (ae_of_all _ fun z hz => ?_)
    have hz' : ‖z‖ ≤ r := (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz : ‖z‖ ≤ ρ).trans hρr
    have hTz := hT z hz'
    dsimp only
    rw [hnorm, hH]
    dsimp only
    rw [mul_assoc, ← Real.exp_add, mul_left_comm, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    rw [← Finset.mul_sum]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_le_mul_of_nonneg_left hTz hn0]
  rw [setIntegral_closedBall_add y ρ (fun w => Real.exp ((n : ℝ) * ψ y) * H w),
    integral_const_mul] at hmono
  have hchain := key.trans hmono
  have he : Real.exp (-(n : ℝ) * ψ y) * Real.exp ((n : ℝ) * ψ y) = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ((n : ℝ) ^ D)⁻¹ * gaussDiscMass M r ^ D
      = Real.exp (-(n : ℝ) * ψ y) * (‖F y‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * gaussDiscMass M r ^ D) := by
        ring
    _ ≤ Real.exp (-(n : ℝ) * ψ y) * (Real.exp ((n : ℝ) * ψ y) *
          ∫ w in Metric.closedBall y ρ, H w) :=
        mul_le_mul_of_nonneg_left hchain (Real.exp_pos _).le
    _ = ∫ w in Metric.closedBall y ρ, H w := by rw [← mul_assoc, he, one_mul]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights

noncomputable section

lemma gaussDiscMass_pos {lam R : ℝ} (hlam : 0 ≤ lam) (hR : 0 < R) : 0 < gaussDiscMass lam R := by
  unfold gaussDiscMass
  split_ifs with h
  · positivity
  · have hl : 0 < lam := lt_of_le_of_ne hlam (Ne.symm h)
    have : Real.exp (-lam * R ^ 2) < 1 :=
      (Real.exp_lt_exp.2 (by nlinarith [sq_pos_of_pos hR] : -lam * R ^ 2 < 0)).trans_eq Real.exp_zero
    have : 0 < 1 - Real.exp (-lam * R ^ 2) := by linarith
    positivity

theorem UniformBergmanBound.proof (hP : PolydiscSubmean.Statement)
    (hC : ChartTaylorCover.Statement) : UniformBergmanBound.Statement := by
  intro D X _ _ _ _ _ A L W₀ W₁ dV _ _
  obtain ⟨r, hr, M, c, hc, hcov⟩ := hC A L W₀ W₁ dV
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hI : 0 < gaussDiscMass M' r := gaussDiscMass_pos hM'0 hr
  have hK : 0 < c * gaussDiscMass M' r ^ D := by positivity
  refine ⟨(c * gaussDiscMass M' r ^ D)⁻¹, fun n hn t ht V _ hV x => ?_⟩
  have hn0 : 0 < n := hn
  have hnD : 0 < (n : ℝ) ^ D := by positivity
  obtain ⟨j, hxj, hball, hdens, hW⟩ := hcov x
  obtain ⟨ℓ₀, h₀⟩ := hW W₀ (by simp)
  obtain ⟨ℓ₁, h₁⟩ := hW W₁ (by simp)
  set e := A.chart j
  set y := e x
  set ψ : (Fin D → ℂ) → ℝ := (W₀.lerp W₁ t).φ j ∘ e.symm with hψ
  have hψy : ψ y = (W₀.lerp W₁ t).φ j x := by simp [hψ, y, e.left_inv hxj]
  have hsub : Metric.closedBall y r ⊆ e.target ∩ e.symm ⁻¹' e.source :=
    fun w hw => ⟨hball hw, e.map_target (hball hw)⟩

  have hT : ∀ z : Fin D → ℂ, ‖z‖ ≤ r →
      ψ (y + z) ≤ ψ y + (ℓ₀ + t • (ℓ₁ - ℓ₀)) z + M' * ∑ i, ‖z i‖ ^ 2 := by
    intro z hz
    have a₀ := h₀ z hz
    have a₁ := h₁ z hz
    have hS : 0 ≤ ∑ i, ‖z i‖ ^ 2 := by positivity
    have hMM : M * ∑ i, ‖z i‖ ^ 2 ≤ M' * ∑ i, ‖z i‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hS
    rw [hψy]
    simp only [hψ, Function.comp, Weight.lerp, FunLike.coe_add,
      FunLike.coe_smul, FunLike.coe_sub, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
    nlinarith [mul_le_mul_of_nonneg_left a₀ ht1, mul_le_mul_of_nonneg_left a₁ ht0]

  refine ciSup_le fun s => ?_
  have hs : (s : Fin A.n → X → ℂ) ∈ L.sections n := hV s.2
  have hs' : _ ∧ _ ∧ _ := hs
  set F : (Fin D → ℂ) → ℂ := (s : Fin A.n → X → ℂ) j ∘ e.symm with hF
  have hFa : AnalyticOnNhd ℂ F (Metric.closedBall y r) := ((hs'.1 j) j).mono hsub
  have hψc : ContinuousOn ψ (Metric.closedBall y r) :=
    (((W₀.lerp W₁ t).smooth j) j).continuousOn.mono hsub
  have hloc := gauss_local hP hn0 hr hM'0 hFa hψc (ℓ₀ + t • (ℓ₁ - ℓ₀)) hT
  have hρr : r / Real.sqrt n ≤ r := div_le_self hr.le (Real.one_le_sqrt.2 (by exact_mod_cast hn))
  have hBr : Metric.closedBall y (r / Real.sqrt n) ⊆ Metric.closedBall y r :=
    Metric.closedBall_subset_closedBall hρr
  have hlow := le_l2NormSq_of_chart (W₀.lerp W₁ t) dV hs j
    Metric.isClosed_closedBall.measurableSet (hBr.trans hball) hc.le
    (fun w hw => hdens w (hBr hw))
  have hpt : ptNormSq (W₀.lerp W₁ t) n s x = ‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) := by
    rw [ptNormSq_eq_of_mem _ hs j hxj, hψy]
    simp [hF, y, e.left_inv hxj]
  have hmain : ptNormSq (W₀.lerp W₁ t) n s x * ((n : ℝ) ^ D)⁻¹ * gaussDiscMass M' r ^ D * c ≤
      sectionL2NormSq (W₀.lerp W₁ t) dV n s := by
    rw [hpt]
    calc _ = c * (‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ((n : ℝ) ^ D)⁻¹ *
          gaussDiscMass M' r ^ D) := by ring
      _ ≤ c * ∫ w in Metric.closedBall y (r / Real.sqrt n), ‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w) :=
          mul_le_mul_of_nonneg_left hloc hc.le
      _ = _ := rfl
      _ ≤ _ := hlow
  have hl0 : 0 ≤ sectionL2NormSq (W₀.lerp W₁ t) dV n s := sectionL2NormSq_nonneg _ _ _ _
  rcases hl0.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; positivity
  rw [div_le_iff₀ hpos]
  have hp0 : 0 ≤ ptNormSq (W₀.lerp W₁ t) n s x := ptNormSq_nonneg _ _ _ _
  calc ptNormSq (W₀.lerp W₁ t) n s x
      = (c * gaussDiscMass M' r ^ D)⁻¹ * (n : ℝ) ^ D *
          (ptNormSq (W₀.lerp W₁ t) n s x * ((n : ℝ) ^ D)⁻¹ * gaussDiscMass M' r ^ D * c) := by
        field_simp
    _ ≤ (c * gaussDiscMass M' r ^ D)⁻¹ * (n : ℝ) ^ D * sectionL2NormSq (W₀.lerp W₁ t) dV n s :=
        mul_le_mul_of_nonneg_left hmain (by positivity)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedKleimanLow
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem MixedKleimanLow.exists_monomial {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (hP : P.IsPrime) (hrel : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant P) (a : K → ℕ) :
    ∃ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = a k) ∧ (monomial μ 1 : MRing ι) ∉ P ∧
      ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (monomial μ 1 : MRing ι) a := by
  classical
  choose c hc using hrel
  let μ : (Σ k, ι k) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun p => if p.2 = c p.1 then a p.1 else 0
  have hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = a k := fun k => by simp [μ]
  refine ⟨μ, hμ, fun hmem => ?_, fun m hm k => ?_⟩
  · rw [monomial_eq, map_one, one_mul, Finsupp.prod, hP.prod_mem_iff] at hmem
    obtain ⟨p, hp, hXp⟩ := hmem
    have hp2 : p.2 = c p.1 := by
      by_contra h
      exact (Finsupp.mem_support_iff.mp hp) (by simp [μ, h])
    obtain ⟨k, i⟩ := p
    obtain rfl : i = c k := hp2
    exact hc k (hP.mem_of_pow_mem _ hXp)
  · rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
    exact hμ k

theorem MixedKleimanLow.proof (hI : IntegralAgainstPositive.Statement)
    (hK : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefIntersectionNonneg) : MixedKleimanLow.Statement := by
  classical
  intro d hd K _ ι _ P P0 M A a II hII h1 hP hP0 hMs hMn hMc hMW hAa hAs hAb hAc j hj
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  change MixedKleiman.AtDim n at hd
  let L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun i => if (i : ℕ) < j then M else A
  have hsnoc : (fun i : Fin (n + 1) => if (i : ℕ) < j then M else A) = Fin.snoc L A := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [Fin.snoc_last, if_neg (by simp; omega)]
    · rw [Fin.snoc_castSucc]; rfl
  have hLs : ∀ i, IsSemipositiveRel P0 P (L i) := fun i => by
    simp only [L]; split_ifs <;> assumption
  obtain ⟨μ, hμ, hsP, hsh⟩ := MixedKleimanLow.exists_monomial P hP.2.1.1 hP.2.1.2.2 a
  have hAk : ∀ k, A.a k = a k := fun k => by rw [hAa]

  have hpts : ∀ {W : Ideal (MRing ι)}, P ≤ W → mcPts W ⊆ mcPts P := fun hPW z hz => ⟨hz.1, fun f hf => hz.2 f (hPW hf)⟩
  have hchar : ∀ W W' : Ideal (MRing ι), W ≤ W' → charOf W ≠ 0 → charOf W' ≠ 0 := by
    intro W W' hle hW hW'
    apply hW
    unfold charOf at hW' ⊢
    rw [Int.natAbs_eq_zero, ← Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero] at hW' ⊢
    exact le_bot_iff.mp (hW' ▸ Ideal.comap_mono hle)
  rw [hsnoc, (hII K ι).2.2 P n L A _ a hP (fun i => (hLs i).1) hAs.1 hAk hsh hsP]
  unfold recR
  refine sub_nonneg.mpr (le_trans ?_ (finsum_nonneg fun W => finsum_nonneg fun hW => ?_))
  ·
    refine hI K ι P P0 n L _ hP0 hLs fun z hz => ?_
    have hpos := A.pos z hz.1
    unfold logNorm
    refine Real.log_nonpos (div_nonneg (norm_nonneg _) hpos.le) ((div_le_one hpos).mpr ?_)
    rw [map_monomial, eval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    exact hAb z hz μ hμ
  · refine mul_nonneg (Nat.cast_nonneg _) ?_
    obtain ⟨hH, hV⟩ := divSuppArith K ι P n A _ W hP ⟨a, hAk, hsh, hsP⟩ hW
    have hPW : P ≤ W := le_trans le_sup_left hW.1.1.2
    split_ifs with hWh
    ·
      have hWv := hH hWh
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact absurd hWv (GroundTheory.Heights₂.Heights.Inter.arithVarZero K ι W)
      exact hd K ι W P0 M A a II hII hn hWv (hP0.trans hPW)
        ⟨hMs.1, fun z hz => hMs.2 z (hpts hPW hz)⟩ (fun W' h1 h2 => hMn W' h1 (hPW.trans h2)) hMc
        (fun W' h1 h2 => hMW W' h1 (hPW.trans h2)) hAa ⟨hAs.1, fun z hz => hAs.2 z (hpts hPW hz)⟩
        (fun z hz => hAb z (hpts hPW hz)) hAc j (by omega)
    ·
      by_cases hc : charOf W = 0
      · simp [hc]
      have hg : 0 ≤ geoNum n W (fun i => (L i).a) := by
        refine hK K ι W n _ (hV hWh).1 hc (hV hWh).2.2 fun i => ?_
        intro W' h1 h2 h3
        simp only [L]
        split_ifs
        · exact hMn W' h1 (hPW.trans h2) (hchar W W' h2 hc) h3
        · rw [hAa]
          exact ProjLine.nefOnFibres_of_nonneg W' _ (fun k => by positivity) W' h1 le_rfl (hchar W W' h2 hc) h3
      exact mul_nonneg (by exact_mod_cast hg) (Real.log_natCast_nonneg _)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end
