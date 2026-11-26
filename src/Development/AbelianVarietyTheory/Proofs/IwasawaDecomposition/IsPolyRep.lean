module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersSqrtNegThreeModFour
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix

namespace GlobalTheory.AlgWtHW

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def upt (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) : (L →+* ℂ) × Fin n × Fin n → ℂ :=
  fun p => X p.1 p.2.1 p.2.2

def IsUPt (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ σ, X σ * (X (ComplexEmbedding.conjugate σ))ᵀ = 1

def ratPt (γ₀ : Matrix (Fin n) (Fin n) L) : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ :=
  fun σ => γ₀.map σ

def evM {ι : Type} (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (x : (L →+* ℂ) × Fin n × Fin n → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => MvPolynomial.eval x (P i j)

def Agrees (a : AlgWt L n) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W)
    (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) : Prop :=
  ∀ (γ : GQ L n) (γ₀ : GL (Fin n) L),
    (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) →
    LinearMap.toMatrix b b (a.ρ γ) =
      fun i j => MvPolynomial.eval (fun p => p.1 ((γ₀ : Matrix _ _ L) p.2.1 p.2.2)) (P i j)

structure IsPolyRep {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) : Prop where
  one : Φ 1 = 1
  mul : ∀ A B, Φ (A * B) = Φ A * Φ B
  poly : ∀ i j, ∃ Q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, ∀ B : GL (Fin n) ℂ,
    Φ B i j = MvPolynomial.eval (Sum.elim (fun p => B.val p.1 p.2) (fun p => (B⁻¹).val p.1 p.2)) Q

def IsBEig {ι : Type} [Fintype ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (v : ι → ℂ) (lam : Fin n → ℤ) : Prop :=
  v ≠ 0 ∧ ∀ B : GL (Fin n) ℂ, B.val.BlockTriangular id → Φ B *ᵥ v = (∏ i, (B.val i i) ^ (lam i)) • v

def IsWtVec {ι : Type} [Fintype ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (μ : Fin n → ℤ) (w : ι → ℂ) : Prop :=
  ∀ D : GL (Fin n) ℂ, D.val.IsDiag → Φ D *ᵥ w = (∏ i, (D.val i i) ^ (μ i)) • w

def IsWt {ι : Type} [Fintype ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (μ : Fin n → ℤ) : Prop :=
  ∃ w : ι → ℂ, w ≠ 0 ∧ IsWtVec Φ μ w

def DomLE (μ lam : Fin n → ℤ) : Prop :=
  ∑ i, μ i = ∑ i, lam i ∧ ∀ k : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), μ i ≤
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), lam i

def Sle {ι : Type} [Fintype ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (lam : Fin n → ℤ) : Submodule ℂ (ι → ℂ) :=
  Submodule.span ℂ {w | ∃ ν, DomLE ν lam ∧ IsWtVec Φ ν w}

end GlobalTheory.AlgWtHW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceCompletionEquivUnique
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory

theorem _root_.GlobalTheory.splitPlace_completion_equiv_unique :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : _root_.ReciprocityTheory.Aut.SplitPlace L)
    (i i' : s.v.adicCompletion (NumberField.maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous i → Continuous i' →
    (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) → (∀ x : L, i' (s.i x) = algebraMap L (s.w.adicCompletion L) x) →
    i = i' := by
  intro L _ _ _ s i i' hi hi' h h'
  have hd := HeightOneSpectrum.denseRange_algebraMap (K := NumberField.maximalRealSubfield L) s.v
  have key : (i : _ → _) = i' := by
    refine hd.equalizer hi hi' (funext fun a => ?_)
    have ha : algebraMap (NumberField.maximalRealSubfield L) (s.v.adicCompletion (NumberField.maximalRealSubfield L)) a
        = s.i (algebraMap (NumberField.maximalRealSubfield L) L a) := (s.i.commutes a).symm
    simp only [Function.comp_apply, ha, h, h']
  exact RingEquiv.ext (congrFun key)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZeroSymmetry
open Filter Topology Complex GlobalTheory.Mem.An

namespace GlobalTheory.Mem.An

section
variable {q : ℕ}

theorem zsym_gammaFactor_ne_zero (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with h | h <;> rw [h.gammaFactor_def]
  · exact Gammaℝ_ne_zero_of_re_pos hs
  · exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

theorem zsym_differentiable_gammaFactor_inv (χ : DirichletCharacter ℂ q) :
    Differentiable ℂ (fun s => (χ.gammaFactor s)⁻¹) := by
  rcases χ.even_or_odd with h | h <;> simp only [h.gammaFactor_def]
  · exact differentiable_Gammaℝ_inv
  · exact differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)

variable [NeZero q]

theorem zsym_rootNumber_ne_zero {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    χ.rootNumber ≠ 0 := by
  intro h
  have h1 := hχ.completedLFunction_one_sub (-1)
  rw [h, mul_zero, zero_mul] at h1
  have h2 := χ.LFunction_eq_completed_div_gammaFactor (1 - -1) (Or.inl (by norm_num))
  rw [h1, zero_div] at h2
  exact χ.LFunction_ne_zero_of_one_le_re (Or.inr (by norm_num)) (by norm_num) h2

noncomputable def zsymFactor (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  (q : ℂ) ^ ((1 - s) - 1 / 2) * χ.rootNumber * (χ.gammaFactor s)⁻¹ / (χ⁻¹.gammaFactor (1 - s))⁻¹

theorem zsym_eq {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {s : ℂ} (h0 : 0 < s.re)
    (h1 : s.re < 1) : χ.LFunction s = zsymFactor χ s * χ⁻¹.LFunction (1 - s) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at h0
  have hs1 : 1 - s ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; subst h; simp at h1
  have h2 := hχ.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel] at h2
  have g1 := zsym_gammaFactor_ne_zero χ h0
  have g2 := zsym_gammaFactor_ne_zero χ⁻¹ (s := 1 - s) (by simp; linarith)
  rw [χ.LFunction_eq_completed_div_gammaFactor s (Or.inl hs0),
    χ⁻¹.LFunction_eq_completed_div_gammaFactor (1 - s) (Or.inl hs1), h2, zsymFactor]
  field_simp

theorem zsymFactor_ne_zero {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) : zsymFactor χ s ≠ 0 := by
  have g1 := zsym_gammaFactor_ne_zero χ h0
  have g2 := zsym_gammaFactor_ne_zero χ⁻¹ (s := 1 - s) (by simp; linarith)
  have g3 := zsym_rootNumber_ne_zero hχ
  have g4 : (q : ℂ) ^ ((1 - s) - 1 / 2) ≠ 0 := by
    simp [cpow_eq_zero_iff, NeZero.ne q]
  unfold zsymFactor
  exact div_ne_zero (mul_ne_zero (mul_ne_zero g4 g3) (inv_ne_zero g1)) (inv_ne_zero g2)

theorem zsymFactor_analyticAt (χ : DirichletCharacter ℂ q) {s : ℂ}
    (h1 : s.re < 1) : AnalyticAt ℂ (zsymFactor χ) s := by
  have g2 := zsym_gammaFactor_ne_zero χ⁻¹ (s := 1 - s) (by simp; linarith)
  have d1 : Differentiable ℂ (fun s : ℂ => (q : ℂ) ^ ((1 - s) - 1 / 2)) := by
    have : NeZero (q : ℂ) := ⟨by exact_mod_cast NeZero.ne q⟩
    fun_prop
  have d2 : Differentiable ℂ (fun s : ℂ => (χ⁻¹.gammaFactor (1 - s))⁻¹) :=
    (zsym_differentiable_gammaFactor_inv χ⁻¹).comp (differentiable_id.const_sub 1)
  have d3 := (d1.mul_const χ.rootNumber).mul (zsym_differentiable_gammaFactor_inv χ)
  exact (d3.analyticAt s).div (d2.analyticAt s) (inv_ne_zero g2)

theorem zsym_analyticAt_LFunction (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ χ.LFunction s := by
  refine DifferentiableOn.analyticAt (s := {1}ᶜ) (fun z hz => ?_)
    (isOpen_compl_singleton.mem_nhds hs)
  exact (χ.differentiableAt_LFunction z (Or.inl hz)).differentiableWithinAt

end

theorem zeros_symm_one_sub : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
      ((DirichletCharacter.LFunction χ ρ = 0 ↔ DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0) ∧
        zmult χ ρ = zmult χ⁻¹ (1 - ρ)) := by
  intro q _ χ hχ ρ h0 h1
  have hne := zsymFactor_ne_zero hχ h0 h1
  refine ⟨by rw [zsym_eq hχ h0 h1]; simp [hne], ?_⟩
  have hev : χ.LFunction =ᶠ[𝓝 ρ] zsymFactor χ * (χ⁻¹.LFunction ∘ fun s => 1 - s) := by
    have a : ∀ᶠ s : ℂ in 𝓝 ρ, 0 < s.re := (isOpen_lt continuous_const continuous_re).mem_nhds h0
    have b : ∀ᶠ s : ℂ in 𝓝 ρ, s.re < 1 := (isOpen_lt continuous_re continuous_const).mem_nhds h1
    filter_upwards [a, b] with s a b
    exact zsym_eq hχ a b
  have hρ : 1 - ρ ≠ 1 := by
    intro h; rw [sub_eq_self] at h; subst h; simp at h0
  have hL := zsym_analyticAt_LFunction χ⁻¹ hρ
  have hg : AnalyticAt ℂ (fun s : ℂ => 1 - s) ρ := by fun_prop
  have hf := zsymFactor_analyticAt χ h1
  unfold zmult analyticOrderNatAt
  congr 1
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hf (AnalyticAt.comp hL hg),
    hf.analyticOrderAt_eq_zero.2 hne, zero_add,
    analyticOrderAt_comp_of_deriv_ne_zero hg (by simp)]

end GlobalTheory.Mem.An
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FderivCompress
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift.VacBd

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
  {om : V → V → ℝ} {ρ : V → B →L[ℂ] B}

theorem orbit_lip (h : IsHeis om ρ) {f : B} (hf : Sm ρ f) : ∃ C : ℝ, ∀ z, ‖ρ z f - f‖ ≤ C * ‖z‖ := by
  have hd := (ContDiff.differentiable hf (by simp) 0).hasFDerivAt.isBigO_sub
  obtain ⟨C, hC0, hC⟩ := hd.exists_pos
  obtain ⟨δ, hδ, hC⟩ := Metric.eventually_nhds_iff.1 hC.bound
  refine ⟨C + 2 * ‖f‖ / δ, fun z => ?_⟩
  have h0 : 0 ≤ 2 * ‖f‖ / δ * ‖z‖ := by positivity
  have h1 : 0 ≤ C * ‖z‖ := by positivity
  rw [add_mul]
  by_cases hz : ‖z‖ < δ
  · have := hC (y := z) (by simpa using hz)
    simp only [h.1, sub_zero] at this
    linarith
  · have h2 : ‖ρ z f - f‖ ≤ 2 * ‖f‖ := by
      have := norm_sub_le (ρ z f) f
      rw [h.2.2.1] at this
      linarith
    have h3 : 2 * ‖f‖ ≤ 2 * ‖f‖ / δ * ‖z‖ := by
      calc 2 * ‖f‖ = 2 * ‖f‖ / δ * δ := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (not_lt.1 hz) (by positivity)
    linarith

theorem dH_bound [CompleteSpace B] (h : IsHeis om ρ) (T : B →L[ℂ] B) (hT : ∀ x, Sm ρ (T x)) :
    ∃ C : ℝ, ∀ z x, ‖dH ρ z (T x)‖ ≤ C * ‖z‖ * ‖x‖ := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun z : V => ((‖z‖ : ℂ)⁻¹) • ((ρ z).comp T - T)) (fun x => by
    obtain ⟨C, hC⟩ := orbit_lip h (hT x)
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z = 0
    · simp [hz]
    · have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        norm_smul, norm_inv, Complex.norm_real, norm_norm]
      rw [inv_mul_le_iff₀ hz', mul_comm]
      exact (hC z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hz'.le))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C, fun z x => ?_⟩
  have h1 : ‖fderiv ℝ (fun u => ρ u (T x)) 0‖ ≤ C * ‖x‖ := by
    refine (ContDiff.differentiable (hT x) (by simp) 0).hasFDerivAt.le_of_lip' (by positivity)
      (Filter.Eventually.of_forall fun w => ?_)
    by_cases hz : w = 0
    · simp [hz]
    · have hz' : 0 < ‖w‖ := norm_pos_iff.2 hz
      have := ContinuousLinearMap.le_of_opNorm_le _ (hC w) x
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        norm_smul, norm_inv, Complex.norm_real, norm_norm] at this
      rw [inv_mul_le_iff₀ hz', mul_comm] at this
      simpa only [h.1, sub_zero] using this
  have := ContinuousLinearMap.le_of_opNorm_le _ h1 z
  unfold dH
  linarith [mul_right_comm C ‖x‖ ‖z‖]

end General

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B}

set_option linter.unusedSectionVars false

theorem heis_dH (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (v w : V) :
    ρ w (dH ρ v f) = (π * I * (omJ J w v : ℂ)) • ρ w f + fderiv ℝ (fun u => ρ u f) w v := by
  have h1 := ((ρ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dH v hf)
  have h2 : HasDerivAt (fun t : ℝ => w + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
  have h3 : HasDerivAt (fun t : ℝ => ρ (w + t • v) f) (fderiv ℝ (fun u => ρ u f) w v) 0 :=
    (ContDiff.differentiable hf (by simp) w).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h2 (by simp)
  have h4 : HasDerivAt (fun t : ℝ => cexp ((π * I * (omJ J w v : ℂ)) * (t : ℂ))) (π * I * (omJ J w v : ℂ)) 0 := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).const_mul (π * I * (omJ J w v : ℂ))).cexp
  have h5 := h4.smul h3
  have e : ((ρ w).restrictScalars ℝ) ∘ (fun t : ℝ => ρ (t • v) f) =
      (fun t : ℝ => cexp ((π * I * (omJ J w v : ℂ)) * (t : ℂ))) • fun t : ℝ => ρ (w + t • v) f := by
    funext t
    simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars', h.2.1, Pi.smul_apply', omJ, map_smul,
      real_inner_smul_right]
    congr 2
    push_cast
    ring
  rw [e] at h1
  have := h1.unique h5
  simpa [add_comm] using this

theorem contDiff_omJ (v : V) : ContDiff ℝ ∞ fun w : V => (π * I * (omJ J w v : ℂ)) := by
  unfold omJ
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_id.inner ℝ contDiff_const))

theorem sm_dH (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (v : V) : Sm ρ (dH ρ v f) := by
  unfold Sm
  simp only [heis_dH h hf]
  exact ((contDiff_omJ v).smul hf).add
    ((ContDiff.fderiv_right (m := ∞) hf (by simp)).clm_apply contDiff_const)

theorem fderiv_compress (P : B →L[ℂ] B) {g y : B} (hg : Sm ρ g) {φ : V → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (e : ∀ w, P (ρ w g) = φ w • y) (w v : V) : P (fderiv ℝ (fun u => ρ u g) w v) = fderiv ℝ φ w v • y := by
  have h1 := (P.restrictScalars ℝ).hasFDerivAt.comp w (ContDiff.differentiable hg (by simp) w).hasFDerivAt
  have h2 := (hφ.differentiable (by simp) w).hasFDerivAt.smul_const y
  have e' : (P.restrictScalars ℝ) ∘ (fun u => ρ u g) = fun u => φ u • y := funext e
  rw [e'] at h1
  simpa using DFunLike.congr_fun (h1.unique h2) v

theorem vacuum_bound : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, (∃ C : ℝ, ∀ z x, ‖dH ρ z (proj h x)‖ ≤ C * ‖z‖ * ‖x‖) ∧ (∀ u v, ∃ C : ℝ, ∀ x, ‖dH ρ u (dH ρ v (proj h x))‖ ≤ C * ‖x‖) ∧ ∀ u v, ∃ lam : ℂ, ∀ x, proj h (dH ρ u (dH ρ v (proj h x))) = lam • proj h x := by
  intro V _ _ _ _ _ B _ _ _ J ρ hJ h
  have hs : ∀ x, Sm ρ (proj h x) := fun x => (Osc.good_proj hJ h x).sm hJ
  obtain ⟨C, hC⟩ := dH_bound h (proj h) hs
  refine ⟨⟨C, hC⟩, fun u v => ?_, fun u v => ?_⟩
  · let T : B →L[ℂ] B := LinearMap.mkContinuous
      { toFun := fun x => dH ρ v (proj h x)
        map_add' := fun x y => by rw [map_add (f := _), dH_add v (hs x) (hs y)]
        map_smul' := fun a x => by rw [map_smul, dH_smul v a (hs x), RingHom.id_apply] } (C * ‖v‖) (hC v)
    obtain ⟨D, hD⟩ := dH_bound h T fun x => sm_dH h (hs x) v
    exact ⟨D * ‖u‖, hD u⟩
  · have hg : ContDiff ℝ ∞ (gau : V → ℂ) := contDiff_gau
    have hφ : ContDiff ℝ ∞ fun w : V => (π * I * (omJ J w v : ℂ)) * gau w + fderiv ℝ gau w v :=
      ((contDiff_omJ v).mul hg).add ((ContDiff.fderiv_right (m := ∞) hg (by simp)).clm_apply contDiff_const)
    refine ⟨_, fun x => fderiv_compress (proj h) (sm_dH h (hs x) v) hφ (fun w => ?_) 0 u⟩
    rw [heis_dH h (hs x), map_add (f := _), map_smul, proj_heis_proj hJ h,
      fderiv_compress (proj h) (hs x) hg (fun w => proj_heis_proj hJ h w x), add_smul, mul_smul _ (gau w)]

end GlobalTheory.Mem.Lift.VacBd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneModEqOneAndOfDvd
namespace GlobalTheory.Mem.An

theorem _root_.GlobalTheory.Mem.An.normOne_modEq_one_and_of_dvd :
    ∀ d M p : ℕ, d % 4 = 3 → _root_.GlobalTheory.Mem.An.NormOne d M p →
      p ≡ 1 [MOD M] ∧ ∀ M' : ℕ, M' ∣ M → _root_.GlobalTheory.Mem.An.NormOne d M' p := by
  intro d M p hd h
  obtain ⟨A, B, hAB, hB, hA⟩ := h
  refine ⟨?_, fun M' hM' => ⟨A, B, hAB, (Int.natCast_dvd_natCast.mpr hM').trans hB,
    (mul_dvd_mul_left 2 (Int.natCast_dvd_natCast.mpr hM')).trans hA⟩⟩
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨k, hk⟩ := hA
  have hdq : (d : ℤ) = 4 * (d / 4 : ℕ) + 3 := by omega
  have hA' : A = 2 + M * b + 2 * M * k := by linear_combination hk
  have key : (4 : ℤ) * (p - 1) =
      4 * (M * (b + 2 * k + M * (((d / 4 : ℕ) + 1) * b ^ 2 + b * k + k ^ 2))) := by
    rw [hA', hdq] at hAB
    linear_combination -hAB
  have key' : (p : ℤ) - 1 = M * (b + 2 * k + M * (((d / 4 : ℕ) + 1) * b ^ 2 + b * k + k ^ 2)) := by
    linarith
  exact (Nat.modEq_iff_dvd.mpr ⟨_, key'⟩).symm

end GlobalTheory.Mem.An
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubsingletonJacquetIff
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.CuspEntries

theorem blk_two_stdSum {r t N : ℕ} (h : r + t = N) (a : Fin N) :
    blk (two (stdSum h)) a = decide (r ≤ (a : ℕ)) := by
  obtain ⟨a, rfl⟩ := (stdSum h).surjective a
  rcases a with a | a
  · rw [← two_false, blk_apply, two_false]
    simp [stdSum]
  · rw [← two_true, blk_apply, two_true]
    simp [stdSum]

theorem mem_unipRad_two_stdSum {R : Type} [CommRing R] {r t N : ℕ} (h : r + t = N) (u : GL (Fin N) R) :
    u ∈ unipRad R (two (stdSum h)) ↔ ∀ a b : Fin N, ¬ ((a : ℕ) < r ∧ r ≤ (b : ℕ)) →
      (u : Matrix (Fin N) (Fin N) R) a b = (1 : Matrix (Fin N) (Fin N) R) a b := by
  rw [CuspMax.mem_unipRad_iff_entries]
  refine forall₂_congr fun a b => imp_congr_left (not_congr ?_)
  rw [blk_two_stdSum, blk_two_stdSum]
  by_cases h1 : r ≤ (a : ℕ) <;> by_cases h2 : r ≤ (b : ℕ) <;> simp [h1, h2] <;> omega

end GlobalTheory.CuspEntries
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsImagQuadIntegers
open NumberField Module

namespace GlobalTheory.Mem.ImagQuad

open QuadraticZeta

theorem exists_field_sq_eq_neg (d : ℕ) (hd : 0 < d) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (r : K),
      finrank ℚ K = 2 ∧ r ^ 2 = -(d : K) := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  set p : Polynomial ℚ := Polynomial.X ^ 2 + Polynomial.C (d : ℚ) with hp
  have hpdeg : p.natDegree = 2 := by
    rw [hp]; compute_degree!
  have hpmon : p.Monic := by
    rw [hp]; monicity!
  have hroot : ∀ x : ℚ, ¬ p.IsRoot x := by
    intro x hx
    simp only [hp, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hx
    nlinarith [sq_nonneg x]
  have hirr : Irreducible p :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hpdeg]; decide) hroot
  have : Fact (Irreducible p) := ⟨hirr⟩
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  have : FiniteDimensional ℚ (AdjoinRoot p) := pb.finite
  have : NumberField (AdjoinRoot p) := ⟨⟩
  refine ⟨AdjoinRoot p, inferInstance, inferInstance, AdjoinRoot.root p, ?_, ?_⟩
  · rw [pb.finrank, AdjoinRoot.powerBasis_dim, hpdeg]
  · have h := AdjoinRoot.eval₂_root p
    simp only [hp, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at h
    rw [eq_neg_iff_add_eq_zero, ← h]
    simp

theorem exists_imagQuad_integers : ∀ d : ℕ, d.Prime → d % 4 = 3 →
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (ω : 𝓞 K), IsTotallyComplex K ∧
      Module.finrank ℚ K = 2 ∧ discr K = -(d : ℤ) ∧ (2 * ω - 1) ^ 2 = -(d : 𝓞 K) ∧
      (∀ z : 𝓞 K, ∃ a b : ℤ, z = a + b * ω) ∧
      ∀ a b : ℤ, Algebra.norm ℤ ((a : 𝓞 K) + b * ω) * 4 = (2 * a + b) ^ 2 + d * b ^ 2 := by
  intro d hdp hd4
  obtain ⟨K, _, _, r, h2, hr⟩ := exists_field_sq_eq_neg d hdp.pos
  have hsq : Squarefree d := hdp.squarefree
  obtain ⟨w, bar, hw, -, hspan, hemb, -⟩ :=
    GlobalTheory.ringOfIntegers_sqrt_neg_three_mod_four d hsq hd4 K h2 r hr
  have hwr : 2 * (w : K) - 1 = r := by rw [hw]; ring
  have hcoe : algebraMap (𝓞 K) K (2 * w - 1) = r := by
    rw [← hwr]
    simp only [map_sub, map_mul, map_one, map_ofNat]
  have hw2 : (2 * w - 1) ^ 2 = -(d : 𝓞 K) := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, hcoe, hr, map_neg, map_natCast]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 4 * k := ⟨(d + 1) / 4, by omega⟩
  have hwsq : w * w = w - (k : 𝓞 K) := by
    have h4 : (4 : 𝓞 K) * (w * w - w + k) = 0 := by
      have : ((d : ℕ) : 𝓞 K) + 1 = 4 * (k : 𝓞 K) := by exact_mod_cast hk
      linear_combination hw2 - this
    have h4ne : (4 : 𝓞 K) ≠ 0 := by
      intro h
      have : ((4 : 𝓞 K) : K) = 0 := by rw [h]; simp
      norm_num at this
    have := (mul_eq_zero.mp h4).resolve_left h4ne
    linear_combination this
  have hli : LinearIndependent ℤ ![(1 : 𝓞 K), w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hK : (s : K) + t * (w : K) = 0 := by
      have := congrArg (fun z : 𝓞 K => (z : K)) hst
      simpa [zsmul_eq_mul] using this
    have ht : t = 0 := by
      by_contra ht
      have htK : (t : K) ≠ 0 := by exact_mod_cast ht
      set q : ℚ := -(2 * s + t) / t with hqdef
      have hrq : r = algebraMap ℚ K q := by
        simp only [hqdef, map_div₀, map_neg, map_add (f := _), map_mul, map_ofNat, map_intCast]
        field_simp
        linear_combination (2 : K) * hK + (-(t : K)) * hwr
      have hq : q ^ 2 = -(d : ℚ) := by
        apply (algebraMap ℚ K).injective
        rw [map_pow, ← hrq, hr]
        simp
      have hdpos : (0 : ℚ) < d := by exact_mod_cast hdp.pos
      nlinarith [sq_nonneg q]
    subst ht
    refine ⟨?_, rfl⟩
    have : (s : K) = 0 := by simpa using hK
    exact_mod_cast this
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range ![(1 : 𝓞 K), w]) := by
    intro z _
    obtain ⟨a, b, rfl⟩ := hspan z
    have hr' : Set.range ![(1 : 𝓞 K), w] = {1, w} := by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty]; rfl
    rw [hr', Submodule.mem_span_pair]
    exact ⟨a, b, by simp [zsmul_eq_mul]⟩
  let B := Basis.mk hli hsp
  have hB0 : B 0 = 1 := by simp [B]
  have hB1 : B 1 = w := by simp [B]
  have hrepr : ∀ s t : ℤ, B.repr ((s : 𝓞 K) + t * w) = Finsupp.single 0 s + Finsupp.single 1 t := by
    intro s t
    have : (s : 𝓞 K) + t * w = s • B 0 + t • B 1 := by
      rw [hB0, hB1]; simp [zsmul_eq_mul]
    rw [this, map_add (f := _), map_zsmul, map_zsmul, B.repr_self, B.repr_self]
    simp
  refine ⟨K, inferInstance, inferInstance, w, ?_, h2, ?_, hw2, hspan, ?_⟩
  · refine ⟨fun v => ?_⟩
    rw [InfinitePlace.isComplex_iff]
    exact (hemb v.embedding).1
  · exact GlobalTheory.discr_eq_neg_of_sq_eq h2 hsq hd4 hr
  · intro a b
    rw [Algebra.norm_eq_matrix_det B, Matrix.det_fin_two]
    have e00 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 0 0 = a := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hB0, mul_one, hrepr]; simp
    have e10 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 1 0 = b := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hB0, mul_one, hrepr]; simp
    have hx1 : ((a : 𝓞 K) + b * w) * w = ((-(b * k) : ℤ) : 𝓞 K) + ((a + b : ℤ) : 𝓞 K) * w := by
      push_cast
      linear_combination (b : 𝓞 K) * hwsq
    have e01 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 0 1 = -(b * k) := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hB1, hx1, hrepr]; simp
    have e11 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 1 1 = a + b := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hB1, hx1, hrepr]; simp
    rw [e00, e10, e01, e11]
    have hk' : (d : ℤ) + 1 = 4 * k := by exact_mod_cast hk
    linear_combination (-(b ^ 2) : ℤ) * hk'

end GlobalTheory.Mem.ImagQuad
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgHomEqOrConj
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

noncomputable section

namespace GlobalTheory.SplitPlaceExt

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem _root_.GlobalTheory.SplitPlaceExt.eq_of_w_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L]
    (s s' : _root_.ReciprocityTheory.Aut.SplitPlace L), s'.w = s.w → s' = s := by
  intro L _ _ _ s s' h
  have hv : s'.v = s.v := HeightOneSpectrum.ext (by rw [← s'.w_under, ← s.w_under, h])
  obtain ⟨v, i⟩ := s
  obtain ⟨v', i'⟩ := s'
  obtain rfl : v = v' := hv.symm
  have key : ∀ x : 𝓞 L, Valued.v (i' x) < 1 ↔ Valued.v (i x) < 1 := fun x =>
    Iff.of_eq (congrArg (fun P : HeightOneSpectrum (𝓞 L) => x ∈ P.asIdeal) h)
  obtain ⟨e, he1, he2⟩ := _root_.GlobalTheory.SplitSep.exists_sep (L := L) ⟨v, i⟩
  set c := i.comp (IsCMField.complexConj L).toAlgHom with hc
  have hce : c e = i (IsCMField.complexConj L e) := rfl
  have hic : i ≠ c := by
    intro hi
    have : Valued.v (i e) < 1 := by rw [hi, hce]; exact he2
    exact absurd he1 this.ne
  have hi'c : i' ≠ c := by
    intro hi
    have : Valued.v (i' e) < 1 := by rw [hi, hce]; exact he2
    exact absurd he1 ((key e).1 this).ne
  by_contra hne
  have hii' : i' ≠ i := fun hh => hne (by rw [hh])
  have hinj : Function.Injective ![i, c, i'] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  have h3 : Nat.card (Fin 3) ≤ _ := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h3
  have h2 := card_algHom_le_finrank (maximalRealSubfield L) L
    (HeightOneSpectrum.adicCompletion (maximalRealSubfield L) v)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two] at h2
  omega

end GlobalTheory.SplitPlaceExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceProjMemIntegersOfIntegral
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory

theorem _root_.GlobalTheory.splitPlace_proj_mem_integers_of_integral {L : Type} [Field L] [NumberField L] [IsCMField L]
    (s : _root_.ReciprocityTheory.Aut.SplitPlace L) {y : _root_.ReciprocityTheory.Aut.AL L} (hy : y ∈ _root_.ReciprocityTheory.Aut.ALint L) :
    SplitPlace.proj s y ∈ s.v.adicCompletionIntegers (NumberField.maximalRealSubfield L) := by
  have key : _root_.ReciprocityTheory.Aut.ALint L ≤
      (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring.comap (SplitPlace.proj s) := by
    unfold _root_.ReciprocityTheory.Aut.ALint
    rw [Subring.closure_le]
    rintro x (⟨b, rfl⟩ | ⟨a, ha, rfl⟩)
    · simp only [Subring.coe_comap, Set.mem_preimage, SetLike.mem_coe,
        ValuationSubring.mem_toSubring]
      simp only [_root_.ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact _root_.ReciprocityTheory.Aut.SplitPlace.split_le_one s b
    · simp only [Subring.coe_comap, Set.mem_preimage, SetLike.mem_coe,
        ValuationSubring.mem_toSubring]
      simp only [_root_.ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact ha s.v
  exact key hy

theorem _root_.GlobalTheory.splitPlace_loc_congr_one :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : _root_.ReciprocityTheory.Aut.SplitPlace L) (N : ℕ) (x : _root_.Formalism.AUTREP.GAf L n),
    _root_.Formalism.L2.NG.Cong L n N x →
    ∀ i j, Valued.v (((SplitPlace.loc s n x : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j -
        (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j) ≤
      Valued.v ((N : s.v.adicCompletion (NumberField.maximalRealSubfield L))) := by
  intro L _ _ _ n s N x hx i j
  obtain ⟨y, hy, hxy⟩ := hx.2 i j
  have hentry : ((SplitPlace.loc s n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
      Matrix (Fin n) (Fin n) _) i j -
        (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j
      = (N : s.v.adicCompletion (maximalRealSubfield L)) * SplitPlace.proj s y := by
    have h1 : SplitPlace.proj s ((1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) i j) =
        (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j := by
      rcases eq_or_ne i j with rfl | hij
      · simp
      · simp [Matrix.one_apply_ne hij]
    rw [← h1, ← map_natCast (SplitPlace.proj s) N, ← map_mul, ← hxy, map_sub]
    rfl
  rw [hentry, map_mul]
  have hle : Valued.v (SplitPlace.proj s y) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1
      (_root_.GlobalTheory.splitPlace_proj_mem_integers_of_integral s hy)
  exact mul_le_of_le_one_right' hle

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FderivEqQuadComm
noncomputable section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift

theorem IsQuadOf.apply_vec {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
    [NormedSpace ℂ B] {om : V → V → ℝ} {X : V → V} {κ : Type} [Fintype κ] {c : κ → ℂ} {p q : κ → V}
    (h : IsQuadOf om X c p q) (L : V →ₗ[ℝ] B) (v : V) :
    (2 * π * I : ℂ) • ∑ i, c i • ((om (q i) v : ℂ) • L (p i) + (om (p i) v : ℂ) • L (q i)) = L (X v) := by
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)]
  intro φ
  have := h ((φ.restrictScalars ℝ).toLinearMap ∘ₗ L) v
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [map_sum, ← mul_add] using this

theorem fderiv_eq_quad_comm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → IsHeis (fun x y => om x y) ρ → ∀ (X : V → V) (κ : Type) [Fintype κ] (c : κ → ℂ) (p q : κ → V), IsQuadOf (fun x y => om x y) X c p q → ∀ f, Sm ρ f → ∀ w, fderiv ℝ (fun u => ρ u f) w (X w) = quad ρ c p q (ρ w f) - ρ w (quad ρ c p q f) := by
  intro V _ _ B _ _ om ρ h0 hH X κ _ c p q hQ f hf w
  have C := GlobalTheory.Mem.Lift.DCalc.dH_calculus V B om ρ h0 hH
  obtain ⟨h1, h2, h3, h4, -⟩ := C f hf
  have skew : om w (X w) = - om (X w) w := by
    have := h0 (w + X w)
    simp only [map_add (f := _), _root_.add_apply, h0] at this
    linarith
  have key : ∀ u v, dH ρ u (dH ρ v (ρ w f)) = ρ w (dH ρ u (dH ρ v f))
      + (2 * π * I : ℂ) • ρ w ((om v w : ℂ) • dH ρ u f + (om u w : ℂ) • dH ρ v f)
      + ((2 * π * I : ℂ) * ((2 * π * I : ℂ) * ((om v w : ℂ) * (om u w : ℂ)))) • ρ w f := by
    intro u v
    obtain ⟨-, g2, -, g4, -⟩ := C _ (h1 v)
    have hs : Sm ρ ((2 * π * I * (om v w : ℂ)) • ρ w f) := (smS ρ).smul_mem _ (h2 w)
    rw [h4 v w, dH_add u (g2 w) hs, dH_smul u _ (h2 w), g4 u w, h4 u w]
    simp only [map_add (f := _), map_smul]
    module
  have e1 := hQ.apply_vec (fderiv ℝ (fun u => ρ u f) 0).toLinearMap w
  have e1' : (2 * π * I : ℂ) • ∑ i, c i • ((om (q i) w : ℂ) • dH ρ (p i) f + (om (p i) w : ℂ) • dH ρ (q i) f)
      = dH ρ (X w) f := e1
  have e2 := hQ (Complex.ofRealCLM.toLinearMap ∘ₗ (om.flip w).toLinearMap) w
  have e2' : 2 * π * I * ∑ i, c i * ((om (q i) w : ℂ) * (om (p i) w : ℂ) + (om (p i) w : ℂ) * (om (q i) w : ℂ))
      = (om (X w) w : ℂ) := e2
  have e3 : ∑ i, c i * ((2 * π * I : ℂ) * ((2 * π * I : ℂ) * ((om (q i) w : ℂ) * (om (p i) w : ℂ))))
      = π * I * (om (X w) w : ℂ) := by
    rw [← e2', Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e4 : ∑ i, c i • (2 * π * I : ℂ) • ρ w ((om (q i) w : ℂ) • dH ρ (p i) f + (om (p i) w : ℂ) • dH ρ (q i) f)
      = ρ w (dH ρ (X w) f) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e1', map_smul, map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_comm]
  have e5 : quad ρ c p q (ρ w f) = ρ w (quad ρ c p q f) + ρ w (dH ρ (X w) f)
      + (π * I * (om (X w) w : ℂ)) • ρ w f := by
    rw [← e3, ← e4, Finset.sum_smul]
    unfold quad
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [key, smul_add, smul_add, map_smul, smul_smul (c i) _ (ρ w f)]
  rw [h3, e5, skew]
  push_cast
  module

end GlobalTheory.Mem.Lift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteChars
open IsDedekindDomain NumberField

namespace GlobalTheory.LevelChars

variable (L : Type) [Field L] [NumberField L]

def compAt (v : HeightOneSpectrum (𝓞 L)) (a : (AdeleRing (𝓞 L) L)ˣ) : v.adicCompletion L :=
  (a : AdeleRing (𝓞 L) L).2 v

theorem compAt_mul (v : HeightOneSpectrum (𝓞 L)) (a b : (AdeleRing (𝓞 L) L)ˣ) :
    compAt L v (a * b) = compAt L v a * compAt L v b := rfl

theorem compAt_one (v : HeightOneSpectrum (𝓞 L)) : compAt L v 1 = 1 := rfl

def levSub (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) : Subgroup (AdeleRing (𝓞 L) L)ˣ where
  carrier := {a | ∀ v, Valued.v (compAt L v a) = 1 ∧ (v ∈ S → Valued.v (compAt L v a - 1) ≤ WithZero.exp (-(N : ℤ)))}
  one_mem' := fun v => by
    refine ⟨by rw [compAt_one, map_one], fun _ => ?_⟩
    rw [compAt_one, sub_self, map_zero]
    exact zero_le
  mul_mem' := fun {a b} ha hb v => by
    rw [compAt_mul]
    refine ⟨by rw [map_mul, (ha v).1, (hb v).1, one_mul], fun hv => ?_⟩
    have e : compAt L v a * compAt L v b - 1 = compAt L v a * (compAt L v b - 1) + (compAt L v a - 1) := by ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ((ha v).2 hv))
    rw [map_mul, (ha v).1, one_mul]
    exact (hb v).2 hv
  inv_mem' := fun {a} ha v => by
    have h1 : compAt L v a * compAt L v a⁻¹ = 1 := by rw [← compAt_mul, mul_inv_cancel, compAt_one]
    have hv1 : Valued.v (compAt L v a⁻¹) = 1 := by
      have := congrArg Valued.v h1
      rwa [map_mul, (ha v).1, one_mul, map_one] at this
    refine ⟨hv1, fun hv => ?_⟩
    have e : compAt L v a⁻¹ - 1 = -(compAt L v a⁻¹ * (compAt L v a - 1)) := by
      linear_combination h1
    rw [e, Valuation.map_neg, map_mul, hv1, one_mul]
    exact (ha v).2 hv

end GlobalTheory.LevelChars

open IsDedekindDomain NumberField

namespace GlobalTheory.LevelChars

theorem finite_chars {G : Type} [CommGroup G] (H : Subgroup G) [H.FiniteIndex] :
    {ψ : G →* ℂˣ | H ≤ ψ.ker}.Finite := by
  classical
  have : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  have : NeZero (Nat.card (G ⧸ H)) := ⟨Nat.card_pos.ne'⟩
  let f : {ψ : G →* ℂˣ | H ≤ ψ.ker} → (G ⧸ H → rootsOfUnity (Nat.card (G ⧸ H)) ℂ) := fun ψ q =>
    ⟨QuotientGroup.lift H ψ.1 ψ.2 q, by
      rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one', map_one]⟩
  have hf : Function.Injective f := by
    rintro ⟨ψ, hψ⟩ ⟨ψ', hψ'⟩ h
    refine Subtype.ext (MonoidHom.ext fun g => ?_)
    have := congrArg (fun F => ((F (QuotientGroup.mk g) : rootsOfUnity _ ℂ) : ℂˣ)) h
    simpa [f] using this
  exact Set.finite_coe_iff.1 (Finite.of_injective f hf)

theorem heckeFin_of
    (hA : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) (ψ : Formalism.L2.Host.HChar L),
      (∀ k : Lˣ, ψ.inf k = 1) → (∀ v, v ∉ S → ψ.UnrAt v) → (∀ v ∈ S, ψ.LevelLe v N) → ∀ a ∈ levSub L S N, ψ.1 a = 1)
    (hC : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N).FiniteIndex) :
    ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ)
    (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
    {χ : Formalism.L2.Host.HChar L | χ.HasInf φ n ∧ (∀ v, v ∉ S → χ.UnrAt v) ∧ ∀ v ∈ S, χ.LevelLe v N}.Finite := by
  intro L _ _ I _ φ n S N hS
  classical
  rcases Set.eq_empty_or_nonempty {χ : Formalism.L2.Host.HChar L | χ.HasInf φ n ∧ (∀ v, v ∉ S → χ.UnrAt v) ∧
    ∀ v ∈ S, χ.LevelLe v N} with h | ⟨χ0, hχ0⟩
  · rw [h]; exact Set.finite_empty
  have := hC L S N hS
  refine ((finite_chars ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N)).preimage (f := fun χ : Formalism.L2.Host.HChar L => (χ * χ0⁻¹).1)
    (fun χ _ χ' _ h => mul_right_cancel (Subtype.ext h))).subset ?_
  intro χ hχ
  show _ ≤ MonoidHom.ker _
  refine sup_le ?_ fun a ha => MonoidHom.mem_ker.2 (hA L S N (χ * χ0⁻¹) (fun k => ?_) (fun v hv x hx => ?_) (fun v hv x hx hle => ?_) a ha)
  · rintro _ ⟨k, rfl⟩
    exact MonoidHom.mem_ker.2 ((χ * χ0⁻¹).2.2 k)
  · have e : χ.inf k = χ0.inf k := Units.ext ((hχ.1 k).trans (hχ0.1 k).symm)
    rw [Formalism.L2.Host.HChar.inf_mul, Formalism.L2.Host.HChar.inf_inv, e, mul_inv_cancel]
  · change χ.loc v x * (χ0.loc v x)⁻¹ = 1
    rw [hχ.2.1 v hv x hx, hχ0.2.1 v hv x hx, inv_one, one_mul]
  · change χ.loc v x * (χ0.loc v x)⁻¹ = 1
    rw [hχ.2.2 v hv x hx hle, hχ0.2.2 v hv x hx hle, inv_one, one_mul]

end GlobalTheory.LevelChars
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtLineDH
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift

theorem hasDerivAt_line_dH {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
    [NormedSpace ℂ B] (om : V →L[ℝ] V →L[ℝ] ℝ) {ρ : V → B →L[ℂ] B} (h0 : ∀ x, om x x = 0)
    (h : IsHeis (fun x y => om x y) ρ) (v : V) {f : B} (hf : Sm ρ f) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ρ (t • v) f) (ρ (s • v) (dH ρ v f)) s := by
  have e : (fun t : ℝ => ρ (t • v) f) = fun t : ℝ => ρ (s • v) (ρ ((t - s) • v) f) := by
    funext t
    rw [h.2.1, ← add_smul]
    simp [h0]
  have h1 : HasDerivAt (fun t : ℝ => ρ ((t - s) • v) f) (dH ρ v f) s := by
    have h2 : HasDerivAt (fun t : ℝ => ρ (t • v) f) (dH ρ v f) (s - s) := by
      rw [sub_self]; exact hasDerivAt_dH v hf
    exact h2.comp_sub_const s s
  rw [e]
  exact ((ρ (s • v)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1

theorem dH_integral : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → IsHeis (fun x y => om x y) ρ → ∀ (Y : Type) [MeasurableSpace Y] (ν : Measure Y) (F : Y → B), (∀ y, Sm ρ (F y)) → Integrable F ν → Sm ρ (∫ y, F y ∂ν) → ∀ v, Integrable (fun y => dH ρ v (F y)) ν → dH ρ v (∫ y, F y ∂ν) = ∫ y, dH ρ v (F y) ∂ν := by
  intro V _ _ B _ _ _ om ρ h0 h Y _ ν F hF hFi hS v hd
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (𝕜 := ℝ) (x₀ := (0 : ℝ)) (s := Set.univ)
    (F := fun (t : ℝ) y => ρ (t • v) (F y)) (F' := fun (t : ℝ) y => ρ (t • v) (dH ρ v (F y)))
    (bound := fun y => ‖dH ρ v (F y)‖) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => ((ρ (t • v)).integrable_comp hFi).aestronglyMeasurable)
    ((ρ _).integrable_comp hFi) ((ρ _).integrable_comp hd).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y t _ => (h.2.2.1 _ _).le) hd.norm
    (Filter.Eventually.of_forall fun y t _ => hasDerivAt_line_dH om h0 h v (hF y) t)).2
  simp only [zero_smul, h.1, ContinuousLinearMap.integral_comp_comm _ hFi] at key
  exact (hasDerivAt_dH v hS).unique key

end GlobalTheory.Mem.Lift
end
